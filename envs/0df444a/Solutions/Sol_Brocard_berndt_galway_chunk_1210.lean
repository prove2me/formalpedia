-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1210
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:47:04.969951+00:00
-- url     : https://prove2.me/submissions/6f666f20-ca13-454c-8d9f-a998d1117588

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 217446043 ≤ n < 217625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 217447293 1250 217446043 217446067
    0xa120b03030703030903110105010506040e0a0b1203040f060e0d2907030504170a08070e04111b0606150415121a0108070c020306060d14100c0206060d030c17 69
    0x84018180c0c0001e0f141c20000050580103040f1b10551000c87c002849258100004100d6a10562003044084d40380d00000034003074441a800405450002010400e800608180c4c02c0d40d207421a0085840490b4080400076601d4010321445000c2c486c0070380301c00d0000700d864030b50310350039104104800100040c0c40440e140031700d00802130b03070300c00d0445480000302801e081c02c000c5001302960700914001d00c8108864484290082c003542c3c2d0020300d43ca884a0142000c102060141c040c0b81d0700d081d4410004692801c28082045003d801c44a06008131074041c0c4d5260700300508440758030302d10b18481070b0800c400d00c10000a5010194070340010309041480d00d40300c5642500300d1303032840301c0c3c80e0b900050b110481e00150391014840742c00c500c2500d4003503041c0e081600043c0e1103600c06402c80c0d01c1403c4488020040108060580320341c44100425190441002c5080501520801d81000014010b0200048152074490b090000854240d0303154069140c0996420f0f1409480c0b01d0090b5600a090180c011007078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 217448543 1250 217447293 217447297
    0x50a0b09150a0f0315080604140c0a0303030212060102010501060512100f030501020901020c09010b090d050c030105090d030e060c0d0c0306180c0e24070822080616050a120b0303 78
    0xc100780d80c442501d0f0714540b00007400c4500200c0340c1004403d600004104400c00061040d41140d0044a10191030700c1c1310200311328081c40c10070110b0300301c1c01000300001419015030113004000b408a02052507640d65900481c00c9500902880b0041403041c440c0200100b100200d0560003903c201da108651a110000e4400c02c07011070784101d900c0e81d00001d107140700d540c0c103000d00400e0002c151740d903244950400101d00c10b40d0044400b0a03002d5400c140800c0c2c00d0103820401e00501c004050000c00040c1414007540307403070706201e100e80404a401e101c1a00740c0310348000b6003240f10780701d00c034070a40c00e085020003050084c0000300d03984001c040d103da202140904807680040c4c005088164001440d809a81014000d44030b182c550f02c2c40740304015480a404262031380300b04901d600c02995950794060b185860080c0f4001c0c0c0c0324074001c5507a403801750300190303034040e05080039145000111a42d035a02c024101d6960721440c0744010000b441803218005d034600441461741900d442180100e40d41004c00302080c51a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 217449793 1250 217448543 217448557
    0x301091112010606120b0310020f070c080d020a030804021809030c010f1b03090804120c030308130312050712050f07180b090906040902030a0f1b050a0b0915 69
    0x1800000d05400614200098034032031100c50000b440083c0c50020b0141180c07140106008035035854143d0000b40c1d5070140200329510344072a00c110b46941c1c021a507006036030040c840454020040c0c2801245180002400e5001280709500419050030b282c1d5080343c0110018104a8003d840004011007000c404000c5600c01c41d01c280040d6150107203442c40e1820344e06241d10f070071106454040c00c2c40507200c1034001000180001c0c240030440e2102c614191115100701e5004a00410f40b03045a6010014508600002c0b41c3c081d03500d5903c1500c400001480e01092444000c000c56030200307288409101039040240d111449040c1000c1507565042c405050f9a012160941c00d402c14404218205400400041e072071102203c0701c01c8028182284410248184030f08548a0b114000001740165181d4020400895025066643d840e40f01d01c3c08003005648000c040b1500d80440786110302c1e100d43c0a04040c00c80e41d00078490000130b4a0000c14501940c00710303984a0b08a08035009001c44809548010010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 217451043 1250 217449793 217449803
    0x80d031d0d0f031a030712031106040f1b0e04120e03010c020c0a0e0615090607120804061a062d0a0f080601080403091707090507050a1107050a12050c030109 69
    0x610a500c14003c0459010050054546840e01c032035040944000450400b0307101c5c8407600c012291060304003a00d040985c0c03600d00b0700038414141007201708140c081d00111b51500c901c40c401c18006224905070340e00b1140340a0358103422000c40c00200840c1201d580e10000c507400b410244070031041140404c1c00e4034181c0101c1805a0b02500c020402810101f400000520400381003003007500b4440700080e01c1f079a00310503054450001152403a09a9590021604110350003181c0798105070160902400c800301c2242c054444619211508000142c0c058401d071000c1002001d42e450700340c8202c440e2110006a03103d160f250301c0b5402d84142d004002c40010802c0100d80c0d19044400d1760142030007015440c00810080c1002011400c0c08002070300306184800381e50400d021403000c1c1d161002c20301e1400c2d00c6640f10800712030034101030001e0160044010b0100807070590715521008601104540d8a00451081a07000110104101728100b0300d1428503d02c035104000b40c45040c281d02d40000d00392805200c040d25 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 217452293 1250 217451043 217451057
    0x50904030f0e0a0b041d0f240d06060611010501081207031205090604050607020d050324220e160608180313050f0405090c060a02030f0c0c010f0504080d031d0d 70
    0x1042201401b000c540c4003072050210154904640b05612010300500001110000d40d4109820503807080e1511141c41030141c0b0a040010f014180b01d006444244074503000b00d0908080c07000641010b0003404d050700c0c0362a000304848160142000c0c0c940d48102c00580801861240c1000145564055140140714441c014121070034541007540c24502d01410340015135101d800c550320851342101c1503070783c80040c40124200e00c00d145081e090240b2200e40c2d0b0598070044421400c0b41d1403d1004d060007200c1003e620030018001e00721034160b510401840300303940c9460041c0c0c041048a218a140c1e5500c0812544a501d03120010644c3c0b03451900840550b4820700044141071280381080110150001012070302809039080002c0003e0301c2e6000c51303603102d0140340001082c9032118020401c46d1503400d92100c0b499665665130000a03150040722812034001825040b00d9403005206800f500c00b910402c5000c0e06915150f00001d40c0101521002d041d03004404d60380600039400305010701401c12120f500d17014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 217453543 1250 217452293 217452299
    0x30f040608060607032c030a06051f030b01030602030c040807030501061404060312030b0f100c02090a020f0307031a040501080307030909020a05041a0c01060b0406120501050904030f0e0a0b04 84
    0xd03044040040580b80569010303c02d03103005c03a0784940a108205000801c00706c2c18200d6141c0328540c48038040c01d460309885404d915808002c010b03030000c1e22407074040444051908509403040c555141e107110243c0aa40114010b01c042405540219008200c84696624040da16409241440260fa0096480d03940d50303c4200103400100303ca1680f00c1c02d0449040040d6425075807070031000300e040e0700c0c00c84c1090359403541510700d030316650000039011000a20b10000c03a6809c1c440280782c0c0e03200b51800c078052860302002c1200c055140c004c2c1d6204c0700b440c0030003604590f00c910b0114001d004501d184080f1004a50030b86559840c3e52181a0190a40c80069a83c074220b074140603181c08616844075815510420200403110303442801d8905440414000101205080c400e10f1054000c003481c844455180250008007211184003c1c400c0300c40702d88074443d10500c0040e411048030070910506800401c0c4170002000203100710010828007669040040107107012002060707201ca42c54104440c0d00c40300103028 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 217454793 1250 217453543 217453547
    0x91801080706110d0c060c02101104080106090902093903011401090b0906090a050402040b040503120301081207080c07180b19140d05030f0307031413020120030f0406 73
    0x520f14102d00f00b001003080c002e04044c01010300c410004090b0090342e03202248180c4520911008024155860083c13090700031341c200101060703010b445205d86540c13a0080018215056000301c51030103800034030000841da00e02400e0008032180d5010304500719280310025a44401da118000c1070800c440c00f00503200c0d81060003100c0d55040400130141840742860042040440350b900711078480c5010f41e506925003110801007491a02a038005580c8580046004220303c000d4102520403036408504a40300c4216401c0e180c0c1ca248001c1c040c03002d0b1500040c41012a134000c607030050440c140300d580f4061602444004080c08d10060f900080d105600b103040700341d12040c440c00b51603445134040b10000758401000f6044044200c0034440c3c0e01c4500c02c81c442156441d41e442d0a03452240d0742103002e03a0b0b42e4546480c00b140b03080e4411207205c1c010174075200d1200808002800045e1060a026416584541a42c1c0043d0b8502042c1804c00284080440b001c000c2032109202411442c561040156110f600301500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 217456043 1250 217454793 217454807
    0x60207050f1c140c091e180f25050a0e0a090f020904120f0207060225050603070c02150403020102031e09031501090f020307051615020a1101050f06030a0206091801080706 75
    0x107070741e0001c524849990300f41e511550a079400c01c40030031034005074400201043e8107105023400b42d4001070254000c111608a03007140c030068074441d13400040101a071aa81003140040c198000d04014840e02000601202840d42c003e0404501800100d40c200c28164005a580c00045804507084040c0316a00d002d12900065420f0f00c411850000d171000c2800c00000035a41c40f0a80401c200613800d070804864003010703582d0350720090540a041c00e0f1762403402c854090800760000d2012801110360114010042c00342000355426a6070590145140c4020440e0041203e1a184100d0b0400b04007000700d41259039080101c0f40d0004041ca000c04201d40c0340003e46412100ca024008102c540100b040110060f4007070121503940351030103004045602c0c070b030a0003150000c0b00780c09180c2e070520005048008607008512030011200d290000d000b02d0b03440360300c0e22000c188141d46c8240c01d40e200c04030300740051820102500c40a6800f600f88221200110b02c8021000401e134410079850b001003100348000c60380b00c85 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 217457293 1250 217456043 217456051
    0x4090b0312180103050c121e0108150f0a0b030118050f0102130e09030c010c1d0a0e01050d080904050411190302030d0c060f050103030e0a060207050f1c140c09 70
    0x1205a0816401c20b000041ca0300d11410000d04040e0358000089002e42c03004c091307800487e0090b04610741031400e0b1408a000c1c0d40034541042d07a6101d650000503241c4400502d14001c28102c5002280315100c01c00c103540040c2d000340c4009199030326403070452180e0f00d0074445d048038a001e882d28038150010078103000f410400502542500d07640100300c0030b524850a501003004a03100180e6115040d500d82c10024114000c1000400c425420850300c00861a441640c2e035028240c00725143e002e07010407404005070f06803588280c100c0c0840702c1c401044540740001e44120f285000700091850301c0240750000e422a0030444045078503241c1034107040c11a08100c03030412100b45603c81310704821419900041e540da501c1240c554104606c880c80c0c54201b14140d0002010500c7c809014070988d6103c1c13402828081c29501c003d4000c2450100c001112440001d035441210406403003c407019051000b44407851261038803d200342c442c581c007000006840400c0a500a51120000e00a6603a020080180c4801d000e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 217458543 1250 217457293 217457323
    0x170d06060305060d082101030507180213090f09060e071d0103110d0311061602011a0d14030f0301030f050c06030108030d0b010e060a17010819030e010e0604090b03 72
    0x1c00c1101c00c1d2250360014030702a8101c00d1083d115054000901160600d044089800002c101b000008201c0009243c03800d50301d60820300d0315030300080c01003002240140350b003080980e440810100305040c400d5202c42d4190f200c18801044200f2a178a85805485040d0322100441c0d11111382004283c004801001c41c14043d000c920b03009500d5078035408059001c0c0c840c2d0502c102c15201c41042010300406000381020142016140103182580380503c0494011180002550a1492102c4201220340e00c140c280f480c01802000803640c0c50311a2424030010f094441e0750f87c03100b0008900006440c0003d1402148651025030320b045107481c1150030700d500b040f401c40c003410043c001842520000710548114166001c00011140c11410040383d02e01010744440d80c00900019440084980c884c0b801c3d2561001200860360710799032114115a25034540f00c01c1890903564981800001f48944e00701140003405140442c100d568080c0010700d01d5109502600340030340d503903e6580003810705100440da401003c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 217459793 1250 217458543 217458551
    0x909010903021f0207060617060f01062106081e0c09010f051c0209070201140f1b1b010c030c020c011404050f0d06090308040c080c0625170d060603 65
    0xd541c002e5640d03035000b0701030000403070084440e100342c89555060b1100c02c1d82100040c0141c6640c0c0c0d110a0b459001200300281500880000804061000b49080d0403582c0076039420100400000740824090006184038941c15124040094035100c10851110b10078440158000074080350b2640615004a10b920140104040320041060b07000504140b02158402c0ea40081030030003070907000c108440142030081d401040d81003407108459055108441d030f42c592110300350f41a102c4c500d00e0f00140c1d43c09c0380c05c10f89a03000d0040249013101150003424101c039038601000181030950a0250a4550210241d00025a902c4840c00410740c1000800319014080c00d1210711101200f244040a105500809004980aa890b04100d0700c130702246440482c0c00c90070030090f034200c42c907000301310b044c0584050701c0800702d280d00414034070004151030002c0304004114034030b0003c1c841038007c82c44c000506440c0303040c80b0076100711000c94480e003010500d001041d1100c40c0da90642d007044500302c542d1070700510109807030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 217461043 1250 217459793 217459811
    0x601021c0f0f02010209030d030c030e010b0d080c0f0a051c110606040b030c0603041511040e070c11061c0f0c02070506030424060602010c031413050c100806090901 72
    0x80000c0c0d803048801480c200744620240ca600343c1c060306c80c1e80701054061051f408401481c41c0d26078401000303100181d030305000750303094030030058203a41ca26101c0b258003102d40340d503680000e1300c000010804050f07010b0980d1f5492001000c000d06241035400300fa10141c12040c0440024040d220b1b034801c08281d50700b0308072003092031441c20320380d10840101a075000e240d0f9002640200d650402c003003241810000c0001c1c2d035914042c80c01c420005070405003020f1642c00c1c00c040400302510142034505071784484500c14000c2c3d40e04a41101e0b8411408000d441c0400c0c20040303c10161600e07001410480702c0d41d84120401c1a805450a049810200102c000b03031380341c174000d40a039030703404502403084640440e4190740300c1e00c3c0d5050500540c11140c12004d40690310105101c040d1b04190000c40071070310203030020071240000d0b85041e800d4036241c0c0f0846065014200015062440ba0f240306450705009008841c03a080044000c00c1c00709400c0c140b44008207028504216662030210710311030744007030003100034000009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 217462293 1250 217461043 217461047
    0xa0c08040b0f09120c0304050406050301050603121305040f09030e09070f03020c1e150a02090109030f141204030204180b0f190c0309150501050a0b091909050601021c 73
    0x400680004004886a00401c90859040010394150341d003040480d5625441741c0e80b6155030342d000d4800e0724012410f202e0b0010f42c92406208540c410701d00900034000020a220345070b015540062000701c00420708a0000c40c00b500c880c071441c0380da10400310703001409242504000c0d00001c580f42c152817103801850204501160f00200006e2284141e082c0503072203c011502040c00e040d520b4030b8201e001c03659910141004c0000080103484202c8001c1040550307211040120268402c0c2c941d07080c00b00d000d000702040010001000e200382d00c2c1c01410304104619044000500700b0340c41724039046092002003018025480c1030310600200307031003900030020300645581d10074041e50001001e60003107040c032400181445801d01d148503007050442c1000c000c60300c00c12030060000c10317400340e003620100348400341006245918403801d41030320b20040254408a29019a190283c0c2c441c140241d0800311a8001c3d45403104614816005000030740004291454200002450803185541c101544200c007071058030829 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 217463543 1250 217462293 217462313
    0x5070e120d14091f020738090103020c2b0801030218041a040b01030606050f030a110301140108030a020123060904030c021002100f0b01270b030106080a0c0804 70
    0x102812030b44a4032068a030b0000f03501e07400d9120000100d0b9400030007014001d039003c9861010b585000440311143c0c201e80a0343c0800d040d032008042124020b042c1c3d14502e070440d4901a05014205140243c600428401c40e50b0404006842d86a581106c101d0185401c50350900c034440c001320546010b07241036141d50001071403120841c543c4c440c40d0150402140900502e000c1201c4881e201072054016801c20f850401c003010700c01d00c404e1364810314165007c5041d29054201350013507400140100010082d0b6280e0300909022046e250743e041d13594691403000c2c4041068242c1c02800480d02540d01c4065809004c0c1c20f5541010340000b0308141d55001e205850840081c15400c040b0950b040942c550b9a4a81034444501207400694081101281c00300441c0d800903418024602c600402e0000046c030010745800c1d25001c0001e5804102010b1400c11449183d04c59001c4000c038006040130503d0ba94150100c540e8000c1c1c2002c00010507010403c100030202c0c1c001c04100000615161406141c180c50701800ca03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 217464793 1250 217463543 217463567
    0xf0e0d09050103150b1605030c060f0a09110103050c04080106090608010605010305100e0c1e030403030b03030a020d080a110403030c0b0f010302150a031104080f06010503010606050a08041505070e120d 88
    0x10440106e00e03660352084916000080640c400110b9a0f00c4030360003d042ea1341c41c41141d030719640c600004001400c0885500070050701c0c41d805820f0008a04a0400640240c400102490000b4100388000100c07a1824000c03480203091840e0001040c0381881c12050a40d5600d40059051500309001d009100c1d860030352810880703080f00180541070302c0b10403480801c1d1084280f100c40031a0303404806210300041d0030065000e648207440c104000e5081ca401d01da2240611140040940c02880a58030180e00a0080c0c50340150070502c0003230303219101624030b4080e4005030800e1700003c080421890410011402458000001ca000644190702d990300040408104100820b4484030201c0c540c0300043c0241c110070030a4440d6007007aa151601d40e0f0200b0769604110780e00d00a60f01c00c81340001803904041c8105401e480890752610b160905184040d9101403010700102c0d4400104400e00c10502003e04c10f843c05161143c3c3c2e85c0780c0110541080000040300da08003054650000c942200d0b0868000d07019100c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 217466043 1250 217464793 217464809
    0xf071e090b03120a0e0306070809010e060702100e120c0303040b1024182c040503031501140406020114071706100c0f0f121e120f0e0d0905010315 64
    0x1503441983c04c202d4011901011781d640611841040c80344954201c1c20552043c04c80d4402040030b54440c000c1603580e41000c1d2001409600000211240c0980c180c01c4007103001e100d001102c1d481c421801c41c8007015481600314130010f41010040c44100080b602e10300d60000704c0a01140540c90510409200030302ca403c09001503810181000b202e018010f01162002e01c03080090701031b91f580c0d80c90000300945100710800032000c07000c9402507030301400b00700c1141c0100c0d0040e00a40c159030b078800748800620300c6000720906020800181c0c2c214036203400c00500280400ea4000f080e40b04800025110b0110064a84800e10113801c8005c0080c0c05d600d030219a01c07282c101c9140f003031000e0310740042e9018401d00724064526100b04c019030040c41524520120307494401c0521459401c80b0344001c4601c81109103800c0340c00e440c02043d071a6280c0c4680c03070000036a003100000281c2809800f2080049071324100e40c840d00e42e044010ba2900264124440e40d00610081c00d092004421750495040c1e00e5085005041c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 217467293 1250 217466043 217466047
    0x210020724110d020d0305060a0b160809060d020406030b0111031806040f090e070905090312061f020a0b0711030d0e07030602030403081b041a0703020f071e090b0312 73
    0x98481d10994905000c46000003d58200d01c07100312009403a40100041039011a0a2401040c0c03107052440d980c40441c2d505444040c1004241e410b0030840000c0142c0950f000c080520400d00305980300001010f150441c1c1c00c005070744900d04400a000c1d00c00d50041c042c1800f0b9076003d2030110110100440b0f81c00c0c02140111440340c07000d840000c3c402d0045400161000120b500f01003143c02203980141e1504100744200e030b90309540e1310b840b80207840c011204004207030010b200809400300000c07040d0790405170060203441c0310810b503549c580030984045a4400143e0169902c0024411a42d2a00d0341140441c502204103c1d0b00091f803e40d01d10070016080452039603544070f40940e00d800e0100c20003950340010305540ea03041900300100321881c142c0780d0b110605410b00c4c503040b0041044003100c0844000103800340e0072040c0b04201d452660400c1740d09900b5405035414640c0c801c0c0e0244074410290a031080c900c5856022044a40300e4100d054010320f1185240c0605080d6565000511070346d0f0002100d0029 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 217468543 1250 217467293 217467359
    0x30a0203040f081615020a0f0f020c06030a0b0909120316050f2212020d03030f1b082d160212030f010614030f01290d050402100207 58
    0x4200c0d6001100003401040f0080381d000c00d1440c1c404c001981250003004640031251442d0300d854128032583c045d0340e0110301c0d801481d03100c5034000c1880141c00441801170b02d07030048010bc08a8600d52048800201075592a050300d134451400104080d0003a0351000206100049107900d2441840003402c040039001154441180b0607206004403100d0b0f0189407100c6031141602c00c0c0300c2d8041061903206107a5044901c02c0441c3c2014800d10707016980341c005080714084e9107961000d800810903100b00c0d2260fa86c0324030819103408420202e412604c5060380d1603d410385050070f440244040740c1180683c04071890014400e000445c0c0c0c0744260800d01c940080c2c4854090814281c4c40e000c0c03c0c6081c0c664204002c003c00034030b110300c0d602d42e90407210301e0348426450201c4404880141e202c01c0b43d034114010860030051010741c01480e032503081c101d64511103402640d01e040a12081342c000034503940009454404000850a1120300079020000c1c6000a092280c14410300c0c00c190300100c0321070440d58003003031510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 217469793 1250 217468543 217468553
    0x17010e1003200319051c0c240c090305071406030606250308040203060c0309030d05040204060f08030304020418030801060c02010e090c0c01050c0906070303090507260d14030a020304 80
    0x801c0c0a1400030202e401c091600f000320309202c4d401d540b064500d40035080100701124050112005104844d945d40001a082c42d03450b6640301c8020f141d070311400d0100082003040d48841c0d200705054040d1548600d20681c0c07841c0341003842c2103500d820541004070020110790203600c490041d2608528100e88040c4c8071034221807030700007003164811004040c5c254048400103240e040304c50702d40614001c1d81a541c039a0b542001255440c40140c0d02003045520401035007041300c000e94400d07a00503200030b0000c500d007555101c0c50020500d5607040340420b80c00010600c070841c80c213842410003200307119420200121013500c001d0089601403040500340001c40071220210380c4074100c0592461300051842c042828200340c481002e810407003400c05150700e40008034482c0c080c507006603448050000d040a24229a83d68200c0181891032804c480610545001160b441c010b0040e480100c50041c005a40d40b14000b0f500c01e190071070014680d000d10090f000004512420300c0212503110f0041140076943c4d40b602d140c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 217471043 1250 217469793 217469843
    0xc0f02030111040f0e071707080702100609020c0f010b06040e150d060c020d09080c0f0303040b0f031f12080c0f070b0d2d0507020f010c17010e1003 65
    0x3042c110000980800d00c0340050f4038040a441c0318280d12070b002c0d681c03c00203550408842904450307558040740081c1c2068400e800c816441036451054401aa4844e888c7c40103a03101900f00c04011500454540d06000007040541c0f01c40000300c00920401102401144c0144a40e0044814403520080012101c0440e00781c020040c01014280f2000c103c13182c02c001c00181440503140f0014010008440e10341441402d5140c00c0d69206d10181200c2c80091381009061a5100017068041c00b0a22000580185130400381c5190110407a00705e40e40d1030b050445641000692044026400d400101808006055400d85103543d034003010955480c103420320224940440c01d0903150003032090500100b5424450005402c00311007801e4140505103140c9840351002003580c1501000404001c4018029411a0007480c4c10402d0781c0192800481c5481c0800c2c2540c19803480342c03005c12102c0307640000200b000419070b4010305040c17107450428242224a10a40f061030300c40276140460150441c0481402d40c16 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 217472293 1250 217471043 217471061
    0x30a020f0a35130509060916030f1415090702031207050d0204171f09020105071203090f0308010e0c0c0d0e010909020a0c0203010e0303090a06020a02011e0e06090309010c0f020301 79
    0x5111500c83c070098441d044203a03d01d01070b40340682d01c008089030301810803010003405002c00001c032a0300e80c1c500c40b04c200d000303240d280084d000309a1903681001440013aa010503000b0f11805005056030012074052001005c00070b030884c42194002c001200e126000000d64641107801460607030b560f0a02111400080d000300d41003004a81c5e442ca200c0710030b10300d001400301c50f0612444a80012805c9403600d29040310301480c0041c1c0071410400034800004e424451038895085070b4100010114426107070200c0942020300c0c114041088003006003c50303c2c0d01092030340d2003d01c0401280c0703000d0403c1109610b40441c3d440349400d02690303104540031070780905600300140002034800c548400741298000c00f240c0e100c0005038083e51901e200c0c0c00c1c401c01c01000320b0f407056000d8001031201010b0f60b61204025404400204119580c464a03400315400c02130402c0140c44110f2000301d00b00c000400601c2c03c040010b000e04c2c8060b8010440c00302c050b40c00502c0c030428541c100700c01c8206502c680c0042800741260107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 217473543 1250 217472293 217472393
    0x2070f080303011a0f031b19051c0b0604031e050106080d080a0203070e22050a1a030c0a05010c1407030f05060601090315090804120f0c0803030103030503010b0d0207021002030a020f0a 81
    0x800786416081c1e105000d4070001c103140c81003485c0b80190000004c02c2f10702040420350450301c208414030100c1c202c02c0e5032507080d0b0f001250407500000d00f5140e941c00c44413030b6000002a82c001c00200082c0c5d560181d036070351300017085410462450030f051401070003000503000110300694420344070b04103100f024403980710420001d80051280385001036081c402004100f900c02d50f50200f0194441d101d040010b40a41d0019001d488405994206001550503443d81081220b0502409128803c10401880514011031080c01c203580610740600c0d040d4100300303009010b5410031001840030008603a81d5104d0014060300d003a0006048111410511864031690b000801e081d13048148401c108080b400441c030800c1d00500c0d00d120496181c000280d1a40710070300c40a00056001c2c401405105a013074010034101c0c0c1002c0c0014a460352503030215080700c0307911880c6009a040821004809a0148503400001d00b20401400680d600e5540f40504c15078a1170a0750508099101c000d244400c1015030010488202 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 217474793 1250 217473543 217473577
    0x603010209100908100203010e0f041401140714030f0106050a05070b010b0304170c030304060213051003050a0b030307020102060a0c0201181223160302070f080303011a0f031b 77
    0x401e0015180c001e01c0e120303060f643c0c17082070803c421143d07141c400c0e241a07030100c50030300c842c076180c20382d1400c51000d0150003a0790510b0102060300503088240f00300b02143e0400c0c2ca81088034508690302424052280f41d0201001e201042080300142489801c00c1c10b41c0d11f00c1c1406038480004400445281c054248000d01c2241240c0c0040b03150690031000d0761042e0b100304080b510003642d04040d002e15024840c901200ca034010b00200e0300059058024002204101d88508903080c0e90b0000a03503102e80343c0c800c0e0404256180305008443c4d1590140c02c48001d81a0000c500d0881150b00003035959800501da604155aa280c1c0f04991034400e400805d404040e8054454403291542041c5000481444182020450004001d204402c05185450341030401858413424201e905010f0200422020802c504500900f40701080c3c00301c52280017009044110019510387d030501003014000210080251600709040c03000d82d0704086070004880c1d00498445180381d1040062005100e20702620b00300500d04c0c030345 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 217476043 1250 217474793 217474819
    0x2010804060c03241401050c0a1401110a030203040201020c01110a020108041112030a030c0201111b070510030b090a0209150f07060207120810080d030e10020c07300303050603010209 80
    0x3030b55110f101502c02410707950011417507050040d00e440c840d0380021411a04048401c0c0702003554958103070820040c00c80086421a0f90003401c0c1c06e2a0300158140c00469408000e110665034108140d0203041020b0826440f00300c020300750180c2c0c0768120341c8000c0c10061a10001703020041c40c20603444002c240901f0341c01012090b118042d8680e0020141b500000e40f07401000100f00b031050285100500f03000d40e50710b00d040c1c40001c41c1c140c034441242400f94580310b04000000c040c0c8480340c0240000d60986e400007007050f052001c000c410400074040b040c0b1540180000f002c0c65030303480209803040c01c0303601c0703041d984412040040002d809901005461548045203010034050108101ca01c4943e0661702d81c0000c1c0d4860480e040030010074003540c203640c1d1105206999a070300a43c0960f034600c0c94502100c090155580c1c0725000ea1380580a164a030b134020ba00c0070409282c21000c00340103002d00d01e02c0503041703000c3e051840b0080c240c2c0c90030284c10940c45030301040f0740e501c0a45c100d450f50300001e031240034090b407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 217477293 1250 217476043 217476101
    0x7060506130207031b1e05160801140105010c030c050604061b02030a120c0315080706170910200c07030506061e0f010212070c09051302010804060c03 66
    0x508482690060080c40c40da004000c001c0e1003220040d5034191601c1e9110404080c0303010000c000001c0c100d41040c0d8040c00c074a05180c803040a6903115100c0c0300100b00011525820540004250344041e8407a07041001800d9022020940c00e419101c1c00e00c0e0040d071078585410b040b98070141110025006002d030f03205210a000790b036040180000206140303005902000c4404981c1e07032007644020f0700010442e040001c034040319a08902c81d020000c1c0b90101d2600c2d84400d1a000301d0003690312084140e0300080d000c0041070380044000069644058502483d46010203034180ca0340c030070401c040c2c65195034400d8808070000c5030707481c44008d6a0061000b51200307010240d40d551200ba500094070240f00c0d00d130001d8514034084200e172044071030b078461400350405541c0600800c10a102c0f2850305602801c44000c00000040002c1c0c0034082c080c18803000c0030f0780341140e44001c445010b090894441d55130000c420150360051005a08558004000601c44814403021801003640c03601e044800c00400c0004042c0d04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 217478543 1250 217477293 217477301
    0x6070611030a050105031524041506170a4a030a03110a121a0d0c0617060108010e13021017060a05030a02150d020a0f0f0c0819030207080706 62
    0x70015007c60b10700700d2114009005a04c0304940080300d5503450400312105c2a40290401d060035070241010a00031541600000c0c4020b2030380029000074290180d465085403031001c0c4075000b1810360400c21100e51507400c241c01d4100d200440800b003450303403120046020b0606848003002c0d4068002500009030348040d864980c0d00072480070000a0400c0700421400d440030381281c000889540b5a1441d06001a803820058450f490b440204001c0704898132550392190a0b4003806203204134425000d25007841d0f005001c00c0c0200041c03920710019001001040e903000138401d819646451101c1b207041e070751410703100e59035901040000d4000a0036001c407078041d900108e00d0429181000b5544145903118003d0161820b0345202d00d6626030301c5404085c0150901a181064000d0303030b00e4141c0e180003110030220050340d01113030300c0074002218540302083d101ea010849480055003450301c4403101e01941c8071a4018000d0060700030180104d015420b881e40e000740e04896500c2d901850b03490319805103041480c014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 217479793 1250 217478543 217478549
    0x4080904061202011205060303090d020112050a021309023412030608010b031f05060d0804180b1c0308060a03020a17010c17070c02010c1b051f02070506070611030a0501 74
    0x110700c4020f0030a62100060249170307c244005001181084c9821080000043c030700401a41071080ca00d0f80e02ca5032100501400d0301c03600c4103000c05070351034404140e0b031601034685e940891406c51050011502c05502452458890b100c004c0c22031002814000500000900a5100500b000303864404059001c0e0144c010b6011030345584002c000c060311401c249a11044425240c086c419022401307140303041041d40c00700f030700044050081301d07a2000c542e844150359401900300c50304224180c010503440780e080e40103009105000f0344100c01d890340e0b07a00c0c20a22101c4001e00050602c030b08000011a162601c4800c0c80c000c5070001d14000380e25a0f80d000e007480240c10001440042d500705040100c600d03014084251760500c041e03070f1031000c5660f0903104640101b0b803103030101c0c10022072020740f2000c01c0c0340c040c040c5900d100c14030498041601d002c04102100c5032003501d40c0418040d148880074203d4000c0391420845800717030389003995511545041401082c10194241680c0c0021040c00483c02165000782d0503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 217481043 1250 217479793 217479797
    0xc011a091305030301050405071e0201020c0c0402090d060509010f090c0e070c02010c0305160f03020102090102060109060b042601020a0906090602012d09050607170a0e060606030408090406120201 86
    0xd4507a0a481044204200006401a802040100094181035010f030340d20882c1d80c503041d514030071140d0342d455840401c0410080141c0d0041920352076031000f80005812094119002c51421b48100041407580060300c070040c241d0340c1d840e4001403207490207400502154408403c1000840e1b0285820b07540d88095010711804031103805e0001d11118003070320860848a40584a03201403468036501200d203540100c0e00d184442c449a211280001d07105000b40c0203092003500050386980490000a01d0040e0590120549604150040041810342c9003103e081e83e80b14100325001211002c010852000d44940c0c030342c40c86d840021081130179a031040141c1d007901c28075071b905000c40d582d640c0100e00741c9401000e401c100c1303401c003a2000e42c0e0102c212401c5158400d1418081030340d444c95105c141c1010412140703078010500d00004041704c42440081242e1241140e5800c120902c038003001c10790f42c0e0070300401040c050700c40080410300384010542a42c0110000170014001035881d45010984400c4189041f40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 217482293 1250 217481043 217481059
    0x182c0f0709121a1f0e0c0f0705011506051b060403090b070807150510151b050f0a0302160f080a1220070510050307020d0503190608070f0f0b040e0a020c011a 69
    0x130701015650170180a01c24142c02241424403043c800007150707000c1481141d079036680c0c1204600072520000300900030805902c425403101622800c03003646c0b030b1030600240440e402107020800040c0d009510307141910313020074901d074694119140000051003100d4002d0301c1c1044001850407680f0140c0c005500ca20074060390300b0b00d000d661f0b030820542d1307004d0f640d01c03940402c14000c09617190700c051686038140e06000f001210303008848241f41506000440905800503004140803541042001c403994004058a00b06449203620302804141c41b840c5454009105100c07144588074440c2c807a401d0344d05122070007007081203505401c008956a5000d54441c01d405222107080d4198224050341c10b5910030b0519401030200005014012149988002e113002c405a24050344c4a440c1d03259441140081c1203180002c0c5103e42c18003100c1600560140e000c1d52950319420300501040c146242500c00304d90304c0021210407900c070461220040d008407000200d071523180408400c600e00054007030845284064403a10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 217483543 1250 217482293 217482299
    0x303090b0307080f04021c061406100903060b010c14250e070c05100e060919051b03010204050d03030b040b030c060a182c0f0709121a1f 60
    0x8034041201c1c0e40001c201000300081c0c445a1101540b17500a01c010900f0140858002c1000005201003009913091941c2c1c6103000500066010b1315a0806003c41d17021205c2c901e5148014405103160200520290f01c6444141d000d90046615640c0547d01c01991141c0c0240000480d555071302c0004c407811880d00b148482001001f01d600c10704213a402c0c07141e1460b45aa1900303026621040c0c0c21004170742c140300e6012003080621a40c442c0c508480141d1010740304605140c01003d01d004401104801c0361b00300c0804040020714000780002c0050005412030542d2030b80700340003034028010756000e103404c40d008142800406625601c83c0105d0342048500304906030359102810350342c428003402c16411190800070829441e0094800034000d2030003100c4000069199400c0d614801111a241109001c02e000c1c0031803400c1003000c16961107494003170419000d1038401c5008017080704034886c0c040703148400c00d00700d8140200aa242c9240101c1400884203904080030101c02d01d01c3c1c3c0714044400903113500c4000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 217484793 1250 217483543 217483559
    0x120c0a080d0306060f0c0209060a0e0c040f090b33030406060513090302030306010c0204020c0d1e050313020909010e06161701050603040204020f0d110d0b030606180c160804030309 79
    0x2440c11031250707903d6084c06d030150700744002114060f145642c40484500005140e000d51448144140464494580c031240b80030790580c0350300120740140000505010742d040071a12034031100d000d2075142e107080074204200b69138801d140051005807140460000010130051203902d4004404036101030310b009690400506101080720040500100141c0040020900d02d40c85040c951040600060005103030012808510b4500328030740031180c0115140d40465109010717207122900394500385041007840c40c60030f00000b0000e1070b814407000f4420000780d0041030915000b58410558140307010102c51060402000510192400a045900203900c0c7c1c1d00852403c0c9030f0144260485001070210350864490780c0c01c100180d00900b41c0c2d5040c0c180305102384102c03007803940621400100000f070020342e2151543c60314025100303102d0145010358000010f00400e900e4a5040d400d1344188110b07130f10f2090316401519842d030311840070150402c03000c80e200c00c0f082c0300c1143c0051007224825200c1001699540c104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 217486043 1250 217484793 217484807
    0x20114090a050601030b1810090515130308040305251103150604021b0604120914010c020d030e0a03110907090b0a03090201020c040f050402032a120c0a080d030606 72
    0x105241c003c0c40042001034189182d0b10f8201e10620080040d2203142030400e0301d03200c01c2011005c101d54031101c03480c05100042c00104410764000c024491a0702e0610a112415403810340300a00b0081e1b83d00011b01414450016164861a07420a061000c4a6021300150707504819130281d86100340034400c058035182c00a0142d4104003c224002035aa0b81c220420000b50000c5084181c42d1310840039042c008c45042c040c4610880c8a02e500001488120000414202c80ca0300407590410358550401c180f81e8102070708010460b41241c1000c03480b0403503d0308076100141400410340103105141c012080142c0d405005e00b0121007940d1a0b02640e403501c40c101c44445041c403a03054940010080790170030a22940003801d042c0d006004a83c0c0c2100c1d440003060071aa500490306403945d554009020441c03a042c060180910a03668805803062204003e00c1d0700c101201711014401c9442c82102000c3d1101400522546040107247e03115440da00c0fa05a501d85c0b00f91081000002c2c5008004144140941e003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 217487293 1250 217486043 217486063
    0x50a0816150f08130203012309030a0813020a1a0721080103020d061e0606030b01030c0e0f0406050409030509011701030b040206070302030d321308030c0c030a02011409 74
    0x2d03440c01c1d90961480c0a450554001c0d01d8000c076035140c0c254210150300c090244150a0300402d40090070603280d250b803c00c0b454130140040400e608208410f1600c2035102d5505c030f400c1030403030f50310461016641c0300091802519030300c280c0a50f444126403010445011014142c80d6004021000f40d03c0c040080141c4100314412000c4c0c007040c00403005001604003d0b0031104a9446a034000540450718001c40d940d40d202000e40c2028286c48507010702406d54580a18a1a00b800f800c0c18400c0710300c45070b40a002020f00d032580c580212040000148140d0390380e0800d40003000302403c1042034010605004140d0b901039000580818124a800040b00c4515800681280d0300404a82e4841e101d41d0f0802c80d140e0300c50b0300250114070040c030007105140b030359205840714000150040c070042c640079684c94007080c2d285183c07540c000d81864200002810401c40350710030b03ea0300c400d0700340d030f6a6240c0002d00e0950040051100c06484080b41000030740303405511141a04001407002505683c610003196078654a840c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 217488543 1250 217487293 217487297
    0x2040b0304030c1e0609020f0d0309050f01020a06020409021b0f0312040c03200a06111905030f0409020c0601090c0f12180b0f010911040b07030504050a081615 70
    0x1400300c0d210710204607403688070b182e00c813281044031001034048000c4c0316426a0035aa03038680101c01c5107803500210079881025142d0854000c041d07200a05454014800c09000301203254607419141c0c4244030845c03903698004011512076407600760600c001d40150307580c2e00d21a1200d102400111800194514a09112200a52800b4042c0318400b007114405401210609101440400061000904507a4544540c0054000c40148a08200b100c415682c400070911420711070201010101280070700380c00480070201d000304081031034203610714460714900b84507174180401c0c00f2510103c01d030003c26050049404445450b62200004000c84040400c044003040540f0030b01203041e409150945641d5142140004030000320304900f005030341440b0400c680c140e035002d0800c101045050303984c50141148201c00c100b600e40a8421141070b2085009110001c200424410100b6200d08111000303020f01a0068040e0355503a2420380d692944403030f904003010320b54800420b0107080d01d07075403000f09a415 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 217489793 1250 217488543 217488547
    0x15060201020c0303010b0a0512090604020108060f031b180c04063f06051e031b0906060c0c0406090b01030e1615020c1509030f070e04140f011505010f0302040b 70
    0x1000421f9800391501009001c41440200140265024224400c5010401070304040c6404d20004100c00e40040407140b0800805101e0744880d24000780c49030f1958a180100c02c095181500002c6002c203080032007850b1003d00700308010600c01d80902030400c031a1141c072404803c1091403a484a007280c0301d5498140200c01c1d140c42014172610000c80100d03044820350029580c0d4807080440e42c80d5000038102c0301d03140b0b9048070920b19414100801d16400c201c440545400d030000c0400039400d0000648154440c9001040403110b4410074080041d949030000c000304240c599801444000d403656000c8030f4046881e054109540e4100401d500c480c0181c255000700d89642042c504c8013044c05803005030381c21407103010361f07168a0ba1145101d10204588ad4602030b5110030030704d401c02d4501010306009903115000a2020800102c41180306504964403446154035680351011407441c100441419260940c2042c908444034515120202d00741c403020303a2582c0ca900c612038426801c1c0e21880c840c4914100c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 217491043 1250 217489793 217489799
    0x6040b060904060219031a030705090703240e010302040e2b020c03030706150b07212a03020d051c0b0d0813050a0603050f04060c1101060915060201020c030301 70
    0x808224030b0b40c0980304500060510070310031554074000c0c90200c0740d9000701e903a1309845404915045580d1006050480c01005900d040c100030a020300e03c00313002d810034543c8410745d0a0034200279040050414096007814000750743d941d100c1908452007032006a0199140494207080c900f0086400380d0140b980d4146c86000b080040190700d403444680202904600070715040c800740da5400d01c020318410780201c0000c0b480c100d40385402c04050b085580440384080d0708003e644006000d0182c000d4965159014126600b810f00800b9201e0b9071b22445049017015068032141c4003003070300e40a08500c19000741e00711804240e10721010340d42441441da61401601300c3d182d903100800c1c503035040b0b01d5060238003410302c4800046560300c0c00413580010700034295009a010040c400ca0a24201900040510303240c03c1c815402e10440c119000080604050310980d12540c84440450041c003c881d456a1400000c00c0030681d41c0003014014100130403c603140040c04a400501c641c81402076a000d0944080510300d564a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 217492293 1250 217491043 217491049
    0xa0201091a1608071e03050402040c050a08010603200a050c07060905181905160e0f06090d02032104032105041701110f040801050a06081c020f06070e100206040b06 72
    0x1000030809020090000710b0001c008178001d00021035100309450201e91400d06204220680d40130380800c00c200309050080c510f040364848042d074115030007400d00040c040810050320f90041a2b0560400c540e00002075100302480e0310400404454004005031959940c80703c40480342d800c4e46201e05980701d0300401070190b00000100001c0e411455520045407100c036101b800030291041210381c09500d21503205454400c680241c0d2040c043c200407500c060043c0448030000f03810b0300031442001e00501d401001e000c11510b040044008498100f4840c910b80504400f40c0c0045500601088032000111400031083d050408801c4000c80c0e050b48401d401c1070708200302e41c00700049801701160b584d9255020421513442c8200248600260403007a83c0d550fa051032800380c01d5800280403030082d14a800020005500d020501c5140702040e100306d103c201ca103420041b4906081d000e40c01520303014100501040603001200091040320554840f103c007543d80805a03140c1c0c01c1101c0190944d003180d400907003285 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 217493543 1250 217492293 217492307
    0x309010e041410030308151507030302120a0501050a1a0f2508070c060e01020d0e010203090a090b0102070503030a0e010819020d0c020c030a080f03040609080a0201091a16 75
    0x41d00001d41c1814001060790701140a403a00400104420018014541e2102e45968000b40e030058200303100101d42c002c5413895800e07071001d005502010401c03d080500c2078045a21442c0c2c4240466401c0c00c1113800040203041c05c1c461144034400002d400580005a110000040216109014281041c4503a8000d00d40d1100001044645611400c0801c840c200103140100314051011141c907080e60389080d04c40c036103040e008a0140f0202801c5801035130390000c0c0c0e9a1010a2380c0c0703400036603074544400507480c6015508065600580418000c24541c50b10703480b0300c40c008426800c41d24016510014180c81784201c3c400840010700030199815654082c800d829000401a820001d0070302000320620103d812107a01c800180d503c1d48bc1d0717011099410091540004821006400c254401c0d542d01c0d0342c0340c800e2100103030b8078050220008090140551004070001d400542007a510300c1584002402443c192104803210000750495085065190007210f01c03400c8001001404001c1405007030703c4903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 217494793 1250 217493543 217493567
    0x10150c02061b0a0c06020609010606030e1f1b0507050c0a051302030c0f03090c150a0c0b0c040815010f0909020a2108040f18091208070219030507060e0609030901 71
    0xd20591440d44001100090410001d24046c0d015203442e00b003600b075176400d482243d403040e0100350a0250311041841c01055802084e2000c10340e032301000328002441c00150140703040c4041d006000d080c00440b910b42140c010b1416620440a441c002d01e00c1104000050985005160300711043c1010038010500c0f43d802960010f1103481c0300b0b4200b208803102c24180d82d00440e00e10380c480d0800c4185801906041c0402d0301009040c107120717410101c43d03440042030790201040190105480b84041415848000100c40151103034030150359122000804a0b01201000e10591294103034000e80090035010034801d104c01150300038400840146803445001c050b104520740d03104080b188195440c0014641e0004000030329032032680680c0c1d0382c03506210000030040c0e82101c041c40c5050030b41c58000241220b070194591205400d1048564451587c120b140080310380d01000200c070310540c0c1506058108010f060b80c80d104a9040c041c01e81d151a086032505015502701c0000c0c6e1040c403103031440758019240e0640e5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 217496043 1250 217494793 217494847
    0x10c060905030a0903050d080906070f0e03061e130206090d0525060e0d0b041b0308070b0609160c0602030c0702030601120b10061e050d0510150c0206 66
    0x600605901e50504641c45040e582c1c0110f8401c1c00c0c1082009002d10402c00340c514641886d0701c1c140b601c991140e0300c3d1700000300320004101c0107607241c44146000d54200046440003904590892422121004400125aa40c10310300f0005000003000d900d19142109001d81e409490301e41042c052a041c4594401c0502007103030359005112000d4182c030490041c0c103c5001000000400180c60840003401d140200f00e03402d400384a191080c3c601086080504607005548481c00124801118440380c88503885900000d00092000407960180100e403040c66000304c000301e841500c16182d0010034031035404a0021200818814907070140880c0d0740e54040c40d44040e01030841e525001c0703079500280c20860240c00011320801c00030161340500c0f201441c0310380c0c0311008a203506219403c141000e071050708091010024148a0b05087c02050f00c2481600c05014419209100342c0c1001000c4d082201c000340541541d43c0108139941c12214450078105801c2078000e882149061030b08516280202802406c0d224 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 217497293 1250 217496043 217496051
    0x809120a1805120a1439090a020a03060b041811131206050f040206040b160807061b0302191103090307060f0305010b0a210b03010c020703021f0e010c06 67
    0xb0140c44003103080040710000c0001e01039a00d0545061041c1da0140c060129455000c00452410280301c580b4004071750754401e4102c5032211460400703c0d541d100400f52035030040260300034411002000d801414540d002a1000c3c030505803584070b81e403070a0003284180c585120701501007801c40003040d88200068601070106e40e10b00b01d8420030f200c07000a4a64040880e00c2d840f4406038042c0002485201c1d00028608040d045900b069000285180218020142e184000090112481c001c00c0c0c81d01540b1603000840c40d454401d9070924200410640410303180161071100c0c400d01843c8244200e1300030b200324641c5101040e08201d0308842094042c80390040d180300410909099a03010040c0d500203000702d41d5074103c1d84140304001415118181d02005407458280803e440c915004049031245110240361150b000e0080014040504000ca04094065280440114040341d0104030388094900944440e124550a520b9114003004d42540c800005035100210400c0c9600c5600c01d070580d94040c2201003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 217498543 1250 217497293 217497299
    0x80c03220b1e0a0204063009110909010c120902010c020d0b1f180c0c0b01030b010602011a03060f06010504030602030903130803090d06020d1104080a030809120a18 72
    0x2008908152140211010b541001d010070300c0400d035080d90b0042040006504152506e030011342003d40540c41210030651078004a08101550f035004d4811004039503003400140654145050b0010038841d2090003100e00400181c488403050090042c05403240d95180070359050210000018001c40008904220901035a80d000d41d4999030b05900b264000d0708400d80c1800c1c01c4c034001c0300190161001103030002c504032041044a880c03404d001e45940d407484012072042070055049a0780364074007034010040315038400084288a00500c8403810385445400800a0700002c841d108036554000306400c0c0d1550084c400030f0722050320708004981022042c18441d00385501d0b0341e5001c050341c1080321100e05591003c901c001d6814046450a00202030f000d02441c9824074480c041600b80c54001c1016044039000100310500c030407280c3c8039150394009a00c00548641d02c0d0b000c60703911025a0002907001900500214030f20800c00309c0d0b460b1052900e41e0025150005081d420390308400684142003010365011400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 217499793 1250 217498543 217498553
    0xc0b0402040c1116060305010e010608041704030218010608010b041208070302030702090a1a04110a032007030e040e01020c0d11010f0c080915100506131a030405070501080c0322 78
    0xd130303d0f0145403c150340c0c2c2c0f03828842c1c0242140d20503481801c0c4102d810004000442d04840c5054000340c21110031440d0301c61009002409220303560009410030000c910001c0440900d0344010f0507102c56540d10409070740c0c0c6514a03149809580110203480d00b1074014240003c28040040180610030300690741007504a0700007a2807d501110301400e035a0322111000d441c0c03116040700032000c2d40c04803800c01c10003412001e0413005000d4070602e035003490360326025041071b00c83c3d20480c03100141b620b035070b0640e4400c46464024400e04038280c42500a5041c0a22808181e070113000b65003150f5400d900078123810030b101c01c0031103009011031400c0c149550b0340c4400c1e054403d4140201e150122094644011900741403032900e01d004c2c500c4a04100d034410b1071080c0b000c50340841e20540d045820444075140c688050001c115072000e0694041040702d05031900001070303040350304040c40c4603502403020b581e511981c1e0300040d070f0301c500d04407010158540c0030000241c034068042e041c072480600811107a00007006070b82d16 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 217501043 1250 217499793 217499803
    0x1b1305060c070306060909030512040f060e0115140d0308040c08031303051b010f050d020f040915060201020703020604021c0512090f0406050d140f030315040b010c0b0402040c11 78
    0x701003442d04141d01c14010302551340038040007499005002c20880c643d988000f00140104e50300c04d100d682080d00032405006031814240c1e1102e8010008100c400241070701e440c002c01492260034040c003d001c0000500184542031104820005044041c15255a541c02c0f030301c0c007000030002c4039130000d241d0001c2031101301000a044012104410703002c803107080d801c01e945010340f041d8107070245404140203041140d91100c0d2001d4502c0f05820086d85507019465580041d00441d440c2900c841004180040c000c0300c0d07a003000b018240d010503410f2106448040c03c0f4281d01c900700c4c0c0a405079101e100402c1c010708041e5844601c844003001c40d280b040f000c07540c8140c10701d041104034120411001c106500c0350701d400030080e4513081c07084030204400c42c54000890711302c21503a60301030000a0605100400910140200100d44035400b00740c0ea9646000d4064170036442c0e800142078000c901d01148650694065440580720a4018010381c060340e540c3e60801014103804200007040003000b82e0341412032942000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 217502293 1250 217501043 217501057
    0x9050a0b0c0a0614060901050906030c15070212061e1e100503010504060507030605030307031409060403050d02071805010803030a0905030c01090812060103020f0d0207031716080f1b130506 83
    0x13213484450828800304103500c0c3c4181c210780c0c480c0201e001401466a0005880c1182881c180d0b2020f074032803519180d2140c0d5000703011010b0340200c4c9440c04240340410108010780b050380c440164200108600886144001080f641c8120000b2620031007c451005044040e90052010300e003901c00c40d0711800420700359102942c04803091b07601d0301c090160144e01409008054401500150700b0030b14a6180104801880900d80e0f6803200c00244c150415141c1c0c00440f8051500a41150003203032449100035504c1c4004d2141140311000c1038048000749540303001da18122101140198117503120100020b00800c0e03002d8049071139200410010101140a00800108030300402600b912414041409207411b80d00600ca41c1c101072040000c5a031003d400810703500c0c3d400c2c0280005840d070b2410b282c00d444074008a45882540c2040e6030411001861419040d204561980d4907a0a50b485001060030305030f0042da06950102e110b9540e0010b40300c0400042d11003183c8020b001d6031640c0c2d03a030000c140c665000381 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 217503543 1250 217502293 217502321
    0x16030e251511010b01020f0a170d0618050603061506030907081903030f05010e0c07110301050a0c110c0a0b0f191107060203182707020607090609050a0b0c0a06 70
    0x30220788103802c00e1043c090800750030700103000d03a501c00d0f0000c2c0d6294201c4000040c41c0800b240444080310038210180c86541c9a0000100300554803208060707131028a140202540c68204000a159400d022070420701079000300000e80190400d1004100d0305400c0102540500e22501d08002a08a4204a21072840f01011000903020f030460400030203403110ba1099042d850b041c64010012440368580e01640148980c1c402c03601c032201850b01111005100060702e43c551300300003d001c014039455020410850307940d11030440d4240969642d40d200d642d00100e80381d100c03512a0003040b020010400900b5aa90121003c900d40800000ea8001134500c0ca400e410014850341a920781183d0308100000c0909038a000841c10409107a0320780c40c0e8500e0070b5005d0350160900e4500f0a10141411200065400e030700c401e640e08603d0002002503480301d08a40c104000780c0f9100e00050b100d4040c42a800546801401d1a1030740c508000131030119620880b9824905e22501300d9103804640307640b14511150f1060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 217504793 1250 217503543 217503557
    0x9090f0c132402031315020307080c151806010303030f06030b1302010908150109090201050c060415050a0c05030a05070e0910080c0f060d0902040204091416030e2515 73
    0x308100c2070b40c0da02c0c2e003111602594020020f09292800314060364040b15944d00700440100300f4070404030b0450062240c010f00c04000030070036290070000400ca05aa0003070542210b2141c1d952000850045200034010701d00310b070880001480828070075000114603400c1c03450301054003a9241e95111110008680b41307400060050303c41000c40d0390120301c0e00000c2c400700c8010001403500d0791802c0421201031040d00295561a0340d84011a4000c1050b511803600071400e031812031400341001c05081c484400d640000e18502000140d00300070a200c1c0134802030740c1e9034a8505541c2c1394002040144005040f110510a40c0f903c1032010b0b54485a8042c400d0440140c5151000d140c0030400d890000820368180c403948201c0302044030342c0c5030b20301900c10501c2e0310240454008a80e0011800910642d00960030700750030b0103080b0030b000e0001041e843c02007100f80c91000c546001d02004504848031503140d002560480c4041890443c4000015023805205800c0e0f5180296508080c110025816494101003050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 217506043 1250 217504793 217504829
    0xe040b0c0f040b120609010807060509031c05090a150203070602180a0632070807030908121305060901170703060b07210806010f050a0e060c071a09090f0c13 69
    0x85a40c4c4d203070300210140c41070556541088103203a03c60205001c0c00301001801304581d00c295130b0410054110041210304800804a281c0000b08541d0100030558040c0700541030025100c4d40e01c0001e4134102440f81e010310304010031543c0d854041e603c8800c1801d10080d40f551030280d95941d0401032001130140f5206c8090001c800c504840f00007151940e550f40c4100761407444440f03154900d04442c0029070043c0003907039811003450155000029508040303200d01c10600c5a99030030800740010036261030f1051102e0103032503695040107036611900e007103140003030907800078480f10071030115103140c00c041181400314419032910a41b081c0c5402050083d00c03c030b48600c20821504080340c08031190400103242c0701155241890010b410150385110f445c0401100003034000700b042c4980b550100313043c4010704095403440c201c0070303030b03682c1d46214020300d0500c04401030310032034511209045500c9510042c1100c012962004010801100003c9c40c03d1807002e400c20611700c105c200e607605203001d00000c10000141c846 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 217507293 1250 217506043 217506067
    0xd11040f0b03072015040506340302070f0602070605010e090d0c02010503060a0302030a201c29040b090d03090f020906060f0f090103150e040b0c0f040b 67
    0xc140d4000520740a0800c00c1c02215030b40f21440716140d0508525a03650f41c2c074000c0c107543c0b0b40b00e0303001a1145070240c9101840308100000c1103160150000307849450003503207840c04d181d03501018018001c030030410610340980c50902a8000c0c043c001d000301c0b1007245040103034a0303c806981c01000d0880b012035842c0018000a40803400c0503070081002c01c01042c481024082c042c01d541600d01c000b030706106010001402c00e03070700d00b078001014607800b80c203444019001d0304c3c0003092104903030882800d0f195407102c04101414805040e00701c69142d0841402440c845444a0120507078540005036111031703214030320b0300141070780700864092880707a1220403181c03411000090409214481400405084c07400c12401714196180c07000c0101d4040f5482d100944410b00020325070700c1a502030309100d80010070316183c0882d9071006020079050030380341484502c448200442448143c0d010703501c145540c0c04017080c007003042c1d0f407025644011b0400c1d4103480c000c43d0b2034200f40c803504150b00508003240c0000b4401c030440c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 217508543 1250 217507293 217507319
    0x1706101e020309032803030906020c01060b09100c0210141201060c06060501030213090e0106120c08062a0306010e1207180b031c1e0801031103150c0a050d1104 70
    0xd0580403100f144c078641410a001d50b001c0241c01404050700c6002c0381089c0259581290859888480200172460355503c2090841c0c104440300c0f03200755040d00f4030000150107807056601c05c070f6000700311014089020000381c645117190998102142d4060182404490b50000d0a5018007001c0c0c6a901e00b1000d58501101915016004941054010301c41e10b4416030071002e080301900c224a0011400c0070741d46159500500391644034850303d6000c20004002d1004801040050704c0302442511416505c070300d50120f0740081f0103101140310701d03003041004a00400d4409560803d2051601ca96003840c0400012080e80c00542444c8003900400c004106900d000400e000072090400c1c01408403945690020b0748840020701d40712218400740c160078901502c20030240e03020308042100c180c105081c12000a0a520b001d0000715a0140a00e000584a03c1d0000f052181d9042e68075010807190340758107461b086908070004002c14800244202c44540c8583d0203000404140381b005030303461382e14045100d030b042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 217509793 1250 217508543 217508563
    0x10f1a03010c0e3a021f0203031b0f0403060506090919060b041409011a010309150209060f04091409010504050705120f0a061a010c05250e130302010c1706101e02030903 74
    0xa1a501c0c0507006e211070300441540d42c00548204400356060100d02c4c0c4218a01c43d0544c8401116400100803042140580c481da00035a025a0800d45598959040075a2403e0f00300412140302043e5040c4400150150804080c040000e800407501d10501c0075070f600b09441c140c40200302a5101c104602100e46422181c0b00100300918050101c1846915181002805000e0b24501c0f80e4000139841000d4403040d044581c0c00140c0c441a0b0790361036541690000500ba240004aa40e40081c408664029014000c20b4005c1350002d02500d0114941002c20181003001540d0040a0240c000701d222400310903c407a1442c2070040601003a18090200c3d940c1d6000040d100c00f03410b00503280000c43c003040000880ca4581082c00e6082420b00034420031041c103004c8181c2c05040700902c40c404000c803030f44107c0b03c0b40b2402c5210b81c0090250060010058800a4010b11000d41e8002031130000780b0f41d440c1007003044864000750f041000c0074050307030050201441030401c080009644005900d240300d0404009100c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 217511043 1250 217509793 217509829
    0x30d0f020c010c0809120c0a0f031a041113060803070b0604150806010311030a060207051b0f1e04020c010c17090a110906030c03010f1a03010c0e3a02 66
    0x340c43d103a9a900810750160b02c0003a800340c003c58a856500d0007081200030000400185034030110742c0ea50f4002280c0c0b05080c00f040b40c011200700b985281502242501a0085a0101d0b04191183c0708a050100c00100311580d05640d944444001038a00018030007444160302840040d1400c1c82c11400384000d44000c925018034040d01301208000c5118081025415039900910749698406e1680020703140010005000e800c0510024030001080000103803540c01004000e4035122a40311441008040e540b204001500151f28440b684912a50040c640320103040c020310040c28a401809903d00b15005959944041000a89210304481071440000d5110b41c64100411880304be0b50b58070313101700d59905250743c00759000d5400325126660911150158150245c001c00c4140000e6506401520901013000c1d02040c0b148490f9500c0d080600641c407038a4455161180202c00e401c1c24807010741d88401465802c80040d9060901c660203100f80301e04400d40c80210a44e0b44552401000040a54a106090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 217512293 1250 217511043 217511057
    0x150b1b060c0909090a0b0106050403060b100509010513030b010305010519020304021c0206120f1f05030312070c0b070f080903070b0f13060e030408011b0203041a09030d0f020c01 78
    0x748100001e4102c07601000c054804030b206854a450191a15150680c01402c1460445c0045411503004000c1c008413070191005100280182050260170b0b4041440c00c000620700304001c0c10903502071002803ea040059001080040d0b42c0d440702e010301e49003a001103031265151005d205048608010410510000c1c400031869418641c0c00507001c1c0c004113641103004003080e10042e0039555401c0955442c88200c0c20012010719100c420400c0f4020119003060612509400ca41000354407583d0802c141c42c0003030010343c40e040303040d0248007000c0c3c0020a007008200b1042024800210362004544c000c000d15241c41201805405001d007119400a2040016500030b000000c04901d0140031381741c0140074a00d0340c4155480c1c825420044407209040174000500b80b40b00050704610002c0100200d0380c5d544020000d030308072088883e40002064400c900103034001d010500450b10100c580c1c00b10b030302200114616050000000c01d04011309000244003003000b000f1006010368040c0902401c00701c0c2464081d17 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 217513543 1250 217512293 217512301
    0x71e03140d0903060b0402090402030f1006050c0a0b0604060f0303020102040e2410050c0f0c0a09060b180109050a03030807031523030a051905101103040213150b1b06 73
    0x10190b9002e848007400c83c5460344001c8144d42c8503907045540d010000360040d9924074103a8071401311200305452a45000c400440d000030340c036201d00151520800075001400c5070200580741c0b204800c0000e0b020700d81c401e58640c2c0010750076245803a07100003941320b80c0002da21185090000a00b8000041c08800d420b425842080006c24031500748080c26982218103280d03041110808a4050241c500d0200c400d2080011100e8000b41c002007038148071904030340d8842000e48840d03070241a24601d2042d40d485090600202c28140d002d0000c8540141040c5403003d40103646000003541e00c60f142c0e00c190045240c0c10184100c2035858080c1800e04c0e0048501d06007441e2411801460010304400000c048035500d008a900f20303070703003408840c903115041011206c0c04003240707801c1302e071010817030798102c80f544220000044148124000c0f00403040c01194031508698440c2c00340034600542d484a115001e030355010408001e003001c0e4005028200411189440705071405d0601e500b2003129003400c0c11640048100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 217514793 1250 217513543 217513547
    0x130b090303070c0f030c0b15030709140103230307031205160906231b060f040b060f031c02060a0b091603090c090606170f07020607030e071e03140d 65
    0x1059030741d200f094044040c485080c02c89001141031b00003410b400c5540b00b4407283d14003000f03001c540a0002c4003650940c5582c0d8285000322010719011040708400740f4010404035541249030744001083c004614002483c0381200e50840e0704c0301ea01100843c641070384c000c8504c17205100307080d44945560020140d41c980910f025181c0c605600c07410301000922010141292030107604d8001d000c00b030301c03600c1c0c0e20740d500400d4510070400340c62080c20407442000300007107409a210140300e001e9070300080c6160041e183d200c1440b2901d070581503d960588500441c01c0c1056008581d040c1c16030500343d010700760509180840e001034a03841103402d0f03c00c81404080c0000c0b0840300c009042d0f01c031003034240001c1c2c2c0300c014a4000c080044030703030060308010315040c000160540c203c0206041c10800709a4600d0b180c0d1842c42d606c10208094901600607400b40c00018a140d00a44c40308003403420500071205e00d10f9445079000001007140300e051413010462102042005903008403520700d204000003134051406500b05c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 217516043 1250 217514793 217514807
    0xf1305060c07030b100f0f062c01050703030902060a09061b051005150a030501020406180311010e06251b05060a03110702130902030c0f060d020d0b0603130b09030307 73
    0x2806000b80c0d1408645c10f03012400f111030003400000395000f15a652070302502c0110403148611750228040105a4609500881c8045c269806854854410142400044070641c00c402350031001d2655400601c005650707244003034007a2031031745d5680315145030400c00d00030b00303000c0301049487c0301c3c007c5040d0050004d0004a010f22120049040002d419683c0504408101c144580419001900d613040401809419001001a1401ea8035480703050445c1058504403101d0074030024088925501c00c0c1581036200d001844082c4000600c0f40b802c240c3c1c81000364060b08a40008018a024503141c9070f010488010070340c5180c1d54100001c954450325050119210f40b09424411080580e1a034400c44450003075410f40300d41e030307401510300482404100c02000c0200030a04050b4420f108016165440e80350060341103c4279480500b0340d504010000011102a4201e400c0306030440d500c583c0081141c0e100c0c100558400c1200e0f00300d841c00d101c80d50030904034500002c0d0005440781c2080081005a41d00004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 217517293 1250 217516043 217516049
    0x212061f050904090c0e04031e0c020607151d0f0105060612010608090708010c03050718050604051201060302040507031e0e0604020105030c0d0e0f1203010302091602120f1305060c07 80
    0x1402007050300c00f5140103445c548440e00325412804004041c00b050541c40802179520380c96a18945c03021441c00042694181007546d40298000003c00803030380000c100c28400b000e4407950043c003180790748007807500181040901052182903030208001d4880c0c850309001d0103420050640300c00d0f1901140e140c11103500e0344140201c1c802c0c41151000309100071410022500200005e00080002410a1030010003502c1c040e20014000b0301011121003071031451034054012540e0003420f10f46002c0c9807805000c0104144101620a0756031601d001000da1034500420b4030562032a540000c00c1c03890b20602c4a035080d00701b00007130100307031404c04c0f400c0100c540042c030590026024200b60343c81e40c0d1a0b0003050030603c56030b01b8492202d818400d40c039900702c000152001d10b00e00c4950a99140e030900d000c0348000c5000904c00654406108008200f244034841c1d69081d0500c500c0c8140c2c0d0403c00061040308896001184401e1840b0001501c0c0c007880001c20400300107448121140c61406030b007011082c1d80c2d01001c1c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 217518543 1250 217517293 217517299
    0x6050f070609020d050316020a15120c0c0503031314030a020304053601090c03020a020705040b0423061c1208071e02101503080f0a02010209040212061f0509 69
    0x6202c82c0c00c0d5130701c0b41d00c40389041e54088200c4c0e035142c013a2140300140340c1400354101d011310069039012600d8030484c5c44001412040e580c4540000c014110b01c10003402281090320140045400c550000c035400748015441b88050702075851010206260020740801002c1c1d248103581c00a1080700c054680c0842228200d0b00c0071202c403541d86070200301911540d000703800d450200e00143d6010760b0f00039083c849068120b070102d00080210800411068059215000381a401600002c10a00c41450198451100c4080c083d100040f802c4642101901c044002c48034940c1d2490341c1006c100d610715046414510040180980b0065207250307a40303815215103200600401d102e40100020101c0b031003510020103403454852283d00e11502d10700080d440b01d109038010364009040810304034100c1e552140181c03c0702c0e8810400352070001a42002c92042d0460252202103540030400541b5613519400940321851104401001c0f41c02e18504000010b89940c04450f000d44001a05451036500002540d500c5e500135 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 217519793 1250 217518543 217518551
    0x105030631030e06030112050c010e240706050f090d03020a090509041121070510050703080a2a18060504050f220e0d09032607050a05030c010606050f0706 68
    0x40c82c06403080d00c0ca003403200b03800c15408000040c9140c014524800a54050026a840b8851000044543c1500640700c1d42c1c22581c0500240b405000200502d0004481502e60710704040c4103507030300030948909880d40242c2201500500012040510002d04c41c11100d060462900d050500041c1001c10180f15051142180c04000b609224000300c0801c4c00c0b40b4000d01800b03507803800d4030850900074500c492182d281e10848101007290704140703055581982d82c50712903230b00341f45540e0390031906a00010300015003191100b1000740d10b44145191610b00c40f10548103546480d50300c4e07900410403511041e43c400030101d0701000b002019001421117007034900503601e90344040306c11004190380961420361303d08040c440b198101000c40302580001382170200134082e5203c40004040440f040da40b580000740ca0511000340c034012101741100c2d80d07030210400c0c454603420400c0e05e131285e03410040012000c0d81c942e04001030800d80f0b005c0038454000a086203090082c282400203899110314001c459008040c20348d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 217521043 1250 217519793 217519891
    0xd09030b0c040e130602090301060801022508041505071a0a0e06240a030c0b070c0b040b030a02090a08030d240f090b01140304050c0a09090203060412140c030301050306 74
    0x1745404880144030080d0003071040c2d0359140080e44c000e500c0b6900440b183c0250011040d00b080c0c207035501034071190300034038039509142c140031110711949000e021110034030504004c000c0c0020b00d001d10b241d50546041940d242240b500140003000d840520814030f0144c2c00c80c13000c01010090311420070007078070001d03c01d10741480408000f203401c440150300050418086c00707100180304201d183c02000081d00c41c070010503180f41e40d500244e9850080d80038014a050003880092035040c40c43d80a000d40100c010030359812995240405070842e8050105505003580712200643c07100001e5004100061400c0034000c41f25140885210351641c01e401061307100e40d1503201540d041c1c0e202d0000d01c11054045210300340d81c0c0c189841c10690f612501805580507181514000070f285809105480e405a0040c001d840c1550341c65445007801c003612500712046c001c1d0452840000d00b00c84020b0460355100000850340c0b541014100342c605280141241105c40c0400d0803071922412070340140d210140180d241102c4040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 217522293 1250 217521043 217521053
    0xe1b0a080111090307090905030d020304260c0c091e0907150915020303040305070828030b0102010501080a022416030c02040b0d02030c011b050d09030b0c040e13 71
    0x405030344415060760800d00180c2814607002d009006061040701180d0301340f591540d010701505c104003006811500b042c00041881481a001542d111b03200740003000804c841100c0f2000601c000310210f89908102203424540c0310010000361514060480d601141c40c0740c101000e4501c40405880b805603000c5c25000700f14880c1e81002080068844c3d03900b4a0000c204441006101c0c90482c419940d81d960800c05800740030780007004076400b540c0c042c4d030f0311454902140c84481c41c6502c0600c0130b112000d42c030130040b0f2042201d41400031150b41c0c5950081482900240020b0941e0010b800450507130300071141030001030f90346490417109880c5096600241c0320060310900d0741806511000c030300a13116052101e00f0160700c1b406102c1c10610880d42005009025002d01c854110760000081d050303803154416000a43c060074852200b012450045520741c0d002d907403101d040511101000c804a2a841070920421050749070641e0301480d001317581410286410000c034107500d80078022034180000d590341034003132107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 217523543 1250 217522293 217522309
    0x50f19020c070e34020703020d0212010603060515010203041d1e07020715021c0302030a020d110307030e03032511030c0615030d0e060a1e02030a030c030e1b 69
    0x648002c9600c40c80d03e407040540c28041c0210301d130b042c441d61079008100441d800600505809103076004180c400e045600b4401281141c8405991201003001c0c5130055140c24002d8074041c40c0b0894003ca01d6040546003d448019011042819904180b00c2070040105c203202101c000100c5004030340c01d5441e0410745d01401c05496850100400112040041e4141c0014500c011105041d8694240f0503000900300c0e1121708119040240150a4028030002072183c0c020307582000013200010710701317881c6d00c19100490b22243c5140040400200800c41d103190540304440c40850040091031443c500b0406516540c08001c00174001c880301000e82c081c405218080c10304560340c007401200d42d01c0031740a00895032840110790341e403100c8101d180c8134145400c010812860909854448034144c004850802406400c00107a9100304038241c4100b41d0641c08103401c030a02c42c182500910343e235108107000242610300300f104140506041c02280795048900060402c5200307002d2480300454014500040c1c80c407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 217524793 1250 217523543 217523549
    0x30b06040b061207020105090c0406060e0d08090604170706020601260c1c0b090f0d0e03030706140a0c03090f06020d0e0706210e061902070b0106050904050f19020c07 73
    0x76034143e04100000da01540003a008512002c00c444c40910700004010540349980900c40c0043d04207100090103041c2080b200c0e80032440b80400310300b411421800714550390403643c040d10341d01002518020307121606118040c082d01c05807010300045d6044c828146120b83c0444007440d16189003401d03c910f160001d11105100610003400880c0c400419085c44071480e03810341d0240c83c02d4010744003043e102c00300003034441c2e01c4020605c050460b20402c44002d55902000344001c54060008200181c002411445403408220208405d4041c5052013030818044400d40c9102c1d105145c03a1400040210751005d000368030140c1d00000c0542d442c0d40000c459000780202138499010f500c038902d40070440d82e802c2384802d000c02800031901565100c0606038801910b200c40c42100d5603410103800b15000c04220340e2140130a205d4420050700c3c081540da5070101c0740300c0981c00540000c4000c940c0c17100b07500d824021560400104001c441f9103042c000f8800031b0090141d411110300650018020a420f8024000d002c02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 217526043 1250 217524793 217524817
    0x307020405010807060507080c10020a1e030c120905150a0203010305190f0b0402031905010b180f01031b0e07020601060305070e09010501050d060909150509030703020a0b0a11030907140a030b06040b06 88
    0x140d0750140405884101c1400d1090b83c440340d0003d00c2d0303a403b0b2081c8604000003c0566400c201600307203034031050050000100640300d500915030b503030810f0b00c0504203c5000712039080d0b005a40b580b55042250904402d411006120010f87c0d60301c0c0041070080240d03010407a044143d900035030b00e4520010f40340c500c180405002c0c041c4401922401d0100c19841035118090070359602040c0c0c141d00d1004000c06508a441403008119100144085041c4203182d16000744205800c50350151101101d40d0014000ca9060006030310020051055907814003c0c25002039060070014044944000029070303585050007160704010300402e0101c6181c0d2150080c4008080c0310404002145503801d12154110f00000c000c3e4100b414080402d04401000044800158250b4098132001c20720350b0741d003c1510409030420316001d448044104103070101b40e00440c010600600100209031420300c3c2a481c1001820150384510301040d42080441c2000c21075590002040f00d000a08079018400502c2c01d02403016603480d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 217527293 1250 217526043 217526047
    0x215090d031706101205090c030a060c02120901020303041b0506040e040b0708100306201b1e03090103020c010f05040803011a030114010f0309140307020405010807060507080c1002 79
    0xa154005180303000d00d440710040c02c021075031000240300c125140118444005055018010141286548a1600320080000381c3d1180f25581c030020307181c40086d070026075509a503002c801c0e1065404100b0b000380000c0e9003a6a6051000010020f92a03020081c4082c10350401c007007060703035030240d800710b054041c16005003c2915a41c950000540802040340e00719120394107000455501030150b4403031842640d21011a05a00d03045540e80c1d8060300d0100c109141021480500392160040d100103800e149413140111400506440402c0741392050003100100344581c420300c1484030a40c0030080784e0a640b03007070030050390300d846d003604150041c983c14030f0019034a0302d080180410417028600440c100d0b02d040180c0c1c000700400100d2141607100038400c4810096001c00700341450b50060015590b91016400c000410610742c6d101c0c0c02e0186040d100d40001c607007001800f84214545481402d01501c0d421005108850030404007818034410900701400703031000807544605121080190081c9401015401e41d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 217528543 1250 217527293 217527319
    0x60b1005071106031528030602070302010b09190e100c0201060608090d050423030d0509040c2f03130b03010501030b0d0f0803060a030f080a18030807021509 69
    0xe006801101080b10302408040c40c07510301d441c0c400180c0307004041c40306044641035280b204210302910f4010310003a040d03464034100d030781800074103004100950003984096520452454000e0071140d01c82c00701807046d803842044c000007041e240c10010019100c02e00c00560078110312040c2e440c00c14194040314005007021490450035a040d0081c10480e0510f07181c1140c65112101415101c8140740384440004900b40000c01501c0303803180354100c00f144800e44241000c045140030031b092006d07201d40d060200d08005103408542c03e241c0b1402c03510307540301d00d030035200180700c007160600c26029015940e911010903007880d1400f074800d20444107a02a031050301146141d03103507200e5045420900c00c031804685819000d03142810005000303002c96074046030351010604250380d00c1d245d91300f000c0c0450f038001c180e00c400400018001d2000302a89070080b800345441f00041c00c00207240c81c0640c000e0320341080d40c560041000425000585441541c1120389201d006008030380c52946025007528540c0c424041e0003d9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 217529793 1250 217528543 217528547
    0x712060209090606031312120e0f0c1e0d050c1201051b030906130804050d03030204030c1d0109050703090b010e0403091e05010c020f030a080d050106090302011407060b10 75
    0xa200105042c0c0b2000c2c55a9035682c104100350100719000c4c140c441101c0f02e041c0000c1c001c00421400d000090814041013484091214111490360b000c01009501403501c1c0c810a0b9070402c401c580d4050112011074141142100c411148003003070f52524011650341c2401c0e010020f05000c8488540000b4001c0c480d201c42200000d40680000d035956504000c1c4036944180202e0400c0480784220314500080c4082d4aa61a100020040340030301552004070620020500355280740b02282928000da078056262415410701412901042c1c0c0080759030b2243d03150150f000c2d440250b85030304542100302d00048907036680318254050b012145000344240d400a00100703160b44000d04507030141d0b000c0d54401c020307603803910b059038903201c04840b10948001c803504042000d90300c108000c42c21144013620300110101181d0201e03180c01e506060403101d41001068034192051a4800c00e40100083d01c1c00542036072564002901e9940314200d4070001184c0081c449007800340c143c002804444000c2c0460405081030240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 217531043 1250 217529793 217529797
    0x6031e14071704020906010c0201140a02030408120403030e01050304060e03120a0c0801050a18110c0f0d05030c1c18150c0c0209011e09092904031706010207120602 72
    0xc000481c40c040d20782855420240701852103954080c2044000e40c403542c0040d5a03140d09448c04904001511103003885048008015007801d240c0c9070000c40c0c5581c1444012030924007200390402800805000410220ba404002086503440c2800c01c0341d500d80b614103280f00504400258207100b03210000d403490200b0619138059119040b000000c000c40495020b0403680c3d094207204107030b8802e000000501c20070700c07803410010300c1c855202800641c40060396051041900301800310985a001015130352402807040c849010b200d02180341052541c5031060769120503000741c4809403111445105c07074950560302c1c0d90020f00e03c000d00b0b070050700010b50f242c0303040c490800310544a070807210f040109128500d4081c1c20103803881c55000b0b081d0b85440e0709008201030b180e260780d400c0e061058040c403c0050003440c0c03440b3340d24a20b40552074038030101d100ca10400d03514082c1d500d00c08810400d20300030040820744c4410b8041c06820900c100b2070303c549907180100e00e40004c940108103c2282d0802420400c031346a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 217532293 1250 217531043 217531051
    0x130618050904150e03130305070e010b120121140601140609060301050d020d0c080c0a1505030402010c020a0504060905011511030f07051e030c07090b01020706031e14 73
    0x1a8016299264824400703581c1c02035800400501008250b01d8402e402500f01d440002c1000080b6814064149000c0940044540c07041d0303580d412a9400b4010044460f200601414151006070300d41a080d60640010b0b41c0148103c642c0d0120010344003140b12a4051034003480c6401c90080d0a206898070000d680341c0b0750070300c900c40c03056a0703842d441d40c603a0400b0000d41e100000003c290b00d042d6031802c014407001000d614000c0b40e2011890421000161103448070f07170f000c0e0800e00c008009a00340c1b40c042c0000301200340c01440d580307200c000d4110740541c2c2c040101daa0150f03080c03a201400d070703205101242806116810030b0760b0250071b00c10081400030315540003504803468179a0841550040720801d4542d18060703007198110341c00400540c0b100950003002040c1c03017445001110b9580c12107540e130720264800e0b41d1001c40da80d00300042c00a40280100101c40c041c100304002002604400c6001030341d03a0010740300f803006042d2165882c101c02c0740303003411030001c0e5440130005002049600428070100c02c0110b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 217533543 1250 217532293 217532327
    0x9050307080a0f0327080f090411030a0b01080f0106180306022d0304080726030c070302060717010603150f031a0a060e0109091e03020717030f18061306 67
    0xc20481c40c135204c00c8140d01015210f060740c04818841516060700b47d0380402d4612820740010484041d2546907171017030b02c10201b04000c0c1d081d100e0604020403402d035041d010100341000800d1003801040b925007050342e41101c0280c10143c50717014480d940d5980d504400c1c5c3c009821a88003055003060440980d51200c80407030789802141c00d407410341d041d51060340000e44005e000542d06100c13100014000385240091004c108a11038080c145d04051141154411105420710503800b140c210105a01049419000300490421603200006810100140d50051144c00105500c418580501504409908010f0f00e00004080104c1e0380301d00b40310756414410341d40014002c051030b000a08002e0b240c803c050070348103801c41c086000c1e440c00c008400640b401e0801902c0000354510140350b15103444100c42280c62190f009013818510300916007180518801103091b01d60020407100c21040031a40440d1400c0d074002012482d4400c000d00891454084e9103109042c3d6183d003180842e074590400d00607030901c1044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 217534793 1250 217533543 217533551
    0xd020d140d051207390c0834081203040203160f090209060409050f0a1109010512101203050d05060604180911180901140403080a09050307080a0f03 65
    0x604100d4680c4a01e1190f6024118410301060105100d0105120b091000e0b0080180c88007201c0f400030504412520b800c40418040c0c01034400b000348050364100240b0f51391016064080240b10940080302e14014000d01d000d00c040d500c0c01140c2a450301040140c50104102d03054404c9407501d91142d5402a2002e030712034815040b00701d04807401c1d69504030560343c1c51080d42506920305084c01029402001e40c45a10000500c0003080c289550f116891090b00d10754811501740c10b00281880c220350000600d90b291050410044640e640c020b4119010301030001c00454199903010340380f40795030007a6000304810102d142450020715034050041c2400b201d08500402241d01c41c0c90401c0030310b1190740b00b04171200301d07000300c2803000e4807280c1d000043c41d80c0a10041c201850340d240c0007800c0c40020050f0600300c0702500c404c1c0322440c03101344500e649200d00024003c0b054200303520098040d01004250700a81501d0b21014410040103000792562643d001d101703103444401c0b2100c00b524408166a100f40000d1034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 217536043 1250 217534793 217534813
    0x2152805061f020a0b0a09082a07150e04060803030c07050c09010303320c0114010b0f07021009090906020301030501050603120a03112503020625030504020d020d14 72
    0x500e564805030050b5030000c205404565980c2c0c0d40c8003c0c000c144c1b00e034640c1e0395141000801d0840d0010181401d802c403882101850481d03840b83c404414880b203656682c00300d00280308619103001c131145202d016043c10800c0c2900e01d40000d003d004681c00c0303a502c501000c4103016440d601d0350041c01030244070360144d40003e9040c405000125800b444007400103030741f10301c0c15240103100c000300320070041d42d4175040b0b421580442c0040e40254094601101c0c02e0303544000d200301e0380160045d0300740580740800005140010b4003080c04c0440c0106a0064031030340d0101001c5445a0042403038000804130901c0c00e002c140c4150900a00a41091105860315402c1400140040c0b03404500c1d405203008542c5154240b01c80c5150460007841c202400c0c0314488402c020140441204000409002d008088032000c8042c480c03400034141400540b02c00c0d4002044080b000c2c8180010380022101c034842d140000d0240d841c1d00010b40866403442000c2d41041d1203107421014440701d407104105100120301250541c140c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 217537293 1250 217536043 217536079
    0x9130504140c01090501051b011d01060b0408030a140408061306060801020c1209032b0e0303030c07110402070605090703050f150109050c0405030f010b09060a05010215280506 77
    0x10030a0309900045513a0414000d56000300050511049220030301803180c0d0805140c142100c00300841540072281005286030460002d00814010f403444d4101141443d01c1d00000541da801140c4401b028030001a04068010207100281d0340100302c010105c1d0481e041641c0e069080171407164050310303ca81001c5020407410f805000326901c2c1d800e000014800c80c84081e800e0805600400308456041c061480b41038160a40c00ca003c00541e41c0756440316501078100c00c0050121090010814040e8100340100030048044405031001c940c0c0202049058501050000d0024031410b480200790a18200078080b0b00c103000103070101030b40d114604807103513207055181c015941c83c0c109081a5a0703101ea60014000c10082c0d4115640110740603502e00c0c10035840c0c1000030304003419007007503d2250b03650300c07500d144074a01043e003182c010300c064600440180c14000002c1d12609a541a40e070322201d010042455403440188650780c43c0040a0b032841d080b40d080740400c01400054034200d20a40d0601c040c010b03a86 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 217538543 1250 217537293 217537303
    0x90c01050a0e13060909060b040c0318120216080c0a0905061311070f030206090c0904020a09051f09020c100203060a1214030406210606020705040b060913050414 71
    0x12240e44500c0706000030b82003040280301c54503040162458540701d0020b0941654010b203c0484d01c10100840c101290005100450700c0b4440c1050416007014031111280002d8103001e80201d8018a400780034104100d0140d151a11412103208404032107080010380c080041123000040c20704446480c5250b0b56580da40341070340d20036100c07551301c00034803e1903010421b81c95204446030048510b10a09016194546903c4800b010b0015009a0030001c01c04c504000180044061301a0803203540b01c0600702030f00451031100e01806604c24403640c6070003082006204040e0b81c200070801061030a1036a0b110b081c0b00c80a500001080c0d0400d200f014182d00c0b0300e9445001742c03413080101520b04a00300d0302c1c0640b8446c5a01a4a6060300c034076034807103414003810005100502c0500140e031500d46c400c0480d807481000b030700071030003a9810252600718140200c6602041c139404889003140c01007080e8031040c0000c3c03600d20a035004039078040c03465940c0074030f40003150b0000391242d40500c0301c41e42c80d207200f4004140c0310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 217539793 1250 217538543 217538557
    0x7020c031b0409051603020a120b0a0b040b10030e0c030304030809010503040215030109090c05060307200c03030d0f3e16030c053009030a051005090c0105 68
    0x5500300340307440030254445550040c00458001d002050704039850315060b050080c104418a254031002d4010300950502c006413000918810a44000e8200282c8030300d00070100c050720740b540742030b00c0e6605100181e489400020800b41c1c000d15100d892580400d0140040c000c800000901f800351018998291801000761400c69400c441c60720718088202004580c66400280220b078094124000c020f03400b000c0070080c40c00f0700110302c40000c50700e2550401c5e0aa103181607100b90701c40c0408008000d14190f014681c1d030307801c00304001081d8510707400041d01814080c3c0c01c001d03d034051001040d20040c4a02c0b40d08440210030304204108208001d25005e500311240b41490403200f50310841050355a01c000024000e5070042c500e6801d030800307000890002640c6054003069000070041940c00051001c2840510700342c40c3c3c3d1030058074520540820a11000131001c0e4110054800855811401e0310f05100003044503910406541041e45149200c1300209415100207820344a40f400c100c6a075409041100c1030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 217541043 1250 217539793 217539799
    0xb03060406020304030912060e01061208120c250b010e160503090c041a0a0e15060702030f0d0f020d02061e060111030a020705010e0303040b0a0f0509031209010807020c 74
    0x8240d0351500d4040195002078001c504100301040002612142c00c100841000e1007400080b509207542c2c810507083d5416508103200011582e01d5540000c1d90351012070314807420580c26581d0fa60b40341032071140e1500030b800910350a00030300f0800102510100050000c0a0321840808010b40d80b241e00800c4420800c03558070390020700c0328404504460242003d164450701d0042126044000803001c1800e680c07148078090340620000c400c2035003902d04103012038040e0442a541d006c040c9400884108070b440740060185c0a08000180701e41551414003011601025007001c4682c07400c40d040340200754081c20312843d0018003074506010005840800e285000354907028409446181c1c6810300b101152002d015941030007004004100107210034009003c110010f900035000c22890b00002402d40008004154400d80040006000c46582031040e07425411081c500404510701d0b01005540318812840400e0740b40c1700d201448041405864000c201052086c0c0c0e41038100c1e11260010313071b900c55900c00a071740c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 217542293 1250 217541043 217541053
    0xf0106050304380f060301090510150b070809030d020307050709050c07060f021801030608071a130906180506030604030f0215010f081510060507111003050901050a0b03 74
    0x40454002909079a4074801d882e03484007400990343c18a1482070510881d101111012400c1106031840f699250344d20190580080c856583e441d81c031940c0361030183d480e004049554042c50700d00164508480400f810503000900d554004904040c0705a4010036071461091140c1034032600403510200a4400d81980540207000090801c0d0408002d006c0040c4003011081051100c240405c80078010000c03000f0103603800580d2007400070b42c4440180b040100c0d042c140343c1070507010031402c82d0000d615030031a190344040740c402070041c3c50b148540e40329080022440541c104d001103144800da5004a04864000c400c40c0f03011448020034606403502154090350541101d00018003213402024084e49011582c8140c8004544021402e043c0071003c0e046a80c1059031030405105c100303410000000f014501c2051403000307241014404100d1041c90140c802045030103e541c0080102c0c0348d06402c00040b00500300b002c00c1a5801c0020300604040300c0b110025820b106c003180b598002d51195800c40040980909 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 217543543 1250 217542293 217542301
    0x2030c040e0106020a0f0b0a0b040207140d0f0206150a03141605010c02030318030313091a090c160201020c0a060309061104050d030804081303080c10050c07140c04150e0f01060503 79
    0x401e80010042004a48c1520b5040540b259501c5100070711003144610481c0403603d644010251400340c03144a41018001c0954980d4211a0006402640170b85110364403004400d4a2022035010740040d40010b0800b440d0035060501e070500030401b002c4c0074400d1842800041d81c0c2c0e5004503101c1030740b800083c2d01508108141b0303484062070001845c403054050112031078204d5050405103160569480450b5280c0e80700c01a0868000c1900d2911040c80f01b01c035210f8450814002c2072440b48100e510120b40c141c081c42c80101164001d009401100d4002050100b07041d0ba101c0d0050b01614501d001240c0e0281340c50403a00c02502e401d025036003071305d50141c1000300d6042c15a82c01c2c0c801c0d080240086d03520340c4042c0210740c46444103110798030103107100f204c0031502d0f0000144070b145010b00004070313074911034200403c0000094110043d514202c0c0c0004d0030341100125400c3e41410041b0740070780c1640060918010103a500341000c01c45085552003000344a80c2d50350034412910700c240a009071400610100041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 217544793 1250 217543543 217543553
    0x81303090b03090106031509030201050105040504030915110607080603100627020f030405030705060a180213150807060f1704020114040b19110a05070509150402030c040e0106020a0f 80
    0xe10f80c8144284000030703403280c503a1201c424400c50001d54070480303502d4030b2100b02050350a000b110300502059070305000d903040c01c2d41d02500607201805404990096890404007903449003c085500035040c0040c0c0b9458200305400415000c000c4034440d000344941c1c2c02c48100c1c8141c40c440c40044030b0183e145050340c1c0c078900400070074607040c9445003da0300307130248a441c140c400702500950240e8411002180e0342c12031440d00a040c1034000700410301081c98034030004100e2011140c560191541294140349420744800079100901c07c4a4003800803581e10000812510340020f0303520285c801c980c403102c5c0c00103400807048600c1200100d40380075502b00c607400315005501403206401034010302c0703a000307061503200e101941090704400344a1701046d000003806d4107900d1300b10005903220300002c0c1c041d0102e00c18548075281c0e21035841c803407180180312040000d002d2102042e1a140c1d0030400401c255524200611200015040340c001c111629030800c00000340503000142d0503042c140e0010301404023242d10780310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 217546043 1250 217544793 217544797
    0x60906130c090b0d050f01050d050a0305310612270c050627060403050d110313060e03060702160b2817070503011a0706150e07081303090b 61
    0x280707418000c40d810040384803040d12014009152000200082500e45842040d1043c24107030301c9030f8051130756000744ca00852004640b10300001e030141030295985807500d2944111500d503546020201c1240c08129848000c103641c044100c55040d07468110000c0e641c4068411a02840b502c0040c101226032034000307400f214203c2c1051580124522a00c403566100812480d5100c602204100847c0340b1b402050341072440c00b0409284010390701a4205800c45d40c1d640e070785076052200701003441400741039540b0800e0b0400444682c07003010020f85115594900700501000c15070100b8901c1b0b4043d80000450581c070005100400000c110030f145085031a02d20321580d2540601040b0740903040b03030351419a0614622408107000b02c20307a07803550b00d10010103071085800d2901400d0b4600b046420401004004007002031554480c50f640070003179840d103d80c40c24a00a11410780c502600f9005003000103107010700c00503045c0c4201c0e210344401c02c1a643c0c0503140d0000d00d14100b030080101c0c0e00b00368284221107401c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 217547293 1250 217546043 217546061
    0x1115070f08040803030708090f0a020d1113021b010e0d080705030702030f03160e0d030806060c10050106180806011a0304032d2a020405061c03021506090613 69
    0x4028038060f12400d1050840c0c0c4100ca13160f000c10b40503420301548d40340402944030050718410142440c04080c0c0c4c00181042600b02c4064074010a414010b18103550707141d00c0415135041502c0c119901d61302d0314808100701140005948665281c00c61601100030042854044000541d9800140e07540e110000d40d1541c1010301004110310085c000d00c0704441561000f9809622001e0790303d5002d00c580003000700701000a00010b40184040d500302c0000ac0d801002c841e1704074800725030803500d4884010a41c0e140001800200030001d040c03c0000500540011010054201c1c481b440310440d611480000d5036180c082c8500c0070760301418003203052008070200203541c21500c02d207010302c0690142c100350843c1c1c02c003031107043c880d100746101c00b00c10040d001801001002c089100d1108003803c00207030a106041d0006010f8003980d1950f00207030180da500b90040400c41009222201b1a03038031030400a54421009071420f11043c614004a440c5103041c0106c03a205c1c5030f0082c401d640c2d04a00f00050000341400c26 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 217548543 1250 217547293 217547303
    0xc190f09020a050c010903030b0909010c0207050105030a0e0105010b0904050f01030b01230d0507230306061c050312011d0415090309080f010912031107080703140f03041115070f 78
    0x4c005804a40020300400c501c640c040d0b5408030305074040d4410090020406882d00507582c0c94905c140c1c10080d00171903c8405c864090800580b02d507607162110003c0c0882881801e80d9501c0c00d00040380141200d0003070403011038280d42c100b140e0b96401d90143c1c220942808064050512000104107030068000d6440718125003005040001a6000118081c20f270005421601500041c0085c17108548041280340700354140401c10b40352031422030200b40c0301c080280c85c403800748940b20081c015010403060f540c40c00301d901804403980c407481003070031581c601e40a00503604e42021a044a05026030304002e9980940e8212001c248410040e045000040c00d50600032000d1081090000603000010b00008003180072040001c110911940740804404003c42c0d0341034181031420403524030304105a0256414a86d1051a0582e55400343c00e0a8402880b110a2005648070008000c0b05040c014800745000b1845032a03407890000c00407040003a1403104556102c1039080901c50007000c12542d004180c030443c051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 217549793 1250 217548543 217548547
    0x41101030f1803110102030105180408070c080d1b030801141f050c01050603120702061e04030809031603081c020403050f030306190602031206031606020c190f09020a05 74
    0x8284010151080e628202c0d106244a040090034150024210180c0c056054000c40c07843d81008000340d80c41d00d8103c00c48070580f180c00001020420035030b045404050304102840b00c1241c0d078180e2541d492201c688004001552704140700d00b81045250070000c101d0385a01ca808103a0700f40342e40003101c800410035007544809061500a4241c554a00c001d00d40400c035603403170350703510444501c1034291800581843d000c0d60195203041003000c441c0342aa105035604559a079a15076854a54aa800400c050010240e040000f8000204400e000007403807403810550682d00d804000c0100c000101320346101c090030b11a41008501c58600c03a6003c40b030b520b02070b08035005003403079243d071030ba98500014007040003120340c000014020b540c50220300201c25203040007080030b520307030030410004d45a0180e01d006044000340800882c0c41c0307503010701c0800d61a00d51415115009036642100035901e820451800b4010f242e1104a603204400c10607908007030b81c14040001c1801131820480382c0007980400807807400c01500b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 217551043 1250 217549793 217549811
    0x9330b09030c100801210f0201140d051905071701050f061e0903010b120a0f030c02031504060b040c1d0402120c03010806070c020d0b1503010f02040e070509010804110103 75
    0x10b51503e000300a4503d58442d0032540c1090000301d01040059100311b6114180c00300305000400d80403008284941c2072810b01503c2804a0440344240226005080300c98108020000c400009820110b6149664074060001c1c1e04c545209403004182c0340902611514002c005100a0500740c400d00c0c529a00908400e28280701d15150340500c1c1c034a10036094007101d0000c0d45010a140034001c8003010310b01160145a4075005008550340c0b01c0f0780d01c000510103a08100401c09150049a951400d41c1d0041c00f5500c20f80c200c40c2c004070304000221011101c151414590414071300b080d01c0b4100c201805034441505c0c0340d50340f03280c8905501c46855455130003902041000c08001480d020640034083c40d456940d140e506124600c0d0501c400100244100642400301c0c00160341c5028600191940045000d0079685601176021401d000503a4199010340c00c2181e46060751013549d00600031a04840c0d00b081c2140c070340703807011203943c46940c0800340001e401001041c0030031041c0b207020010507014100000d014034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 217552293 1250 217551043 217551049
    0x6080a020f0a080304060905030c040b01120b030a060207120306080f030702010809011b0507030806010c0f08030402150a0203040302041803050f2203080403031b050d110f060109330b09030c 83
    0x1c0f261b0072020000e40700b041c0412803820304020351142000c04480500c20032460600003003d501c0200306e2043d066444100030342158400380880c3c20002e03007202040d50340d80c80034100031001501c0b1849541c00030703142c000006035900021038918004081c0343d01848c0b03019007a80045882e003001800031a0345550f2031304ea01d904800402d001c03000c2401551100394603224507082c040c001400c0142454140100e4020391400100765003011a80e89500144440d1a61941e00105505664032103003800750b03000020310b94059580000250040f00e2080750180554007507080503681c440000d02000700443d005200f001c003041150f00c080d100c0c00109451412036a90b56507141407042010358820340c0c50b42c81c005000d1041c5a070050154884404035522141d030080250350f525582c026080341402044107510300d640c2034400c20302c0320650805480c41211003550f150380300e13940180300d815507001900030b40f65124001c5003401c2600344a00c0c110030000a2141f403802d0a907100c2c950101031266418018400482990b503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 217553543 1250 217552293 217552297
    0x91211070f0303020a0201081f03020103230a0501050f0d17090d0507061806021b010503150d0b090f0d2304120b0603010b030102042403021e0304030206060406080a020f0a0803 77
    0x50700990085c860340200e800003410640c0c0150a40d442e152580f1820465545000307540e070100d949c2803800081591640024680080701400e102c07100f54600790a0100070201c5401242c1600d8040b582040000070032810070000740d01030100204003c4150031054842000074024000220010348100c0000b501961000d040c110542c0181000c80c0c0c41100505484000700c00000182c1028002800c8208c62082e0071485206d012407101e0400c00c001002440c41d921500ba400340250001d030001d0703001c00c86484c004040050841b602002c034401c00220080301000010b0003640080c540d21061107012a01c0030328440c00310340b004000400f02d4200000543d1040785249100039074011071082c40503007040000c00d402d40e20380d42a02c521aa0040c00305212000542c2044d5031040861080e10b1058034141505078007a0142590038000c505549418440b0104260011072145200f03a098a0066403044100801c585250040c1c3c2810b0340050320810040c1404140308409013001080f4550903039841603103920b19 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 217554793 1250 217553543 217553549
    0x706231605030d2306040f020903100e0c09012102040b090403080603061b0a030f06030c03030f03060501080c030c0307020a1218150e010f14041409060301091211070f 73
    0x381d48000383d000f0600c103082c8251030b20b2034040c0b0b10030b19421200c0c2e4640340010501400b414421760352a44220140a6241c2c12140000c50260503107005100c44c00c4050018401002d01111a00901c0e0101c0c19628008503d981641c0c0c00080178000100700b4100443c0c1300c098045c049805c80c0c4d440990089682e07444200510a510a55402c225464000c05160603c00040c01c41c0001c0c0f0000404601c035032041c034055030320f4000145000619030300040002805050103600c050010480498088249548544000e48800884d202400b03003d966100440d401841143c8240303190707900380017081100c85203000441c0c11144074411074100070880d03220310f00d048800d11940c001007550f6a1000c00407480c002e40c0b01000b010f101150070a10804100c0140941c0c1d1b0241180381081001076031614024095028102075034072002c46242c6858448041d103d4400710360606520500e004000281c00b441e050043d0004158840071582e032482900700103a0f01100681c3d002c0c044e601440e81b01242002e81c4005450007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 217556043 1250 217554793 217554803
    0x140705011a1201060b0f070c0f03050307050d090302030d0c03050d1109180903031609090e0303060405090a030207051320040311011107051c05031209010c0207062316 73
    0x503181da41c0411456400711035035614103904080040002d40402010f5542290508820035038a035003618142003031910503041207441d0f0810100100512100201030020280f02e50200c590080045c042a0b03018074403840700079410750180000c00e0683d441079411840c02442411300da41040140741940d029110a00c1c032003101c1d808041140314643c500031940ea03c0042044144036032505050300c65944a00c00140340f4900103451220100480348248100c034020294460100b0a0070505044180c0369070081d200310703100303500307003000725001000c040703071183c0c40d25855001813205516007010312042c02c0640c0f0b2005840b03550f1b144041d0440f1596001e0400b540c100c5200c0355995419444d1085207807800f241b19504012801002c0c00403848000784078400d886085030703407900007040910f8590303410700c030110300801600021419849003518030f005107010b40c01d00c20003403265150071132003280d13901030074401c90300080c007115402101203400c03d12042845900c3c07103900d498007022101207130004041e1941210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 217557293 1250 217556043 217556081
    0xe010507030e060105010f1b020604051c0b0c1c0518030c0601030c0b070c090203090c04141803031506130e01120b0903041d0a0b190f14060a14070501 66
    0x70340b8410034000e46024250034201607180009601c00140140c0300420780c0f1020b9600801e80c20290341e10107055500800c1d00800f402c0c5c240c2c05841d04001c203414101822603565170f140001c207551282402c107a52620306102c950030050480807071917602800010340040040c449403691000d1400c800e1000344403054402008002c25459881c00c0070040000d6840f1084180d400d001007000548014511011038110761805070720394480240960815038a1851198013501d0200138800c01c1038250109807107114440080084030000d110140e8803484201c0d540c0c440b1b90110384a1880500d07100c8064140080d45220a071581d6445a4941d06520001c2e0410700044e10801d03076200402c40c28140f1540e12201032030255040c14546081960368854160111100b202c000c3c0c001944058680e0142c1204c40004255a1900c200100c1122030002140120704072000d1070796020030a0380c4100c1e4800c440f000c000e48850319103415424101c4880d0b0140294900c00d010402102c03001c01d2090043c0c0441c0400580140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 217558543 1250 217557293 217557311
    0x1050913020a0947161e1104050f0403020c04110d06080f1b0d120c050d0906120501050904030c020a090203190b03010506090c030c16050d030b03060421030e01050703 73
    0x5400c0d918010a00001c070100c444404d165401c18a0544522a6a6800e032000c2040186415a10300e000c981e0000300000d07481c030145080c84600d15181c0304000040e00d0030003041d12220300c0500380c400b040f500500981d0200030010203a0426038060082c00350340b035200d903042c511560306c0072054881562017000c0c2c5034000c0e002440009001d201800115080016851203407000300041110f050328584080e0044c40c440d10800303802070140c05030351205e40e8444d007070384d4400c0104000500340800d07600400000a000b0160300e80070030102e01c00c3c18180c132401404000d403136549903401c5883c00e0300d2607400c0740c0000381c040340066510100e0001e140504104006805900c1512101e001100c4100304500e05c03070b80c1031809120071034076002c0b8010740000c59400007a980343d17144070005e045442058081d40e0200e0050100400307100000c101c1207400b400654091007903601e98810155241c00545018202072080000041841c2c080810450714164504011030b5144480070140d0071250100d81c61408203803600d042e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 217559793 1250 217558543 217558619
    0x20405070215010b09010302041502010c090909020d06020a0512040f110a1d07050c15101a0f13090615081803040b13030206071b0501050913020a09 65
    0x11540c0114148028441c0c12601030801c030301e114042c42545420f200001d0b40181c030740d100f81c0448001d00360000a120364604070310f00080c000c00301c1c001c16000003090740741d010035070328014003800d494107400a00f410359201240d00d40c4002075014444080a01c0703410040000700c4c140b54690b0b10702c03440c006c0c00803505805090400c9204604060013140c0704880c1001c090046401c220442c01c046030700b080340e00075141c1d0303110301c1554103104190300c05489200b43d10458003000180308010f8419008902d680c118503560b030a850407011001c0300c3d141000d0f802408650014003407440548440c00d0f500700380502682c1d5890448040713900640111440d05480d00304402220f800080d0705070010314803226000b20183c00307800e03d074a0340540e018100064800140c9607035000304501848000e950004c1c010395a0702c2d01c0b07150002e420b285030510a41c02291000340020b80790f000d001035441e1784502411000c0800c051110311002580017410300002d100c45c01da008100a401c90079502c146d4aa0036601c030050788850450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 217561043 1250 217559793 217559801
    0x5310f0e011d0106080601020a05010501090c140705030f0d180308090c0307030b010506070f080c2815020903010f1a030f070305030d0504140d09051002060f0117070308070605040204 80
    0x10400203881c0c0181c2c0c080b01c422007038003400e0456200d840c1c21411902d82500403030803d800008040e02035820701c0f001190402c0c0a07804110070048a031640d0b03410600030040c07041c2070300408401614640040c0300e2082d065042c08014000440044800141b510704440720348903001041c241540024200820000170079020840d84903008400c80040100914554901d80c41680500586000b0080400c01c1e03400c00040072440c005070b0703034407810441d140c0f58400c100b26910f0900c0401c4c0a02008120240f0400040703086d0001c0804e5001100707240710b020060200b0b8040e6111304080307138156591352003a007204030040c420300c0b00300141071000b0040c0250303c000301450000d618465940540000b4400c000056000088908517988110003080c0390b80c9034100762030841140e03401d0010340d0043c2100300c01400e6002c6101804c3c2c5100711040c48110a00d03d400721782d21803084034500c000c1910500140801c02000b503100c00380302d69410890320740640741e82d84d151950708141011100d2a4a4206010461815000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 217562293 1250 217561043 217561049
    0x3090f04090c05010f02030f0c0d08010b03070e0607080f0c0c010e040e0a140a12050c010c09080d0e031f05100b09030307080c072d051005310f0e01 65
    0x50240030002490b2100901c2c291288951070501101d2107038100e82d41d00a00503900c18103c100b029a0300d03050040c1e0000e855002c0d008601300003403c010000b14580c0640c001781c034010300716075440c2c040102c41d030400c0c040158092a815640030b0814404201006440030091891841c0300010f89903114443c00007500105189074414851414246402482500001d0f8101a075030852400522200031100392405c0001002c00901001d403440035008130f4513084030040212064040080000340400d09080b00d0a400340d00800700c4a03040340e0022118544608108501000d00a060360314587c2120103a0b180b11a5030030395400c00c0340d100c00c2003003020341201045100070310b401e1060600c0d102074080001d841e0721442200900610f00070680f4074001c0c008000c0400549849100d810500701d81c0e860007116150300104901310740030504004a0b140c10417140f500203e54254076858146a6681142c4581100c1e503102641381220056108441544d125210b0300102600030740c058150381400400c202900050f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 217563543 1250 217562293 217562299
    0x90d0e01020d0e040b04021620010c11060a182d03050c130e0102030109090b070306080303011814012405091804060b46031e0609030203090f 62
    0x946500c61494003c0d80e64003044100310b034001811500030740060001d020703509070511400128054030040100208a403110b03a055407400141e6032406400443d07034207060480003060740da0441074241e20381c180300c400b40400c000fa5081c40d84107906030722490240080c26600c501c41c503c46c8280c026030000e04940003e81569a9030700d48140c41815601c1e45c40ea5880240302490050310340d01d084448113405139201c40f03440c0c0740107002503550356901c800c81070240c442004103071030800c02d060115000703600900c1403004842512000d503046a107800c44082c0c4102100a001c062103898424480001542d044002d010b0511145011440020030001c0300848100c1c00365402801010025003c5a6440342140720030505140d50000f41c940d15454100040e00d00d140c4000c0d0010308407050140313109000f80c041c2c1d9000c5582000f07504580340603030803044c01382c682c0710200800203c0a907050001c14071214101034030f0401c1501000c0001c50558400003114480c00007500140c1000c80e007008207203006801da02c6100b80803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 217564793 1250 217563543 217563553
    0x5100908061819030c0309050906010e150c0106170f070f1e0b070c080d0e090609040303090210050a030b0607080d05271e060408030109090309030605090d0e0102 71
    0x1200d4a994101c081d0004031100482022039400320020000340694004804620b00800c07480d1902070301d261a07140c0c048000c1140c0c440042400d0500490031482040144e440c0d81030502110305202d651610000340c000f01180410001140200c240200802003c030561900309008030707404a28203104000e802c0c802150001c080070080b08044400c1e02090300c601074550648280c14036a08184840c95a001d4582548042140c00c01d0203114040241107511a1041d20380081102000301c03000084255103d40c4403d0101c003040240c240100480d6216203e818002050300305900002c0d140380d001a0700200048001609208056050040101740481511028202210b6a40b00250341c0100e00c142c002c0c0a43d21400034429414000c4001d40c032a900c00c030032800c580008241992079410028103031101d10000012043e14030700000320613205680003083c6e0340c11a401d14019602400858106074200000c001c0c0202c08200c0a00c10103009141c20402401d1101d08140050880501c0c12109030540d002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 217566043 1250 217564793 217564799
    0x180503030a0e03161e120f030609050106171504050c070c0e060d0605090c060408071703030c2209110c0c010c05031c09051005071403040206090103020901110610051009 74
    0x1038034601040080c1d0003c0700085c510301c03104003040c4001e0484806000c1200e00c01a6040d0b403504030980348038100d40e603036091020580702c403070314019034600f88141d40005008a0410b40c2124000241541001d0001130703c400b000c0013080005c4c140c41d0250740042d2480e40000781141082412342c3c45a0060001d815458441d251104c00a06590701c44a8080d200c9910b51000981c00c040900000901900080002d41c9a07521889450364610540c003814000000342c0d501c0c2150040c0c0002520312840144440520f440d1000e41c40b542034000b404070416008510f0900800c08001d00d00034040c03400700100049032280e0007110303020701d81000c52501ca410300001c8528000455030100c12142d4240f031510045c01c000b00c102888030001c143c0c40c00007510380d005900c4000b641100326000b843c040c00c01c9da039514100020301415864103100595000b50301c55010480c1003003650190300a00f084840505041c0c02250951007600d08061045640b06000b80720a80144064580458503a40c51a401d14042e400b581c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 217567293 1250 217566043 217566067
    0x60a080d1b0305070203010606050301090c020f0307060b133611040518060a0507020c01140a0f030204030807060b030106090c05040e04020a15020601050108010603090f03080a180503030a0e03 84
    0x404050008401844001c0c0c0c6424180030300704941a0b1540076008102041c0d807050010000c2d0000c1c0100741200b82040d43d0038803074506c002120300e004429003020b9071130100785549200040807803040742038009800d04184c4060642c14421142c2c4800952602a0a4003807000352a4070a001005083c0c441c018007001074011410135441c108003400d003030b075001520740c6925a200404540c40400800d440c03240d001003118101c0d07142c002c18001c440310740032102c403c0201001035400c540100d0455444030750600a4424040c400d110038080b50f860303420014a03164403515055001c1d48003000694109032100810007640c14244203000003023250003410000700c00c0341e00c0014070a104902c1075412010340314000c00d043d0350f40c0d41c070107100070910300c41c5420710101d0901c00a502c071403091099501041e08900005103203070180c01007040c0b040c0c0c0801000c2d0103d0040d60141d4240e2806000303120015551344428203252180c1d2002540240540015a128506030916205079071b4003c00001c107507041400081c020b8a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 217568543 1250 217567293 217567307
    0x207032a0b041401030504050c040f0207050d080615071704140307080d0e040e010b04050f010f050102070620010e07120c051e01120f1404031818150518060a080d 71
    0x1c0702445d003c50b10340c480381071980c43d081d040c0c003603a94000d02c0e01d025050601c00d10360051440602c54002d841420814010540750140215a0a43c010b039145606500e00c083c482c00a203c560300c20f410548026040c03601801450f0010340050035005180b141a10715407800708449001030404030003c01030101000401400300d0200e2904601507611200034120404c400c0d0040300321450054410406480c0841c41c0d5810a0000e10403a0303001214110045019480031440700c1c1901e046881d01c1c0d84001e40b041780d070b02c0d41032407000c034030340c45035503541c540c120b016400384403103401410002100c4205040701c0c02e204250030391607440540301e0240420703070360003040b001240f9020240b401d00301081200002813052000d481d504010001e1907103032420800302c4017514225940114000e50b00c3d0340d075514896090038001c16450086006219182001c5290421a80c001c000025030780311781c2d09156036451b0080341c040c44110303a005440a04140c00c00001d4142045031500030074030b06004003094100d0800c068804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 217569793 1250 217568543 217568579
    0xf0605011d041b0302071e030203030c21040303020d2417030f040803070b070309030206160c08030906220308060f2701140103020403050c0d030207032a0b04 69
    0x19007a400d004a5203682c0b182e01c401861408604560440100c51000800075031080c1c0c0304603031000d008284151204a25503c480c5a070b03906800035407031503c0301d00c00c00f80300350090405800041454541e140c0480015403d10b80283d21946025072a40034010b002c40640e90740588403d1000901a1030302003d4401700a91004c03a1940d1020300540701c0c42c403c2141c154845d2003010104043c000400007025180000200034580c0201c4a024080d103840e00100d0564548240142c01a405800031031450b0244d894603443d110003034244020701c0e1800c2d54418a00f500110b6030a0140d8000f64100a01203813034100f00b040c0c10b560080e9009481989640203009072102030820f038064201da080299840e299504142900e501048200302d12a404145105450b1400d0182d401021828590584254040c0c000e850541c0e60040c0540f01211020090040c02d0040500030f0341140f0426000001003600d500d407081c0e0303041c0603030141e101080c42c0142440c101422039001e880d107144100300c1004003200340d0b4214225 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 217571043 1250 217569793 217569827
    0xd031403070504080304060909110a170907080a290705030408030604020d0908030601032904020d0f0504031106071e030b190f050901050d0201090509040c150908010f060501 76
    0x1a6103a14070700701c0e014040c54000b42c04e10720001801191003074014083c802182d81d40c0506010184c8080b0325500c1d58000c41100d09c01050851010403420340040c0b0074207a1040c070701000c603506503654860b8240350506240003902c103052000040121060f048200072240390100074001107500381660010714078440144003404005001c00400c1455030356804a070320903c124031041c040c49205003004145035009440c8a40442d14080c6e4000403481d00c00c0000704118041c0d80042a1740040005110280d030000c0d0300d80020070707940c800442110001d0300c82c00e07008a000e03039a903840100311000300500d040e80161040e0144840301418000c1104000d110307903e90f005e80c0c900441d440402d840440c1c0e24041503442e080307003c0c48500001c142070503112410f0088070400c030b4024502c1d90b0391b01c050105440200c3e03006800100481020b2006040c042d86240c0c00c117200e0f68030340410a959030f500d082d601034800880800110304410030000a41e0074040c81402d814950b9040015a240c44006440c822042d00343c040d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 217572293 1250 217571043 217571047
    0x91724091c030c030b030c100f1b060c081803041716060806010318020d0303021308030a051209010b030c0f060d02030112050d170c03060f030a0b060a050d0314 70
    0x10305241889100304840ca0554569490040d00a0140242c0501c881c5000024506511500140740009440495800143c40003103403045459080701d080c0601c180f40c40034010724002812140020803078540e031980c000c0d100000c5110365408010080ca402030300302c000c840104020841c0d03912000c4112001c0f11228611140038000c1c40741020b04180d6120b40f000398000d142e00002540c45d40ac8420030b4801c24003642d040100440c1e00011007056040ca4101030740089101441d040060b000c2d41c0101142401c03d0300300da00c001d654010180c510360044004000044011542c40072a400225000c0e8101c00018002e100c031101042c04250b4a400d0b40c070380c85100d108080303203d02050302c80d0310441c1e0701030b00440e109550700c0d0384071415115404800b030b40407503161040f03503c007021161182010901c042c500300d4220301c454a0701c410a6a0a0b04090106980102480c0100120707079010010b5011807807080115405502c0c1ca8401c01c1000c80c1664082402001c1c0310342d46500296100910a020f018040905a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 217573543 1250 217572293 217572301
    0x2060610080a0b0a2c0408190915080604112b06050a080a1502030408030f041509030c0510060b041e0909120801080705030d080a14010803130801060b0d0b040f020406091724 76
    0x101c02d401d4a5000c0102130b0b115218491440f40d00000be20302c0340e001500c0500c10050103800755891481044100c01010b601c50041c00c0880701259601c10488402a001041e800c2e11034000540310380e92940321540366880140080704201a0401805803040c5e0000214110305d0326454521241c4002426800000340302c400007401c00c419402c9080003040380100030002c1643c5d0745005400b000041b90240e4283c4510580401c0e001001d0107480d00b502c40301c2c0c0b0041c0c02c151a00010301441611010f4a02480c02c00341804076a80c103c43c8540e40403540914100c400b250144600a020900c043c2c000d50440e80241c50140b040351000100c04000007914a01001e095403040740c000000c088024003400312048060001603603080000c0030b04002c4110120072820305640761039003800caa039184a18403000409008542d06001c0b107611580c50f0a03000f500c04928440e0b0070765500101e901540041c2d000ca00f20140130b1080c06040b0101400b2010400300909001e0003554901902803105d55a0307141c00102d010001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 217574793 1250 217573543 217573547
    0x50115030215090312040b040314030304030e1e030307030806012706051309050405060106020d0315060c1a190c03020405060301050913050102210702060610080a0b0a2c040819 77
    0x800c0c90042810382a43c1b078940300e95400c1e000d0b41c490b203c00d69818403182c10345424924040304032400386906481301210b001700341c800d1016501140c0b180350306503002615104440e44040c802084072510036a1480524502000058242411800030708884100140d465540038039402294054620a003409900c840d0405180403805c0c19640200003428102418402042070015066040c0c911a23000d0b40c40340194520100c00300d40405241e09483c8540f03203410800d490089154440d03030fa000f0a4034a40c0000d0b078072000082407105903514107515540c00d90007060450548921405242c07103107010340c40d00785040d0000d01e5501045c043c41d440786038840c01054010784414407404e0402c0e070040080d51240b80340520307007001030030840c54400c0f509010800aa409440401d00380d10a6000401c000f880d0450b000d41100c030b2800080c10140c00360b40c0c800340c11600741d68143c0080000c004880c1071900b001d140081c0c0f8030098040d040f8003080720020302d05000c00141c0c0702040e5607030f4a03003030782c0c00d500f40c0c075891041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 217576043 1250 217574793 217574803
    0x71212020f0f030403081b03161403100302090a0e10020906120a062309040b0402010302090a030c0801271401020913020d0c050a0c0b090106170601030501150302150903 74
    0x90107a220078000b540844405060014620450207501d0320300300c079030b502c1d4030384488070940848510205008100189200200614a01c0f02d074410b4a4000440d214207035504265604c02d9491044882d1100002c0046140c9500380e03607071180860905201c1d001030509c00d00d076180494849805d00c1500440c81e00000e072120025542848200c8010103a00e0404245180c0100f0250040240020712140b101d14924102c444081c02208068141e00c51643c490321040607d49020303200302d04240d000c020902c015039070324800e2005180222900048d0900d81040142150145c02d000c0384000f180c5003000c040313260406681d1034110341040724905040e0b40402c81500920844403155885101d0940c2200c8518255024003180c078440041088641410003080c2c03064003d20903618006283d00c0c81401c0010b0394450b240c0c0d041480e1000100705252142e907002c0118001c010800c146600000040082c0082405011024004d4003240d124840c10760300820030583c80751072003100f0f88200003265501ba03201089 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 217577293 1250 217576043 217576057
    0x270b030c0111030c060408040e060d0b010924180e010606020a0b04030306030c09051503070506040506070f02030d1e21091b03050c010207050102060c09151204050109060c0507121202 80
    0x200b03075030051402d40347c01e0f4403541081c0111018000010005030603410034030721541d419a004041504140e19041090000e000d000034100151070701c2411300e070080d16240c640b00000c0c1010146103e00d00000788143c004072003080c880b082c1260704016080100e40c0d00459810843d580000300100c01e665282000c0e400303452030342e0006250500d8481d0014580f0650b07800726004000c0903800b06003d00050302016503c141c68001d0b02d5000c0c00401040000b40341820052604501c2b648082c040d101031900001d080501e0f0030440c9004c5040e00700c1d6401d8845942aa44500c1402c03414481d040d44c1224034140d0708000c29580854919580741095401d02400c4181464680035aa2890203081d49a24000340c407003002da0401c5003d4421880302254540c001b040082c41403000000143c1043d450004002c80108001e440345ea100c01c08000c1400d60491984940388290b0040b00085404529850704008551212090008200c0d0a0140354005072540b401c074881500c240ca01000c25043c11100c000007441401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 217578543 1250 217577293 217577317
    0x20c0904020d12170907050a15020706050a020a05030d0209150f090d020a030f0f02030d110606060a18060e130204030b0f04110a090501080106050103110403080a090e01270b030c011103 81
    0x9020001c45c00000101c0b8030590308103598051045541300c0b4280c1407001c80500b09805a0000d031814003a2134483d4001e410070004901c115000c210309130b120039080d075000341176071403040c1d400203141001e0341480100d0740410480380300c1c5186013003044481c2d201c140c000c4c164810312800001c1d05120955032050410006540c00004103552103a181c541030540c001e9014081340a4000c80045d40d41c6035005014401c02061a41c0c040d00f5a5900da0080019030341c0004070750014051a41c0c0c0c800c40c0054410300d00c0300540f10a8403810034003000a001c21810002007030412a29a0041000b0b07c001017415180d2900081407400904460b04d82d8600183d6820110003125003009504d0400102d000c91038202d01d040b503810a008110b0303213807a40c0044080c1c4c0c50640801c00c940100300010000034500500030403180e01c182c544404840c1e00c420f0300001802082c0d106801042000c41c6450043c8202d00d45030742100300104082146c3e41c8840302103925643c610004030b050140b40d07180507400e500207100301c403504001d203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 217579793 1250 217578543 217578587
    0x30e06030a0203041103030301080703080d020f040f080c0405070c061e0c0c020103060905010e060111251d06130f02041706011d06130c1206060807020c0904020d12 72
    0x940403070000c0d001100d041c4c43c0f84543d4443d12000b4140441164142d5408401404201d42503496a640c9503000b9004a850580d080104165952031800944040c001d068191600c4a00e05a040c40c03400300c1d41c1c990544074600e00000c1c4020180c11030008940d45502030404640051041345011048501c807604418035030a01c10301c070072440d0344100724000151013620104401510740201100b2680240200300c48003c59030b01140140d03015200448100100a04641030500000d031007046280c0b00300860445203c0d407035824065007495140c50702d0031411007403001d0913519141000481c580307a00c5003020003141d42d8892414440c80c817601120701030b0001e600d0340c03000002ca810b805e0b540e5007030034851018210f040c0c40807140c0141c2200070782801640000c101c11840c069440402d8000d005079540f00d4240611940514110223150144400a007000d4030b440410b8600300c80041d0a101c03040070707018401c1c9480c03400c120059884881d00800f41d50002ca0b000c41d89250b10741c0507206407505c030246207081025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 217581043 1250 217579793 217579801
    0x20c0906040e060a06050a080109080901050313061104090c0e011215050306041b06080c032710051f030203070306091a010f0510050306010e010c031b1a010503030c06070507030e0603 80
    0x61741004045a1042c0e4030440b269955210b40f5088980c2a60018090f010401440000398801c001450300000240ca80c6441440181d47d440d003190160a00390400d80d40101d400c01010401d0320075151600624105000324000d03100000b491002c00200203032159940b2006c4040001503071240070b000e80005821180242080d0403c48114600505217448420114201240f0390303120303c28040c0205034000b00700b402c607250700e0440803040b849864400305100304056024604041001200c5501034035800004035420311505014100141c08001c950300a94109c0410050b1400140302040307139085040044e80b41040e2a006440550102d404c903400c10300d410002c46c1321000d1485100c202e50f0101d070704031a03d00001d90140d074503020841e0030301d01055505618034455401000c5101c001842031501d0549000c0c0f003440e03810513100300102600c050211345406040e031041c14051300c1c0034007001c070001e5041c6998003100c0c5950b028001d00030010040003103250002c16009260080401000503e40c54881c60 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 217582293 1250 217581043 217581061
    0x22d0d052205030d0503060411040e0603070816090e0c030708030c010f05060a120201020109050319080f010f1502030904061206050a1b03021e040906031202030a020c0906040e06 78
    0x40040001c044041000c44038041190070001501102c0000e006004240030107001519542c00041007035401c5a10b44100a0300100100010300c06800100d003003400304d04080c2d06061401d211900600c07100d502c00d4441051244001e0403003400c6452038880422481080420705092184411020b0f40501c00d08901155105000c400b80c210301209000070402c0301007600c6031a081d100140d40007500b0a811f4841804071800c81c10084041c5401800007040401c1c41c0c2c3d8800c1d00e59030100003c0d9001010404065482961000d62a5000412a441003416505094010012030762503c100c1d01d06107c01c980c44640745009009072014024020300c2000004d075641050f0b40d8011104000f00c40300c81c0350000168000c0e00300d1007600c130502c1030704825200f85080c24030305034020742c0034000442c4420060070402031419001c1d8000c2028040c40d40740403071317803a00d0761900038521060035007188155002440883c4d17a4590001e203d60ba0030204541162003600c0d00c1c40410002c2000c4504541d041c0265020010810f07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 217583543 1250 217582293 217582297
    0x6041a0a060c1202120a0e19030b010f0905250c0b0c04030605090109030c020f041118041d0d0e13050405010c11030a02120a030b1207060f0e01022d0d05 67
    0x74041d43e0446591005840300300d032101508041820034101c01d201c0c1c0b0400c1d0348222240d48481102a010301c007415032225603802a00c8040d0700456403124218018031100715450020030042c41003400520032410000c0408074401c00200c0c203c801d14078051900d44415104101441c03040341c204c2444116410706014800e0540d1040c0010b642941c101400300e002d52074144581210150541d94003e90420140d00b000403168010401d9640b244e01d0b00d909070039480b07240c030091000c0d01040050241160750b45081c80141c49050040d00303a100441d00c2c40729400d0801140942051800e0b140c4440c0100866001614038000b6407503450303801c5d292200700003c00805502c40020300c0099152048100018048241d607407007403c02c1f80b00140c124409001c40342d1010b1003c0d01d00c50700942070120380351070a00301040182e81c003510b1400c3c25a00c1003e0404c041c54100b80064002d4084d072500402c606d40050000c0d40c0d80c150982c0c17580303c085035031149014031455003c02c401030010f000e05643c00001c804200420395 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 217584793 1250 217583543 217583567
    0xf14030702041d1e01061517010f0b0304060b18090309150a0c0303110904020c1c030b06071101021e010914070e0105060a0e1306060e04110306041a0a06 67
    0x100d10b80300207078016046012410031183c003420700812441c060365806080c00c542400d207459071036407a036101080e15500b200003a1003850060761549082803003048500c84500c01a4496000107249030405d0003940010b9040300d03405a00b00c040450181340c86004104200d80030713100d999892a00740d060140400c1c01000814000c00102d0f00550030422030441403030719200d1100ca9001185141c80190000390294119040c0749a40042c1c05003056043d001050580e4080d00a000250300100c1d5403d500d50f2400b60160100c00d19440d00300550440726010661380e106032100508800002c03442203038070341e108100600005810342c10600c992098803903410b000e054200011504c00c25602c1502018010008041003220b89610038100e050b441d190a0049540c80103080400300300c1c03034000841c000d440c1c4500c2401d0403d603400001840300c2c5444002031184502a40b0940700d0b90030000d1100240459030240da401081c12030300000c0d20002524000a09901c00b003481da0400110500000d01039044002850305c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 217586043 1250 217584793 217584799
    0x513080313050f010314060f150706020c0d08130201120213030825050a11062107120b0d12030b031c02010e06070f0c0c170703140708070306090f14030702 68
    0xf041d0407080055081c0e400c49554134103500e03100400115140350440c00f1080c08a0041c251020078502d480340116194450b150640f520390f000280782d0b030310000401c0b00702c5c3d02c280c1600e480000d5051000310941a40740404001c3d041001c4e4413019480300e242ca50444021a0303803050320401c21552843c10755101c0e04505001c01e100fa200d102100d44051409120316074043d408400f91504a805a40e50b07190142514050b68111300c05101e80c11014051114900e8503840c1202c0303811076850001d00080c4403034400600030840500b842d58001d40c0d620ba02c9800320381243c1c0f20000c4c030503003102000120001d01883c80c1079a0306201e210382c000c003c00380688214080c00c7d82640280305003154100002d6441d001620441c00107070600203001030b01882031450b0008a0701c6200c005148130b6840c2a0219116070000c0345003413a41158604008000411030341809500c2140c01a082103407034025055143c0b5201c0c4000342103203449203241d60410100624600410f030340300d0420020340010150b802c1c0e80c0c0c2c22264080340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 217587293 1250 217586043 217586059
    0x1b0b04030e040c0309151103180705030303090a0c050a05031e030c01020d05040b0c070206041a120a1b021b01120902060309030a11030412020d050f060702030d060b0c0d051308031305 80
    0x1400406001d030944a07c000c8081d1407850725452819451070408000510b42070240201c085010364051004501454011300207100c44041030425082c1480944c0c8028480c1c000c2d03500030045506c01040f15084140310355031000301030401d0702c0c0e041e0452042c007440210652000401d0303d915541fa90015020701d000f2001030802d580d42d0a00c1000c1ca110300500690301000074042000320701c42c006a000f07447c0c010380d48400e041c140000f442c800c02d510141ca541404580f60319010810304000f010401c01540300d88010b110b10720310070700c0c401c03643c6011906040c1040304400c0c003c00e03003039001d41045070380640c080d0450344e5924000d089643c59030003003030f0300b000000c454250840408a0000c2501c09881a03e500d51174050907070750820210b0a050380d401c1300d03140106d600562450a003030180502c104a80d0300a503641c1e0356a909d02c5001ca5003283c01c81c900c106414481840c61880000b200c08150500342003540da100c140d607040099101e420340c801141c0c1d2200085441d02120b54155600880301c0584480e9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 217588543 1250 217587293 217587323
    0xa0e0609031e150604060b1e091806011b0b072307030201240807060c1407090219051801050a1e02010b0a1202092406040b09090105011b0b04030e040c0309 68
    0xc0705941b0b0354803030f8039042101482004c55100f90004600325051112420600e014031a4000c212210b540c4a0403881c0801c2600400486581151b21741100100d075114100e065030503a40da0b075070101300160100b001c010740c1d002c0c0300344075156003485072340c110854082090320350301c091074002c0c040d0046c20144540510301c8121222840302d521070035800c1d41d07078030303009403078140d05110702200d0180031401e040d50f2017a0043d50051000390b0030b018a001401c0c0c01900542c3c1c0d12035000048000100301520351041080c02c000039141c5485806055105403800d10b0080d43da02103c0c1c0c011075034841c1c103850804650058041c421099901540680c40844041d10b90301d112030307a5400c12900d10880701e00041d4100e00018001030741e05c0111a080100700e5941c2183c00c00a03045440451001e41081e0008005800001580c007024a0802161401081c09107040b0a030a0b990880102e681200c800004112100c9500410b02b094080c002d10415a82c01400410013213141b0328008000e4015480c5c1921828103412842c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 217589793 1250 217588543 217588549
    0x30501020c1606080108070b09010e060a0e0906060f04090504020f06040608190203041104090203032502090c0313110105071e0311030405010c0f020a0f180507050a0e0609031e1506 79
    0x2031350481d10300030040c00329980703041c1c200d40c02c1703074031504005040081d404c00c060701c00da803440c0182070001d60598a003a00802c1c0c401c1030000201010307114901c0303444180a078550200c0101c040f10203403401c1d08800310382904c0e03c1c03004c0342d0164564040540e0100c3c0109010038210740c0301030038510500130741c00740c1e0001000848042c0e040b48403d44018040c41c80c44c407070f19401810260000c040051018088a14004018038805040031b01c06210408502ea94080c00c4103528110500703a0b00840000b42284ca541803464040c602c2d5202900700600e44640650380386040c1c1e010307009a907090364111212013040340544c20050242c0101d94006c40100e42d40400e06250044004140c03001d48006844000d0051515110f828070040401000c070380c07116122902203650300c03000040600900c00343d5001d08038504244140000d0f14401809802089004c0c445d088089500c06035800c45407230107480d100c3da03e0120002090801860804c1750804110030440038000e0030b000143c1c90824683e200081500d0f231140410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 217591043 1250 217589793 217589807
    0x16020d0b0a0f0b0d06150f090c0e04020f1e040305070b0a17090d0c05010f020d0c0f02120409020702040b1224040203060117101a0103060816090f06030501020c1606 72
    0x840d801c4580c5044004c0041c0080d4410114605102d150400595454210f959164500d800c0100055181c40440c11000d800041c040c0c03405c50203c1d001e50620080e514521014020304d4040319212200203000742000448208441c091364000e0161914592141c008201561015160400149204500208520f84649268041c0f2143d0014017600b138160207045520360f100060a54807035584102d40c010a54103403000b44001c0d030452002044c0300384180c4002d4419840c5d00044015500034821100c81c5aa0310f04c211380503240302c4000140c9070800f600114000340506803900d41c01c14100c4440e0060084006050448610501a9880c0c120070b600d241d1442200c055070000d4155212030014454800c583d030003200c1c841a003c0881d50a144042c0707201040e2155809001a6a80e00d076588880c55685401190050901c6000070040000790110106600c00c0300c3c49000342c1541c0e0b50031060280c9a468101a0055400200941d00c4600c40d0080039258039104000948080046100207203507801815 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 217592293 1250 217591043 217591061
    0xf090c06032003061201090507150503010e13170a0206100f18050c070b040809130e03030601030b0310060617060d1203090f0c03080a02100213050616020d0b0a0f 71
    0x100b010781010001191511504003800d507030392120540710540e441140900c50780007954001c00c01000c00d145400c0340c81c68580802000442000b10820042c800420650840b03600036000d04000d02500e0140e0618403080d00d81080b10b00f443c201d001500c01150b0790b001440038090b0203144030a0000d61391341c52094119000c1d40c0301d0006121000741900115010a901042d442208442d8152505405607140c00c001c1d903085500b15141500807a194100341400640d010304503d031004100040011940c00c90350302e000c01080d02d4105510352107010200e4400384070009241650401c1071180549881000d4203d0340c10701c40d82c03030b80d01d980c0d43c00149051400402a65406801440c500e0300f0210f0b8100440c040d0989820954408a02022314400100c02c50125002036014085080d00c43c181030070003d05100003a5a900451360048c060860803008441110046881c1100d4036541c450041d5181080c0c4450b030302020b540507a101c0950001e000c0b008240d00e21500104504019600b1000f0728041282d003005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 217593543 1250 217592293 217592321
    0xf02010b01110a060b0a050303071a060a050901261c0e1c03080c041203030b04050f0402010905010c03030e0102030907080f07030b15180405010b0414010b0a03021c0f090c0603 77
    0x3440400204240385d014007a5034001405500d142a00d8501092035940b06205c2101c200c52444000c0307006002d4407041d2a0811400c448440140d840c050010b0740040d018001d00120007442e804c04802c00d00000503900941c80b1880a0311200082d01009484150304041208003042034000c020200380b500e0601c0071002d1804072900b031201c0c84652422140c002d8000d010700000c000401020400c214400280307101a88259000301d00343c014a41440f003550009818074013841940b40034040140e030003262183c1a5030302840c107001c5e01c02403420120040d00d4500c0c100c941c1d07035200009204150fa004211075040e2440300c0101c2c0c118502d5141c145d03030703290010311000c2d00300d040c10320102d0440d002203007030040080c20081c00e1414401e012100c1804070841030300d046131940c0d5101000a9542081d0042c0c1031101c0156210601e550700d000881102482380100b040100350340003178100001d0305544001c95001c1000c407020041c130b41c4400e64400c01051080b40136100554100c900003082032089c001d080b030350a504 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 217594793 1250 217593543 217593553
    0x10020f0a050a0215090318030a050703120903170304021002030a090b1608030f0603010c050406170703060e040503030a05010504020a050711041e050a110a0f0e130203070f02010b0111 80
    0xe5422552500b11481860450180b40c8842001c403c22580f0640034261040c00b4659508100e00c101c41c0701a90700202c54000e422888004020450106400003241d170455440080c03401e05000480344114182c000400c0144800c03040103003030f40c1000c0918816403007520b10180e2102140c005a0fa680508651200060140c51061140b0565500640004c1e10344425031001303441c55540e00c071a01d0700129001c1c3c0000e4103207400c21606243c00d00540380103d02e0350600c64030745400d10900805080115034003294010841012070221381c4a58001001030001c0300c403400884c04c01d440c0003620380d8001d680e508a040c0c00c1900215052074030b4421105180103907141d0502d4801c07a6904d14520f41048400381d0381c819905c41d40c0f44400002041076940b40e45c000c54000885180a1f0802d00c1111003038041031200c3c5005000c1c0c001d4450f0440400c003120003c5040001c030102c4101e0004854464900c080c400f11800441800402904501c00d80303011000d0b1380007404840350780001110a0815000c1c1d41580741c0c41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 217596043 1250 217594793 217594807
    0x613111c05130c15050d0f230108030901050304080c060403050d0b0307050901030321060b0c1603030c022e05030f070c0302061b0f1305150c0c12030c0106080106060210020f 76
    0x103441c020b003c401c4c0a082503818400c500064404a40c1d07148003540701562a0302c2c0c081410004d8040380c03a0b900070425441d08a55042c043d449030f480c02442c010f0b505100300080414140188a410f41e0307501e000d100200c1350380d86014540100a40c0206078100c1c02142000b5405005181c08103020041e100b01415004203a1319640741140c805141106500241492402c61140f48500b0b01940014105840265039a4409082c1c070034609407003940039241d020340c0c80b002400000c1e44064040c84103501106c410040c140d40c00142075281c2842c0300d0740c0c882e407107206030384401c220b0300030000e507209500c5888900802e50300c42c80c060343c1d80090904024016004400000c00540307442401d4101184800550fa0403c0c8010341d4904460744510800ea0400f0b003491301c20070407480c01d0b52800714040030940d80e070350a101c4004007041d1f44901800702e66100b490821000c003401071040050b2006114000003e001055132582424000c2c8014040c80005001c0c001c4e6a0314901098000c039000f144441205c6450720750 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 217597293 1250 217596043 217596059
    0xa090807060929060315090a03140409050a061a0313080307030608030714010b010f020309040902010c02130c030608190f020604081e06011202090613111c05130c 71
    0x1c1150442c2da200c6110034494007811110150140d01070b181084801c3e50400344e040516140f02c0c600344200c40c0000c00c04000c013951001c515081c0a65050804803442c85442c1403221242c040d0ba0025128103140000f00100c41e040c3c0d81000b42210406450300312130f41810340034008030307200c2200c40c0c9401903038801880b07001481c40d000840d030107a028500060200d44035000f00f400c5611681c03003070340c10040310010b030b180e400403e1140d841c4c030001c00d0800e000f4000700440c0103510f81c05805d0f07d4610840d81c0300d411368296401800030040f01c5500030f20707124600080c5585c1070005d105500203003000a00c1c103800856894000500c80014160b4210000d0081c3c2031079568045000d840034040343c200d0b0341800001141c4008100703101401d103000f41d482c0181d61080502c03a1411105a1041c1c0d0a208880ca60101584501c50002c0d04540182c0f44041001141d9003450050129000360380c158400000f004203c440c203903418501d0384142000103014607260343c4130f03440300c0c1c00c0c80c0c200141c0401384da62000c0041c03807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 217598543 1250 217597293 217597301
    0x30601080406110d050a0f050720070b0c0109030207090203060604050f0a030b0907080d0503010b0f0d0b030d090f0f031205181305070e0103050106020706050c030c0d02010606080a09080706 83
    0x5208020114080f480c5121004442d080640742a20701c944540c14000d13070b500c13540940c0c0c2d10008200420481d900d4082002400c01038070141c046414283c0f1a0b018015030424810813020b4140c10310b28582e104404000c0034000c01c0f0303901083d40180034045000c2610a07642c002c4a0084c0c1c001440710b414a0705140421408c8000500060b40c06011024000700041c14610b040d807040b00c150010348199481d020301c003801c0803038418409081000400c01844074004200c190781032200403019294a66614801e12001046c0c1d80c0600c60345442440e21310304409a11134202d006071520845131910340c569940d0080502042400010690300c0321482224a56204101a0a0303901c2c0c0443c0c4080c01c1c0350608081121068218100314800b5281c2c000c100300c41d03410025140c00c05a0070b20381002998134040c0003d4858003680145020030800003411050750b00c0c10400d0320404520001901c3c01d000c0b800740041d0080903e0320401c408100d0380e900059580d0403910541c10100c0d001440146404503540d9020020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 217599793 1250 217598543 217598551
    0x15230a020a051b090c030105090f0603012003151f0807050403140601030303050c270a090212010f06090b040e0601111b030f0d0c02100c050312010317030c03060108 72
    0x1807041032503041c0425000c002d40030040c180f94806107034515008043c403100d4000102103040914080004000a0b121750004a61181d2180740215050f00c0d25000240584400111980381c0c1d24500303060710140018400641c060182c1e4240c0340450441d0005220200d252841c0c100d60070030480044050003402100b0150340440c1910308640ba0a4880e9500d038110301c000000c0f1400c95002400600400d6014428181c01100c2072015130b0405407002e8550b40804c0b050f48580719410350800e000481501d500c0c1d00640036059544055440c3c4094040c9420740650900c0b41c1c641522010300d000840c503016525000c281d42c9070701015031070309007046440007201502901160401a40340345025036404280010500e00b2000c0102c2a8504011410103141102c03608011410781c010725202001c0c5600503414400e025416900e088005800b0f0105a0302444c0240e4043c285020010b11800388400d84208141a01c5c0f04000008a0480c2d80000040c0750004031003b2503030260810104880703600401d4401e41c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 217601043 1250 217599793 217599797
    0x60d02040e01090c0f030203010308091302041d0901150302030d030507020304170d03050c1c0e010b0603040c03052103060103050405070302150a08010b090619030b091015230a 77
    0x50555100714104122000b680540364050741d8209403150264405030f100b080c400346140540c155419511040790502c03e03e00014400c955143c00030032884801d8058600629282c904982041c0294000e2a41d80e40111400700e0554030b00317050b004104404144184c2541d401030000d140b00c00084005034020280a0091020b503c800d200000701075040401540049605201030604030b6400c18024055860240140300d243d8410302203105690803c0004116010010383c001c50b0042071280583e00610641031519049000007042105010340142000200c1c2e200c3c004842000070742d40d410390344070311001c015001021020008200c10b90300c250071981d000342c05401542d58042d40d03940011040fa0009810001040f004920005440d420600b40c40c010000060140c2ca401d40324400208584034041d400400020101501003a6034400d0f03100304441c1c3c070090300f50700d0903003480407010402c0011031280c0000341e175224040210052150000f5005144040d00780000e02410f00300f000001d82242ea11001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 217602293 1250 217601043 217601047
    0xa030c05120a050403060c0c050c10051e0310090c09031101022406010905010306030b0a0c050f0304030c020f01022413051b1804150f02040e0a050601081f05060d02 72
    0x62401100c0d004240c900403e8a40b00e0340c030340c40c5151500a0301c02c1c030b8021406201c50035000d14007052000c21500d40c8400101c440304210000c0120030780f1707240980203981841031100381091071954015001075000d00883c02459880741d50f03c0001800f0b075044a80841c00180380b9140820001d0442e01103400710841c1401a40c20380041441448155581920240c49032a80141070100550300b00e0300d032202411003864180169800c60301d8070100d51601a215034411941c03135410711181407140c401d9030b00301090203406a0ba00d091a09001f04010200c6905a101e02e00e54000300070343350700004041441c4004c807040000f8000008028504c1c0001c01010380000d00003001c11580060001c1c00b00309448500d9400c0007003403110100502060040303500c1c002041b105048280310100e02e0481c040c58500c04880d8012a564510005040103805160f0010607030005540600c00000481c2c0c001d94400e5a0a81c1d40c0903840d81e4085c5c0107600510440100c07141c0f00380b8041e09000508100c0010b0142035040300c8054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 217603543 1250 217602293 217602313
    0xc04290c0a230604110409020d05030409050a0212130201050d0903020a05070e01030302072c070819051902030408091c0c1409060111070e0a230106020a030c05 70
    0x1416441a440404030760010035003030040200c49081d44001c0286100c041d18040c085038000e070303903c54000c2e00180c4400345c07003d028800343d51a80c20003a1000d501030724081d40c110316860413640d00e402034041d01c80c41c06e08040009103086154825540408150f0703a1000341034075280c5401da00a45481416410030800300b0518403101c03418000e94407072038800d5000f403600541906000d030401d849900034140a40100c0c00404c040703030b4009001826030b8110f200c5804c0c1e6174014140e840c1103808041c19041d0781583c400c02c100300b2603007058150f8802d0b042842420407003900302d41c0940031100210340c48800180344191040c1483c00030340c003855000c0c0c42401210300d401901c2000609030b440c0c03a0520708101c100070809078200f10040d00114002d0020403101c5403149200c0c00001d440d6000141914100201044044501441089101e0044c415036200c2007d0f4117000400306c014005503080d240300d190845031101c01030020001c0c020304036611503024214415466034102d4000014241c1074481d407080c64604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 217604793 1250 217603543 217603619
    0xd020402031609090903021c02031e0c061005220e100203090d0201050609010b0c0a0b1f1e0620030d0b0a1508010b0309010e1f05010b030c04 62
    0x11802a9500c01c2e5058411014102c0140000307800e410260020341041d141100081d0005007007149420580310900620000100803440c50146c20a41403140c170071400310301c800001c2000117040d020318200540d082540d40000004541d1000d210b40e5030002c4182c110002e03044c150000051103200da201010600c000740c4032407645001d0b03142504000c2c0a07030020174002c0000e420811004003441c90700003806945004000140c40c0780d0144100101030000103a8036100c11014011034421660041d0080381e103040c10741d02915007038064401c4188080c0e40c104082000f1400409a5000c5045540c0e030f00146414071908841401d0500308000590b080b00700e4a0200c440d080c0007070005801c0c82000080d1080700242004400a86070b888441c0e03100261b10340b044040c0d0300104842c1910301c2c00c8040c5540351196044180141001d01c00481c00d40246442c0054031801500ca1224100b02c660040c002a40c85090406452005a92040c500c00d4100f1003040510040440c10626110b00c003110f02d440d0790400d0342 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 217606043 1250 217604793 217604797
    0x150d0213080c180108060c0a050904021201180e0601090b030c0907052d0a0e210609010609050106020303041205120a020910051903051308070c0608091c0503060d020402 74
    0x180c0690304107208510b21070400d100907641c41c2502080103003180d450502c41c10b4403120090050b81c0d05400c0010071007880c90040701142c03905c0707030050f00455071550074128041030b0b140203004040341082e02c48880004000030703002c1d100954a070f000c0076000c50303441c0c81800f00013031000c8490340c1d33007600030f2410303d2401c0d988880c9030034810306681d213401c0c1e5a654080302079144414445c0c41210802645a00d03e4000541030068401104007400c041c0c07184400900014180f619034007098181c0c03078050644903081600800e086000e0340c0180002c0c080035840710000c0c01510024000c42005034800d100003008118520702c0f891500e9050706009207052030848003544003d00c22122207002c243c0000740c0700340e0342c200907801510780c15280c9007090505040c81081da1000c0300140b541000c15841d840418001d50034201403401242d8890750140c0d4480151800296090b07240c480d14001c1150540060700c0c603400800d03c2c0c00021301c1a150801c09040c0c0c40d90a9909800191801350001c5031002104016100d902c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 217607293 1250 217606043 217606049
    0x1141b0703170406020c011b0b10090218040e0a030c020907030e03030708061201050705030c091f0804030f14040501050f0903010501090204143a1e110f150d0213 71
    0x30080d983d2810010301074a040d412501d943d041000941340c020307011950121014003583c1c040a40b09039900c1e001c0c1103600c46481d40c2c02035071480740f00040303c0384e054484240030b541100c810740c2d0600a030070500f5400c0348c851400310005004241c0080344080149403031504940c4c081e45030300f00090029081e0707042e81e00e103401c04c4070303040085100031060082c0c619000b00d0541e841c0d021040244154542500010a6400007800241031a1000714540380560f8510400c9084440c400149160083e18480300800604055a068000c6a45403803500d40345481440d81c10701048147d503e95181c503141100440b425804094403c002410601004c10240e6007805218020303d0000b4001d6142c41c2081d160460720104041c0b4031744601c510446000c07440112255180851450801d003030321110b1650002d4100f83d030700705070003410110015001e00c1d10303c215103a01c0f40098012071600c07241420f40b500340300709c4412030500164000e02d40281c5d041180b0b038070300c001c1208034548000503060140f004600b072507071201a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 217608543 1250 217607293 217607333
    0x81e070807080a0504031416020d06092603010501120902120f0d03060807090c0e06120a0c050403022d0a06030f0b03010506100c0c0308030109090b0601141b0703 71
    0x1209104078264020080d6800c1410704104115a0030a941e001d802c22504d281150600d200104841c2000c40101c82a20b003da5009800c3d07403511800d5103402001080d040008840010400e0b04900f01c860441c1481071000e080c032070625140d070342020010341ea038801d203503124000030351500e803048016181ca500c42e01040700210014070001820000340c0e03091064604525041504c4e04000b0880ba2100040c0813045070445000000c8a05d40810116131021501a00c25000400020181c2d800a800411a44640c0050808018021003104101c0e0b0038401c0b803001a601400c02c0c0d01184e00201e2030750f00002101c85442400202207031100c0442c003c1005548400042540d0b100c60140981a42c0a450640da80482c0200124900280041c103e51510610300d420004c0701007000c0e081055840c520005903801c09151740d140e6a480c0704501c06050f030348400311900501c00300454490350080e1440b4424415a07920030382041c44011034241d42403644603582d54140b055010010100d11101101200c1014070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 217609793 1250 217608543 217608557
    0x33a0b0102010c0302090307050114220f0e06060a0e2b0c1505030c072609120a0b16030f050703020306030d0e01300e0d0e0409050d081e07 61
    0x80000a421507070a841101d0a060041040c0d01642c2c1e4046884410355109082c4000b010001ca0701100030390160480071040c0c100c07600181c0c1048100703010000308403401180c2d082c01040d103070364040c0041002910642d410075020b2190798505801a14111012040a0080c02042c0c159001e03400000d41049010f129080c2c06041000502841d44240e00c06000003a820760107040034000700a000d8840180001100200410450b0400c114084115100d0303401c40d092103130a5101d03503a402425401803040034401e603421082507080d64400309070240d000b90000303104400d50b034903400203480000c0b1f04041c020070566503245004205101e031281902407803065800584915040091500c4c2510b0103803039500b03200301d030084003032941e034001c60000411410207810204481ca110040c400001032408810405081045000c0822000154a0b842c0310a030f90f5001c4105d10441c00340002c8400c00c48000e4695000350150310402d030300800060750010041300544140d81548850402c0204003070b0b0340c00700001e20fa = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 217611043 1250 217609793 217609811
    0x10e0604021227010203060a050603222907021b03010608030d0203090106060519031d0a030f0207211e1b0305060c12161b0b09010c050a02033a 63
    0x40c0001c2c40088803d80c400031855820b046000a5000d034052240354810540000040c0c0d08100c0944480700028003108a1020503286141002c100b40c036840d50000071922944541764804621003005020b21100d8001d0403a9405030401403400045a2020b90703019926081e0000e0f41d00400c2004094401c020540181c4a0070001d15060a44010398402400c016050100101406400c2640d0b14000c21509000884a81c12500200440700291000c2403d004030001c10050582001000c1d408803c40e500362054640c44030103003032081c9025441c0b0785070440b0300446800041c1d000400840d008030105440c070100200c1d551409910380744c090000214913488071080080000070081103810558040c5000d0420581514801d2600d00003400c02d0203208600d00f159482d10b000300906c0c1401035020107100d48045450600d1103420740255070000d410340c030345029802d001d44188140c030301c010b11541c00b0354545105042c02e110200d002c40f1000c5680d0100751809031080007405001c022080800c0300209800300c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 217612293 1250 217611043 217611091
    0x80f0612030c03130b07030207061805060313020307060207060f0c1412070b06150f0703030905030d1a06030103020d1b0b161b0b030c07051507030e060901060e010e06040212 76
    0x109079884105e4004060107040d0000f5004500c40080d10030390301c2d04143c501601d403007a022940d000d9110700e80001c80041480740c804159090b901c0c2041c0258126050350340d66100490760b030000383c4180710004080c49021501c00b8031171000c014080740030303108000960280d881224140018003989117901400021030808022400d1440d81d8000301c21078034501184107550041c07655118242e00c0c2074040d98006481c0041600a5000c4002c10f41c010007100d49901170001d121000301008100d005440344206178840041c030b0f00f0b604481c140c81e4085c000110340302d190340d11100820085480600000b16a41c40821841d402030090091103150f1543c5070030354012030031718101d001074144111a20640700441405501d44110031240c0002961010942d1800300382811402d200e40c0007040400011020b060000301a03141d00860b035192001404e4032241d03100c150196088840c603115801c43d0102035801003114840b007082240e80040090005442d2048040030f014070624201c4960180400000300303020401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 217613543 1250 217612293 217612327
    0x9060807091809050321060a0f080c0103270614090105060f0108100504091104060608130605180a0b1801020a0207180e06040312050a020a080f0612030c03 68
    0xc45a06100c51414209500038100010041040c40803a4646180304100b0908004603240060203c0c04200b01d1144414030211902c0d058901c24401c00084001080400746490100116000c9000030f0400140400043d405881070100300d2005c00030120301d10104c8480a440310303400c0351203040700007603032800d500990240342030240c62105560316040400c1202d49805083d201c08003001d003050041c0d66515405c2c000450000e0f0020b0740c1140c10080c07281c2c03c0180c6141418a00c0004030b8080c02043d440f070404903065202210030380502c01e1041180790114500c0d03400541c101081410100340714074001c000c02d2600207800300844140541c41e0800500000091845c0042c0b903c84000303500e8140b00640c003d50300d102600580b546c12130075500a00b10400c103544061411520b071400e6503290b15060030040d09400d031490745950b08a0904000030305c40c00f0944200e501010440d207809295844d000d0801c01070510041038990050084414060141000c0020f03001300752031640115641c41c51407840c20429 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 217614793 1250 217613543 217613551
    0x30b010315080d03050414190b0c07210302090414060123040605030a0b04090506070e090f071112160c050d0b0606070602041a031807060e040b0619090608 68
    0x404001e14144030310500814a0f0110a07058600440c9a0b2941e0800100010084455075280d100e181c1c0401c4941194048110400d0f004400343c440950712940518800d110b00c000c020700084d198000d2201d810030a01c0000101445407500608044111011504403024400b05101c243c09120802c8140d69000130812014031850210702050a07080c205400c00c2e0240f40902c0f02805000b00019141c250543d006980c113840040050112160340c2c2800c0e5141d2000365042000511400f00790082403d00030a603501401c0f118000d0840f036a1210070071101e0724850101900507018065240c1e100c0312a08003c4c0840c2500340d400360301001483e00e00840d0070103076580058021070440014a0100e221031040b250302a9081d2030b083d0344c41809140c0390009100e65007004001403044c2e1800d50200668502640c1721b224600075418440003030742c030703001da0b900302030304c200000900345180d070341403a0400c2d4110310403501d0003406550800ca000800c8400e03280140903050001450b41c401000344560143c0501d400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 217616043 1250 217614793 217614821
    0x2030606030d05091003090c0915080303010602031606021614010608120702040902240301060f0e030c01031e060b0a0810080601030b1003120206010524070b09030415030b0103 77
    0x41c204524400f410b280990800c080c81104d0b00d80e603c2c80004c0c001d0b0000350006901802d022203483e265030b01107004105800604a04542d600300209030b0b09000400c40c2e05a4289800442c24100c1211416012503009001112030a40071f02c1500385801d45104680c00c102d209015543d2129900400c0e24210f80d44e60380502d80950041c1c00d58107038083c2041c00c40f000e1540584003c2a098241d00100701c9442c1894600f04d411200e1200c0801489012000786061b22000d076900980043c0840c07088070302e000c1d00c0101a9054000c224058115030090344a40c0741071005002c1c0000340c8041e0452042107a065501c0a50380e034000081c0c2c100515400940b469211990003a0300880c0c5050601403555013005000c020182d80e0090045003585000c800c0c00030003580d1000380c0d41d04903204210003c3d00d0b1078080c421240524034030010803069041d0b21211b00d044e0380220488a0a10101b07448003054014050040c4910313000400c40807031751680000e442d00b00340d0b031036480102d0301034600700006045030b4a46501c285 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 217617293 1250 217616043 217616053
    0xd020a030339090e04080304051b011205100914011e0b0414031002030114010905040e150a020c0a0f0c0902030103030e060c070f3206090d050a0602160203060603 71
    0x125205020280035000c0628800d40300c0c884001d410780d07150b1100e0b00000f01802c184005c0104100c07802c00154880d80c1325400342c490a15044011900c0c0c5440c00007414046580d1150340340b05200564800341d030080041c030b00d41800e96604c01c0789200311401c03002180084840400184000d18600544440810261400b150324a02c1c003901807043d4021401081940c40c001c1e080505299002c100100071400200d4046580356500c0c4007014000800c0540503000c50714211002605103860b101d1942034014a07405010020180580555000b000600c40030007203a091100c001d4000c1d00b00329000c202031099401081d407800608040609a0850744403043c00c1e8010801800040d903c001c0390040c8170303010341e142600c901644070b1403800d0603240c1c0c11444080b8003504002a46101c4506110743c88440c0400701d04440c410409030f00c0e801c00c02c901045401200c10024082c142c01c1c2802c5038803019000e4010383d0002d0085540700c10603a0301107490224040403000000056241c04d001187d0400c030201c00400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 217618543 1250 217617293 217617341
    0x60f0b040311190317040303020f01050f07030b0307030803040c0f12120c02010507061b030f02030907050f15120109060806040506010b160204050a0c261609080d020a0303 75
    0x1000358288400d0052000321440d4410a00d10381c01c10010b51360120400040c80245d007010901c0340c000348425401440351041c5032a0400d41842441d0040da181d41107070b80c0d40e40d030f8980305a02602d03d0610607509482450000000b18000801440c06107101da08107460301403502041c8064103202d60841d01855202c030310100300099200711000c41d1200039003850402c6500c0b40c00183c915000f4440042c05640c03d00740da0790140c006540a00301c203d00540c0f42003111800c0181c14008900040340ca501e196881007205002c0e918040880042810009005002140180381016066000844071820300610300e00180022007050007003801800b2860000c0806150035120240d0340c3c0010711590300340084c0004c507a44a03813444601c640041d0303005441031040b03040c00781340b07034009090942c407041c000ba84405030100400f0340305021303c01c0d00700b03240c030340c2485da850700a0140c0e01051003114070018086100800101a9002d120820407079078140c019003012242e030b00300a01914110b10f818044030020602003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 217619793 1250 217618543 217618553
    0x516080c190e0d030c0c060e060d021b0d0305060f12060708040501060f0b040302090a05070c0803130f0f150b010f03111213060e03090d060b0d0213060f0b0403 70
    0x15480c0070303418240ca44845100507009440315a070000b072030394000601400b18000c0c50342104500c1d1501b80700e0030300d484e11140e0382c80c421280c80c1000c1046607800b29041100020b01c4810340c000c0c00f8a0000b90b000c22340312a052010031031401100900140c04651034408102c1e132890400c20303410f0000b20a980782038030701c6001c80c80907441d484010100400d100310313240810140300007584128090302c04a0825100b40f9282c20300000541c109100803845208824000703240147c0b1402024000c2d1040e44582d01041c4555039920901d40000b00705034503c00000c604200480d510201c1209102d000c1d038603111101d10b5030706000501c07040312035800102c00e0070314070002e4859910441643d103021a515002031200020740040c2103078030440042044d030040040a01821141101030754980c6486210108004010300071266243c0c003854809a600c1041090f5241c041480e60700840d082883c01468000c001c820340d4005800d070b4040c82184003100b03507100000c5c0b00030782d110b40380c10004e007107503582040c1001d01d0341d510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 217621043 1250 217619793 217619797
    0x60402010806221508120705030301050d08130f06030c0c03080612031b0f19080406270806070f080906040314040b07080d0c050702011706130f0516080c 67
    0x642c003c0680a5800610340c402440d60301d0311689401060240c9140d0704410049442d550243c2c200740d00503010303108690b25080003210441c42e030203800395086a28000800039101c030340314800d985c0410f0821004a01900049000e400b6000754000e066145003000b80080407584841e010905100c4564035001c0466000200f07982d0111045424541d2030f034101000901318020b0000c0707100c1070750307021884c42e290741030118004100d000ca10040760350f502546095503002c40340229000c2c000c00010402440405e209440d0b0140b286556040b44009004001c00da800c03128441c8c1c0900c04d20b03000041401000382c0d000141900400c06854110150304040c0b8400e900c03000e002c0c10040c188460903141c19030b20b032000e000784c500800f05101410745030342c0709051a01455028100e02000e03640761140302420305000d03130103565045070103942d02d0074104008452002e004034050060350303109000703500c442d81d001568050741c0210b03e00903d0201e801e00340110210000640203484406020100c03003044001c0d1002d43c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 217622293 1250 217621043 217621051
    0x10503131511120f0714030613090503180103050a0c09090203150d03170f070804020f0301021e0c07060203030402011b1a090d080f01060903030309050c090f180604020108 75
    0x54503480703a01c4080d2140300181a41e420741c0a2240010501500c40b00150410034450030110300b00c000d2651750b140303040384d001c618440d00e00e440c0c0b1018008540c0034100ba602404103034051000000d0300c4407041d240e40d407440d00080315003010311300901c102804030b59160290a8000034200418401d461004601500352006070103600401c2d6408000181c111383d0aa107411104440134103801114a103904004000c06042c101041030003203000c02180d80c0c183c21404461040b1400e94414906407101c2e800c2011076102004950b500d0341d003e0040c140070500d001d20034504e007080b145803a980c500c40030500303d041c080160702c0442590404e20402c000350340c024640b00314800340c00907400e052900a1074540d00503c548001b11501c0c111410800403500000034406000f50300720f0b200e00f105540c0340148100320308800d015180001d01882420000070f8000d030001800f4910607001e48040500090202c0c403800c100b00c404116454500090050008a9441c1240212007002c0644640c0c60142c0000e401c13036038080c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 217623543 1250 217622293 217622303
    0xb0a0309060b040c080a0c0903030e0f180108010c09050405010605041a0c0105010306020322080a030c020705100905090f04021c020301020702150d230c09010903050709020d0b01050313 81
    0x1403442008615031003801c01c108002c104006910030080000c08080084504e10015484e040400c80e00500030010f540490b54550b841e55002034132001881101440142002e4200c0c440294a090310810720840390702810600b0000540b40000c08001003030001142d00241c095171070200140459076100703080b07400350347ea22070090041c50800c54411181384240c03c042d668035481c000000c010014141c000790701a1048540744019036880f040d06220004000300300410b400700401081c5002400f83d0402d1500c6011401641e0740c40760f03103401149032016490b5114001406200c0c00f80300354540510762540100009010320300c0303843d0a43c08242c840040032421200e14070451100c40856509404a4045a50190991070b4580030080b8880042d00700603071114445080c6202c01800104071200075540ca00194046807554641c07142809a95001020341e9040041c2010080302051040102900810301e60100681c3d4003005126407080314511041c1c0740c10802c040042c41500030707075601c5c20f01d403d60300720b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 217624793 1250 217623543 217623551
    0x91401030b03100203010306060302040e2b03020d0e03070209011e12020a09230c1804051b041203120e030901030b0310090b0103110907050304060c090e090f0d03060b0a03 75
    0x301c80080c0c03904440304080041140000001b2042000a07000a811284250760070710010240040d01a00c44044813841c90307190b0305645146c100e2001014007803804280c02c0c240189000e58030700b0190309480214821040c0380d4030000f44907046041090046004210a81c03d07120146502c602a00590f102d070b00c188102110490a40c005655030561040018020980c00704464140300c11032003500c080d0355a55900c9601018005045011840d085843c9404044c0302032103800f14000411001744406403142030b28418200d0b20180b41440c03c401440548801c20310008500c0040c5002009000340210035425203017484089540c220001040e212815000d003000f060303220201005c82c0c940241860380222030f5080071903002c00d01c03099100540c16240141d036413030301c9040c9034428490314040513242940011380c1000020013041c0b840d800b550781c0c0300300761400c080e0080c0d0b40e60002000c000c041e140580d00f1b400603601c03058185010040c1400024850600707100c0c4614020420f41d2a000b403030014001d064071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 217625899 1106 217624793 217624811
    0x1807052205040507050d03080a0606030614060307030e03180901050f0612090c0907030e011404050715030e030a03020307021005060a1401050c06070e1009140103 71
    0x40d40c44a4109011852030000d0100510942e0f10340104500450300d035441c02040b26030b441c001e07074415481d400c0c910a204101d031a80c0d13001c101454a480300c1000300e18170300c040c0b8074a400b004444103038896442ca5000c0d0f0103050350ac6d041ea22280000984003012286c0c04440b00c142a070290b814952681c0c1702d4091000c1a8143c01d04a54400b100f07001d0790f48a443d03006070f0150300916603c103485e844074072040414a20300090782c0c500003203921480c41890141c000d2185600f8000c2e6040c1c2501242400c0d02e1b07440e00d51155014509500880708240a04980682c00600901c8100b03000c0369924103a8dc0c5006002303400682c0e010005000341003101c0300a4a2a00070140607090040800c0e8082e842c0c00600140c0392100000070341400b409200c0340084003801e00c000f40c031884550b2220851440d403001005161040b000500d030902c450f0000601a86004220008601c082802c00080c84c44c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 217446043 217625899 := by
  have h0 := BRFrame.cov_init 217446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 217446043 ≤ n) (h2 : n < 217625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
