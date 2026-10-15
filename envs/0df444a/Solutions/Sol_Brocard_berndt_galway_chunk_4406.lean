-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4406
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:30:58.261563+00:00
-- url     : https://prove2.me/submissions/5dd10172-660e-4124-b07e-89f11eac1186

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 792266187 ≤ n < 792446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 792267437 1250 792266187 792266201
    0xa020c0a05120409111810111204030c0e041211070302120f010b010f020703120509060307032c211204140d05190f031b050310152a0213 60
    0x1c6102e007800385046204034840121100c0f0610f00c041c03000070303034152030a000740440b0f4040100c040c0006c6204160380d901052049275001c002c0c1c400c200e03650f9070071071500c56a0002d00e07804c14a05000d840b8104800243c0342485900440c5003410328000030b000c0c00d41c442d450200c9a81000b50082c103110384244000c000060811020612440213000c805076980045450b0080500d000d001a40b01e10020008aa417100811200d04014500f0510300001c410100d5a558400d40360003000903a10061030004042124800e03140d080152285c1c50560b42400d81503a40d082e41c1a45045c940010b952124419049142100c2e99030707504510100c0c05240c00d060244094101c20310315a15400f4840da9445002c0c8120111404d60340e000d4002200200c03202000c4a20701225001394090540e60001550000804480c8a5071a40c19545a03a40c0b82f80003140c480c00c4c00301e25800342c4008407882c1c03200c04005400c0418001201c001075808110721021114070301a500c20790101941044034035154070501c0700741d600008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 792268687 1250 792267437 792267449
    0x604270606030b1b0301090c050f07140618070e0a060f06020d0801061b151d010c1103030c0a120b0910090b031203060409020402090301151a0309060a020c0a051204 72
    0x80036592200c4c00c0442000b0410340a5140365020070041c05441034541c0240760102140c9000c50a00840b2202c40e00298002c07041502e00150400410303420031030422506901400e800d04080000b44e00c581199990043c0c1c0c01110007903d503180000d036031700071294031410080510300c458405180d900c400181d20ad05842c9203013000148190008141a13004600c140c03000303440041c010820112545805144812504484071401d444011030744070f2549800f019014030b092000006255101260064074030305800e151811250828420001060b800c0e105030f4004800c6e50908080300c039504901c1c2001443c11851603580322110109120684050b04100c805503252003508125100d0190f0405645a0b50f03600350000b80c18041001a845007010340240301001c1c80a4009814099800700081c25540101225420401c44003420000700038a5042144444010b1650a285007809040513450781802815245443e0300040d0584a0341c0b0200052000c09030000309680901142104200b104d40c820300c0b0720b07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 792269937 1250 792268687 792268703
    0x2d230403030905070e0103050a030509031912021b06070609020d051203010e060d0b0a1107020423072307230c2407141f05101508060427060603 63
    0x17055200d0701072080c905aa41100c0145898405613500322800e80c004048690140036440c0958881c1040074a1002e03420700c201c40f4200c80c0c000350203000b0315040300c0d4003c41301c00183c1d00000d070000f503c60710300720b070220b6400030801301725620203002240a6141c00d07080140144100480060b00610301400345042c0d4040c804d2801e4242c072a442008081e090101c00a4000c10300714000c20303038000b0306a200b100110060000d01e4202000b81d0000b5040383d4800003480640604480541070399005800a01e6102c2c03242d04060b0140451802a0800e21008081c104003041000524809124174100c00347d0280680741c2c0d00012440c109540f03291a01c0b030f5500028040d6011100c0e04d8510703681d1003001100c42090b5040c4a00b0200385490b21700f90121038900f01075050107005201c102c0072204071000d0100c102c94200c085014240011000084003048d8007409002d90170030340c0c00c240190303c4405107410020480b404185c1c1700c0d00c1001041c2040d125a500f103003840500181400704032460300302c10226030090b201c3c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 792271187 1250 792269937 792269939
    0x60a06030204053601150801060e060910060c050c04051302030c01031125050105280213060309050c0307080a0501061409010317040f03030302030a2d23040303090507 73
    0x10b41649400da4130095115a00d002c0020161036200c10b40204803014100001c0303250504041000c003a443d4540100c0601d94480105011400002c08020740250090310074400e9480d11480d1880e414006029840030403800c6d140c0d50701480b504000440c01458024810042d906103005006030152503410128040c0c01141c0204d0741c1036000340302b8440380da60b4000c0300d2403406048402503404010b459140c0100d0368803040e6141c01148003449880d201705e0301c00a40000c400114011b41258400c291511024280100882480001c01d40c01c0c1d8011108241004505042c581c504941489500c10f0020b8040c4074045000618500016003c0c440e48c0c0100000c000541e121140d1100480400032913540014610f4010000a1071031020f00700e0801d11490060300302925240405403100c2d2a074401d03000a0703004018860441801c0c8100108000702c5c62035203202030f000500c007000f0100c0320342852603c10399520f5480300c0c0f0010344c002c0e00013072511045e480c80d6602d020705d005001000c10740741c01e868512035004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 792272437 1250 792271187 792271201
    0x2010b01050315060c010507050c06100b0d05130f060c0f0c020a03020d020a0b0a0c020a05011d040b0d0203030409050403030b01230d0e0609070503010e01111b070503060a0603020405 80
    0x4121240404180d4440d441e40c0d9402c491000d40106010600e500000d0400540711091401e100b0140500c8665a4031035503019007541d600c0ca400d801138950b951401044001300900020302c0c1c02c5581c402c1091002140e25540c440f403018019800b488003400d101c2e00304000c0410040c2c07a6010071103039070041e01d48035031a0102c00c60480d24014004002034001c00616002d102501d80702105a56161008040d00051501c3d60006a0181c01007103410010500051444c011440c109490a01520080c603024043c8d11000c1c54003080100c01211041c05141d460604032029241c0c3c412000300c5e16000f8048070780d516511101000100400c4070103800080c5010320242e625071082c60740101c54401e9404064004807008200b00840e4070040c081c00c415035491001e04007001051203030b03620130112500a0001d0900d840145130070340d45c24001954030f59160030086a01a180007064175054a161228003820407041070350245081d0268210f650700d0310138081013295101190b0459002e0740d00c281d60600098440345 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 792273687 1250 792272437 792272441
    0x80a0b190902130b03010e2506050304150504050f12030a1401060503040303050c1603020a060501090501080d05090604050a0b1903021c050a091b030302060c04301e030f0201 76
    0x7101c000d50203003550b800c0204060f0740e500300002c0148000e00000301c0f00c0700c0303004040ca411281f0744164603510303e83c811b0901100025071241e004048a0a182e0f14601c0d09a0b01c0340000d6280158980c407203039640f00400e046c03190401c0001008400d4000f228410400d12070300712040d420494a640110741003500d6180e07401c0c9002c03086412108143c0f280390540e104e80e601500a81402000130300840c1c01405416481031100c4000c1c0c0e01640282c0181503108100e061442c10307148140c100940306820000100601140081c0114007400b1a01d0300a440b07640c0340b00040c046104a40c01103910007407031000850b1140c05040140b4a031070040144003407c500803403043d4144e001d18840c007a6036074407029000401c44095000280d03c0095124002a81540c55484822250828051024014400c0000d0040640400c003080d00105100c022504007072078202c084200c2418085840c1503809103a00c5031f500c00c0000142102020303404031954045400c2040c0400d40702e207440e24103900040602c442450100d0040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 792274937 1250 792273687 792273701
    0x503100c0503070503040f0206030411190f1401020f032a010c0903060b030c040e0d020c0102060103150c050c030d3303060e0a1a0103020906090906150a080a0b19 71
    0x2544a4a0441e51410f10940300c0ea00010411390b002d558003c9800e005903940030080d48241d10908014202d140b440040c0b001002e02900c0e13601d2901c0e080706043c03010802e80715100c4100d680320035524000491640042f420600310380100351061001143c80c002003039045540041c000f00c0154025240c45149050a00f40ca9824401e50045a0783c850700780042030050300300204c1d209001e002c4881c2140d0803004070f02151884603415903a500440d400310710303203941881100c0010f40248020111541161540d105951f101201c51107000e9581940184150081082d52084608501982d4450701c0101c2d40c0005000c1d020808560f407640e025420200a103112080341c420002d1001c2101c090741140c7d110801441303c490501141c0c42418101c00005410507840c0e1600c620280c01c00a40394598414040200c034042d200c603101d014040c08021b0503441c00148141d0048402002c1c80c01521028082011003207640c0091400340543e0034401e082c85001503c02d030003421900c0103091a0894100b0550444e102c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 792276187 1250 792274937 792274961
    0x16030309060f090b0307030c180308030a020310080a0302070503150c0d0c050c12040e0109060303080c0a090302060316110f100f110c0f07050108070828060609050310 73
    0xd290501100b44904070040700d410080c1840c003100c07600c85030404030300d400856031007000a1300c849980301d103142d21031400d02c2e6502203e41d604407900d0559440b0952800b0041c401604580d0110004040e043c483d80c2c40c0004103150004d90300032050300c0c14002e498001034000c2d80e000384a155048440d20146641c100d202d1f00c0107145007414500c0340100e400207414045900410060b061229252060003440790490300351074414425030369480c040710b03048140070585c420f01c81545052410030100350408110342d0700402050300684e543d50781c85025506071020340c1000e0f401440101c1007290b0040300c14964100b94820f030f01d800703274a8840d00c038496945282c0e0944440294010141c0f01800100030b800041001d40b4a0401154101d01020001e4603600034034051443c40d44541e400c5400f041080c052038000d46000c0c64622101d251040c00502652006010001c64001210030303030340081c0e0781c0c2c40d09500115840300305002c02581c9150081604a8a001c2c0078441d01070080f0300e06202585104004003d28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 792277437 1250 792276187 792276197
    0x160b0901051e1306060f0909060e01060b0703050c0709020d0b0f0d02010e010507050c1f080109020906091e10082707030803060a2c06120601050405060f0d06050405160303 75
    0xc0c0b200310450114020b20710480d1403548a00c00032551b040d20040d45030140c080490005155030750342c00c084c003d59034000c11513003850b49441000c1c01000e0300c080c115141ca54140c10002d58590245030391a10384407190340800d110b1440403c10526014a50b0410061104112423440140310030801700100d001d50038038001d02284e19420030300c41c19409000a0079900d030286040d50314141c600d0002c99641c011042440085002e2540700c004800c0c0c1116403035000d007145a8045043c4501c0801086052003621110740c8240070f0f40706004548035070502800c84420000e00b503807840c490448001350907104291107031540000c819a104404078062001041c01c0d03003004008040a514648510f02c17613038005003500360841d0f815040800d00b0b41e0348502c000041d5110b00014003120381142d1050b820108098a050b20400d00e14001c9c1c62a48800118a070544500316000a80c0da01e0341c00c000380c891002c80d0120703a040100340718441c05100c4181d000903c1240120242c81d01c80300d210a500381c1242e50b0303000040c0030813 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 792278687 1250 792277437 792277441
    0x308010f0b1c0f091e1407141e180f070c0302030f16021518010306080a1410150503250e071403090f16051e06160b0901051e 55
    0x10040d400203070f24518241e40014494045844902e9068800401022100400c901c813030200100b0500403040c19a011001d000c1c010304000c02c9130070245211002c10710a00450040c0c401e112a2103050001140c00200300d003200a00c910060a1410313000c8415000c81046480007545040c0500407140c54182c0c140e000c3d40c900030003840c443c05690000d0000395240d040710070281c0b005131035003140849030090180c18035803102c3e814407841c440700621009440c105030400d40b04118861000601881c4079501003094984450b42d004254500018090348600603810701c035528900e50144528031042c1c5000f40e0a83d088000b4030300c9240781c0540c5e80c1c500c07980484c12070030082041200c50102c0f02d0300203246150003d039600c14540d01c091140c206880342c2c176154000e2051040c1e20b210800015a407444000b0020351194a020b0010301780ca81c011205280c10040d6003a00001c1d540d820086900300100f41c0b08008d8802120b04000d032501c2b8003110508601d42c03030f00380805e41c400081041d00518041e180c80d031312269 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 792279937 1250 792278687 792278737
    0xf02060603071e1a07150c0801150314010618050f1f0302070512190804080316030921080a060305030a0516020a06021f02040e1609080a0308010f0b 65
    0x140706141c280386a120720540c0c01207400300b0940f0451450440c081c5115480b141542007541c806c68483c149640c0e00c0f80742600040303001d0b810940c00c81c11141680c41c452007980d403c84080d00908200444031081c5500c80c03001080c0c00c0c0e044884468150750424040c00310301d4a950521440a98410059600000e01d54600000083c00355005580031001c0c41c0140c01c1504981c0c1e658504002c0f9202d046140b5404100c0711444561a8901206000c0525088180d07042584a185485c400900309000c2c812025640c60500c502170b4004049466000000c11400540c10240c1b011003050201444002081d00d000700329105164000c102c00d681c0c001c0c0c091131810202074015503141d0b110304049886501120030510169070b0b00400e80004040c650003500c07601100040900b10f00351407020110710b17244148020f20584042085180c1d0000700203207004074444641000342c501e11141e52140035944648141002019072000046040302c51724001c14683c542c5451a542850103810914503010070722003c1080780d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 792281187 1250 792279937 792279959
    0x30109020a110307030801030b06040c080606130e040f0b010605070c05010f2105060a21140a0507090212011d070e060d09032001090f03080402011e0c030f0206060307 73
    0x1e0780c0650420307189400b10082018116003040c0c2c4280d000c00da03080010401d0080c903c3c00c03180c0c80316045900f003180702c010010141c4400350182030300e07001c0c0202145259201041983d490060403000040060303a00c1d0078508090490329006040340c2c0359503458000240316025100380c1c3c2e202544144402c1e4010705003001111524001c040c0d880800001c40c0d1030300100ea00d842d460702c001d0b42c0035403070106803844c00e4014409008a250701c000c00c518601b40c85c1075101008521031242d603540c400441075821050ba40400c0c40d08000c1a0090110b020f20140003404000590051460007030b503075081d03c402d07a602c0d114100d981044404403080f0394102c1001649040c420140340d07080c9040200054107003108001900d00300d401d0324004602190f9200309042c030390f2046d60b560380340c4055440000d0221004d165118403440e4207010004081c8a514030104085a02600c83c40c01140b8407540c0c85c80381455035003c0204141440c0e10184c0103d0402c01200e501c02e440460a14841c1401900501d0014a45825558 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 792282437 1250 792281187 792281197
    0x501020304230d03021c09050604051207050301020f0307021b10030e0109140106051903052119081518160c020d0809011d0307090b03010f0c0f091a03010902 69
    0x36032a5518150340c42c060f41e54240030400716019600811500c1e4410350071602d0f100a41801d0810312038845005c1219948807001c43d070940d08140d400c400a1a0000e8540d80303070407401d40185030f0550001c10900e071a118204095403140d00c1a500b2654400010381144040965020b0460f41001d001d079071a050042c0240c01401650900d4400022900083e44451082d0418000903d4039a5162a001c0013540b802655030154401450042c003c81880e42d0707a5a81da911800007250820289903002c0c40b503401910341983e0b4005440d00d24a2204805450010311911b01155403005c25808a00004040d007405200040c1c031061a010205560303ca041c007900e0110701d000907550810021004480058513801001e041151058144648480140f0009000070a038414000420710300788914490319940003601d030f400c4a0003d900090020704082c0801e0160200c416070251150900079000000c0d0382c4449400c0150380305d541c0b0030001513224664107840c0c8100310106c0218100a1005001900480d40144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 792283687 1250 792282437 792282479
    0x31803081f0e01090e160e040503041701021b03070203060a181a070906170a05060d060c020604060c050703090b0d090c0902031e01051e041517010b09010501020304 72
    0x41c40304500c141e2084882603907080480c51640600040020b082c3c81d014000d06001d0400240006081c0d0041450010039984100480f1400240c0490240030003130080300e0250515400d0750040d40080300165010394081d0203c2907400140b0150030001401c088142c81c40503900801070640c0c2c0d111084a5805880390419006030b520070790003a04c00144191781d002001880c209403c84003032409141c041c11180007640180180581c500c9908254040403010300c1c2d20118028000499443d5540850700d030b1000703541d001b400384d4942154180010b4001408038404c52003020140100c419030442160039004240008000c181c07490701c01e2203408141b20140200d40c075010000102d0280a13100c1e8240d901c01c81c2d00400c2c02c164008144a190b070a01082100c0d01030409400c0780503549400c011540d10609803c03000340501184400540e280e43d42d0b0486c0c002c0c035075101d43c581440c58031090f81844122000c54003415540ca00b84070441c403800c02c0d4040c40e0480700141c0240d0b00300303480c000840400c014009420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 792284937 1250 792283687 792283711
    0x4031e0c120614090d02060406020d061706191a0103090f1a180307080a030c122c0706080609130f030f110616050705070906170d03180308 61
    0x3045010111007400000c82c000d05011610000c40302d124180d05401030b003260300741c1e001400c0a840d401e400156240c2c20a42c40003005035280c28025000c801072400390000800d14990303d108036464440000c001d4019034140690210040d024082001260510030803880e00310900e2010000c1c542c000c0d40300d5601e150150b007443e1412062507a400500f05141640c161681030210306010380f411209451004001a2000031450b265260302d841a41d4002d0240000825840e920500800c52281c0380000c07842d12401018020b45490242443c00d415180e1800b080300041c25907140ca4480340042d807201102c0709038561205a844103401d204252500800000c03d090001035034800040e103040301c3d05842c90095642090800454400814440c0c0711100f9210070350210042c401490010405001d00400034104243d4417030262074440e052150550055450f240380a20016018044010103021000c2c1e40003034481041038060250100c079010600c0703502d00790800752290002401010310303a4211000b170b011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 792286187 1250 792284937 792284939
    0x512130e0f09070b0a090e04030e031501080c0406050916090f08100c08091209010225060e0102030304050604080d110a030905011a4204050a090204031e0c 68
    0x200035150000340d034107802224a0408000c1903003000d11914015001c0441001e28010700060014a03403502e1b40141c80c407010124000c107003018014810f00f401000041d0540d050b0050950b06070030000003d1240403490300444a114665280910820050f10030082c40c01d44039480b60039007d20010741c1171040381c00380300c02a400880e5008860311440c0040c860203009214840011031010103488044ea0700364140304070308040c801c225502141d40c0000d081442d003415102e40d80c05004030720340344130020541707590486c0d801c0c010150101c07281c540c829103030701e80c549010003041071004a0b504e21003290050031581103071000c680058007100082c49282c1d038100020070541c030b05040200c0544d0154a10001203640c880c8068200217083c000d02d034108505410b00c86003201c0d01400315901e05071100040c45044510050081c009040310713001c40c00e032000302d11101e180300e2400c0b40401080d84203000c0e00384607002680380058030792800d00803241900d40c040d650440051001c0800384400a02850482d059038600030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 792287437 1250 792286187 792286199
    0x170a080d20070f0201140f09010e031608060f0603120f09270406060b04082112090703051c05090f0103060306180209060d0308061011060709090507020a051213 70
    0x14020755409100415510f140500c00500000a43d5050b400d0044007030080341c4003801c6810a48001c15020f080c80100701c01407400013402c0c100c0c0e1501849003820300340d2011408690020b6a9032040c00000483c040646541080660341e00000c41c0300d40c641c0508110841c412038121000e00340c522000b40080300c0c44d0613010340c90107a1a14032040340341c20903983c0c010401403008902814008001442506140a0a04024a44803072207249196808032140c400d0543c0c0701c1c514002c48040600059110b00d241c20009000d54465002c0d03c010ba440b0320030103909580311001641070343c5d04003040e41c440300e250000c0b130005e02c42620380b922aa00d042c1951703040008085400f500441d5260760200c110108441130510401c141c4280203032040303010740300c42d144c66400241c015a5660300314408490700c08818041e0001203035140030165000e11140900418440c200382c00c412880250f4811140c180f04a03030310700c00120703a00c12800d60f024019911030061001c5000340d03d001008450500c00c610f03208507031100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 792288687 1250 792287437 792287501
    0x52e08030304030503060102010c0e030705151303060e122704090b09010c0f171f081b0a080a02030a02120102160c05010206060613091a19170a080d 65
    0x2c0341079000c201d000080200039a82845413160314422804c0c2134445030100380202e0b07a1246603000c0c40317000c0e021311520250b181d4401070544200380f24000102d1200d584904e00700000e8100811420031078465901d218640514107416240c1000002a400b440d01280380386202c620b01e07030b0056403a0480e9030344981c42c01141c0a50400c81c443c9034a00004184160b10041c0104070f00c82007102e0b801042a402c0030001491141c20400b60000404000b0255110003001140400c0c801a40814224411103142c03800000303034543c208041a40499032078030385595500c4581d0b120105028000e50580002501500529181d86000018200340c0d0006040c8403042d0311514000307228032002d403544001c07607008005540c3d04003d1254004002e0f6149030820a11040300b541003000c501520035215140e01000820241200c0040300388800100300310305083c5150307851a042881ba000340311081d00c08130307401c03a5842000181d10404981c4844d005180c03516013142e83d4002c00410924407082d800914240d00340c11010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 792289937 1250 792288687 792288691
    0x3070e12010606080a06210215072904030c021302041505090a06050405030706110109021c0c080303061305060a17160905061302070510020f0703030b04052e080303 72
    0xd000000e0440c14100040c0c030310a0f00403c400305c1c150070301c4402e000d09082c03030441d40f0321080300d460324012412080c030024202090401c8400c00c0128007080321403d000640380c8108031441c03050003807103040344092000041c02c04100c4003d8003003400d9402d10710040c280481408110094002c0040c00c1684400ca185203448034114200e0001e0400704038000310b4a00603c00c0070007800c031030074024a490310702000310341c0ba004c20b441035400f40804c6828080a03e2000e4100005240e4002c1c001429000c07454500e200b1010003100640c0d5021100078042080000082240d0241d80c000700305404100100c01c40b440a0000100081c1d0884400880001d4900030800c2460035542a10081e120b0301c0c412703070080b002a120960003020220b040000f80a415180d01c5030140c5902082500580d40c4e24040c18810700d44500d8010902550b40b0003d02c1000920116020b054000d100366014807000c0c2041c800c010940c0c41c01d41381c1d80080ba5582140701c1c60501543d1401100c6009000c10f0f040c2c00b590f81103d1802c613041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 792291187 1250 792289937 792289969
    0x41502040b0903010e0606090f09070b0a080a0c090b1b0703060501080102031f14090901151701181110021c0801030b01050111070e0901061e050307171203070e 70
    0x7010800c1d0005107000e0090758815402c000c0105010320300071000a03000d9201503c050a09800400490403001c1e0a001c18001703000a80c000c2d0381d541031480802403400904a802c0643c1030b00c3c0401d0442c4c0325209040400450395540000da081106454401c0e010100c00e0100040903c951200000091928001e50b8000d1507208001612440c101d15226455951407041060000c000f0b0800d114040500320311215804007178070341d4480b0707980b841c600d80d00501400440004003441002d00282401c4a0300b4a28000850b500c000c0c8050b024210300ca0070b0250300c0b5400200301144903018140c2e0307410b204c0e1003032000c03120910440f000c040d4034503000070713500c41c0b182c0c000750010b0041030040c001d0180d040080d0b401803900303103400040c011186007101e0302c44c9500d0251b480c03a20308031004250084002d42001000e0300d240080740b01c3c42d42110b1042c080c0c4035014490360303020740600d420010700582c602c00400515041c01000d088920300403042000c45030310003400c4a007881414402102c194440300c4108240300d030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 792292437 1250 792291187 792291209
    0x7091d01150611030a0206133908070b0708070609020604031103160501051206030132010806060d060c03090f0b041709010f03200a080a111306050304150204 69
    0x410254010325401c0d060420302440e61003017240c00c5045500150351035029a500d412002c40000e2423078540c485058a240301c0c8650690441c200e036020107400425110040440847d13401150b5406450792107070401e100c1e0300d4040c00305200b50404251440001c0c00e150384201c0000640098a83c002006504070b5042940c14003e10b40c0445941d0504001822418800190b260340051a00c03000801e10710400703603c100d843c0c01b5500410a02c0c2c03802d4001c040c52461180049847c0c40d5052814000d11020015885ca5080c23031000006402e01c0c00301d440c6005010241c0704491300741c10b9448000240200c1d41c01e007410107a071186400045200d012841012910960244440d070506061801420742d503000e0303005800c0010001802c0e182c0c1c0004001951a0040c20041500d401e02e00400b103400d82c03070702002d80c04104000790054480d940a22550f10034103100008214040600750712004a000701c1001841c58600d4690070300c4078500500c05194064070404098000d522044c0c0700c80d082e80c1059005d00c10301c3ca = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 792293687 1250 792292437 792292439
    0xb0301080d03061a09040f061d0f070206041202070503030f07060e0c0913020a050306040c030c0e0712020c030c0a08030a0b04050c19050c0304122307091d0115 70
    0x31405100e01403550515140c24441e01c0d0803c90002d41e0701c103c03070840318880c1d20001981030b01519aa0040c0040c4003078204104400b95554030159004400004100001c84030000058901d01d20100214000d50b450b9005081c560380303d0b03079907850b0000007002c030f0801d604c10b0f1100007415540420017480701141c650348050312420310349800410380d01e82200101c11034101f6142d103a001e03151020301507405103000d0441441158140042500085a170300916010702035441000f09000340106000200e0b440750b04084805035403400d001c981c1d244169a148002401070f2198280401c481e00030740100151401561705d8812540c10702490b02c1b1580b0411520f201d404001c00104044a00c102c5810315030584040c0000c0c540450100302a201f54102d110400820f0150561002c0c851002e031216080708000b00c1c0d03600d5132500c0d680c403440c0d810349000711021401c03800e08801e400484a81501403d228500034504107041c110280c01402800d00790300c0100920a8044900400034000e4074203c8600241d40a001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 792294937 1250 792293687 792293699
    0xa1106250503070c171b060c01090c030c1a0910210507020f01020708091c020a0306020408120a17091c120b03120a120f020d0c18120807051005010b0301 67
    0x1c1034207640800f0010f0000b1800701410344001c2411030484000051140c000d0724500300003070160099102300100b5610b00035421081005c42704821007920700030542c0d00c5203aa80c80440d1019044001240c2c907103400240311480450414100c0984c03140342d82c0c184000d1108690901b2407440c00c0107046034000e00c0c2c51310188031449805210350800808264007c5d4901076694031205a1885880400c2d4020b59060501d03044c2238006075100024103078001d141c17103005a0b90741400b50103900140101643e5000e2664031080f004529800c035503503031806440708591250203445010200300020007040c4503009442018500f03100d841402c100c0b4511307945451194101424030041126084072009003e5800f21100103981c0c80d03004241e0b51045460b150640c58103c2080351400904407000300910040e0012035541d51015031078210700281c41d6940e1f51084011801003004200c01442d1103040e000032203000298010070b44035030041596601850484541800d00c003541022104242d00031007c0184c00700040c003a07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 792296187 1250 792294937 792294953
    0x207020d1e021806011b0c0801050c04030b090304050d02090414060a0903020c09010b190e101d010915031d160501020d020318120a06051501110a110625050307 70
    0x51540e0f030351442d885281000c0043c01c042004070b0350381e451481010f01401004a070b1041c00e4042d0800000038041403c00f90000521604107000840f01c203802e1100003404c1450001c02c3d06d003161402024204050460780a014540b48060070584044c80707040c0780c2c1c0c1700c44841002000d0081281810000f1146100c2c10001e003092440f40c0d200b842000d14000400000340fa101c1950581450204d00d940504280309054440d0011440f07a550080411a49001e03155084204400c8403a1100d10140c0300c0c40803100111012002c90041220034128a6040c01420303204c2d5004d07400303186681d00c5001084e010740701014a0200e4082c100258006110700c2403119590501607a0145143d90004508120001d403103802d62140c01d02115003c1d035180c29580c101c0c24010001880304981100040055040000b004002c4108400303281e070200d2010070b003010300c41d100064503030381103908020415201d0b82d0900400c62154416084081c003802181c01114600b10007002d10f02e8054400e4001310760390411850200c031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 792297437 1250 792296187 792296209
    0xa0c0e060f041a0910030c0b1c0203250c0212010c030608030a08040f230c0103050c070c03060c090509070f120603030e0d0c0b121503030702060d0207020d1e02 70
    0x2000b141400703841001d50809200c941410074044a030040559140c82500080322000d078406048050f04110024001103c1d00080004401d10500e04510143e04801d80e0281d10040e0380c1e035166030700819107000744d100c124518884075480c1e03440c01d10b45000e202c1c0c0006500d0303904040d01400d00d95446054051441d0540301e203000034181c520180d03041400d513220141844c5002000600109a442d9809041214030740c020307000d207400c019201c200c0b001c10904099503101c12460150101c0d1903c40405e05402200702601c102c180d000007508103a500310394a8501502025407031a0600c03050010100f5503941d0200514030400c1e20341e6402c81c00c2ca108410080042e036104511006007481c003042800440e1317000045202c003000030340f20740b2104003961a01c0a1095030703a03807202c03052050100d920024462124001405441c40d04180c82c190f6415030105030b00c900c40c0a4000398004001c00c000d14074400e0b0b1307030080d016040c00100880499100341d242c031108070080305201c001c2664510b50380011454a81c0c03280b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 792298687 1250 792297437 792297439
    0x60519030501031703061c0302010b10051c02090607121106100f0b3103020f150316020a050604060b011707020d1b140c01020f010b0f120a0c0e060f 65
    0x2016952450f00da450060b118864814480440000051b07801d48a5080c10008042c0a610707100300e410090800034003c01484c1c60043c0b06550059580101e070780304e003050380c00c941c3e41030f0405951485920200c1000390302010072682c101e02e003440084003041c1104003150510442e070300d44a083c4a13440003090b007400f9004000e014218040c11051080700340c04440c1006842d100781c1140e540f40004141070088a180c90b01c452401d008844203604142d0715401130200700c0e40700707890204080300300070204400003800c0b0740550f00c98a814000100084040040c05030b89503000c1c015038070440f0480d11402d0410504840039990240c49010342112541d101488007032500490580189078180701c40001c0d180c4d000e80084004003c4940010003030b00206d40c0e02074003101c2e44020900d01800c9090360301303500e4003003104d10140503014001c94864901418007803540c032524024400c3d601c0c0c14241c0100140c0316441d030072419082c440c2d800f07907400240e40100c1510282025504008041c0380c00e00800c0504c070f003060303e85 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 792299937 1250 792298687 792298691
    0x70909050c0906031f080705010f1103070609081b16090903090303030c09080a120e03060f070c030306151d03121c1413050123040308040809060406051903 68
    0x8000c90481d0410380b049804103c0f16141e0700d880380e80359a6448100c1e0442d0f0b8030b03850001072002034000d1000502c002124001e0300c0e0140400040201a03450701521540803a56070403c001c4031001500c05e602c00703c030b03c3c0c4c4500705040c180204011864290014280740490503444520380d060380038500c075104802841c4400061040007203a0340c00909043d040c0c8070090074540c0b50b6074440e4050b800f0306042d00242180c00115010001d03541450701c5016109100c442c003081c44110020218140895030610944224420140300e8503000700c03ca0707609a5118042c4c08041d561200800c04103a260700803107c0c1000d035504c40c06801c42c00c0285822403491103801520992044440f0481411110142c91074003642d40150341241e0701c200c0e800e00150144204040c5001071030760800c0450307140c4c41040b440c0c00d800f44000708804540148522503000702140390a46040c1040c00140c0080d02c540c9103185e1040c403c81e5800e08050300b200101d685504181c0015010450101b00c948054110b030400480f500350510f02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 792301187 1250 792299937 792299941
    0x414090903220614090d120516030306050f0a030209011a1213020f09150103020d0914070906120b010320150a120b06030c0703030e07180e06070806011206080a03050307090905 77
    0x99564100c01b803008081450200140840070701500983d040071201c042c28890700322081c50000d00070241401340c1c51040058220601c140d041c540245820307a039003e0103500071039090180034548042001000c0743c1c00da500f044546a42802c22003801d0048440741414001004144100b0200c2e0911110080c01240f001d010803046141b004507803c1501028200103036210103010543c0080c125a4102404a07000c1d4441c3c3c4210800020b075840449958100c20414140c50301120044241d148401070070020300314006001040d08001034005032258222a08561140100844d0600042045401d80208041480c1050f6604a0348804429194100400c45140b442c0c0000b103071400007a080000040001c1140d80030180281e00200c010b1180104490645075686100c48121040350341c0521018100000500f610340c2c00582c41d800388a9544800350a9900d032030046a041808000070403440e9264080004c00c100c06200682000c0c0c00b030382c0ca156407440c1c680000340000c0d050742d000c159507a01e0002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 792302437 1250 792301187 792301189
    0x1031a0c04090b01050d060b19020d020d050f090a06050c16050a03030f0c0803090313091b1404171b010c0807021e040f0c030b06041409090322061409 66
    0x12078050b07410755600002d0507840c807401218a4040d140041e50040d151080204600c159880030344000060001c407031003000805201213171144841d900711000b5030b0014022460740c0c0c0c0214041c20400e4046000c0f04c0c00c1c808280001100004542c0c010340118900094051400d1020f000d50410714440d680c15031410351404010840910841c0320250030007503d04c0000d24560710074080030740e4003a00180303201d0326410300c803005584030f6000e2042180d81074046580007071800c02c180100b500c522030002c45060b240c0400c2e4001e13140c83c200400a0700850b0300c10880032510303200300c410124420032100d0003007010ba100496003069510340e00000e941842513a0001000151060045550030766040c4c5200310640030080006445c0c0c41d0030070300e090f4070600f0415001482c144543c8075101e16a59550203002039821039051060904c0f450142a55440d41d800c4039003c1410031100341900000414100c03480c050104803428201504c0700038540c008050840e003040304c2030303010400e040c2c010f184a403840c1c5059030300f030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 792303687 1250 792302437 792302461
    0x1b010b01050c15040812100509070309120c0303110c01020304140f0703030f020a0b16020d140a0e13051311030111031302011103040906030b010f050a030311190b01031a 74
    0x14007100301c000f1403080024100300790b0b0010344411040210010045003460504001046014080d10340580c844400080c0103901c0303402190009604002c079602d184003043e40c01c44207407002c1030042d0103041d21985441b0119184100508940381e10800044c0c4034145848d210b00c00c144014410001944032041d000184080868510f0481c0c1c0c3c1400c0161640042110507400c0c0081c44a01074803800a4400308140000016451803144000394240c902d8040d040301c00750703030704185039014144004042c4059207415004940e01500c0780c0c0700425401c891f171000c81c8000140c60702182c3c3c1f84c4226055002e030034104155040802031b42541100240140180c96240d05454007005084c1191401d4558000c1c041d079001740061910020070b802902d584545071408a0007070083d5100465803a81001d00015695004e41d1102d02030304e0703008142c03540c1c1c285552001c649610900d80002c5840c02a40c01c20071840c01803040d0b00003200c1c81540404030a615506000040051054410315130800080030805603100c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 792304937 1250 792303687 792303703
    0x6190902090f0a15120b040c030c0224220c090c09060206010b090402030402060c0631080307030c120926130308030a0e030304050312011203082a1b010b01050c 70
    0x252501745c2841c0304806001000d008028440790700146001c500a1034035074507070404141c0d100e81d902181d4001d04c42d84118800c0c0200c50041054110052010541c00c00030402c070f5100076000a038000b5902605503e4407159400103a0184005982d6080780d006440d4208544000038038072400a0041980351152603c4284a0080d9440c411a40040080d00719601c14007900c02d0000040219486480d000c01070200c010603842c824100800c1300300e41ca00c96140d200d42c0c0300c48200d0b80406500c0c00d5403107180c3c095001c0c2083d80d0104083c04803070300700c1c0303024280184100384a19001c0d43d07401da030f082d10010940302e9144001440c00d0364600b003000300201c015000684002200d43c0611055903c0d17441c0004070f0002c1c01c40c1e022001403400b00009010034020f0010290543c4030b038421071081c0c42c1c1da03640480000c1e501415801070101c0c6992001070408819140044c0807581d20001c5600d40382d12501d20700216a214203a00e45196281c05643d65031031900f4481e08000003820b08003245044c114131400c96032a107803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 792306187 1250 792304937 792304979
    0x109060f05010f210e0607180b090f0405090a020306040f02180702250b0703050301080f0d1d011b03021006050604120b0415021201080f0a031706190902090f0a 70
    0x300064219400000c3c0d014803030081101041d06e1140c10201e900404070103408100d019062142d440100d11001a4030071107a12500003002240b61450a4041c000035003401010042c00340500364903d40542c8040c001c0c144a00d2064441d4201496144104003045800060012001d4440d504000126400044604100d01d0748451002c02c101c03003040d0716402d0052a08604003111002c6080c0080641000c091416685154251010f4007007251103140c1e92460003010328006842c03103c00740d403082c1741000c4e4070418a60616241c80e0420300000d01520a1000110840040c2d00090070061150701e41d12914000e01400c5a52501e07141c80c00c01d80c41400448400c000c0e042140540c04030301040b00343c02e540030700402406010740d1030319166400035000300400d12541c4410301031411001d200e030300003181d002111075140d10741000b030074613280b501005014001e048641040d044841c840003044201ca80304000c0030911009642d03086040e05100e0344d820300c0c2d6015406614910428451052403142c600c2502c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 792307437 1250 792306187 792306227
    0xb04060e031e070f080c030703020c0906030705130902060328060e06060a055208070206120c040f06050301290d0212070e0d020907050d0f050109060f05010f 69
    0x201a040030f0307005640130180188031102c001180d010b4090044050158180a902520048200340b814462450411210243e043d0400f080902c401e20b440505220610302480713000070080308590100b0b140d903109541c0340c249074102d000d4210011501400e2030031100101502408540e00e0302e081001000d034040c0c02c25104000c0800c0d8860041c1c4540c02b61411508800401ea10003144201c0820350980c1d40d0158401d03024600295244910b07250706444401a203601c00620490360607207901209401592049a00103020054a012540822012030141441c41d40c203680d96403a18040040c841c2d0107a2042083c4601400100490121318820b511218100c140308040051299040342d29403282102c6803404603c08502c030b0b4810207200c10344078402da22607240ca0101c49040b008215072900c0c0d0000007540401c02c50002501c051040b80540181c13281c005020800280651540d421344c0d502b600110702095448070101b204900c4518224018042130900c2c1c0300440384202d0040030b1744102c91148000c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 792308687 1250 792307437 792307447
    0x20706030b0d0219034b06021305040506030706050d0c020a05060708092e0c0315140307050108040b04060e0c060a02030a0f0f050a21090b04060e031e 66
    0x92650b10085119079402440408512052500f209104500d4002500d052002d550360190f01000801090a00d05941c4441446010140010f6420a13094410050350410b9070310800300082c21070002d405114107070000d08075020306001c00c1c401103e800904242c865480311108108254100e8100c860302072820401042842d410030b0181c5c640060782c1002481c900c990401c001080307603c560b01314015500002036804002d0000c55010305007640034403051f500c1c100110a89035201d0b244c0d101e49403070009401c0c0414401c00e068035160303a00c042071f80280d456442c40c20100b41c1600d42030000d4000350009080421560825484001c0e020000500c024000c40e55218500041e050070000540201c500a00442e5a04100324009440c1c3e08000700c65004900c00c6840d503c495130003604585035600e4181c0d0303028203002c8245806c480e0170310038214100c000000500d0541c1c0403c824007443d003116000c3c0c540d043d10340c1007500e8040211031402d101c80390103410500002c41071111500105e407101310014140c580703071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 792309937 1250 792308687 792308689
    0xa1a1608010f061d1216061815030e030c07050f030307030503010b0c030d0c050c1501032a080a08030403170103020901030f080d06080c010e031513050f0a03031515020706030b 77
    0x4003e01d04449903110162585588000c01c0015002200d00100c20b02581b40d1a03a6060550f80c010b1840300c2d00c036105581d0001407040300030302d00c01980300f02a5031501044a140000c0c0072411540040703801e00d456000600c0c24456401c00240030340100c81709400851900c1170030b8034000c200303000c1802038003805400000d10f042d4100c0c082003074611502180008210207808250050711a40c0030600105d524013030100342100b06481e0b5000340d4100d0750000102d010030705035110180c0e106146040071685401d60083c01003600f42d800c000c1c5046080c8144409690307400c0c14280a08040c0c00910030415200116005200517265a8203040c112640300c1c42041c4c0708109031401007500d0081031000510640741c03000010301d0801c0040e070b018044400303803182e0258042150038036813100600b0244810004510300868802606003e0030300c00365015074103441032031070b4040700320742040c10801090700041d0f205c200c40361030100c007412500001c00c07920000c40c52000d030040c0003a482c1c8500d4855107050656850612441d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 792311187 1250 792309937 792309977
    0x60702011115100509040302100203070c230f0604080a123e07082505150a0507030b0904150e031c05060306270a1a1608010f06 56
    0x1000d54190199088941002e0380030115500446500e2050710500e42c0004d82414101e141c02d011b160154050024101d0066040b0b010398006000807081211408115010402d0581c1c500d60f52801c1d03601b0b07400d140b20194049481d201e5030030710620f001d030041c0091000050b9034504a5218800c5030078003000102c4803409001c01804c2d010b00d4030150b03280d440150202c2a004445129808039124815059011540d0f0700c0c2c8080d02504c1c0b03004025078000c11045040340c54040c4c070b281484011410314180e00f43d103aa0740c207007002c42040a242c0750540c0102400f5283d41d5501805601503802c1c0340422090b850200003e414042c0600302900074044250241400710b9140c00814407080c01c04212039850841046d0304903810001114041c44a141401150385454042005400358612109000600410b000422142d9030210108039144c442c48821b00300080c6041d5000d0f44d030088041011040d072910002d01c2c1d035988500e1001008000a520042c000401900340d401c003030341d2880c034142c82c2145c40c80240b111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 792312437 1250 792311187 792311207
    0x1e050c120403090f0b09090901061d09100903080411010c0b0109020306131b09120f02152a0c1f030e01090807060501050a0b0c0a0605072601060201060b03010e0606070201 75
    0x85615501000c548840c0305e8004040255050720404541d642c0c4807c0c0a00300d40c1c1724000c4008400e41c141421182403118090150000c141c2c205031015400d0341c04100e021a02c2c54841140400c0343c1c8000c110a00c609161551181039080c2024048ac0040796a46901094140120300143c0e9010021648685600842000035800940100300d95101c0b40c504062840000d4000340005111280100d210900302008c0003a5983c80100202040c859500b040305003205132106401c10350081c09038442003007041d0350382c04840e480041140e080300c9052500900700402010780602074000a00e11414110400b507980180348442d01d000589171000b0003180c0d0241c0300c4408040c2c88160081101d00034442d0030380c0010f048460440e5181c2030b403a40c43d60844210300520f03100503000e810080420300801c41513008541d10022914000c00880c105001d642d0207403100d0301c0ca44400a080e4401440070070303024442d840250403050700b03d9042d907152100584540d6802040c05001300804070b9401c0459010303c1c04c0075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 792313687 1250 792312437 792312449
    0x6090a090506181b0f100203311401080a0c020f15220f06020306060c010515040f020c0703020d060e10020304110906010f030b1f02011e050c12040309 66
    0x9182c6080071544a445002505a6100d080c00f46500302511019841200250600b014040c054082d03081e02c100008021420601d100398001085500402005510424542c01505080701c0c1817004040404559036695001401d688072020901106a82c0140440350707c42440c0c07001003030445c030003d81207041c01c49200541030244a40c5141d1419240700451481c8a2901c8081c11841c940d0b420503091080c0e000c6180281900182c1c91207040420700300c1d0015640b020000c3c1c240b070300d441d140203040d9003143d41c12182c14650000030340e0000000d00e071a0260419040c8000002e6040646001510b502c0d4042c61000904c00d2089140e0b4104000b00c3e40c011070b5114889100351206004886203c0340658030403541228410a61403a000d11841d05241407409448103079036410100d00543c1082d0005d104c0001259480084044014100750002e1040940006030382e0000c541004124080150400f6090148d4502405c210801010130201e906450040800c1000c6151944840c01c2c1603940c0310040d0804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 792314937 1250 792313687 792313693
    0xc0a1d04050c0d03020c030d020303010e04200604030f0507050405060a180e0a030f0e01021c050307090f080d03110406170a020d090b0601111204090207022701031b0503030306090a0905 81
    0x3e0030901d03030045480c04030b0320019400d80303c20581001080341c03030b441300f4050240d1004041000c43d01048a40c00341c00400c032700d90071048800701302c504001440c540080d40102c0c1c1c811100f02c5c00008015003804110020441941e041c05541085d8000590101180c0900c024134200310200c1c2d0000d5056800c0100c800700b100040e101107180354100144010710341401c0c907000c90544803030b041c120b5100017050104d528800e1055100301c414148211055400034205400300419100301251400b007100c03064000b0705c0340c20001c001600e00b8a0024064684d00c002504408909220820005810001c811b030009120508010159110804607000f1700424200c0c415041c5824105010071042d1007905d0b0003200c090704d841040b130b003c0050495840c14000c01070680d881c0c09100422218105801030091584000d01801c550101c80381c100003403c907005490f4690019031001002440304440c5840003040e100c80c070344001c0e05d080601007540ca2101402240c00351041c45e0001d12011110b910120030140c1c80015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 792316187 1250 792314937 792314959
    0x20d0218060109080c060316120e01020307020c01091805060a092c0f0a020906130f06030309050307030803040b100e07020c0f0109030b010504020a031e0e0c0a1d04050c 74
    0xe24540c0404a40041c0480e1114601003220a000500c00310720000042c04a407455a40d0083c1c034010a881903200c1041c0000c02c00900703002d0510b805141d200b10014000140c85e49800c01000f864000c168164605000602e03c06200a0100040d03452006100240108640d00e509000c504642c03203070352101903001c4c9042c2e14100c0e41c10606140c1210341c0081c60225504111a403409911400d003001d5100150340114200e20041c10840c4180d0f80c4420000c01e16905200c080407081d00380c840503c501703203203265070740d009004040e04024110b0160500743c0041003141d0a40d0f840e00e110303200240c80588000d072080c0000300c0070803880728000040d120b036821041d80f40c00c0900740650b5400005141c1480340c848120000e6455100c0c40f07a041c12a900035640c18102d074a071009001c025400020040c0415407580c50814030600e10328089250360840101c00900c200c1c00c05012418061358001040c0300f10709000c8100705481941180803034800c1281030400b02030301d0354030701030b03240030550b2403441e4000311800f80f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 792317437 1250 792316187 792316219
    0x4020f2e09060e1f0e0a1502120c060703050a0e01020a030509060703091505060a030804092009030d26100e15151305130e010e0c1c11090a0204090e28020d02 69
    0x487c000b03010400340c007242d0204142e22a40c0c4031a01071058000e40302d601c00400941018400c0c2c0121b5000814070710006075560500c0f404909a0b409000c010003c030791540144203204208100c0a03601054601c0c08100050b403d54502026101d2545042c017180c4c0c8803c0402c000340c0d00d441c05240210343c032550003130303070307030750749002d60030241011640d1428030104070b011a16425005e04219020540020302501c840c45e603409064860b10030300b10a416241e403010145400040ba102d02c024010105001c41500c014a81072840d104000300520042c01c80f03040b940354291903101e813158092013080102c1210307161300002c402d000c500074041d0b01103540254000303c0c800c071403e4244d01142c4003070720b500020310510507d11641a691109440050381242410b000303c1122030510710212651441100c9002c0245450400121b000c030701500e84001c00340d80040c0400110080340320f614081107040000d0480d90034401a000d108180c0d1451114202c00c0000043d001c640e00c1c1448140301c00e40c01071090035400d034898 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 792318687 1250 792317437 792317459
    0x70609050405060130020702040203100503060a02040503060103020909100f021305030c0a050402160b090c10170109051005040509030c070b040e04020f2e09060e1f0e0a 74
    0x1204060140b460400803482552148820300b0b1088800f544031120b0404081030341e142e01c4041342e07801881d140d0078004034006a80301e0006600940070398003c01030303142c1800b0030103082007800380114800c0707131040108200c1501e0100c1c00e00c2c110b9404550200b0540e0314406641d080100e45643c90341e10b64900480804458203550142c0355510081c00d880f00d0707079a281d90916613141482000d680e8010741c0203600f001035207081c1d001000d1127159001551420340282d5200d0f80c03121000d80d21700c5d42c81d4103d120b0f204007509001d404425910582d00e08031042c0c0108881c1004400c1041c0204124035031118002064610709182c95002000083c10400c95441d00820443c2c4075004112102264042d40c4030010319444114151401c1d9950903020f444c0c1c544032a420440c40200301d220a503044541744010080c01c0e6000b8000c211b0f00301c0e500751901c030504900c0d80e00818040c0a034001d00b0600040c8103c0c61f605499005021b002880202d562191100403034009864845070394071495031046a41b100424212025 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 792319937 1250 792318687 792318689
    0x302061806071a1008210c06010605091503010e13140f03030412050a09060c0302151e070801080d0c020d020a0b040e16050a030513060f090506130b040b090f070609 72
    0xf240307a0b5020b8483d030039140c090b80120b100c1d510640d40038039a11520b9014000508039812211031881d0315100c100c0d00b0302400c00100b6400040418004a00c40001e82002c1c02040704442d080c005003444c544c10540101c0c500c060240c5001800302c21017100c04104001c0c02c8065020a038550b085490444502d80e90326529442220202e07030560721001542c800724040c00039503e0300e4a417900c03184c00e000c1c1403c0f0304551500d500c1c4021b8045105031000080740c807855200d054001c0e451401e40c44800c20f05d41c500c0216040000e0f042000304640390004000d00c40c00401e03654091465443c0078080b6441d00d00004007110709004000e03501c100c0081001400036403144c028421512a400c0c000510354590a10280240e01030203000d02080080101460482c4030342d004503403243c8444000b51850800c0d403200d10442d40081d8070f2075481a81c030581002840b00402c041580f00301d04014141481c0150343e40c1c7e8503200c01c003030030062000c8a06c1d0041041e0030700c01c0c065403c03a554588120340c801c9960312401030801d079003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 792321187 1250 792319937 792319973
    0xe0408033304150609031217071d0d080306012001021803070602010b0a03060203040303021c06080708030f0403060e0703140714270a15150305130c030206180607 71
    0x50405822407040110001c2c0d0101d6115464041000c1d1851f1a50140036072145001410004800c4480398603041442d40540a83c03c01d689445001009104e5088010b15601c5014171815403a1145000112014200e80e4060300c207103400d40081804168400e805180080349914550021602c1c111048a406401c0300c0f140c0d0031021203088030f94401041c0c0c200c600d039444540d00b00d82000742c28404164180c0045070060310a190040c54020002920500700e8005860000210f4468204002c00e8408000d1403020b000b40c0000303503103041055001000540300341d200c000c03c041d8540180080841040c8005001181c001c42c6682134032606100c0b075a2241c3c0c15000300302d0303d02d500c00880074181c2000380b00c1100c1c0c0d103041c0c4e0038500243c036a08015600b1318401045544074a0701c03103401d00f02e20381140074900300402c1c135130b007000000a0101c0e901a050f41c100500d000010080c6410340300100e942c0c1040340c01120340640e2201d40e211030440400d280c90400034001c03a04880c6c0041c0e21020407400542d40418014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 792322437 1250 792321187 792321191
    0xa03060e090a0318120809010504080105070809011109030714030321190501060f0e21010f06140d0b0402010314090a03030e01050c2502040c0906090504060e0408033304 74
    0x1124021145540580170750812081c0c0c2c8803140c00021181c5000300665138050407d6424190745510340b60a40300300700d82400000d140403050040d10603007405040340000354100101e0502561401103665442544280010303481c811070083c110351420300458001ca08459204800c14024203040740d0307911030070f48143c0006a003216445225854910416062340c4044c0d44034400f07042a2541140c060303044844841d8405440641c042c1c500b0704611007008001f4000001140200c00034290004840e4590f00215091060007c1581a40e4030031801560040e4401d10f080065100c50004030700805d60f03802e04c00e0461503a48103000c84014005104c20788244030f60780c140000ca620700d20b20360030780d4001e4804003520803045c441c101c103818980b00740d2010780354a40f6003011504d82a0300040c050324400b41048011a2a8a505014036540000c00d6809000140e40500119161400070740484070000c102410b40da80100105148000a140c13241d4000c2107208400580c00701086000c0700407008103030b801e20441c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 792323687 1250 792322437 792322457
    0x5010204060f12150e0603011508160f031707030e0604030c05190e06040b01030b1302030612060f040803060303090406180f0603050304060c02061204030c0209060301021801050a03060e090a03 84
    0x203501806009030300c20601480d034910505e0b20b01e02050304500a4072840c4d15540356001a0003248a41c10000300034010703040107240044020400f00c4111500c0d4204124001600c1003e001160040400b4040f589450b04002d43e03608080c182207600b15512081e0540c4084002030010030700012044400c103407901140c0c0701500c5031344801e0704c0c08490014807a50004500e00702c00910750345040e0344040c500c5401810702082d207085004c0080c580c40f0312980b207007014581c00320901c140c60414a030303240e0080704244014000c2d401d110050b010210001070004210705030000002e00103440910503260004000340c0305011844c0c4928980922124040100341010720345003440107030303e51078001c030b8003200c1c2c000c03003e1841d260801d030382240c19a04001c0c0a1381c0005c0104203001c412042108450701c21406a40c8407000300074140304024441d1409402503109a0050141c540c4030512003e400101c41002d081c1190b840d88602420b80182259601113a0049a55020003603420030100301c03610a140300e0381d6800604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 792324937 1250 792323687 792323717
    0x8030c2823190f0905150d0606110a06021e0a120c0207030c090f060302060f0301030210141639080d0507060c090e0a0911010509011704060905010204060f 68
    0x35018050010100440b000326201155001d119076200305482d5242052000351181c011401609400007040000c410001e15180c02241c40c0c49140050a0320389804585415a222115a43c00f0401c001402c1140d0004014940b40c1c842d0041c802c03c0c2180c0c0054a80b1a40c21400c06400c5418828030b4410550620042a961074400b0610340f09885c1d00420398400c2ca8200b03c88500180324107100740101c80d55844010015907908000740030b000d1440d1040c10703503070b41c110700c144944607500760701c0b1009004582c1482483c00c48400144d82d942c4000f402c950100500d1410064925006111000d09401000341104054880c4290246407480e003424803d14860b529543c9a54945245c4c000707000003581440030000081140d000301d030301d4820a107024a803241d11040c1240b802d0300c003910091002540c032000d100401c18000d8124040b035100342021420209080000703010004420500300c80020098001000c00c11582c0c442504d46810400071500d598a45c40040c110001100c40c00c40480c200080030141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 792326187 1250 792324937 792325007
    0x21061203030507110d081008060429010521010917070501180203030307051c020a0f0314061e011407030e0306010909150216060c0e0a1208030c28 64
    0xc815604c000c1c141c000340544100d41c92000038102090f100420000062422401c0010714001d40c01003248003a02d03502090054584400451211103420307500f00100304541d98011440c080c903480090300225440032654450041c05030000080840c515400480b100c10041806048490701c02d030003c1000030400c011101116102c00d42c001d40c96072080000035441441180944401483c1000300d02410f081100190306981010380c480c00081c108060b0240900c0d490b0103401d001c924030304040c04407800c107a0040b03055480e401008184500c0e0600c040e521903442009100101419444e80c0358a544007407800403c60030f65a10260301c64480e000000c116000b092080c1411181d0040001c004191031115020103174101ea040701e054103c5814540307010600e40d024032060650b03942e03910040b0308054001c0005101c41078120021849070a050b03c800115110100c0340c05c0995100c0e02900d809010301c10100c01c250091040c0c6a16124640b0380b6180c0f504480310041d01310031420b045140c1d50000d014070703038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 792327437 1250 792326187 792326207
    0x9050a0b011407020111160e0a0515031e10110405090f07020a0b131203140a110418090503040f03050633130c0903050f0a0c030321061203030507 64
    0x25855403c0154030019070290303510308488113442c2d0aa82c1c424050400c00e00075904076901010004035060100403880e1f4552080a070300522010a540900ea000d4002c6503a4110b0b041c0c2c00e5013844007242131105482000c000c1060440e00452061200300c56120408a46820030700c121401004c4280c01700d4042127004603614414143c6078020020203c1a8941240e8118040e01c0d18014a030004c3c81a00814803280008280034801d80b00464050652040c540c101400145140f07407084c6483c80005240710f0b00c40c00c5030200d0b51504248045c120024070f04200928044000604a1000280006202801030105011240510140c1d02140d80d191312450380d684040c0c020000c1c080043c440f0b002e400041490400742c100025082c60344e480310228400c030440c2c090400c1c40001c1408a4810820003004100054070309242c0c4016002c0320348240e50345010010785000c0242030000ea16003074005900d10041707041c0c4550702c0c99028003510740e589244a00003440c854058002030f08140c000f03001c4a004140d591307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 792328687 1250 792327437 792327467
    0x8010b030a02150a0302070209071106010b030106171b0403150b0d0206030a180203010509011509090c120302010905010c030b1201051b1305100e030708010e0703120c0c09050a0b01 79
    0xc0b8220f200c4050100703039580851108014540c0c28040d6602686403183c590b440f490782c90300c6180400811591103441e02038140e02240e0303241410030040c04000e48c090005100500f080000d00c403291aa24071010a000f03500541c502441c0d0017142c00420300c10800e4200d075a02c106060100062100041440320380940074002035041001040400e944c4a01036010743c011858030107500c20341c42620341c0000c0c01e440c400e6800300706517912010980c06110001d91480c0091482150070418520595a04a2840b05520580000810650b804410b140c004c1d001946a01d0307100c00200908100c030007015005041d580d00f0903016a00b03820300062070304c2c014840c0398094580f00d0580b42d49031041950440982d840f0203072450a02080000001d165190030818009146031a1103001c11804100241407a1500d6980240d10356818010251510303c80845c01344103894001748001381d42505160182c1c0c540c559404d00509034030381d0313010000700c00d0490383c0079500a585c030320014402c114900e40110384440400c401d031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 792329937 1250 792328687 792328699
    0x203090f060d1e1b1706040b18010602030a0905180c1b030d020904290d0303060b0307080105011b020117090c0310020c070e040b0a1104091508010b030a02 68
    0x603885850450054207440c2512074022410410300040c1c00316002601c0407041009031582510501107030441429103900282d8500b00e40440490303518406109400341c100f6000d169240e00e0b000045e10740300c2d035400b03a0342d00403a070000b02540d603407400950b2580100b001c3d00006618080c04901480c02006140702284042a12101034a40c10381541072035008d5402d00702c0400c61090b00c055401c40500107007100610424005880c5e5400c48103010694520400310441440d510b408043c0101c0d031186c1403110184c05880e440703014055031400740c00411040e0070131441600c02000300507400791300c040c509040c0c90083c3d0780c2916006000c0017a10b40f040221500902003107d01202005245070081201e40c048921421295000200ca01082c180703415610001c206d03503000555017914100030450100144440c1c81c40640918040d115400e4402000c1c0c200c2e02031035284e0091181000c000e409a0740a00b0441d40d003040780c6a550b0b090109210b8035845034050395420078400104628021440e40c0320395401510b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 792331187 1250 792329937 792329959
    0x140109180506030c13090506010e06030a4110110f1806070b0109050f040f0b07120501080d2a030c0627142d0c032b020309 54
    0x804405060000c02d103c2d054402c0f0a04c44180c0c0d51190300c1c002c454904640b0006841c0d0450809a0600805030040c02c8585104801c6c85043e84000031038104058011f02d07141e99006c1c7d810300b400500300c03214004580d0152610010880d10030395148021541c1c20010131641112400c801c0d0b40151818030541101c04034040c0300c4920040340c1d2000400b9219000c03001d500300c06980d4000a925504000b500f643c800031621300520880c90f951080c29000492841450018a0503595001014402d400300034142280382d0049800180100d0ba00c001040c80060113002d40e60310703495280d40daa07009041c034600280d401840000c4a0491300c01c2585200070722440d0904110442c0c03401e03030356600c030301d082250000c0d56550320011042021444808404141a24414000060078200256803c04c807844a203a08078440c1718448004c0010070340010701040403c88a604145607985080c001840c1120b40c01d406441011b003555400c504409207400001d400c14001081d01120490b601e00450402640100700c20030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 792332437 1250 792331187 792331229
    0x50930072f0a121112030c1e1c05090904110f0108151207032001121b030e03070804090e06010e0c0406120b04180b070302070b16090308030c04140109 66
    0x141824145015940640d40b000399100815201c41710303c4d081400507000030480d207005000920508222684001e40d01000b151070749540358940071038420321240c805804450156103400b54080c1c0361510402040c3e41194030b0036080801500d028031150910803c80035070103032080d41c0603500081c05080901000b404001d821000d111060b24189000d982e10703c1210000000100e6000200311800c110300e0074422178011010015200000346400009004c1c01e103040c00b8021080500c200031034081503d004034003c05070281c1d0382c2c118820300e1400783c50a280018003042844c0a5044100d1060302c1c00f0844c1d0310ba0b0703604c51400d01310030030684200000341c5d000c2008002c070512540798035001e08200300300020380c9241100080c0469079404244c070140b09524140c44148460144595441582170601b03601c0e211a5950703d10203014018044000d05400c9121a2113452065000754061039005503070550360300701b9101454003030300702c0c2c403c00c60580080800c024065103d40708010440310810b0b034030441014890 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 792333687 1250 792332437 792332459
    0x40b0d0903020f0706020c1302270f04020403032c09150418030c050706111207080408060408040305120702010507060b121606030e01050930072f0a 65
    0x60000c1d01188034a1000d10303941c00b810f1145000504158004045210711007041c489860b1521012002c2e5030701c1031051402080342d01c0c1d0710805101c0710703101c00c1d02180121000150708114400100390001e1020402004158028441c02c16008031400c0165000500100080d1507181020381250801c40c500c0c040b031443d007941513410180400c0140040342a00c0400c050988542d000d01d419800502800c0742c0c1001d000c802d210010250266140c1402109403407050a90303200a01200c68040ca00006999410f01c01c0d80c509443c0684190800c1c2d9100d4106801c04104540050205032218040d0200c0b898811181e0700c21510b4465040e151581011400c0e1140303002481e0000722280c05c4201d03600d0020800f041031150200404039000f00040c403609002c4000e0448042e01d02c1d203001a8544070602c642d011001075100002c20300321100d6034050804685482c07200c01402c0ba0380f4a0000003103606002c00510600f03502c01c1081080e54050804181400141d4000840401641000142c0d5007400103101c84 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 792334937 1250 792333687 792333701
    0x201050706200a0f0807080106180e0f0105030f0a050d0503130f12030b0316030b04050f010c0f2c060901050714010b0114030c0a0f0c02130606090902040b0d 69
    0x2880d00040303050b40c02c0d20100c9403000a000762416030400040602c016600101301d88100c3e00149084080ca103081c0703001074035504040c003a0700c0a100a800c8201840b692003a10071000e003c0d0b180c00c1b40720780d080031050340702c00c6035080c01380c0c2d4828050344040caa00500c000070341c81002500080200845201107405489540c406001642402d220751940d04c049600c000d030341c2c2035081c0710b00c0700398080880083c030080464420060183c0310b5081000900528007441807007005484d000903d8a01584407450407d262044031260f440195080280701e800081d003214043c3c0f413504494451048600b118102030384480f060203500704480c0d580d86200c0e101428513a0140c5205101810000c1c94642c250300c4c3d140d80003010503d1144107a4543e9004c10107541c1c4100084039441c58101914250300300403041602502030000c0c0a03041120b00c10120020f58400c1c61041c0782ca5401612aa005103c1d030460040a812140143d00205004d100c00003203207007840c400c0f5022500e04504244c200750744054600054144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 792336187 1250 792334937 792334943
    0x20313060c030905220f060e150604080d020601050a09020c03032a0f090a0617070e01030b0a180b030f0309040f090c0b0a2a030f020a0501110c0f010b060702010507 72
    0x1c010b80204007030315002c0141a002a25002118110b0391120b200170649040d0304600b01c0c4207041c400100180a082203c16401c41c200103001d0a6014044010507483e018662183c1601c1c448c2d5141c6d03034100e0303802103031060684000340c55103100306440340090b00c103030b106441000a850744100000344c5001141542450107111151400758441844d4502840c1c54005108a07110608000b071546000d10781103c0f86802007245041c85101d41240e00c00743c9180d000001d040409002c00c444900342140c0c465888040780070402050549203a840d280e03d41010304018040d205200e00d07010030000503142c0020018032200c01c45008510344030340d140900000e0701190010420781500c40d0103041c0010380c090315803000742c52018078094654000f0800100305c2c1e54080140d9070313207030500d041c00c028010381e254003404400e0700b6060002c112001d8140c12443c1a440350740203001946400103031030080740c544000b0141c1658100403185060765240d500c0e030880b411000550392200b020060a401035010b0405841c003140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 792337437 1250 792336187 792336197
    0x906140a050c09090f0a1506270f0b03040c12030c0311060c0d1a0402190219030e040c020f0a0602030601021506030601030b19090501140a1b121e060510020313060c03 73
    0x2c07512400c440c201f48281c00c040c001c1a02c0d500112040340c14070165141200c1c0c0c0c01040c000c8145030640850900c20f190103018220300d00000005c00f4400308043c0c1d10010041000303100e8036090710b4200140800170800e41200062081076003903201c0f023000914a801213180281e107503c3d12003a548004014a4641290406a405030503d200c1c150340d948050003001c175000b0004c2e030108200b084024208894510405412040403660030082644a070340e0621808060b80c0009207003400d5002a450b1081c0c03048443e500e44030340b148003410041d20703401860042c1c0080e02140c000e10f01d500c1c600354106500300c0d107207038055001500401c0420500052180c210721881189181c1e000004620010b031049000295101d030b4480030540284070b034190031140e01588a601c10001c841c00282c4003014079412015000c01c1080300c8100369088070042d84008494500041c00d050210f8949404c400030f441288507030351188040006112207140040100c40d210460100654032583c18510142c1d102c421040c0150f00b000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 792338687 1250 792337437 792337451
    0x70809190c090e03032401140d1d0c01080f06040e03040f03200d02040908130f091b02030a110717010e0106140f040207060906140a050c09090f0a 64
    0x85155085003840c81c020a11040c2003828501c02d101600e0301c060903101107910030030420462003400070032500ca0700c1030803003a0984400d4000040fa0f0a910300c1d025150b075900c00094a043c0c3c00d800c2c0d4031074401002c100d40076130491030700c2075841c0343c4a03c1702c0e40200740032030b445c440003d4903410000549540600c0007800051202c0f408101103240d40c015402c900030050352100c0a00c140315040c0b1512258103900710103e49004203c4d4045505c0c4449100d00901803601c17210704400300545402640c00d8040b0252501d86141d40c0c42c21450403100041c4074000d2017074586000400080f421a0859034250742603001180b600f0003000f0200c03005520b2250820303090085a10100b080c082c00030302000100c10b100d0002c901422024802c9003103401e40c0d441040340500c00081201b0031740354600c0c00309070488112030060300d59019040540103001d040c203006200c2d510b02542c0ca1080d5841e0306986000705804002000182d85e859205882c07031007118034565100e50a200000c00e080d000d4036603141d10002c0500089144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 792339937 1250 792338687 792338713
    0x2090604090b0915010f1413110f0d0605030c06090d03110a080d0b010c02010f050c0106170a170c0c1e09151003093503010b0403110612070809 63
    0x10105903018815074101e07150090850010f04c030b030749014001d0402c680b06011714090800780001c4000780c0350b42c0181c0c02407100d0755852402e9881031025040c074800142d80d5803650124034003660302070040521020b10313100700403a45080c002042030f441080900079919002c5568208407001038196070403030400c0b051117081d0001030000e000385c0030058481c00038071ba01e44044240304016140a000d4080c1089030340803000000d0303039004020125805050a0030355a450314141c0243c090704c5130341c208404e45968079802110041000480410301d07402a5034195000105404226003842500d01c008110fa101c002d404480e407500c0c140030260300c40842d064082c400480c40c04550007200440b00b1100344100220000c03400d003040c001141d0301c2d10a9180421810b4441c2e51407441540c982c1d844901c1750f14003c19002000c1d040c1000c002d80c45011790848a0b1650b030748014510f842e5206e404115088840c00c0c881d425281403d00c151a40203a4070000c3c228244d944140403610802c004011042d140703d961032103140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 792341187 1250 792339937 792339953
    0x30a15141c060f0f0f0207021008060a050d050f01050c07120e1c060e0c0d0c1a120a020a1206080a060c05040b0d0b030f071d040203010212090f0c1504030209060409 72
    0x1426010ba54003041001007480503034111915000c90740c17070312801000b038031300140d03104501129525203c0c01c01e07034901d48900020a06110854010503048a0700389007030300a20100241ca10b0840c00028000e01c41a9600e010b020300038002d124009042ca1032007441861418010b802c1054001c4014100c0001442180c03900c4140d48071500c800d4401070350790310154261500510604844010983c0d200081441581e52041d04050900c1001100580440c506a03400c0c0603e0442d051000c1c5070002c0700560820411040081d48500c81e400701040015401070000205070280000300e561101c060183c02c03a1585550020308031149640c01001000c00020030462110009044051241d55000030080310041c03d0614003150445007007c03c0d4000207042150100380c1c0d80510b0100a040c1d08404907444510110380a8014104d40b00c01c401518000c025080b080068002c0c44e06942404940481c1600d00a01c030044140d04041c460200c0c0800060000d81090131102e03400c08000b810000c0e43c2070385a02c4100c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 792342437 1250 792341187 792341201
    0x81513241e0903030e1906090204020c0a120201180206040608180d0306080c0609031c02012c0d170109020a0513061823040b1311030a15141c06 63
    0x1081c50b82c8410003010715038035100c0c10103042012001006500356141c2c0c0304e445c01c40240f20007400652504000c808644681d0103607a200c1c009501251041e1400340f52407003ca82101640c0d100662802030080112602e0003504508950040e0000b403409007800e00465902000400b0a015004a0440300e03448420400c50b40c82003400300e0360001010360a0894807030411000c00e051902c2100c06021503900c0e683d01003003074001e034101040702c0f499814101e0302c140d0141000804001854043c010000072068601c0c80d92400d5800c807600b07a42a1b103040c80d0082c3c80641d0756001210700704c800d290050044010507402407441c8403444c00c0445c14505074014907410030010b034210000042031011003420300b00081088030003502048005031a4800d002422031120007400b01c03824807075601e40d1150080d58580d0161002d002c1d44840d0b0a002007268010641000e50013644d0b01d80c1d03d00d1a0554000c84000008520425684c402250950494640c41001024500e00b4407250700016070850300b03400901280300d900f07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 792343687 1250 792342437 792342491
    0x6010303120b0909070e0402010c0b090705090c030403080708090a081b19050c06030a0608030a08060f01030b090c0c070b04080601090605040203070c0b0a021308151324 74
    0x56a46140241007029104460082070244410806206540b03401042e8841600c0030000002c01d00d07511400101c1e00141088000f40c0051803120900c00c07804030128801054400c00c1c0da9007681c580302c5215000c610f100840340035000640f40d0001c0740d1000d1103145496048400502112809a10f903221810154800c803444803c1c113916070b0405074030040a00ca904440340c00f03898030324034407205911100d443ea44604182441603400000103104030500e64080b0300600b4021044036181d0000001c007810040060301e105108203201d55600700345610a00a04203100000381c041d1803181c0300c1104072151034129400400c440d000d03d110100310401944050700007815802d00500d002c3d45010301481c11074800d41c002602580c010030030011195080303012040c840364028843c4000340d031022900c0009020340c1080c1300180d0700c8064006600c9000007160110b1341c0c03101084810984803071900d40d00034240307814010321340151810b032a50302071050307110051260301c00000420032913030b8903007099200708103c00c500d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 792344937 1250 792343687 792343697
    0x213030c080309030d03021c02040801050a0f18020f12010c0f09080d0504060e0307032004050a020918042d03030c02070501050d0c02030c010203041103060703051b0d090506010303 79
    0x10020300c81000e1680d4000c085810146203850900000f00f5150a8560400d90606400040d034a10390031b07041081000c07480c3e11800454582c0d840b071442d1406818240c039042001d904240311000036a0040c1325585d01d80b14113100f030001e070640c0c0b0343c280084010640c003400d07802111400801c40d82c440a014540d01c0c41ca50717564040800300301d0f14000d842d00005404c4008640e01000360080390f1900030707040300d0540707220f420311013101c5604d02c0001c0c1c580341c082e420042400b8001c064030b00d051030381b82e0f074001c0780400c04803010b2150740d90320084a012406066901c40d84040b54130140d00a1400d085426a045801136801600c120700603207020001784610b0451341c491f424100100b9040c582d05208800b2868041d00c0070380107840c5804c000810601441c020021890b6503040600440e90007041190043c80c002c00c000d44d180c1ca401d052420b90002900741140c0a8003c2100040285209105040c80b8140e85010010550b04040c04003556402400c0010011580d85c584480403ca08002240c000d41c425520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 792346187 1250 792344937 792344939
    0x3030d1a0a260a030207030f0f0212010507090512060103020d031b030e0f09090601030201080a020c011b020c01050a0203040b0304020d0f1b0815040b04030e0607080a1b021804150213 80
    0x1c1505210103007504400340d500607480f00c0f00002e501180d480e0440c1c2d00190001a108154140b000030001817102c001d6020715030b0481d50900e19019000203101e81801c1c0c076060422551603091007244205c8820510050300a00014030040c0713048482289401e01030b00d41404502d0a0700e24800101d02103d0302640403410080c01c0c02c0c1c1c2c5282502031805042d006403000c0c0701c20700340340144a603180810b000c02414880803600003100400c1e241c0c103450003500c40100a00c440c1c0f07042c06a1031010103e03074042d480140121660b040d6194018421501e40c02119401503140514000c0c0c5244160400740040381c0c0002c00c000007030045031404180068107401040107030100c40c1d4200c0341f80741c031030744c00d42c045005a0480980c00b02440c40075201d082e03000e6004141c101071179446150031550360078a000500d0380164041208030501004c04040c2107400d615445042000e5801c580000080c00201002548840c0f4944003200c0c00940d40400c3d03800520034403013800c0810301a80c400c02660004100780143d1548044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 792347437 1250 792346187 792346229
    0x302090112020907031116060e070501091a030c09090c03190b1c1104060b0a030e070e01030f11060318100504030e0123072f03030d1a0a 60
    0x901140105900c100a9602101c5a4080707080c02000404a500341075450741c200b044c8122003011600e1045902c509000441c5c007915121009115141d00c83c261481881004541075000707140c000d080c1d03441000c0300da60f00031100c030aa4210f6440144034040e545814040030000340c64000201d40140d54510f00b8a84a00e8078000010341c65024a03020720764141050800c0682e034456022000550300344921000c00c040c51801e05070a003000361004690817514007880081c401321080042c0a1010a03643c0500001c440380b042d03a07640d51110300441a455900030010000101c182c4001c041d540d03c5180c0c803941c0d14098900051068004981c540c25044c0503510400207190140064608000301010802281c142078a008044011221f040c505210404030a50584c01c4294045d00a107040340c3d034440d98990580c41d107140c290588034071403000c102070304005040c1d03502002d644012152001d8002e41c145800801244060b101001018100c040504c0d40546952112660080070b03100ba12250122004645 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 792348687 1250 792347437 792347449
    0x9031006051e010f030c0e03030d06030b0c0910050c0f16050f1e09040203190302010b0906040504033f140f101a0f16060e0a081b030c030d02040302 65
    0x910603a18100c60031002e04516038106410294450f41840d0010388844214016030317400800141d9290715120228542d83c42441c250800b0003903a1140c00c2400c1d40b40c689401044060003605140c40d405040310000c901e21900c00c6000e08525102d40d81182d10042d81d13880340c0c0d8180940352003100302401188805101c50704000c03206841540f010f1b41c40382ca41540180891b142c07821200b04032445481c1c410082015594100203802108070074030701388805900d142c54003034002d240c81c1007410b0050f2400000110946443d10459118035056140c0507101520781c51805243e41d9804e000340e0724028410710501640030030840b10398600c0c0d0b00c0240043c200c2d4102c072030900d1004000b050100d00f01c46a40800400454400548084590000c0300711841d003450001d8800c08e00604c01380307010410740468802240c80d1001c041c0764856004190810114100320b05590700c807200c445000d0b10200c1d081000402d9a48450b00388000011180252030034040240b030558150350104203501c3c80309030085020300942c9000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 792349937 1250 792348687 792348709
    0x207080d1506140c060a0209030f1005070e040203091c0306090c02030c1006080a060c020c040f050f01170c1309050d090807060504151d09090703050106140f150903100605 75
    0xf400c8142d0400e682c1000441e516840140915041c64000c90391030610340b010440202d43c5915081a00e100c002000c1c4400700074401190301c18002901c2c4e0141003003d0034203100303c1c0d01032031130707400a0884120446640000004000140307000c1656902002070140d6541c17041e01c1032606158081d540d519203050000f4a454503620f0501c0c1c01c03510b040300c01c00c2005000114800010703171000380030034103e0300e102d0260304101c0034103501381e0820f05100010101200c280d00c458822006c4449807041c50341c0780d90844c1007100d03207151007040070b6010392103214123441d0803864090000082c0d0804500c071401c90b030350345080500004500b00400c8200001340903003d000d1015030094601481c19906052400191243e0440608524010f003e1790010782140d13451465110500c000016216070b00b00e0428ac1d065903626a070522080d2802c1d440c101d004500200c10a0761300760700300e034020400c03007111034110b0401000025015007001654010440d409642c1c40a201c0b1b110092a07064001401502d09400e122445d044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 792351187 1250 792349937 792349967
    0x308100f1403100209031507030e010c05070201180b031308040302040207081c0e0c09150301060b190219080c072301140319050a020903070801020403030e01051206040207080d1506 79
    0x11720248000e5140015800341d04444000d5110407038461401c1038008240581712402c8550900940e20743c11074100d002400118402c1e038900c0c2c42d10580c04040140f004e400c0c0581803405c81d0810209900eaa40c0824422000307004466041c9440c0d5039070f0000e01240d00202045481031030201e4106070581110b5100f040d4200100001c0c040d0034100d0f0302494641d400f8001c410306c108110fa010824035000c40826003500300c00039008008aa03201c42e01410b050300f0418841c07503521910300b0405001c0e031020900c11405120500c0390003010b429961240d10759009015101300b42d01c21010002041209060122482d000c042000358540403c00d0004000e10300200c204180b0300e8041080c81a030121144994150407840d0000285545440c402c01d00644545461a6414800c5007808030742400194024800c0341d00c00d8440c2c030300b0318101c900150703544e000b540400002c0d40010700c0003d01c1030509070010881144201009442d0200247c412412074450240b0700350240c00e88031007446407a0b0002151411806 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 792352437 1250 792351187 792351191
    0x90d11010306080f10054302030f09310209040b01050306211207050105011701050c0d0f0204030c090207060b151e0c0106030b0708070302040f030308100f140310 71
    0x49a0000c542c5e20120002e51801321665a000035440c0b1260300b03c08580c1c144003c1c903000001d07401300c034015843d0200388021006980600146031815000004880038800c4001283e414410a8420000b5001d00144124485001d82c0100449011509180c0c0203541d2601001a02c0302c500038140000c0360540d240301414443d042051101d00e642e40304030211110a81103110110740600d4920a040400145400c110003c01080441c200041900814145d4182c40d66820b000441c402e003940c00e0365819240b03003805110801c80c00400c148580c00c41070120b40114800351800d0b5803692101c440b40407552007005040da02181000030410b07e40149411088115071010090a40c0e40c01100140300ea00040e088500e82c0c1c408458075800c440c0c0c15500481d0129008004040d0350307040000c04000c0071901100041d10150000f50340078081c1c4292416504403488c110696415907409a503c0d04000e0840100c1d00700c080400035404c04064203d03c0034140498041403501107160a0502e4081e10030300c03001c000d034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 792353687 1250 792352437 792352453
    0x111306080106050418090b011205010b0f0d022b060b130501060e041a13061a0307050304110f1f090509040f26030a0c1101050f150105090d1101030608 66
    0x1d034400c3c261000d403140c40c0e40c8584e42c00451000e6200030302e07210000a00d03009400000061120b8030301480c18900340618000d00680c1c19080402120409120990340c0c8450b00c03e041801506040150104503038020b1528903070898071401c20400c80c8a500700c211400d1382c8a803613007101400c110b042d079502c40e012050140202d50411802610301403490940c6402155034100c00a03203908124010800745070080c042c80c1c20100001130ba000540b0507800743c00c1041a50580c0c681d035041c0d1440440b4071803101d95139040d0851321541c2d1101140c001598100340d100010845121555132a2400000d4030302c041c071300d100500003240001070002204e035806540f045005508100100310024070b108542ca0b44800c4682d880c5414a01c1144040c510403120a81d1850110030400400465402001c09031070a44410b06160001060142071f55421078200f880c2821000101e000d42407000000c00004005060403414201141c0118003055002181a00c1e0a86040c4900300c99581510601d0050900700019006070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 792354937 1250 792353687 792353699
    0xc0f07031406090a14010204050603010f050306071d1003061e1502071202060d1d012703020322092c0703020913030309080d0209040b03062214011113060801 69
    0x180c0131044014000c1012007402c0300b4207030801c3d41250003070b010041c01e658680d40c40b4050921240964002c07140070340b0a0b5004901e15900404100c45a58030504002ca9505d00100074080900c080c0d090f81014181c5811000c02d840410444200c0e0119801411240d5146010315126047d850407005800355000301d4428000d0030048000820110740685005a403a55180001030050000103103c080c110710104200180324010b4200c3d9030184400094031400c0c48420303240011041c41450000c001d64401c12151084100c501101c60f100a04502d950040955941071103040d42c0c01c104554002c1d41e82a00d400d109010708200d217440e078251240041084a040d940030440d0440081c0162590643c42c034584000c01d882900200c4515902481e807039162803c0d541114082c0d0406141c0c107101c0ca0501801000d1424000791440c42070385d0709090f0182080490070103505144112506039a00d414080364007280a4003409081c080c0d81280c0c034240d65500304641c0d04080460183c00c1401000300720700c010003034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 792356187 1250 792354937 792354943
    0x209190f0e040c120318050103050c0d0c02070e0a0e1605010c08030c09030304140f090402100309170307090f0801020708030c0c03090310020306040f0509100902060c0f0703140609 79
    0x141d41c0c580503564082d8503281400c5549400030f5000480c0130340e038482c03140101030344103a82c95007403015007240034102c2c0d48540045d820745008840c1030488400601c101c401c1130f40180c010855424650065482e901c3d1a121400c21081d000c99249502e41d4a5403401c011404003044011144800081801ca1403030405000034892265888098a902d42c044003040c4401d94800c00c8a401a80c01000c40307503240d81d64603044240d280000212440b400c1c011040346028201a88864456a03004101c0c100150b08041b0540040003030007019194143e40d030911140c0381915000950141c41c0e07c0e00d072500d1140c41c0580a0501c500e540d008121a0b900500080f00000e10017010341e1f0704030004440d43d40e11140c849010071703e107015101546078540700d9200d090b041010568001c50154406a405100d402c401441d2401610002d8079950303840e40c48260203c81480c00c56000250403440100041d141801c1d071410b003460302c0019400c541e11600212000c000b044000361203100d00000c0c00340503080c1c0b480c2000c100342d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 792357437 1250 792356187 792356189
    0x50106080618090631060c0f05030907051512040f061b022e090c09051b0f07020402091201060e16020c09062209020406090209060307050705030d06090209190f 70
    0x1d117411445001d101651880c424201c4107020496058030244541c00c1c140b000e0074500ca40c25011402e604501c00c25a441001103c3c42400004024000c0d10303e8181444a041e4503001c20f820601000d00414181f180c10101590081c1d009624410b6410901d051080072100c41e2140c5c45140d00d1000320800f06550042403d1813012901880c203c010342d90700720a0007081710030103003490a20f85000c52035410468184ca9907000e440628000304440d9550301030710900000f484107070084281040c0035107000803100070000c11616102903c09030030000307100041005110003c1082c00141d441e0b000c00e000c0d562903600440e601400c2003003c5012040d0003d8069141d4543c034511a000344140400144103445010009150600320314104000700302444032040140b0307081600700d1041d803c0003c002000e0595000f0758480c01c5008199507d5621102c1007540c0a51280f01c0c03c03101d0340000c0c4103000d18440c0a204050041c00420400f6940c1d00c0c2e42c80420403140890710f00801c01002c00789040c000034184c49041c030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 792358687 1250 792357437 792357451
    0x1005040327030b090303091203070c110307050d030206090c040615111612050c030609061603060e010b2802030d0b0a030506090c21060402010e010c060501060806180906 74
    0x1600607448100806226180d508082c00010203901403050040303000001310311030b00c0241d041d10170740c4000d0000e03840c0d284011f40d4400005079a000e40700303004c00c0042c6c40741d00780003d00604440d0280d59440209800b410300c0c120030b40240e0000410400d200701c00b400805003080f0216000c12049040260b8640350b16801c0c45e2190070040050980c2e1100b010411254841c801f9840c07165103020780c1d402c0200e443c110420000c543c2d9004581f200c901a040000758103015a1091010713141e990b6034200c16088030600c0c2e842020030140c40f5400046d030459003841c05406405049005a583c680500401410031143c81c105005004a08403132641250b020060f11140300262070040340d8855000d001071084051a00090300324003607070080c09400c00001449174030303030142502d40c55241d4042c0141c15400007507003043c4503c107800030340001d40151b00c9500c90081c040ca05040c00b2480f440380b622008202d440982105000c101c4039020310443c2d00d442c6034490211034140d4505403807460208441d9854120150000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 792359937 1250 792358687 792358727
    0x150c070308040f0c03060204080708120d0e030f0301150801151e050d020f070b07020601061b0c17010504030e0a05030c0d060e0d050319060b03130312150810050403 72
    0x1040801544025034031505130414102075940b070312400d2800017581310740302d4a502131092802c00207040c000820181150040200f8190030003100036901c2020b024159108c2035180401c101d042a5000980041c5002c1c081e80349214074061000729000c1c09411068200740c1c203041e003c07804c883c0c0c4207500040c0c40c803c50b10b10101040c10000380d580c0a031414002c080010b011240003060b950441c50540d030182248900030542d1600ca600c40b0703402a42c840d402800f5005c00156884003400544000c5943c941445114212400c2000d0b6204060180308010060220303040e5192001e04c41416800058040d404004a5500c055203142c03500180d9101c00c40b08410340031b042d90400d41c0042c040306034040e01e0017001d024107035203c2c80083c200080081e40100c4181c0594455131402c10442c034060b10a080c03ea880d810701035851030300c0d05082c01e8542c02000204604000e4440d11f41503044000b80203280380100c4540c3d007903441e45d0900113481d0501c88142802d52015183c1010400440e40c022b48403030780303031f2070134041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 792361187 1250 792359937 792359941
    0xc090d1101090504060b0702180108190f06020a0e0a0801020f0a0c150203090601090e010c0804080d0f060b04030311030306060901050a02070f0b1b011e0b0307030f05060405150c070308 81
    0x10b89004100d40d00065000d07280c000c001a002407601c005144c1113100b03c8004400841e203407074081e20300d0002c3c02440340c568090400305515a0180213100019401407107000b410700210f0f80c45805a0b400440f1500c0042e04400800590b424503a01c13000151440c00b0080d428204004a4180240a030300e4002042200d46020750003400780e00c0c44006200102054199502c0c0b6140e80000c1d5103000070321601c20b00902c1c00500310178502040c130441a4004142d170b0f030140c041e03c5c0e03605e4561481e0010921000450307541c0101c600c10703050070721814000306808140d0fa5101e034170354180a000d00c0300392440d190050b0010020004981d5500003200c4008009090013038a84101c0c500880c42d0400d06d4105418000440a0100301044c0c180e000e4215800d1501a05a0a0311090f010b54280c0e020403c149840716054240000340c00d1164000002c1100d019085440c106e81d01d0711459811200108240c81c0c0ea0400b4082c4014400305202c02d80d0144040000e002e1a400c08944c0017980c1d114604000d010400c034240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 792362437 1250 792361187 792361189
    0x102a0206041d0a053603040306050105030d02070303020d031a0307060221090312130902030705090f041a01120917070b060a06020606060f0f1c0614060d02162003060c090d11 76
    0x418007040c0d52145d00b201d40f2140c481c6010001020203000d03092291180b1241811600e20010302e0805803a455030103010004c201c003c0607809000b0041e00040d1001261024084507142000f211004086550042c45544001c0f01d0f10f4440e184c18000d88400d1400030004940d00c0d80f8002500074a668481d1100c659a8150114015048031140c0100e108107000206002006500c44054130075030f5412600c6541600c0a07d0410040f55841000e5050420a42810085542c060200359401076000c540c0030811540581e82d41b07140074030b110040e0341009404078103007080c02211f6148aa2081d0280d90030081c05003841c01c040d540b0900100000d10601c000119940d80d403081405583c0d08031091060680c03102c1c403071085e8511003003140c00d03000011803615200041c04041d2260200442c14050507852401d400c0e00c40001c042c0d03120a84024400c10300b8420f41002a5070a91800e40312802c80161104e82050281010305001028180314140340d02884111099a40c0014040c0c003640d00040314a1030a510724 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 792363687 1250 792362437 792362521
    0x619020f090d081218070522110c070605070b1005010804080304050304150206161d120708060709081b100309050c0a080307060b102a0206041d0a05 65
    0x201103406109511040c0314005c0058140c601c80c0d1991142a1a02c0944400034025420022400703210100035103410185404090f60043c0943c1c500c0b005c500b407410503142c00f414503140b00c07580102e0029600003041d109000e56903c1203a00510f0b14000d8211280c90b1030f0000f03101c480040c1001d0071140e00000814100a0b007003040328000d0190500c0c0c8544801d0340c0703201a46560085540b1940d203010304c402440080d2258084420a00d505d0807142c0700c1c11a41c00501084030395008100f2940d205000c1e01080e40d1604015080c400c4000e036aa203000c15003800390150802560800c0d0030281c510010030600a80d4a25140207185107140c0b4001408031400d041192401c080881d200d50400c440b800041030008001c0010864140180702c14003070000600f0a000c1030085890560002540c80b2107001075101c1c024602c141c01c603440c00e194488046003a0005803483d4070036889a007024464001c032602041952a2003a8040c18400e000c11403464240050303900344a110803001101b0000c41d2901c880d1007421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 792364937 1250 792363687 792363697
    0x17040504050106030c020f010b010212070212060a0b0a06020d090e130c0603150609030816051015030c0b070b160c061109091003030914041b020619020f090d08 70
    0x10020700c1556550200500142001d0389040014000c40c081d2002c890340c14020780b446480103134020075110440101c5508940c010142c102c0e40030b102d1410081c00c000c3d0070441280140059140041c1c816164410049021626804003056402041d44070500c9a0070219440407282810181a25662609403a041e20302000000820135003c001d030110300c0c00e6069011300701d06a080d8090140081d121b0070107907600c4501c0c0c40700404125003000b1a8a100c9031202880c03074400c1c418000c43e08a00070311103055040d1240794a5500c144140411b0400511080d07896070001040525440742c42d0180d5900c803030000b494000d012164102450f40e00c880c10f2407181c074407403000740d4001504108851810400700c0c00c9912601056108075607010218114201280c001000c40c0d46c11b40302c050b5040e14000d00b14100341600302c412a80a942c4400000c10351090160398550b031410307039003c1d000c2d910307207109201d04100311100400c003d41d00c1440030400303c5040104452002d4411660100e07800290b207001506c1d4451 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 792366187 1250 792364937 792364939
    0x6050d0e0d0314010b1e0706090f0807120801060509010f020c15030402040506040203060904030c021f0c0b07090503030d11041d1501020d0c031d061804060506040f03170405 76
    0x500d214070705240d64903070720002c0841d64110403407046903a1000c17108114003e074a1501080388100010451b41c0041c0c5006150543c0308038400329608403940c43c2c480300c00c0740021060715908000030301c8004105022034019100183e600307141c22a9414074030010070a00481440c24140000d1140d00c802141c000c2080020301c10004050211510130059128070f10303001903804038019400c050114131a80307454002d603032141c507020b4807541560707459440494004036080c0003680c0281200804100b51208005548401082500d80ca0108406480c186c3d02c961802008001000f138030450134096540c01100b00c0e4141411401c8c0480c2d1502540710841c002d121795802221150492a0b07554880d100110101e442001c06080b0600440c05407801a0b07103d81c11020341000044804e00c8400009026202d82e11010f200b64032420709803030001000c0780d13159101e116291882c6401004020f10f070703d42801080050602551883d080c1031501070b030300030340103494003000b400300030301c2c0005c1e8540c203510005440c01040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 792367437 1250 792366187 792366193
    0x30c03090c2903010b07030908030a050909041a07110c03010905061605040803031005030709060e0f091f0b28030b071b0305030402040605010507051209040b06181008010f06050d0e 79
    0x11703545180c0e859507484010110301060744503070005501000401541e0001803c1e4492a141c020780300204502d003880208111400101801c001c01034001e001c03100c40c4900d95544030460b000140c00d14031490a804501c1503032103a8100307aa1000000c20220b030554012012802c2c0912041c03050209454a01450300b169041e440040108494242c5004110084030400c0d4260b8410541342c02c5a00300b540c50758050f000108403283c0104083e0501c0010039580080349009855009007801c0940c0001c079000c00310540c0c2641c07120032030455450320b401c41e45500ca030312012281e098140000070030b016151a01c4082d00c01d0403140d0015039000e00510101000c0882c2ea00740b01c004030034a1074041d20f02e4106a406a0040e85810b0010030154080c404684140d07070000f00401c0168018060310b0401d900003400d007500326072124260203c81e1201d42c068103081001c0a1614914141d060034010151440b0441c1010031541500412004016003483c60a4440c51324205682d450350070b03040c03400381c650071701404201d00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 792368687 1250 792367437 792367439
    0x10f031a0d050c0a061b0305090406050d0b16020d0e10030b0901080607092304093e0904020a06030e1c1107060509060909040c0509040c06030c03090c290301 69
    0x2c040030031000031014013100c5001005446031001c032461000084a40111401101a503020a005101510788880000d201040e03480c2c842c0c01148540b0b107036000c100c41400e04c14080c480310301072145045a0580c520700c01071203024802e1500074072504042d8500c1e805613841c00c03041506288250001e61500202906500a651303460158507139800c0100c0d0038900040c204d10740410a030706121900414600755015105940d2150305c200070003800103d200b214030042d0f9815001c100f00d210540082e000c20b07044030550303000e00c0f0030700f40040c0310440f5948a44110b108004000060307603000382da074094450380d2178001580084030000f545002060082d2410a07552a5801920b003640200765040001c54001600c01c02c594451043c0c0f858028000700c0c56021001f801040041d05001d41c9895019005e2050f80509581d2040800d04020f82a50103071217005202c2d2003070200503058080e02852440d6031400700700101c17594443d1415041d15000d0000e08002080150402c082024a645100032134181d495a8035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 792369937 1250 792368687 792368693
    0x9060304140d020c132c15060922080c01090c050111070b04090b0d0f05032110090207051501062708070905180a05030304110d02010f031a0d 62
    0x1a85025808215200300d0740b200240510204544400c032802a08540d01194640807070b9002d405100c1e503250316102d00c48146100e41051111282400d890503004d4444010125420762200000911442c0039003649000e100211150305203107162800b01c540c5030b18001d012403420084d1480f5501c42c0c020b9075800c054000302849803141007041183c8007621009145003003241055142d82c85482030441100b8140410400001e00f908001c1080f18004e007422240e80c0d56a68039980100103100a54a0382d20110b15003101c03111110111f14032401407c1501c5031440d0034840f4411908860083d144610380101e448002c0000c100072000024900301c030409110340c1c584800410804034544200b100b0450b80ba1065040010031120b4002d60303400c1d102800d1254140b91062002d410040c007490300040303a00000c501e54080510070303824000c0c030803405580d0328202802c04045020240d070b9854403030a2100c020b000182e810a03c01c940b0305219083c0400c107003885081c800e4801054041098022142e02d5200f820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 792371187 1250 792369937 792369953
    0x3021e03010b04090b030c091801060308041d0601300f0905060405070b12061014280905061c15080106031202010506030a0b0a0f0c0f020d020f0d11010209060304 71
    0x80c0c070041c039000c101c864107080c1055510841f03e0a46500070441c00d021501d20035606280c610703c0d594007800030901c10360340c0d515111503902a030b002c00082c140c1842410080106030175a2134002009203482c0d070703003500310b48910109003410850752040141da41100c842c200c2031a0b04698612540e191081100750311506040f502c2d24000c840c2201c01b030240b800041494907521003a2044400141421006039035442c0c18014010300c110080b00920000d0111801030034074690003003851440f44818840304964101603d202050041c41480c10b02801c10420b001a807102c800740c0300d0210b40805c20a24815610b10660b00410094100c903162045100010400340015044070084900c155a5014008a011012400c0700e90907648280d054010302001404117401d2080d0942180f0581000034214910103010301c2104c48070b261045c0400e085011400029806029015407003a4600107043e00d110703850017654503200c90b140c41c00c00380002c00301d1031070030000300b5030549101e190b014011036a6401c0c14200104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 792372437 1250 792371187 792371189
    0x171c03180503091021150b130905070c0308241320130b18100e03060604060305032a300a05030f070210090809130203061003021e03010b04 61
    0xf00030070404c0c88040b0954400d1805030072000d9609042c0312031401e029000e002078401c0002e6020304880c0f201001c01d4100c016001002891140d4040c03844d460725111501c4e003682c0d0300405603814403055400d104046600310f03045641c441404901411020741c0e61003c20209082c28100c25040f070800c241c1c000c9900540d511410754944407142806100b04655207046883c4a402d484400c8180300360342c204035208010010b01821015009400c1100c072860020400c407003401094a40040c40340c28113040d05042c240308cc550445000c1d070701401000d00310349030b01e0390f24492a03544642400114203441424120300e0a03103204d8460f940c0c280e400007400540b0030154104219074500007806c2c680d41c003100259010b4102c0e58443c030141ca400d03040d17540d41141c1e900c0c1810003c0c13101055014603000c66212030702e51b12503000752038420109180c81c0e814030000d00c8101c082242c546d541c000e01c1041801441d94070020751134114819031074096a250408502181c1c041c04100c030200a1003400b00000c2080442800544 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 792373687 1250 792372437 792372439
    0x9100f030e0d030501180203010f06030b2803030807170610050705010207060f06050d0b070e010309080d06060e04020a1e051c06230906280b0310171c0318050309 71
    0xc6c403000405181401c9100c28468a1080401c0030010400b650081d081403162480040030740341100c1200313402095040d0701c0d08074000c00001500040c0708168100a4040c1c0120443c900f20f6018034609012a401c0100a001680b084e6070300c40e224030724544211300301c40405510000030754a407045d501d03101016000001c80c0301c0300030b0308100003c100c90034280c0c082c86030039030008002c203601d4403030541c01c0c0e8100c80101c01440c1096154034507a0003203543c04004164034941c480002802034502400140300c1818104101d218600410100d64010f03400b80c40c3d440c40a80c10440250010280602036030395210300181c00105211851810001c12020ba0003c002c882c100c0781c1d800a04000842d4119034507008290a90b842280040412110b003401d42c901910042ca400e1800d05800c4c0d608500d0110040b0381e440340b40c03654000810401d0b410300e03142e0420024200c00d21a89050300701545555114a2701407030042d0518145290145560312907040310700c4404800d01525503140d10760a05030f4895010402da5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 792374937 1250 792373687 792373709
    0x50301150e060d0206120a02091509010909020309031b15090f120301180c0c06020313060e0a0b1311041b0305100806011202121b0a060509100f030e0d030501 69
    0x320382c0e0508051000300c0341c0c1c4c0140071728509035050600c22501741010b0948004640d090203100e4843e00d034120b004400070070100816403501008000140400903681000501324014002c0c8403161500200362603078000ba4a08941090b032034140ca080c94210100503401c5c00c01100003d202e564030021a1aa0706d00c0f50040c00d0700c00006001c40c0c0180144000e109240c00c9201e80e038140610700010381d108040d04a21854101c40c0d4500319220302c1c01ba40c0003540c04118501d42143c00c2070410a883c030400c41129201070141030381c8000e0b9102c45100c4000248844408404042d480e410081500c1041050540061041003201c0242c12058040c0300042009004249803002107041407080490342001c450111000701020b80c01d0443d159074800c424841242c00a4280210ba41c0e5a03206200055442d50341605048100c1d29503c104000d00e9010750145050041c100070352480354070b8408600c1c2c011002030030a043d014008000c110020840010070303040030700139807111019250789034100a048a1440e20700b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 792376187 1250 792374937 792374941
    0x40f030909020906040e070c0c0311031b1e01050705030d06180b0901030201110709061502070b0406020312271b0307061715090a0b040f0203042a050301150e 69
    0x4600c101c0c4240c0220f2a400300082c0b204002c18041840020703030010982c50300008494013503448500410769a00222a0843e81e24003075034283c03c04000d22100018081c0c0850fa0b4100010017149500146400324180300c0000d624041d01c6901501c2120201c6502204880d030301c2140c16011001440940120413421142c180c900c40b0b9000f40e400b950a5900340200000500c0c3d28580c01920b403011112200b1038180901c2d100003800698500c504401400610300c03140c610541504001d088c141550803080041d40280802d0002c00d5002055400c126068480b80016844e0001e000b207007081040c102d44411840c1518030a21907601168400b802200c80c5c0c20312010803245820117484501500802000600c501003100710300000000c42600708130101221000c4106d035201247d4048422564882410b03100c0c0011041800e1501c00c0a40c20040c0032421811030510b5070f207018130020f4840c00c00550449a0340355007215000c00001000601d002002085a6248540d080e020880c0c94464400c540307040e000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 792377437 1250 792376187 792376199
    0x100c0302030606090f041107060605030c060a140d0b09010323060613091e03090f0807050109170f190b18030307180e01030b01090f0b030c1309020405040f0309 70
    0x3682c0c01440010700c0e0b542842c884d64103010a12404401203036126072101801ca404505001c003c016084c01590003003121400c1030103240c58045c400b6011801114100305100c441540100c07107040d60810036030300382e81d10b0003482c500401907c43c10040503404804040000200709821b0b07240c100c251072894469048003441d010186d2200003c440c0d01e81c03c60219840e00c000343c1184d42c451170104c4e01c50903200c00165440e545403505801c40101c00c030045122800144450140c0c142d0a038018800c080c024002d041c20700000810400031849513a00c0c101c107011800e10001c0042c008001d8400c520000c4507403400d9480e4401030390f104a0503003034402030359041c0440c0200c0e07014408500032101050081d8030310745411074105c9000c0d4000c07080e907403580d000810105409481d60740c110b0003903000f00d18100c034035410800c0d4441110188510040c003e031904460503901d44000c940c0801c0342000f200d0000c121820715108402801484a0003540702d0308d480c0c10001080011000005414040c0d5500900c030354641c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 792378687 1250 792377437 792377441
    0x10090b0a0e121216150c20010c021f1d21070507120c0801050118051312121409030a03140c040b071401051006020606060918090a0f05100c03 62
    0x407034100404604108001c44c1050110079512803a20900102140d4611900307400e045444142c16400020740003030f5180d541201d90319085c01e4001d036038402000345242268000c0e54a640c0c0c10400b01e500004050402e903c1da02070340c8100005051101c3c11400e0000110a10784c8400c582c907100c8903400411351900b80c2144540c0251840d40d40c1c0031004010b040c2c00c0c4400700c003a826030004200c40c90581c004c00070841080a0003010b00a20b429202a0300a4000e040c400003514001040f080004c96284590030115400f0a0030001f5070b01d143c20054404490100e002e806060000d11400d4007030000c40600544810020081028003010b82e8204001c4442d010226610714040c1d40003461841c05002c14020110400002c00485209907254000004961003660075030380704807510500300d800c1846c00c00c05a80c06000c215400341045a20768900092131001a03043c000010b4104141060600041c1e9002001c100e905011500640700262640c4280b40c40b40d911403e80c025441c1d01420f0000b001c420500034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 792379937 1250 792378687 792378703
    0xc01021204030c0b0f16060603030801050f030a15020d0c020a150605030a110414070c0b0a11160c0b04080f0f06150f0a050a0b0a020f0604030203070210090b0a0e12 72
    0x101014419861401055004c1e54011004090741d00408005500440b44001c403805041c500c940d00100d18070746507040140100105a00032030150720840503086007a603011400480c201e510561040703240500c540b12000a01071402c4030340c03005141a0250031003a8001840c6c2088511400001d2002e2506850300d40581c1c500c0d118058240c0e11050019001601400c12299100005403000a8050b2140101c10301d0700800d0700d03c0800720312036a05800902a40c1c201c2542c1c4012024000c1c0809100c1c0c6e09600c0807449010489140141070070220810002800007180042000011440e1035544500e01943c0b40c1084514100c682c0c40b550b10b407051038074000715109100300c0f44130315000e06200f02c55045c00105500b19410590000350b0040101391640e07082140c030040e03c4c4441115031120086000a40b03004a0802c03518195480b490403c00040d80c000200c8103150740c180e8040d403003440110030680344c0c1010ba4000c9408204082240350000341c0c0203001502c2085c0456031000d800d04201410747c0c0720410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 792381187 1250 792379937 792379943
    0xd171602070b07030203070c12050c010e06030a020705030f07030f1d01020a060906021e040501030b010203070b01050f06120403032a080c09010c0213092a23030d020c0102120403 78
    0xc84072040000746081405031a0040c0a401543d141400c103903945440c400700c94119101658003001d980051000c00c00c412800c0f20002c0c03c0412031400010002041c41c0801403a24141c60340020301581008014000d0701c0304e80c1006082c05886075003528000c1c00e6185401c0c16040010707100e542640c054100d40440c550032501c10303005450490250b80326a0301500c104181561265020003289020202c16041c0b41d56166240c02c9098555081c0000103040c0d9940c8501541190300c20300c2604040340c3d1003181d66045400440b4035160a526400100b55076020750b0391079461140d2010104814142c254200302ca00c20b6124072071001c04505080f1481c6218500c580c00000a84100001070740c04000c0300080c0341d02441414514010b010903400900b1a07143c285001d00b400380c0714000402003141304141c034100711548a405440800b0b441c1018450b0498a103e0007a408000122110258043c000b1a81c10140050700703803120051005000384d175401e04649928014442d844190390200c20060076603064a034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 792382437 1250 792381187 792381193
    0x222110715112101050102011b08011e0b030c0c120a0210050a110705011506050c0a260d05091c0905210d0915050f040b07140d171602 59
    0xd0590101c1c0c0041c07a115072500040c0320100030241c10040c2d00d061480c2a5021148003000c0ea42c1131500081c02e440049050741d40d8014a4000300b00d802c0d401890090540d1842800359005034084040600300441d96481401c0e100000800c0c040b4010360f540090010341401011100851840c99540c50644600d001c100300603001600e05214007003554000700d4100307800841c08280d15510700f0708032507150300600c021030b820707951a200341584040031084080141018142142081044030140b9111000343e200108030b04581b454138402e480c40d40d4a062121044000030946034031000c25807100904095900701349900c41c0030041d03e000040700201100301da080b6580d0404107864081404000b19035400e5180c01d40300d94400b02c592400080055000440481d0369a08400f0710301070096401d07180c00100382042200400030100c20120203000c440c1103401070614299901003c6c00d1600708032001c1412240607010303d103503c00d902640310001d2030280c0c007035050504c500d440b440510070382109048422009a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 792383687 1250 792382437 792382463
    0xe07170312040305071a0106020d12060308091311030109061445040c1d04020a031112010c020c10080103201c03090e0106020f0619060302221107 64
    0x11340710340d001e4030016201d07490590340306203d0021030403000381c241c104400507800f00115500311544102d000004030408041004030300d0460311084498801d01c11441c0c002ca50760805a00c6182c01540f14550b003403040300c0301ca510bd50319030800102074002849018100180d90350f800c001031a04144480b007450108606140b081810380c4945400200882c1c1018494a5109001342001300464501d01c2540303d104003a4511f03042010801400c00701c130390608040c00403070040100580b01d40130701009582e006205205a50b500a0020360b006000f829122455400c29200da808550002043d0b1400c1e982200d0701141400c2100302101c0405003488050300700108407050b520015010301e203d0124080180a50389140802413800000d080700040803030000e03c1c060800c20012b1040180240074001070700c044d00300c65008950856451502034000361040c1d2160b001d0341003140465001c9401141c3c050400210090014030310316451000e1310340e11506038100b040b080100200113003101c14030780c0c1c0302c000a0811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 792384937 1250 792383687 792383693
    0x170a060e0708160503061b18120307050d020601090c020c06031003020d08130608070c060c020c13061a1e0a030209040509030901030b060301120b090a060e0717031204 73
    0x80d281000e405803290181c46400b1600c200148070b441d81082c800181d41d11010314040034149020001403121a40d20f20441188a138003000c0422034009404604c401c80342000304c1740004900203128003040c042c80c840062010308010f400714003040040309035025070741e403a07030385122010aa900c5804140c0050f0400300300811940340180145810090303522035402555141d60102c0c00f4a42003110596150310085a51542800e989800d140640143d20701521036080080d03000e03080c0c0030080d2008100c0da485a8180146500c00c01450480e40304c000c00030701c1d00380011030a510040100b402411301d5246208900c00049201300221b03004903141c0c1e50502e851040e00d4080c4c02058000c80e64180405808000100041d5241d0107003500515401010356074485040740050100c03000900c000b8000c0105100402603813402507201030b000d81c2c00900c40581552005245402c0c040144002401c980c6800b049503000700002801c5415200d2880c0c1c0000c8519a05902c0d5503203020b40400c0b0100d20846c0301c001800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 792386187 1250 792384937 792384941
    0x11060105010e0d0c050406181b1205190203100317090a0b0a090305031306031805030a1407081201030c12080412060b101d040605090112031214060406170a06 69
    0x8030f4090401c4104c815240c00000b0140c6956900c81d0003000c1d0720b0440e01810300d81d1445142c011080c1c503240b4034042075031178802601c000c11002580c0041c0340d5804c0000d450040c140390001d02c02440350021982c1e0328104a0f4404121110301090b240740b185015901c10550100c003ca8025807001410010031a00c2d00319005e80e56070006030034034108211082e0000c0002d0080010f04482c0041261005005041400080132251142801402c0c0030340301d6001d0022440101c12070308200494a429403030000b0451481c05503105000d4010026103000a480441c80750a15005043e40d220b50034440030965500210301d02c41c116040f0180c0085020881080314198417081c15100510804010841e140094001040c0c3c1c8004220a80440d003403d80c240e818020715850070401a004480401c0349900306004581020014040c0400556042c1407010500d40030703070789008034902caa11003845032200b901e41552004105582c02c50189081035800714522108216080c03281d00940d005042c141c0403030301e9000c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 792387437 1250 792386187 792386209
    0x1b0e010b030f070c15090303050c1603030e0c090a02030f1803030112021503190b01030c08061512090102092e14360418030e0a0b07110111060105010e 66
    0x24414024040301c001a0b000c280f90340b8000c540d500000c0c100846e4100a810f84000500c0701d12441000c102e070041c031108450b00e45405070703014070780040c60f49008505903142c04406038003a40c0c80075032402046505040ca030001d51040f901c032030051446486a404015107402070035072a02107034000388018003808200003541007010b800240305022078400640010050380c410354104100c5106210303418007400c1c041c050b94070034850030718041000786000d40004010000140040d441180103030590112692100c060314181e0307071221502e05040c1401802c05001b507202d180030030b0044d406038900719410b02c011040180d42e0789040d07044074802945603201b260000f40a1903861030000c401c0c01070308010441400200b007505001d030151480c080040c4491a550110048454841e9041403050480024500040c070314040e40740c1041e484506481c0000781203026907810580c805d500c0441c00c0001d004001d91803403101a000c1e02c070400d8503200d503c09651034000900405000c102007045400300f900b03100c04944 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 792388687 1250 792387437 792387451
    0xf0f06010e1609091409010e0c0d080d06051203070b0708060d0308040222140105062803021204030f1805101805040614151806090d0b041b0e010b030f 66
    0x5218652913030340e201d0450344920b0621540d104d9200400120b41030900c28010181d80302c8004044100c3c4032000142051010b0f05c0c0105900700106d0041d805821542001021300001410680004e030b05071403e5550b81c000c02c40a44a50f00034401090b14140640f2486005a2024104020036456910280d031280c81c003900803a0001081d262212140307840140c2c07402c0c550081c0c400424240801d107d0002a804180c00c643c1c400c0c441000f8a03c1c1c0715403001c0111820443c510070a804c654046d6006070000e020b001c00302000c0308008820041055170101d41514080c0c42502c82d0781c2d104050b10a2590000c42500401d60407000c0008100f071203c0c01032604881000f0100b02d114051510f1703070701050070b55500e81c1c00a40d03198004c0104005030314041102d207048004003480785081c25041d40000c80400d411140c0c07603010302c2002410fa1210f440741d203010315810f5080044264141054a0304524000d0102240c598141941502140500c400002d45049851204010f400c40d111101d00300f4004801501e04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 792389937 1250 792388687 792388697
    0x304080d05060f120c0114090a0e130506070215011203020705090a0f06080a140f120a03020f0a0e01090503010903120b0303090d0b04020a0e04020904030c230f0f06010e16 75
    0x30508564401c0380120302c030692400504032400170200050001c1030aa40c84607000e2506100e181d44648a101c1c009045456504001e0382c0b0752141180d0f004400c140001c06040c600a220800c0510b5400103038007032a20b50003e10b401c0d401e0380e031a80040d080e0024054010300582000404120074a460902a5007080c1d04030b80c0025902c10f0541d1110840e00c1560141d882c81d0482c0302800284804c50310110280b215000140203c0e0750241b0419491341c00911150b000c0c008003140d60400c09109505680f07080140030a00c580c0c90b400080e0182041c0f0030310310f01d5030010355580c00c0807515082c1030080c07034582e40e07060312801003842000b600007002e0840a6440d9405200522680000c1d5564110007526503000d0404008982010b005001c10402d86800003060300c0440d0062100507210074040561003500340c076266a1041c42803801242c0040c0144e40c1000b0303040f139050140e81402004c00c5190607031404400710b03a148004510601d46480d001d1003904a81d03120000044d250740070101000d00103071204e14003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 792391187 1250 792389937 792389959
    0x90f0f0c0c030d05190501052409060a08040b01081b0402030408070611250c0b092809060f12080a09031a01140915210f0604170304080d0506 62
    0x9041c41d43c2c10150090540c00d4880040c0055400d42029265040c1c00110050103550b0420b004117046094022800c3e0f125401c4443c90b1184401c00c0d420380c1c506800c0240506d070f60b8543e0041c000c0160400b614191504910540002059200022800160207000c02d4400c02c401a01003000000e41004006860000041015500107021845201c81da294410300c0303503480c0c0348950450306040d84600d400058440c861852007003c01c0c0e07211200c0080b181c5841a25039540e0705034000c210800c010545034006603007a0740c080304401803040c44482c140c0b00368580400105954517500d1828207407074403940203450f04808840011480140050182d030301d00b810949503066a035520344034820fa0701444a4884e1070200c00501541a917903030a48851401120504540c0c00d03c10b900007200e18000032240c2c031aa0342840606e40510140710003551050150b01503600503110001e4080d01c590044900300d0b0311321102549680d07000c40380e0043d80d00464025103450704200c3c052040030010800508440c0d4003c401c024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 792392437 1250 792391187 792391207
    0x21021c0f0513060206010806090d090302040c0e09090f0111071703131202030a0905011e1d031c0e15030406020d2403020a0603020913050402010e12010218090f0f0c 72
    0x103030090030f19900810f0a985480c118604000c800b900640040c1c021541101038503134012000429a80c04803800102c46440140c03c2c2c41c105e10704e407503054102c490300d0108220b48002058082403850301c0030091000f80c1c801a490768a9119500004262400c0b1854030240030a01c132000d90742c07040101420110130f00e802d0321609205031500c0061401603100180c01038200d98408000002401c0a080110140307101c04015405102940580d204211f900d102285040005c114146030750070b40501603406111600107081004450040c801000c0340703024030008494102849001c40b090403881406080d522030388e40d420081e6000500f0840e51540381c0c8901c0400c1500210090850103802c4000509107140d407061109a0b8000e52290082c10300c14080c00040380c41d44140080d1101c00030b203000a86039100e10050b1010300c0c513040010f4110001504890300b40d030055004203174104444015842601c109400c100c40600201d804034600f404220104024240e00da0100d41c0080c40101c4060234100004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 792393687 1250 792392437 792392467
    0x19121b0b091e0a02150a0806010f0329150307090e0426090306010905071d190303050706110301060f050334030b0904020120030d020721021c0f05 64
    0x40302d641c905802052080b421440c0541d00100a600035a92203170504d08140c0d400317460a400104518148010b0140f9012603038402d50008a0080c2400340c80c441d401424031440e00025000711080d400348100c5642c1c0302480102905a81c411529503480306c00003410b01c02407010300d820280c422150301032a0212440040f900c411040c82e06840406480d8482c40c07040c00f0540740203410f9201c0c05a0b1352801d424003910b9a4080c214981c00c08480004000c28502080403072100380d54041c440c40c0c0f00c1007118000c0109a07103c801070846e640074070000d0020801201d811000b900c001c0c0b2038140803405e4074154092590142000d10b030711002c12010040c8003840d4801d8641418007402200080d110190340e440b006a07013610461103051401e07201a8a44c4c5844da0001e819040b05246100c41828440e00402190200b0411501c100c074044006540fa032099107001c00011640000b411071495682c4c0c01c6035207151000403203095080741e000104502030200601625000540f900b80000c203d001c0044240c2e2070030703013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 792394937 1250 792393687 792393733
    0xd06090b041104270515030c0d12050915130302270712021603111905030a050c07081009061109011d0f1c0b0c16110a030519121b0b09 59
    0x3000440b80c2c5486d002c20941003594020009105416202708440030a410088541c0e51100c10304110381e541d100500000c0d40c3e1510902010802c2e0f01c002103410601c00690050340482c0d03c203440c004107503002c0400800b606840d04c160010000e214070f000542252203500c2800762604100b03401480c24003400b00140d200c44000000740d010400401024411103c10420f50010721852000005080750607900d403601c0740315010100303040000100d003080124000748007100040081c00d0031030344141c41d0140f0040103000b606400b511001d14050202c1088200c00d4121a402c400503524206222600f40107510401c2241030800d030442e44046031039a094440d0a202c0d50a084c4000801111000070703c0d12000c0800000d1041000c1d074800d11008010340d00130080c0c0c0340156442030481c041c0086000115603401c031164401360a40c8580b01c4040c46c4003001e80c54100c485030141c1e201070707034106000340c040e80d41078408030041115118120301c01c0040364900c039030386410a520390305881c1802c101c0c8800764146941 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 792396187 1250 792394937 792394951
    0xd0212090c090916090e0114070c030f090605030604110415050301050a0f05090a051b030403120f0c0203040e0a09020a180b010e0a03020120030d06090b0411042705 72
    0x180e01c4141e414600100c1e40c5600608100c020101601426080c0780407a090b803007040f21240c1c81d034103645200035081d04840c80d0b519142c0e204014a250a507402003081003040419804141329104541c00548140c245030299030558031854990785484003400000c00c2100040082c2d55014003011885055020500e1190450381e41c81e16125414481002110201948a0b81501007081810840e90300e4070342110b070340903044440000d402c1c0d60700c0b010440c045003103072001c031703242000002088105500030340c100120a034480c0042003441180307900791080750138403510701d8056070080c481007282e1001146032a60040e80c00c400410150034941c0440d1215526400540000c0300032440b00c06580c40038890041c01c48401d18010b00e84ea400304011469402c0740c2d02000c3d0410185004282c8205190000f403c1803120090440f695180b0b0244860b000300b119006031503e581c2015203415040c0781c9070140380071030101c54030702c40d141a1a100c441a12103413500520a09040c01c0c81d0f0844001c00704d80705d01842054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 792397437 1250 792396187 792396193
    0x1909112101021801020c270405010f02280f02071a0c01020706021c02040609210542010b2d070c0e040b06011b061802180412050d021209 60
    0x540f0b400064103111103545900d0003040b40c006821400c20148280c206040ba014200340203030b490743e081c840e0152403200240c074000c50001402a1001c0d88000c043c00800c0c11610903c044000c10120444130352440840c0b400060b404288180918801001c0000030070f104601028904046024400e003a0b0b08503400503205198041422481400200c0c2280700313078081040114549401c0a402a281d410140229003040c01e0002220610600705240c0344510f6812404968840c0440d40240c401402403002180c0520700c85040d42c1038020194411717030f030140d5401c480e10803a0380c01c210b203100043c0c2081040e1666900c20498090303402c9220f0f07488000c0104840790080d03840001d4101a0007005c800d80c0016054099001003001003001c000300203410a40910340903010a17042e03a482e5141020303820010300307280d1822a55524100c81c1c4815071100030702c29207001a410641c4d055400c000c4508541c05400c41c140c000400c0003507403240d4018280301482040050501200e42e00b03d00340d600781160f02213740d80c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 792398687 1250 792397437 792397477
    0x1050108010e1605070204021c060f05010507051203060411070c08061506070f0c0b0d060f0605030405030703080c1201090c030b120c0409060609050403020303190911210102 76
    0x15a02000d080e000d8070000c041d842d020f043c1610349035912840300620340208900454241d003150b413150101d8850319450300710034100c0340803240b00c4001403009126820015010440c00162940284259000746420002500d8500e04800c014503241c0e00007030005510956460708603503640100e41c06007103401c0c001c0e492641e40e01e0504168600d80f01d4090b100070445503006c10400c1c459610324041315001d0703612010300503049405151240000065030401e050141c80821041c9080c2c0440c4d014800b20303450381c0c4100350711030398509050380c4611058801900c59003007040305401090207006c0c5980c0000804000a180c11619010f42d10483d07001e0300111007107500d0f440002001903050042020320f44c1c0450704c1120504411a08940d1204040020b50107151120b01d500140044ca82c0000001d00300101d0601680c546446c0c003d449620483e080c1005210711042410074000901c640d66126922886010900901c0010001c441d450045004804103415001c445034a0003030016041415100007488144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 792399937 1250 792398687 792398689
    0x4111c03090f031e03090801050901021806092b1506082e110c12030105100905060403021c05070f050f04050c030a0506030a050d12050a0b0f01080c070c0e0105 70
    0x80ca4158000d40c0c0b081c50803041400811403110314800e900c1100c0c448650750001c0352500344c61040c02c50f400381d0f455518090030440d0115040d0010854900c10100c009a000c51b03400401909028004516403c045254440641110700c551010481c0b0079400003502c07080b00581e5064101d1803181004a0380d66250a010030080d10300b004510307001c548000b4801002d0950346400c400b501d01040c10401007503140d21071042a10102e10464880140e120140d84540226000d049841ea00a12949001e140c0d8001d0011050b07104421032030075141c00410f403510f0a032842d000c000e8840907001034403070b19070100540040000c004218500c01029000d01d02036803507141204025880088034410b0740607a00b00030402007401c00d2101280c0e44202c58400004e41c9443c0c01010030325040304c40c0c40062140c417070307208100040d070b420029941002080d000300384029070b120b24100c030943d030306c0f4060140c0050a80f42c4400d01c40d030292071101d80c440300f81d0000c50b080020135117070080b4100842d880303088450320460042c82a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 792401187 1250 792399937 792399947
    0x81b0d12030b1f080406020d0915090507050a150f050f0309010902041109060405040c050910050d110f03161e0503040209130b0f0a14010e06040e070f09020304111c03 73
    0x81060f8144060083c0c02010030103014500002c0004041c9980050514a00340040e40001c4d07005400843e0f07410030810b407034003800040c1003010090b6042d2150400014151902c1800002924000c26036501d41810460080d0780c000e202c5910308086c0002170000c8e81c00d6001e0701c000380d032186000d940045410010b9005103c00c0320300c9001c0084440b00d08000042458480d00100c2d800c5800075030740090f0542c00104121418015080015440118281d0001c403090f80711015020820003200100440c420b13900c03c0900310300c9040b01040e003080d0b0500c00100014142140955289294140780444910400b2241a10b501405075000855008014482503041c402016680040001a103000003d52900c0d40360741c1d940d0082911001c40072080018840c0c01c42c0341c000d0a80c80000c0022507000f075840e0081d50004201c101c0d551801149040d403000b6010400143c040c0c02c80b03900d0303402461154102108000a94070042003075581d03000b40080108651a41075903021320a0407203c11070007092103468001c0c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 792402437 1250 792401187 792401209
    0xb0907120f060c0503070e1201060e07090e06100f03020c1c0201090b18060f07020a020d0b090c03060c16021c05150a0c0f033918081b0d12030b 63
    0x1080014010001b0b5640c00c12040aa038410890720b0108041100803039a015062581100c1103283c000001e2241c1c1c81d4101e594182511300c0422490410f40d511020f0010805146a0351000200312410f0810500d0003940108040c50082d415541d2607550006449001d114454036600103030341d18074440041c007508200e801d40100c1940805d00e22007002c41105546c42c01c02500500c7c22000d40404103200c81d0081080600655020304003090405140c240100303000f50807640140b241c01403002c00d41e0f0503d008506d280c80f4003070003401c0504110416800f10f00719091503100700c1e00006800c8109405400e40b0012881d2284030300001d00d1120f9207020b103603035600c0000d01342c46c0100d401d0088500c045508407041c00f002c51440c2c640003ca501e2300407007103091191042d039850801d0345800b10003503019505c2e2000c4440400b150722460080c00d44110035081c0c0c0c54003407007014841d4020031020000c121184000c10001c1c1d0f0001c10780743c0000229100c0b00031610301521100b012079a20103506c91182040642030b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 792403687 1250 792402437 792402461
    0xc0c03081308031809102309010e06100f11010e0601050a0b0c120f12090a06050601090302210a1403070210110307060f11040b090306160c0b0907120f06 67
    0x5810481c2c0044030b001810b00e00024540700b1700003000003079003001c81c0503483e00c02803000b00020300c00d8500c42c42e11142d10042c99001c4c180150501c7c00003084480180c40c0141c0103540c0900303402501f212011044482c055103c4408082021194241805101c24051210303461100000b40c010b9514003c100810303103403141c0c001203c041003805240464030707020441140d002010150103940b807000c030b40c02c86482d01c90228074280c1024202c05021354405c002490022181c0b040c1d100b00706039110300005490404e0315110080d84803031421408401ca070f4165400000014422044031641c0c410b6039140e803945e041100140c503459001084000075480c1540010000c03c0c56401c03c2485407000308132045e264429040058000381d210303d600c2c0b2204d45a40e008640c6400c8408001d501c858844000280300e91040341001d1181c4a0100420348801c440000004c0510075503d4540c0700d07031240e5644045d0380034002c00c0740000380150320380000c4602e90003c0c000c003001d110300d60604103640e82c4e240a10444105c00703500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 792404937 1250 792403687 792403693
    0x150a030803180a06140a1d0d11010f0e0a0c1203140304020109050301020c070504060b0c2a0306013302030421061d0d051206100c0c03081308 62
    0x800119080c44212904060042101c0e865804220b042030718002101c0e40003000386140c80c02d403401c01425410308a008803090b250600c400c04803114400062154000c0700005500098050030300d550013131540c6900303c4020300c0003207018485c0c20070000807a80c40342e440c0341c16a084680c48404100c88180140040e0400c00e2100300d1015054a00030940750300d8000c2d07032088000c0000800e007560300a988800040c10028002c2d5980c1c00d0030340340d05403120220310400d8000e500b018800700300d50031024141c40c00421580c1c010070039508081c02020700304a2054012043e0118204c2c10f8105403401d01065000c0c00340040440402c400100c5081041c002c0c12070140040b005170000790301c103aa4003000303c40490307014003040c40581404802c41c50700220580b00040417140381261542960391107890001501c0d20140a0b24144d0103950000d49161007011404520b41c5042e00019005241c081d05440c010080f900c1d240c5080c41d030544e242d084031401c0350000c1e560301c1d9010981040803c110394518008e4109900a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 792406187 1250 792404937 792404939
    0x1e020a02030a080c090d12020f032503050d09030905010f02010c0c0b100803030a05060418030e041e090b06030c10050313080903071e0b030f24040f05150a 68
    0x40251203029000b001001c00c4104070103e8504000c40c01501c01d450030060668101c004107152544410940d046190094000d07040c0c88c3e80218804000c0e00e69540740810360034015284a6803144c07610064a00c2101030203003d00c41402e06403c00e100c1c083e541441380e203410700c68604200c000351054043c01182011681406640c41e0b010b54492010003030280e000c80360701803d859140340c0d820104096003140440c0d100210821102001719000a4010502585d04001107030020102c6810621640c40240c046410790f0445996400e2560000d0f4a5070520703180c10b08440c0c1042c247c070b816240d45c0f90f4190782c0e103c94203081c80304038601800300310000e9008071130310007060302c03000c002918a001c02080400000c5140304104284882601180c035502d400400350f516487c0c48030001c01210980c0b909075142940a03140208040540c10100c9018912240b030402a50f611804240340c0110000d098803a10f05403601d202c101038035103000d001b000030f00c1428041a030349010355095180c1240c01c81403a21610030144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 792407437 1250 792406187 792406207
    0xf06051201140f090c09042a11060c0a09030b13200d030c02191e060207050603180718060305011b08060d03020a020616050f1f020a0e0909011e02 64
    0x81e0f544501c04080c1e40c411601d0360b40c00d07030f5040c00380a400c0381c0e190800c1c24801c2c00c540100c0c0703982680ba11604d0008810280c101201c100b1601194160106a03040e40050302090180c20148007500c0007404610740035094540302d03650b0b0341d4030f0342082d00c2307079840342d5141101c0d4802c1004070b18414004010503240c1007004824080040c00016031108060184040700c2d81600554548100030900390058591880c002c9552740030440024030201c816129105044c0c4020980718804101f007403c8a2004000e0b50841e103400b529606089440b4086103107610491500044030020400103190003541c40d0400508189181805400d44086400d082e080e0007101440c1110140c12030102070b0810400e46000c0c841005501c0c0a80c505000003402960141c00414600f5110782c0180c2564a0760344140180c43c40080c511034040e9a6550031141c200e00b41e51075800500520f00141c0c050449000140703010380c0041d0411001c42d95115083d80c401010303035101d14440341c80e102c1807202d000549540413021450401c440c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 792408687 1250 792407437 792407449
    0x414031b010c0c15090e0906070f080a09060c0f1101020403082d0c0c1e0a0501030507050d06030501150501091409060105040b1b1204030314130f0605120114 69
    0x20124a052101c44480b82d001e0041c2c0c2d4102001900007000b002c000420b1301200507020014511074030141340c00c1040001c41001e008a0705d2030085105480f1001d0030b0341003e0050b80d40031802081148010b5541d900303a40031a144c3e000b1500452016220f02c0750b080e0790700800501d01001042d10807441c0e80100400c00c006a1103200715800040b212051052030000b0490a003643c46901c030600c51290f4001c5080386104c00e012a0131000001c0480c1c0d41c015004401500b81c1c100d007040c50060f070740040c0030300b02040594001c4d0030040d8040c54514110740781081c42005082100c00342c1c1c10a882d0b40e0754580a09044000840700d50b40540001d00f40b15400c0b500c0d00c40c900903403807132040354240200e144801180c0c480e405002a100500008250640c03a8001d15800307914001111410440c507100c0d680020513021a0802100c068a0301035440c150b001c0101c45114000b07610000074483c5140b809100001c1c0c1e41e48402196004e40081d0740d9841d901c00300700f00490004041a08420038100c01498046159a20740c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 792409937 1250 792408687 792408733
    0x103030e0a030809150c0601080c1e0102101d0a0308010515030c040303030f0924050a02030903090603090f07150e010206010f0509090c0a1401080f040c1211030a030302041403 77
    0xc45050380c103105c04180910050241c041d480043d48034540c004180c1000c040341d000d41e000015030f441c2034665440c0111143e048000b500880c0540c201e000b0751020039086400ca00d445039041c10100034035140f41200d642c542109042d094001880c40c10051103e4a0f2078100c80b0900c0749200109802c40c10043d0108856115511004045c1903603203400600ba10280c0c2c2001d0311494004a0001c88069400102400e00c080c014068a18514120014030f007001503100744e81c00784500a00030350410132504c1c01d1045640c006811821248520201c040d0098400c10885001c1d201146c001107403550382d40c1c400b909080c604910541507411000c0148080c0f5502045070307040f18011100c80d0395944850711306070b0800c03840d03114403900a030b820480485c24000c1105a40001e001c281d854020640d078000040c40102c5066500038016086014100442401640c01c498098041c0341c804151103503d00002e4580180941d080b008a0b030003144c100000a034a0461000961040e0058885c440c1200e003400315090322 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 792411187 1250 792409937 792409939
    0x617210705011103070c02040f06140f18090a02011e0e0d230705010e010512040b041502070b1005010c230f070f0918050703060b060d140103030e0a030809 68
    0x1020400209001094012207140d1070240d080f0390f62401c0002000380301e44050300081c3c0c05282040f41405e00b15895100d40401c8400c0d01c4c0c0d000e07882c40344000804c81c03016454800300760710071460040b0302c2801c9503d0005038040e200440007084003000d00e10000d8404e01c62440402400078410440d040026006803101d01c007080101c41d0700c4e4481c80c05290a06403015510f0344600042044c01101c25409400900b0f00241d641c01d032610141e04003288011500c62180c88002c18084a213000403400050220414075005485510480006c0080c0c080020498101000941d0b41102d460b0905c5850004000080050f0a003032070003604100894640e1040d0441481c11401043c04a43c62901c01a4003801204a900c5078070781a6580213a840c010b0302c0e0b41c401c05000740c084851410110000381040c9034400400300d81d214002e06440c61440d03c8480060060307109182c2c105c401000302c00086030061103580d2941760040401c040070b50541c10b00405400f0484415405015000c0b020701c08500000196071322114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 792412437 1250 792411187 792411253
    0x40b01081c21090506040302061803160f020306042a030b180118060203090f03130e090a080d0218090c1213290718090504020f030304090617 62
    0x59401c444001840003920b00380507241c074003082c100420030013060103030085000303508941c55030321208000e994500440507480d07643d90041005510580341200300501a50290b0340000e404017864010900f0300714119030845640a02c402c0e45800618040070404442e216152410985400d48d03441d02e40303008000d0b010b80509040000c44005102003500481c6022000a04c01c0c0d0300c2029a240c140065007065036000560b002d081c5519401c800c5c00010343d613500701d40f044c1880181d031408031860405d44010700800118021a81e040007c12580d50082c05120206400181e0317440465450f204540000308170305200e42072500511980311584001e036034400c0004d81e503090980c2c5a4030b9503840502900800240a00034400086000407c00900d850180004103130703a04036582c0f1207808403072194118110318841a9103c0c020301160307203554442d17a441440035100c0f482d60a00000000d16513003040d4081012182c503004140300315001c03095441c070904d2200d030007012081c40545101c0708180742910064150a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 792413687 1250 792412437 792412457
    0x60b1215040902060a030c020c1503070809010e120403062003010b0904020405100f0f02030a08010b0a0513170c040501030215030408120106020717030c0714010212040905040b01081c 80
    0x1903100e9100b0040c0b1a801880941d444110150240143c4a10351540c400342c010203070110480d0601c900e5032000d1111034140c903481c2d80c2c1d0307400090741d0001010388244050b65a4100661071103404000c41e0315102e030040040354580740340d45007820650b4032211000f0390742d00c851408021a0010041a01d0545010004d100d41b200d4100010070001d00030740d0700c995032020100b01c41141c500d4024405e4168101c3ca5078601302281c1858500b030f640d038420070100200103610600100180b010700405420b241e0942d141051800d113001a04044841d130b2500101c201700758518600b84500e03402c10110210075800d0314180015895500005d008004801220400c2800040010300304051801220300c0c501c4035030002c1900c0c1d61507a00c000d5030340c041801044c0040500c2e80e843c0f1421000081503403070f103910540c028404c032820500461001c5003c01040c031306520030350140c1c80a121040010700f01401c68030388001064503043c102111415810307031041c1003a0b00304600d242d6900100383c113012103106890401140e11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 792414937 1250 792413687 792413689
    0x406061d12120d06170601030305090108040201090b0705011d010c14030a0213080a0c090504050c010f051605370303050402010c020a090207110118061b080f0706060b1215 75
    0xc48001e24041c458200300040d003d0340c82d48190300407015180c0041c3c410102c8a020000c50703581c0c4a00f800090041401844402019032080c001d080d485481071600311030503603036010440803907044400f00301c98036511103102c9100c420300a0500e04000c01d0090080c05144440c1c840540510310300550402c00c07481c00400100a03401c0754040b40d000034090480000043d40e1f9410241e1501621081101c400000c0e4500150440c0076000e06402150405d0282ca44c01014100646007000c00c90031184c113009083c8114034500b004020340c5880c450241c4050001000311221740702c4442081c620340040010344039120341c0e600311007100c1b9800305545402c0001d0940c445000584000c40345480080d40320703d50b0344000c6603142c550340160155501c00d400d0f01b81e001ca01c10005446260030702c40f00e40c08066412100300110b42c40b89180385e90760640c010f41002c2101454480d1100d50740000c03078008485000140e080200700044c4105001031143c10b040d2403c05100041070f40c0d07100400b400000300384214001220132 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 792416187 1250 792414937 792414943
    0x9060c02090a0e070f03030201050c0403020f09090a1202010b010206011e170a021f0e0f0906240309160b040303080f19050a05011e140108070c1a01050406061d12 71
    0xa015928111607403507540350070034003c145c81400101c00550038040401d8111958005540c141c95006003c02c084080300d105210043c0d100034424140da114609280c2d0200342c0c0d14a4001070b44029900100701340c0408000a481c00d80103a0003c1d00d294000308000a100005010203000d69030450100b00781c0324440c49100d8a016945080694001d0880c00000307000d1a1500100040c035905848001c605105142000200d92042c0a2141c1214490000072202d142c070205405c00d04a04d4100105080c400708580c2846400071580840c0503805424040c0038401c10815100c01081554021031500d4115500200038a002522a1105600400110310381e226150200907803a880000c007042070b40381561010024200c00c3c030642c20156a41040c9840c03a00c00c000300181692507005146110f02040c0e4011181e00000504607020010940108400150110554020420f440b03640200e1941404200000c03035546a1144c000d02070324981643d42d01c1d002d0a0b40d210380701400c90b440d40d484000c1024041c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 792417437 1250 792416187 792416201
    0x30f12090e0705030a1803090512100f0b1809070e0403050d0906060905310f05030304030905010806060c1e102a0f090e041b090e01050709060c02090a 66
    0x8403206441e070800c46010342c4500030750311814201c2018010240c010403000701e0083c055502400003500e0840034003160130646240001542d005040721a41c00d030203d1002c088828280020181c00d480d104494004e18203a0400c150309180199514100e0034010407141c2c0e45d498a10658a182100c1400101494056030945117061100d907018041d407100e914005009000b90700a00700007030301c0c002c00704800c041c504504492420007594802511010211402e2071480130000468060707100185440c00504140701560040e846601c13951682da0901c03002400304000106014029070b402e12400200000002d0a4904070010303010781c00d150525143e1031806d000406103029246814a485040d14041070b050308140d200c0100700e0f440700f0084030750048400d460000d0300310f00098110401880b48042d003004268000d0321800081c04081130003170704420280441e5011805050340c0e142d446031085000c2c0181d0354444001d280c490442810260301070180d0301004800f034005c4885600081c80d14941340c0c8802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 792418687 1250 792417437 792417449
    0x90b0313031209030806030106291e070302061603021806090f03011a0f06030103030206060625230606100f120504051c0201050114011b0f0b0619030f1209 68
    0x3000d44500ca080117021131070140d464500a40c6001030000360010465102043c2005008094a6000b403620300c460280d0000300301d105170b94510030703030505045100600800c5114800e4000d410305142003241c2201c1440300000c1401414010441c40900b13040413800b40e103840008a94030354550704080080b80c800314500faa071542661a240089004e20035481482106440072a0300c0c8100c0c0070100240440d90100f03110060150744480044ac10711700c1d20381d02074882c850701c0d02d8a80701c40c980901071500da406070b10742080e9216000345081310300d041440d0040303c103402e2141c0d00a01d85420800080307a0380060b072810001c01c01480001200f01507124401ca50285501010240038906140c100240c507250800400d040d0780300300c04280300c09140180100d42c12101e81d440b1404142088070300541c0d802000840e80221440e485040c200058a8126284e094074014204010380349004002e12646015860b8050704405c000081040010820034000d407600d81d11411080040300440b130180c1c5c480718140c000b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 792419937 1250 792418687 792418691
    0x417040f091a090f09070b16030c140105011514070b0a050a06091d1e19080705010e07090e01110301031b050a0b03070f030603020609010809031b0f070501090b03130312 74
    0x70010503138107200103d001303201d004280c5481d0382d5a50701011340b510801000a91100d2420082c00100303010344c1c11014560300460000e46400c110744420b40c2116401d800c540200c0c02c00d00b0b540b08800340d0080302d5240704030aa0048900e03100e0310307840d015403141e001000713460815182c40001e0390704505500604002d0607041342c04d209140d400804c00d140c0f04100000c0740071500c00c00075055521001c0c0c00403c68042038100141500140071440204034903100d003410303520014208000c1c0c001902c2445001c80700c0000b4030103402c805081156040c1070350402c20002042d43c1c103115920700e555003840101d0b03044a42c00104000c2071440400c2d600d202d052140e00807923100c8401900090411080700045105202a82d120020a480f4801c2a802c8500300d0102075040001408040500e50084241c0e0fa0840e07000c5044a0030810089400c050031511090700340d409030404400c006080c031041142001800090030a80c0100e4245400300300c8070300004124850140c1d00d07012000a150003901849c1c2c20300310900702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 792421187 1250 792419937 792419941
    0x321012409170114060904020a0b0d09020619200d1b0b091b060415050a09080d05040302040f0e0a080f270907020f0303060d020121050417040f091a09 66
    0xe64000e290301031021113000f1960000440d00d00d803005515102d42e40c01032501c3c604138140f0f840b51489402428000d541c1c150b68201403005030741d4020103000b100c050125014041c20f4070f03190040404240f464401644444da403103031008224007086401c09080649440194150750303260100c000100004c0240c201c040c19020b210b004280491030180034181e040f64000d0400d684018802e8078402d51140c81c43e83c208840480541d18403980040c040180e881c500324400715124102c890514840032140400710301c00140400850402d40605c50800111758010040554403510301501c40d040c006000f08000b0b400036030180c44d40e090030203a035000ea8000c290810104260320001c409820300a0700d0300e200d598200b0008503118400586a100410484055401c2d0348814045c498010100340c812418462040807003030b007590380e00200c81c184240d0f0080100d217500340340c100403040c41e03240100382c02c4100c07040100340000040c0350310702c0049400382600000c0001e0003006504c0e001c411020010303480764001c4d003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 792422437 1250 792421187 792421229
    0x1e0a1401150602070f060f05120702060a14011505030618092a18090c031207210c200402031006120b0a180e0f0321012409 54
    0x2010100101152142020554680400f641d50707240c20701c10380019050100003401601e10071900101509281d00b010390805021701081c43c41030100301c50140040e4880020809444400d02500700f030200c2d108190840c550400340c95071100d10707125140c8000c0c03020000119000c0d455410342c824000c00392020344c115900707296943c903840301070b680c01d0284060b50482a006405418801242112134020102e84c025002c402540e05643d00c01032121245020b404680750003500c00303020303004d19100c2d1034080c0c1e03540d420b140c50000c0a820b550703032804440038540d170352100201780c1014162038910340010b0b40300c001441165188440a8107190090b030858008028443e080940090000c02d54429460350b81851024008440454408450380303503100340c0b4103004200c4036101d503100b11001507003044041780c50307140c81007103074500003960304503241950002400c5035510300540920b6034403101910014501d5450070301410041002c00c0c201e000c0b0016400f151800307041c042c4031355600030a4550401500c481c0008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 792423687 1250 792422437 792422441
    0x280f080f03070c0b100b1606020910170f0106080103030c11042c1b0607110d1b06030207110f12060901020c10180b1519080d0c051e0a1401 61
    0x1c0e01140c2070b5442901140103000d215220030284c41b40c0b428403a0410b10495034080001440160640d1803603070802910790941c49201041800c0ea5994036100c440c0401d000308402c4902c0010801001000d6450050106a900c6560130303045035050304c0c04003400b0010f0b00740480f49019850001e64800e2501401e401c08070310003400e080700c020b090140c114806142d40b00752511140b5034000d401101320740006225481c50260003814546004460014040c5400d0b800300310003503c04041650301600082c145140d28895040241c082c0c106413405504100c0240d1300d92290850840342d8510804808503150200d032030700030110070b09021050485d80e007401d000d000103000358010000c801041c007030a08010b0a51425001c0d40700500c20041041c0700080ea140c84480800d040a419803400119802d0508041c1c0d5a62040c89100c5d40c580d550071507054a4254094540360013601e92509120186000380e020401c04122542003107250005041c440e60f0b00c401081c100310609000500342035100d10b100c4c41c841015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 792424937 1250 792423687 792423707
    0x91b13031a0601030e0d110a0605131b030213090501140703020a0207080604020d0609170f3006040c051b100b061201061d0d1103280f080f0307 63
    0x103885041c405484160046054907000300e4500d0040d4484552100d40a214105905400501070b06039250031505694040c00e0b54026101c0082ca21144090300090103406a20100395152091246032118039660100e10651000e0004805082c2d0300e5400c0000d0110a41100c0203041070364040d0030003407503d02c0c0090000c1d0001281e100c010301c507884000c50740d050005a1140225001881081d15500aa5882010704800c190480b00903404484002c00c07440c0317010252102182040c1c1c242d403201844940c188408464101d5050281e01d1401540302d0250700040e0345810420507540412802181c1c00301740c400b40714052412901d16001042054500004500100d005021290601c800d11190080200301c3c001c04921032001c03108480100700d000d009110b940011010354812100d041480c2d4001010008101c4056890003c106174003981450207016030122141d414680b81c0303424480180300407078a526040c0003481c120001c000322040c88408419200c001c010025801c0d031741e15000c40001c02141e01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 792426187 1250 792424937 792424973
    0x618040c061b05060c0f070506090604210f0f0320090307060906080c0c12070303020a03111603050903120712030f0c0c0b100510030605031605091b1303 67
    0x700000b140d6090b62482d0b0700c98143c0c0010040055454840100c0704950101e00a075010300d5080000381c0002d181441a10711950796070f009002d481c42c0c90b00b1f20784510851071540018031314082e0341c5000415081700c00c1008900305440c1c000c2000c0c40c4207034164020112191680707018220410784102e0f004040d4000d12071002c003a01030b0780109542c6d6074140d90b040424003c070700102d14000c0000d5803000300700c005011140445000c58100301c170300100710002680021010b0340003980000c0c5245001d501070203034254052102c086a4900507203c4444680007044a900504104001074600c20b950341c204907d40c1000280d41d2072a94842c820310380b1a41501801c4100c001282c2443d0f90200324266078410502d01101c15110390388030050719610344030300e080c008244604031420f0f400c4c01b01d90354650515a0b4210f0340641c5001034028100b030700305403a003a8083c039820201c4100764002c0c029a280c807411550004c10320a000541c003050400c59011500038080050035504400c00008184601e00d403101041e410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 792427437 1250 792426187 792426197
    0xa080c04261204150e0d0201050702010c050c0627010804021309230d02190b161101050c03150a1811070602120a06061112161506030b060a0f0b030618040c06 69
    0x800b141031100f9501c038640048d01050f030901109015501a5170035000c102e103d00144c030142c500200000b0800d030032100c0210088002d4102120b44400003941c0c941c0708034000d003000005440e00e54002007108001451070180039440c1c5002c0310400581c034400040c02014102109060781030b504030103a45981001d0110014030070f800090802016880380c60150039080f2490003141d42d10312400c14050204441184100122180c03899503210082c4507450040881030103a5a4074100040038003181c103a4444071520031060b82c041007003a1101551001d00007000c441002c10201c806039031608940c010140007800450000800401d641962010bd0784a40d1340580b00700075042e100c4c0703011501c00608903121440b590109000700c1000c10401c01400c401070540c10591545504c603034a80c80144014801c1315019030300d80c0001c0c410854240c06c1c0130ba00a00c02e9480107001894200c09aa0140703c502c12524803010000100e045500c428082c08444071074a0301c000a0303030401d4038045214081c0c5200d444000b071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 792428687 1250 792427437 792427457
    0xc05060405030903160b030601050a141c060614030402210610090c0804080d0b151c0e0c031009150e0303070f0201020f090418170a080c0426120415 65
    0xc29000c03000d1040e1b881c140d01150840d5260700064810b43d21916089003800441c243d8041000803110040c884446028089085142d60304110010346010742c0280051080c8a6022158408142d0582783d10680459601d032228200c075403c0109000c0e00d410350b48103400390608002174000006181c0d403c82e038010780d003000310408000301159030038400e0794020070b0a40c0802412041c40d1150304201070958000703000010000c6030f4141400d940d440881e030254020701024202e035035548a0321a032940c10401d080a1320300040d00100081d280d0403600100c80304160b031250b4150601224422280804540183c01c0100c00c011110070b035543c0e017084901c0307000143c40303a040c900c61910600031b4034400c03514200c6140c240001c1f94100300250203800f0402e012049101e00e1040030800002000715800e6402e10a582e0783d40e0440401081c00c20010320100c01144100001c00c100d8402000704d11313401074112038045007511451142c0d81044012000603e50000114000c01c4c08c21201030310102e40c00103910b40501403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 792429937 1250 792428687 792428713
    0x140c0a08150a2421150e0106030f0e0c0d080307020a0515420310230a0902060301090209060c0106081c3603150b0109140d060c0c05060405030903 64
    0x10903007851060f005200b44c180d1051071003120343c020200081082010310140303601c0b200345081d0510241d01c501c000a841d6415014007800521078000500720100140007220342180109050ac5051000180b60610001c0080c0301c1078424060100c01c03036441805e4499082c200445107402800541e40241611089040307030b041904001700d82c0c03280b902011001100284401c1a06013000500c4c08103039014000c0036511a01c00c852481003000c40f417aa00b090340a20001050f40030880d0b0f200070111020140390564080c050381e00c00042c0e90458806003030169990803d0004221680550100b841c2d040d07090000c0400e840ca000304511101007d0154441c0168091902c100c0301c0c8015515101d103071012150560303546800036564004030752840c10200800698070355031444074180d84102c45581d02e0f5a80c032450300e10f40c0d12500200050003200003111000c11050002118003114450040c0703060340da14080c0609034021800143c000380c2050aa90451030302e42440307510f035403001c2c11041c0300b4051204e0031112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 792431187 1250 792429937 792429947
    0x706091a0f0c03090a0f0f0506011a041e0b120402040e0c1e01090e0403050301090b06070515071b0c1e0f1809080d0e01140c0a08150a24 60
    0x8902001092601e1540310401e00703100381d80c4080c1c1100d44500034429500c2c080350454020b203404512420103401c0c01c85803414141d041480680001c208400c600034103414007021030003500e05482a030180c1c0c10001c4007140178080302407581d0f400a03e02d40c42c08510140001e08407190300d84120300a94081c008031410441c039a49604080c521140c1c091a2882e4884203020716034181d101c92081070510041c00c9844c3d8020411418080358220002003000005015482440c000c80346940340984929081c42401e03500c0703a4403807079040400b440e044003520004030614403482c02007480d080c422a00010320403c1e410441c140306418050304003075a01c03e030408000f840b0035680840854440301c02c140c2c3c0050602403000036030101c1d07624078103080b44c9400f250004505440d00500360010041e00014888165200490a5490111220313041032143e204008081d18407400b181c00a0680c0d28022501d50364081c09207441c12102010726400448202c03001c0b45180400501d001c0c0147c8002c0d88400c00000004c080391 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 792432437 1250 792431187 792431191
    0x41802010e2215031410060e010510030c0e1207061d100807020307061a09090d081503010f0e0105071106091005060409060e07050103060e0112170d020706091a 70
    0x190b10350036000030400100740d40d0091000d0112410400b403850341d40d895075003200b40001c3c10000d06030003200e81c020a03240c1910806000381401d600c541025072401b40052100c00700c400034841070544a18940c1b0700107201d11540705070303940c00a1041c80c6014070844001d580d8800c600480f0085510010948024684d090f00c040c45000020130104076400581412601c52001405007020742c031041c082c500000c0c0c46400341101543e400c40608a901c0c03081307030400412210150544020307400400300b000300180e001040960100030543d05002c0b0449290120f801042140e1002a04034601091104007400c1034111034050b444698500356000512070b1425110b803410b544440d02c2d58030102c646004100c50750400ca0340110000e100081340303003803070b1902c01c155000708810396030a03000702005015039a058400e02002c2e100e42d140c580010f6040000c558241c84450401800214aa0481e480700c4100c2004860f02d165820a041d511241070f840c04d030014014684080702c4107a001c2c95211100308400100754 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 792433687 1250 792432437 792432469
    0x101506091a0a120509010504020906180402090903041d0106090519140111100509160f030b09070b0a08010305010b0105070803070c02060426071202150a0e041802010e 73
    0x900d81003200742828840794003880c4a101800412003110309450a1441001d04c50807000c130000c540303071503e4410004600b500501d00340c407a0081c0305042004000c8002c44503481641139486811940f02c000c569813550242d079100e02c01820000207429074100200100c80d0480e942e540352442005c0d1114200f0144000c106480c1446684110f02001121885486001c0803603040c1040e186d00b201c1445480d080604001c0c04000030364442060022608040056803c01d640441c1240317180790038400701c002074004a200203841d83e889100492400d40090041500a18944581329503a1804900260144100b4841540d465103046440c0c103840d4010300c11541707025400700300c19145941d050070584900004040c140d80184d02400301041000300c0c3c4c104030020748800040100f4561440078120315024158100401008546000f080142c8440031400c0400103981d001a480d0200702c502101d040b0105490340e68007a04018031800d194462202c4045641e000b0390f501c22090040d0320a00c9041c0036010540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 792434937 1250 792433687 792433709
    0x1103011409150705040b041d25050906300108030a09061b1220070302060f0a05090901060f02060f0907050d060212271513060e10150609 60
    0x301042020b03103241c1c6980014181809030605031508950081c941054000f0282c0c840072044018140c0d4004859682c4510020802066480301d09889420001103081c1d0f8014810702290b000819a5464203807102d80f48074001589149100c0d8202020030031490004d050403032500350012602d084084112040780203151103800c01185070a20885050780030480350101c610881c600c2c200002d000c001100e003068080d43d0341c2124005c0c10030301444131a9191014600035809008104010780b0740c14207607440341d56070400705501c9814101055503944205800e459102d840140042002a08000304003500b120560803142290f0300c80110041a07034090b2814541a07004080400081c50001000205544240070141c10302d110a840540d00e4034068503c2e0f104590000404030104048040c40109801c0100c01401c02c07414040d0700180c1420040e0445800c0c050301b4107484103000280e003028080b4259070040f250000d850032101d000410608544040c0020003006c0021090712078071002d800c2e100000c0c0740c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 792436187 1250 792434937 792434953
    0x11090a1b0e01200f010b030c0a0b0304150e010f0f2a0525140604031d060405062a0f1f0b090703060f09110316030e0a1103011409 57
    0x1580d189a1084030710381001840380401c0e00d0000401c20f498031601d9044020007440c84081c040c1400c0d901451007581c0a035001c035030064807031b541d0284c5150488800034441b0341c2e81d45690800c0c82104004400200546040ca02c02c00c24141c01540401d0040c05010703002c101c41112200c0030002e5685100707a00c1030ba05001243d078085080144081c00002c1c14600302580350842c100d40f12800040c0c416510001100e9180c01001401b103041402141000d5a50140519240a6a0240c40001590585110858280100f00c0551501c50445020b410300070609a10750b25100481c48120504410f00590008946015901e0110000d5400c1c10701d181300d0094180e03024405000201911640c003100d94450b180c580b0943e00762500d13010b0300e0040c6010b540100354141009818603c5920542c84000340c42e1400134244500c02501042c1e0382c00c41289480140460744a1008038040d03c90580120140d000b2282000108580100c501c000b400c03042d00280b10070100c40d5a401303d01001120103041c15044424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 792437437 1250 792436187 792436241
    0x160302060a0e190303090e010803030405100e0c040e031c200903030415080901150b0304290109020403112b05150103030809190312020f1611090a 64
    0x3942449101e07002d840b0f4030a22066002c000150070050b8801d401088100c40c040c003102d00d01c0820a40940f204031b00642c030394103150795110b60710280d09108050855442420424000f805d220441c0d030080c004005000d803007040e5115540740d0380218883c24882c03141e00485095810540540c403010500701c1c40749080d80c1584038041c5070550164006c81d40c180010840482c1003410620602042a030944c0c485103d407902d2300030310b821200350081e498181b40c41caa03000c201391100d460840740c1c4a58800302030501551400441c0c4040ca0404d180c000c02d160840001096625044e4007420481c1e0185414035460180070051190760045401c2d900c4040e900403130714040d6008104030044c81e2074850021100d0200686284211940080c0c10442c0000d5551302401901e4900b0010300010300042e10003600b0030013507541d0140c00004e00a04031b1000d141c02094072008004014280c170402c0000a003450100c2c4028070300034001c07840c0790f03040501c41c5000030013040210f0710710f1180d0100c444564840c030404c0c0aa00c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 792438687 1250 792437437 792437447
    0x204060e1609230f040911010810211a0106020c040c030501050d17040e010305100e0f1005091f0204091b14030a0b031005010314030901020a08091f020c03160302060a 73
    0xc00903134100282c80d900c1501502d59115004805000b01d140d015040c8441d0001842e160014064409a60000e0310a115980003407104081d04420150441070405291510f1415140002441e0310759188080c000556143c020410300a8520126030820105504a500b42d00300e13482802020b80080d0030079214400942c8a81c0300e441c01900c06c695050400381d0f1034142c041c10308401d030004c8401350050702412468010300d006646000c4140c101420158803941c3c00b1550351004040c500c60003584500210b20401400d001e0f03c070300d2540c96807030101d04074484060f2401a50191141101e06440c2541900c5011144180c4045410f001d50314104c00102c001d1042440d0342000c0d0001e46e02070354500c0c0f014016039003040002c4c512020794070042070f25855810011416090000d0074049a0010000003445a90101d80c4d80c2049a2028201e91108614000300300b514030412803050641c50500092032606400003210210290110100c40c403408904058106070220b03880003e400090910110b43c3e198058 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 792439937 1250 792438687 792438749
    0x60702010201090213020a12090b190b2e0e030a080904060506041217030601121d06010303020601091505060a0302161e0b180a1407030204060e1609 65
    0x51001160f408250707000140c1c40c0d420a42140e951070381c009404030304240c02c900c2004850922030b008000395840c0351034102c00080c1c0201004880304800305a0714041d80c40341d018081e21200506038010701504042e03400510610050412102c4c51544801c0744038910a8542e0b030342030b090140191504885507501d03001a41c21101c00142c0c05500c0d1100801d4648418018200500741100c4841c22070780142084010860328a000383d11210042013040441d0b6008401c000040d103074440d00180d998140321303000c540e0041115902c1c807076008580002007451f40c00540c49041e1481030200704200c1244694501c0360001e20b209941c2c0042050003040a0345000b03501402782c4014414a60780f00e6441d07607071800104950304d0708111002d1502903006080c0700b1000c2c20564003118803020000414610f505c0c0503039035206410000e0205040543c12513100c4014054000156409030050000c80e8a603114040310540446402e07003140c094803600c0440b01e101c1d41080c4202c98a08602c96040103888003420b007074501c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 792441187 1250 792439937 792439939
    0x15021014040309030f060f0f29010e0d0507080a0b06011b05070b07050c0904030906030b030705060306121513110f01140a050c070b041d010e01090f0e03030f06101409060702 76
    0x170310000e40d060001240201090000404000651404a04403025159081d00c2200100c9c0143c0c102c001c074a640c0110b03a08a00001c00c81d40d100301c401445c0340c00361924026800070b41040c0913440101c400c01011442c3c2c02e000e07402c00d03202c45c008a0f07480e001c000032940aa0002501c554050b405c1004142e00d454028a8007074050001d488001e482c400214a02c0308090310102c1c0086d1804408100e680c1e070602c900c0c0442001200034180852821002071910b010151138a841070702941981071014004101d4a914404040c2590001c2d241103100403800300c040e018140c4401c104106040c2c0c179860700e40016916484c058560000116a030301c0241403039002071710102c09015007084000100c020410540000b480a00c0c045640d680c2010320000030340fa1a80942809034803104014000c80040602c1e60b0f0543ea40410002746500201039050b000e0617036511110480e00001047c40740f0b906803050311038031481069a0407404500342a508070703413026000d2964143d03811305000f100401e1602d68000c10303100380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 792442437 1250 792441187 792441191
    0x60403090510050c060f1006030c05190309050613021504081c140d02071a19050a0b060301150306050102030c0c120708030307050c06010603020a0e0f010915021014040309030f06 78
    0x500c1c003145820401c0c1c400b0135500d00c042c1c1c104481f001d00c0d10892400703009549820701c00c180f00c00340c0c0585180104540c00360440e21000700c50702c401d442540014a15a0000201c0d9600d0410000100c1104a6100141e001e00c41300d50368020415100f2007100e00b04e034510b0000340f400044400b0304a41240c20540d031601002003510002e942d80250b03101400011500c1540169101010700e400625080d0350454804600140010082103c140c2c0c0c7c0030032409180b40d0030204441c2c3e030300c00c40b240003002410034441e0302000100001c101d80c075115014a400740d0581c0c03030401040b80c0714001665607014410f00502280d0140f0250b40d0641401002c042d524a1050116028075403100c1c103036030440d04121041c10000b10b000c15407640d500c2d070070000709004151034142185014100c003001071010000203401030044901c00301184491340b140102200401d941607081c8c00c070219406000352681d00c1c84100909017418090346151440892100c2e600456058589244040c510b90301c035010403030248400d4440d15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 792443687 1250 792442437 792442447
    0x103020f0f3007141c0c050405070306060305100e0117010f0f0507080c0309070b1605100c120b06030703051306021908011710050603070504020708130806040309051005 74
    0xc1001c81d55001503404124280e41078411142d80d441c2000e660301822000c0304da0411071100d5100c0315103210080400103d000100301c00c909003d42103441c07a034484c6800c107241c1010015111740c0340d4003000940e500d5507005d00071501e4409901d00d8208486c011803d6258010340108100c4551168004d0580c030002c0002c04d81403084000d40044803e580c810480d2187c8980800462a60003000725a020940b031883c1800c50505840030303640d48503240134482140d40002002c0724050f00c1d00240c8803040364000102e4100b407019520030340280450009440224602d2410f070028110140100d03402d07400d01604081c1903070380d03000e011405400c01908152020360074541000118405c0d000900740301c0c01a4100001c40181100010482c2a050703220140350000200011100341002c074a90205050b558030100d180d03210400024208002c82c1c0c00340368018400a2004104103564015100101180d6058114956610241ca89034002264010005503801a050000c2c2c54501146215107031245480b6040c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 792444937 1250 792443687 792443719
    0x22030c0f09330b13140d03020a0308040f12090807080102040302010e10051b1506010f02030d0c091d0604050a0c02070303030513020904140c0604060f1209050d050c0f060103020f0f 79
    0x169016030b1807018000700d080400c3c440c030510f0007140c02c01101c5c02d40301301003402804d850081d103483c04010014104007071100820180440c6071201c3c2c2009401c0041c00180c42e25022000d03003504982d116014a50092030780c0056107034010f1080d10120f94041e1071b1000164484002c2011140c0e50714a082e0902038284a46440d12251101d84000d031003e1400400800e17041550050080e8001040dc0781002142d12800042c19030100a982c00a6076680380400c0955a41c48147c80c01c101c03940040320010301c0000351705040005810354500444007510f08000d240c680d00c1c00c160a4500e1182964056809484200002482a44010351040c0485003040c8102d03011760014200200982d0140d416810036020408400300c00e100144680700704454040c60189444809440300c094100e00505200042c4140c1d0b0724468160080f10000340c0c840180c42c0c4d0100075600150003a08007011048140c818240450401c0c50002401030580c0e80007844408846a003404118646401c008110340101c600741a100748 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 792446043 1106 792444937 792444959
    0x708160831110a230406050337050303180c040c03050105040f1a10030e0d02010c0f030c120b2701090e06060d0822030c0f0933 56
    0xc4d00c940100024020041503001da601409060600e400540d03064011086040320100c00242d00d024140f0702c0f52040032a00b000400350b40c070400204107074850880240d409045058100c0c1d103c0d07540711020600703650f201929600469100c20040c44a450540039008018181e140e00300554406e03415000004075284180340d001d2101940030050080c0700f80c0040010300c0c5220116554040d000c48001c0c020510a0b07141000540c060300c0b0309072098800d014005140c1c0d0075a48104043c1e41140480009005411240f0b61200c3c03462000c0744c0780349100000348566500499250300c203615107100c003029211007a01825a0343c00c84e100304425039584607500d101c3e41c0d4008805c20f485410740400140c151511050070501e4540880c00001000b40110b03400091b0f810540400d031907242c1d43e980080c207032003000c0e4030940c0101c500c41d07495000009480e00e0342154810b01036000629513480000c141 = true := by decide +kernel

theorem cover : BRFrame.Cov 792266187 792446043 := by
  have h0 := BRFrame.cov_init 792266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 792266187 ≤ n) (h2 : n < 792446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
