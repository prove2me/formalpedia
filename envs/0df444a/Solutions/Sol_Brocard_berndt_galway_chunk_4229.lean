-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4229
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:56:17.789839+00:00
-- url     : https://prove2.me/submissions/04cbd7f7-b51b-4181-9d97-bb4d303a3956

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 760431654 ≤ n < 760611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 760432904 1250 760431654 760431689
    0x9030a080c1005040b09010b0a03030e04201c050601181419030b071d01120b060d060905090c0427150f140c130b09060f03010b041a1305090a06090204 66
    0x103d02355040d01804138814407002c0b50400010b40c01c059111a0380c00152030118a0102c440c1900704000e9510250004030b01001030340501c2240c040c82c03403100718150024200308940300c040c011224281c0c040700c1000303420740181041c0511007405180240200f00145405c141484002c1c4140100725654000c99000d10708409204100d6040b040c12104601000a5061144c404d200020b200071002d0000340326050303803546484400d4481c0b00c00ca038045490000180005a40da4104500801c81164802013034015000100304901d005c1c0078042e012504a04414514080c01e0390046130101031060803586d85002c0d00c3c492100030024042c0e01b0741c024500000007441282c0d085d116000c40c0000341440d401d9401008030081081141b5424030030368800b4620f05071544400350101d045803040a40101a404e008000001c0030000c07440103009443d5843e0450300030980421080e0b405028908203e052043c40c42e0042c419030521070380340c50344628555004190240d891101d00120b074030030b80001c6558440085034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 760434154 1250 760432904 760432921
    0xf0a0f0501060501020d0e040e07030b0c2701020a2312031608040c090e0a0602070c1d092119022401080706050a0527010f030209030a080c1005040b 65
    0x9020043c80e00380007812002104003c000e0902e2140c1c0700781c5105e2540d070004000c04440400021001c0c3d0380c412411046801c013581e030b5a0b896040358081111a02494000d9118841007240c485030b05041a00202142c0d212a0388140160b0a246800d601c140b1280d945406040000c0140c011494804185030390b0b641003034228003a00940103403603d42486410428000061120941407080b219005030024140080c0d030300b407038145044184042c01c4c282c00401e01c40244a4030a04201c100d540008416040900c03651002c02480c4080301c915550382c008001a00c00c083c2640c00a44c000351245c41d14901c1c2030055902900640d40403d51040141c1c002d04400ca045c0004107641e500358807200680548540c900300215544c0c0303c407030142004202020815500b050701510030307110215051000b0b05200380f8040d5000f41240c0d000c4070707400c0c009009403400f8003209000f4400c8079404e00f0040e010700319007100c98036080307802d41c0024052041403007811052000c034040c600c600e9000b00d2003444802c1ca90b00f03041c3c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 760435404 1250 760434154 760434161
    0x301060e010302091003150b040b040617041a04020a0506030a06080d0c0f06020a03060302060c060601021c02061503072106060803031e0a02040902070b0402120606130207050f0a0f0501 81
    0x369414544100a0101995605500c81d0340180c2a858042490f104206c002c090480f200d44c00000110701c00300c0d020a0031303140c61000e070082e0340e80d0707603240c603210308864110210585007984d002e804001403040c00c02080700700041e6103505c54005001c070144180e403034010a1042d4001c0342c81003850b59445038241320881c8103004c00181d00149191021035071016441d40074107641100b4005054a90000d0302204c1e89001ba00903000840d0028021900e481c80c0309110790b102c1c0030844a85006005222103103203800700c250014038000c001c0c0d600500c0e69690b840078903001036040681459052190741000a8030070302800c14858642004000035210108501d010f900f0765101c3d0b0841c502c00c1d00184100300c00d42c070b1103448905071030f071040345544029240c2c8284407000b032203550000e410060000583e003090003010402d06008034803c0c0c03491500c02001e1440151120780c242c4003aa4000c410b2003503942c095240743c01030070030207001d44240d8111049211182c0d00d00542240119031243c000c00842c404e000c428031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 760436654 1250 760435404 760435427
    0x9010606020f0d120f060b040602060109090f03110f100605120d0e0603070302120f1f2303030d14180d02070b1612091403070b250c030602030106 64
    0x140820b5a0060030b050720303007240c0b600d0300040000d001a0704100042a07000045203098601040004a480b07200c2c513401036100c0d000b010003500c2741da400000c42240c01e10038202c2c142d802c4100d18003c1e0040f540d040300c0b85181c40c0340441c2c55200d001c000e502e5181d000d00422203821200d01d00000d01034a02424000d280030b6001052030143c0000d1141510a81c01959a14540c001200c020fa0380340c3e078201e07040e8000d0044070382c0c20110042603c20007540903010b004403405094031030480da49500c0c41e80002c0d10001910b020394540c9445040713680c2b190401c241401c81c01400000d0a5030300f4148860b01c64021a1083e01d952100c1f0071094052100a08044c045110b4550845014250800f44110040d585640c1445050211180003404c08134030f1503440045a0710a921100c1f4003000c01400000514564643c012610a464040d47c003d003549000100202280d041102450800c4d41500358601c0c1d130010141072000c662040721007540014020350542024510400b0016107a5060100007040303000540d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 760437904 1250 760436654 760436657
    0x61508010b011d0d0c15080a0b22150305060c1207020a11060d060b0c010606020c041503110402040b07030c03020c010306050d0b0c04051c1b060c1401060e090609010606 74
    0x901029a108400c0a00c1000000c0300752222103082c020391512174400c2506602c1011945086190350300c80a074084450783c0216040d16090103102202da080040c1040302c5022040c0008070004c022a5064203500811440000345004454042d0349845030b50901c801100d80701c48045000503503051100b55000314a401a4441c802030485c01f1032903465550030302c94801c1080c401d0f280420503603581d805540014000c0e0031b504108a440e501c401c2905da019140a0150700f0140c000e0100030541c50601c0d00c5512515188914100d50300ca255480e10b5601c0c581c2040f8081c0c100d6020840400c01d02504402003070700c54841d60f108811081c01e418001e040000704d09419041500b020000c0100f650b5014101080c00e4105528400c5500d9400d40a1444d02c00c036440542c01206017810380c100d42d08055102e00b110b0780545000940c0314201000060301d54124050000030070210341c8c400c000308943d601c842d8903098641c0c2c000030790152108200320213013104441c0c00303140c4d0703022508222a13104203009180003007425 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 760439154 1250 760437904 760437917
    0x1508091e150f040807030e2704030801081b0405060616050a0b010504050423010e070f03050111040503031b0124051f050f070614090129030a02040207030c061508010b01 74
    0x3c1e903a001c0309449540006401c10a40905480c010f69070402200c00d02440d94401100d18070a04807540d036958400c035010340104031a10000a05001c000c500c2c3d40c5e540600061504000700300600f04002000043c0040d900f10ba4103100b101c520b07001c21002d8000e802d002d0001000701c2001c030b18080c00001c005811203806981020b01307000c00580052204c1c1c0e0b42850001003030400303c402d81c052500415040035082854030455800142d0490150b40410540780200020302982d10580c00d070407014482c610415406610030041c4003030400400c14140c1040d010000041101e0f881100c005034084684220006d00c625181009c000380d1a2140034044a40c0a241940340450014a0007600034007034018215203840700094040100240e5074006205204800d03141d15040c1031500c0c03180d000380f0004035850309626404850111454501d096034541701e900030300401d040040c0307600f404042c0d04001c0007101407107c180c1d03600d000100c1c03c0c015508030620100040210a1a041e20a030a44202000c0203061221 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 760440404 1250 760439154 760439161
    0x70804170c030703060f14010f08100e1929250c110a050909010209190305060a0207140109030c020f100504050906060715020307090e011508091e150f 66
    0x240416201e0031a80c001c0d400017031104207001c600d40504440e03021124003d05d507c001080c142c0d0130480c00006d45041c101183e035a01580107180044950201308514103500c42100b040c2c080d95144010104a0701c9807201046000100e0058803e815960300907002038580401003011039684d143c04c100c80e824821601e5103601411500260ad00d030746545d00500b0044016456507c00e46403801c140c8010000a040001603140980d02c00f8002e400c072024481c03013502d00c3c50300b00050411401040040c1d2303402001070041510340e80240070007544000802c4400b00c01d60300010b40e241d0020322500c0a554082e0f2603001c902800ca1042040030141c1080851190501c508c1c01d01e6016071004c05d41d426210300740e0ba51803941d143c00300010300c24028500018200c01140184070320154041e000740d8010152900e5000e0415283d0000200002c0d0900844052841c001c0d05094450711540c0425002207461041c0c03034907c10350741203041c4172800c811202d4000d5803103240c00f031008282a2244640c42030340e102d6440b4040c01d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 760441654 1250 760440404 760440409
    0x6160806040c0e040507110a0305180907142208030a020717210702090c04091419021812030a02070b030402010906110705040219030e0a1223070804170c 67
    0x990703c40440d8041d55540002030541c501850080d49983d0004d01240c3d500551482e0042203603100800309032500c072040200140d03500340310703000c2c81c0200c85e07907201c03044050510351402225400c000a440504201400c1c104408541c0c00c205d88060520f48010f0350303580301c501c440039181c1102d60380114085d20303a811120a1880c2c001c80c5550b0800742c0b100b80d0a1002c0030301c2410303070700a00032400060760180864060004200201c0001c2c0100c0f0075404082c824441e80e80303202c0c030510030121611521041e18103002800c0209540c0244076800761440c010144e840b60301c001c100c1144007040b03031000581c800180c6185940d01002000300a2a0304c58a4501e1071405900003802c3c1202c030711401003440454100303101d0311030302400224003a01000d0000c54656040f40840c6403030801010102006c68a4000500141000030070154903a58100d400807244e1407000c40c00300c4103264504003000128081c078a04440c0c8240c4040207080840c0144401c68a95081080f0603046490300c1c04040c803507901000613550350f074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 760442904 1250 760441654 760441667
    0xd0215060f0303120a0c140c060103020d08130306020d1d0c01050c0f190b0f04030903080a02030c030d0f240e1008012a03150312020c0306160806040c 66
    0x825078004000300000000302c1d103907000b0f6044408068405408004240c82d040d44a4178001105a4459000582e5207450380402e00c02c2c0c861020564204200610250900d00d800340d842901c0341604600d80350281011030350b00700198104a480ca50001810180f1403998003410b80c0c1040b04118800c0003d944001480e80c0e240140b2116040c020049030b000520b0304203220307a41902903002d00761381040002d05041c036a25480c15008440b200c034804003054468003000180f034851903154903481002820750300d03151030ba50001074103201144400c00901501c1300c0e0520103808140c641c0305000c984003500b040180c0503280d0f030000c101034160001103c1d11491501142e10b03411120b00342070710f403101c1d1110000052002d100ea0003150096082c581c0c005201110051040f080c0900c028418500e480d00000480c19240750a0544a0405464100f400890300070740e96560304000b5801100c0002051300042818004200c6452200d19001c40e0768007039507908114041e5000b40100c400704140384074a100542503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 760444154 1250 760442904 760442911
    0xc031a03250806010b09040c050307120e0705031e0607020d270e0117060106030209030d03050c0904060e0a0b1f0f02120f04050307080106030c05090c040f0f06020d0215 74
    0x5010710019601d08110601002102402940e003c0d103080f50b8407240b42d0040e0b40e1101c02d11a000301e142c41060f504941c442c00549000300166501c911f040c1600070007c8020340300440300300003180501ca9000034207940c2080300c9108001d04100c036103898000070314180d0400300010000c0043d500600c06001790103601507a00c04541038074500c0d598161b000d034800720b140c0d40b0064200e2415210110f0000c240c2120b0b1112004c411010341c0e0032164140c2e01e0340022800d9000d070b00001038240e4800c0e11042c0445000c1c0d08107aa01014004031142014421000903040d12410703480040c407800984148030301ea0b21139010f0015440d10590391840186103004040403e030340382030302060070803200d81403103030b40184240034480b040800400c43d41e07140c1e902d812000101f50701ca885501e200744600480041c1504c410301844003103a41010b0b40301c000078901414840580c0c40100014a026410000418241d80540304003005d4051030404071242c070b0800e2406031820101c40b038403d0a40d801a41c541c0082d124581c1650303031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 760445404 1250 760444154 760444183
    0x4081e010e150a0908070605091c0e24030411030706030b0901090216020315060a080a200a090204090603020a0e0f06060d090213091205072001090503100c031a03 71
    0x1290342d5650070f200107200c81c020080006500140b0071041c040f058101e46d000c0c003c1c8409503800f40f46030240030b0786082040d042007000716040c05907142651030032210306940644494480d54a0b0040b040500000746d01c11a0115800b00c0004841c10030340c03d04000700030280030f1a00741001020580000280c8041d41445644102900042d103280100106c40800074520307406030442d0303807403650a48402d10f40401110f8550080d82403280c00240002c0001c1c9507008150800000b0b400d1133849030745281e5144210300f40a4210402d10307000030b9905005c0c4000d00040c201400001000307800c5104000038044158046d08040010100303003c0e60180306a06240c220000b00c96080d6100d054002101c094a64510041d600101c03841645030703210040c2e009000c00c01e10554412400440760542030b5040c3c00344441c05054112100c40134001044503003041c00c40d111050508090a030359400000382703004921600c0f2100c040e04c64000031865601800382e00c1c0503407500c41041e44041c00b00e0012a98a0b50303680d90340ca9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 760446654 1250 760445404 760445443
    0x60b041a0d0b040c211a10020f0609060f06010518010c11151201050628092d210201030519020a0801210b0402091b04081e010e 56
    0x400c400316403002c0c4940c00c1c082c1061110031a6440007802c90400103042c0d05204c1d84000c80c1403101d031520f1040c8850030002000c03c80b03443c2498000d10a5001c540302d020810751050585036230720564100320480c480d03540200144510b143c8055090030000c0040c00041c140942400340c003880024110041291101c02c1c0b03031a40c00100345080c400f85007401035940c6500020002500603500d10600010617030022788004100b002d076629014010300b442841c416414584050300b00f20f010341401030700142d0790125460003050040c0c03034007041401181700c2c502070103400d08552500700c0c4040030707400c01500a00703c03200113503020654842081140b04602000038101640c80d0005424003502002d0780c1e441603c2102d045444d51080d440281007407000f800f0744600e00003280440d20041d5155980003e0741d41c1d00000c0c12405d80c90303a0307003807090184010301103014106029584941d281d0840010b00010301c1214010070104002c00105410811704090300c2c031050b4140340300f04694000014041d0000f0103404081d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 760447904 1250 760446654 760446667
    0x7090947070c1203140a060f0e010e0f042a031115030106030c0315080d08010909050a03052104062301150f1119060b1e3601030501060b041a 62
    0x300c3c01450b41e0a80c141400328a0006e0050322009948420306441410750b14100e170070384520920307000c20002d02c0740c0303802e9820413000224500320b2110340d00d03042071090340380d01c100c88110642e040d400080a254440c140e50085820018401c580d04045c1800ca004e480908060440064460051005000729000e154071507400d012424481d0780f01c2425281c1c4d0b030a0890107162070f1b801c43ca4a40708204d240c400000c0b0490004104019180306450340715074401c00414480e0619902500d481c1c1141c103620303a0f41040b142080346040801008184598468900003565124590100344074415030040e42550140c414014000c4218020311960700c51254282004e044008050490f049400254401c12602a180d440480000250b00c1d0f8030301d407441004140480c54008040c0000030010043d49802c018181291348043c0c205070702b01180c01c211844000241b1541d26450501d54602e007450001e05411080040041c00802e21405000d003000d20009803030203140c0104620000d0a15060004407840042c1300d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 760449154 1250 760447904 760447907
    0xd0209060f0319081207021c180b030406090212010903050921100c09051005121f06020604120c0f03050901051b0307020a060f0207090947070c12 64
    0x301020300f50005400d80e0300c010245070415064000d100080c03204601080440c003510300100b0703041840040008100120a850030f401c6070f164888400b80340070201c020f034020447c07424140045120758001c2e2400301e040c0030b8074814407002040b8100d4400190f45410184c0000035070000407201c210400b2146400d11951a050440c080f1502c1030f40449240b0075040180d0400916800c2118491669100c1498003a903400a000c1110ba6142c920310010308100640320240c0c42c052807030340d082088800b250248200481c0f03600901d80d8540c1040016900034810002001030324044803c0b01c2c0c0c10361400001c1d002d159600c45401500300070008007889000305410396a0f9104400f034074816614268030300c1c120b005036190740d5144e900428040e0b01a5507002703004103c50740a4685406603e045a0043c100136281400c40401042414021140c0d219441c0c40c460580c10040021404100c000c0c3c209407141d10f9840f01450b00b2a1540b0714580003100000812a860780c01180b00420303907401014500d01034207500300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 760450404 1250 760449154 760449163
    0xc1207050a1425140c0a05010801030605090703020a0f081e0601151b0606030510060602070501120b0904051513150519090b100f0e16020708010204060513050d0209060f03 75
    0x40f80000c0501d0829006100c1e01c982e02c8100428114192100c4844580c244510300340300e030040c1c80c0401c0301000104001542a0300c447d6001c81060140d44405440e907001034894001e69001c1d034070f403002040301407005605c1801400b00c032005070701b103128080825154080e10b130001445980e514610f11400a800f01d0b00501201810100359030444005110526142009029502040c0c80710311406001011103841c82c441c1c0010703158150020404249001c004683d5180c0c410340b0081380d030b0b480322401c503920b0300c4104800d4001c51158026200308507184070448001c1c0c6000702400a09030612b01082c01207011088a0725404000c0c0b070b0040344d0766448502c1c138060700c59600c40c0598a20700c0c3c01014014880d070406658040d03001102070b507440a640700c01c01e0a21000c680180d01c1544254400f0400955617030044281c070f01441d00603240c0c0705603140c46c60360890f045540800041400002c0f072000c030402c444054005000d04540101085030141c012941c2c5902c0140402c0c0520412229142159030400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 760451654 1250 760450404 760450447
    0x108040c0b16210e030309030a02041805010912030522080a0e03030304030c020909072402120310090f1a0f031207080702030c0904050d0804030302040b030c1207050a14 74
    0x3400d88100301490309039129540c1e40d00e031038001340ba1318040b10050315000c012255940d034003c0c010010b220071502004001c1c02855118402e0328066940c87d400298280603260b070b068003a902c0e416452100d000050281d4800409251008141564402445510346144440b664100b60255221035046400703840200c540180940d26201c04020041015802911104081c0c0f0a41e490101ca440b10344c0000e42e609180e0144211000b9541c610500e0100080c848103010812481241d08000c11204850110341c815070350480130500f030700c0c01444089a50b00968070013283d041c5040100002890100c9400e20000c0941c0d0700c165206500301944d0390341001422441c0c641d0101107540c0c1e02c01031070a06507590000b08100e01900401580c60040d01d401c1d20305038070a40c1c019000c0c00c44503103520300455030380c8070081c03085051540c01e20000c541c00b151030000e94420719085c4603265503103030070302c1160101c60070082200080100800070b806220703a101580c007600041040c010b54844ea04070401d400303c0c80800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 760452904 1250 760451654 760451663
    0x515090d0204022d0c030a120b040203010305070602071d06240f12010f030b0118020c0106030b04060f0c02100218090c120c1827240108040c0b16 64
    0x80b0302883e0500c51104a4000c802c80110990300f00c041313460400240d40282103118089400c1403103000201030185168040c0140c8603a80001c8030520761300001d08036082a082030b10950b011400600c9082e404000c41409401da205040004c1070100e5141114000c5c02094103005080a9040d0309450a0007448103015405010005841720b2a070010710045400c07101148403c00d10541c00000d05060900a000980b45c000c030008140380e01b8003540c141c850b20b41c1452588010ba00b0020400807010038421400694415102c240e11401d15007819410b40e924080c1c409091841c00101499141e00013131074031031100c051080540c40c0d907801d0407046c40d040c08400c092034105202804121744160060001c008261151400d215640c44111000c81c00d4011402440042035024070707410198034003101190480c1040301c001888007400c04100c40e542c4201501c40309a0702d0f9504065040d2400728048550680c9020f01c0c020b6842e10701030315121001c4000c0d1003030300288000001c000c084c84200351003082000e07800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 760454154 1250 760452904 760452907
    0x18040b012001020a1803050a120c06020d1a0303120103120306170f070f0b03010308090625060509390d12020c0103061404510515090d020402 62
    0x241c0d5024043e5000080000000d1900b5070703540b01d80c90a0081100030350b0f410a004103000c001e82c2e540e07980300c814024091020b0107081218100000c00c40d0008050414503250049144044840c521041050080404d48240c1041c0003d1100301c9004802074112074011400046941d0300440c240c0c01440c442d044010350b9801304828220003400000c0b0702e10008a1802180c2c0107035900c0b01400c500780414000c01101000420041012403001c02c042d207554840103003c140f0b01403e84000b0040404046100c9011040c0148010300340b0000e481201d90180c880c001130260b103d100718480c1e0f00382c1c03c004c1810120b0042951640099003402040d8811000003400113221941c0381c0c00c10f0b14010300d11030460801031141503100a001d51280c05600221f0340441c0ba0050811007120401020f0000902c1a200d01c0803400c51032990300d902e001040c0811000040508064480c1410340c03500d140f0780702d00710780d42c06419610800907900c0b02c418405444130b28143d1340341c03102c40f07181c0001c480035940340008e17500500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 760455404 1250 760454154 760454207
    0x2031009051c03020d2424032408060f09030301051804083108391e1206130b07031407031a0102060615090d020a12020306070518040b01 60
    0x1d2003141c9510714440c004034083c6c10b40e41c0746d50300000e0000c0094480c00d01da09105070000340340207411000b115a000406003550039201302c0e90072044060303035020101c01c0c0d02800601c04550a01100d0311b42203c03040c00698a15810440030801e01e8a503100b0303001517400030030300280501002c802a100030103607145100108030002c442072041102c52480f060140d0740c203040d00142424001900d00f10150060202302218401f8500030b09805200400c04c2c110101c16000e51502d680d614944070020464001c40e04075595110000c3c05841d602484460042c2c1c0e000005102c0504034440c1c44415640d4004070700301072903581090480240c00380001d1080b4540e03040f000c0c050480d41580046030308090042c05c04181003115001283e681500f5103215402c4440c0d502509808901c80c40280381440c80a4488413200b081da0740441c0c0340c3c180c2c607400b00d020f405078440c035601103150a00ca11900009285400c42c10072101c3d4002601c0c071000b44441a01c01e41d5941c035170b0b601c143d0041c04004030040c11140c05066410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 760456654 1250 760455404 760455431
    0x11503060e0c030f09010b010c030f05070b0108030c010f02070f081c0908090405070e090c0c2b02010c02071a090a05030a0f030f02030408150c160f02031009051c03020d 74
    0x40003602c8018090302e040d800100705c09014850400381e40340507036414041815075201a115507541944403403c0000820054010410301c4501500070b111a00c000c41d1703124501c04455084404030720503003078498010000140481d100b1501010004e810203500d0341c1e900f54000a0700049001c0f20320445610382000544014000301c40040c090107030040d2030500c503d54481d41c04440e40b14801c10503591060085001c65484a4054080c1808074034101c00c50390500c1120760341c09140b05420011040c0c11a0550000051aa080c09118100c660900040080c9401c090060044043c000301403083c1d5880070401c121250341d1fa214060050901030706940c0e640d20103040048411100c080181e01140308802d0144000d4400000c440454010300301400144462035402421000c01616004111406000240c0040300520441000921926442e000b10103984149800c0c4000702d419003401d6840c080c0f120010400114101c0c00c4101010b0120712400c905036410f500a0007120400494285043c80340e19120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 760457904 1250 760456654 760456657
    0x405100801050103060b0301060c110a08150145090606030f050c100c110a030215030a0c08040f0b06010c0b1005041802030a1b05060f04210308011503060e0c 69
    0x8480c280c4c2d05002d01ca4460956440c184006e114400000d202000c0d0140820150a0404140341009001e030421580c1d40d408149030405200740360002a80400c01003202c07041c0c81d14400c60320149904008400a00c0701c001840043c0b0496001e01e01c800c0d2912001040c13035541c0d1151440c540c5c840b604110301600d90910720b50b0030348403402c03c136010300c00c90310340c082186004000e002401c8240e076290000030b1a1130750b60140c2501c0707032801680c11020400c004001640c613815080d00700f1255401035074072403800c0404403094030480b0800b1014007244c0c60912000c101d03181018040d043d04003035002d015486800040b5080c0c45c0d1102d0203400100e0340f000b44850410b1032181c1c8012030310115810300c007079003851007000e00c40c295807074000b945540318454903800a00712445007d5500c1040e902c0c00c030140d80c2c6402040940d840302c0e18140414070002003e02c24103080c0c03420140c04402c54540003001070466a4094020081802003004a04c224401c00f50341e184690092805080d0054030280c060410a0584005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 760459154 1250 760457904 760457909
    0x207031b0302030c010305060906060c0304050315070f0f0c0f1a09011a01020105010b0415050c030c1c050c0a060e0c0a120302120c100504060b1804050606180c030603030405100801 79
    0x240151141d651845d0b00c6801418051803000705083c3d51515602c0c208a04e582c8100082d0105000c240300002e0941e5003407000e0400c04000b0342d001d245920b42114008c0140c2d00d0075000c0c4c030603c08496103094041d540009100c02055101440c000d10500d90306240700004022041e14a06082c26030412000035010b402502d40c101001d004251002103401c010783c281c80090050345102d030400d00040004242c02e102c911102007c40c00d11615114640f01054295484003450843c0c541c00000d05890880f00281d00d0700c80b409940c5170490400054061264403583d5116000d0405031302d418008103000ca0600c03020200f1000102580c02c82175407a802e61003d41140c60080c0c0c0940100512086840101d02c1219095044000503040805c0c0f9000d81c1030060002600030345080c0e50302c9040b40184e1312112a803499000c8110008003186c54a4074143d40381906c0207050781c1c0600a000300344042e103243c00c9840c980185031441d5983d101d03903910000c20700c1e500030b07513021991001c0d8103a8550070705a001303406a410b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 760460404 1250 760459154 760459159
    0x120b041a0306070f02061909080d090c0f0b091318050a0b06010302040303140c031b010b031002160b061207170c040b0904112110140919030207031b0302 67
    0x266544001d4144c071180c8800b1070540140e0480f20008031340034850302c18803204040c2410300292051203902c9032403664000030045048180d41d0f810303000c2071224810b500c0c0c0080200d103030310f4203e40b418501c018409025650343c2d54010841d51420012180180e0881d035200c540342d90100c0c0e0110f0240c1021942d0300510401501e6085182000c22a99440ba0081310f080d40d40548906082040303105a160701c2c1d0703011007000703a420301007400b40c003000d80011240144080302c0e44001280340c090740303000c040c1018070444000015510400c0060b0703a21110350708030171503150401d201c1010b50744c501000c03c480c2c00c5d0100184186000d42000441e103d441d40d900026003400784421640031000c0b46050100b110902c000315a070100c102000100000c03004604005000005000c17404c025580b400c402d03012110381031214146402900010134000c2042c425085081c01040b140e03011405d1055400b13403a41415010b1085405030141c07144285802000600011a48a0101102d0200c0c0150f007080410030b9000c101e2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 760461654 1250 760460404 760460413
    0xd120c03030f1506080c0c0604032127021203120f010609030209010e07030f090c0614030118050408190306170d020c060c0f122104030e01120b041a03 66
    0x3501d10100c0c4900c0081c42a943c1c800c080c81810424180c1d0000701c003c2c52983c0ba0303401085103141202c418003440d400740340300741c032289503503080e88260038011a48070241c50251490044218078841d42035a51300c030800501941d9040112071800452640300b144900c1e042544800109403c00522560350103114011700c18a402481c0d803100c40481b84442203110295000c500080144003043c05600762320380020385803c00144820110040c1400c1d42e529400603140100710110801a40f900712070b1407407044014501321843c543c10003481d4030600404e060341502c0b6581c1c4000140c200040107080b02c1040048521086c01c0c0021403000902410f4240a07101481c0440706180e0b0740e80400081d91071541217160080d0100c83d05142c1481900d03002480c106506103d40812043e0081c01030100099400942c03a0b0a941c070b05810260848422404001e8550601500700700008a50300c60343c0c1d82070500007482c084124091096000020b005d0340c244070b80c1d0040c0b5022029020108120760300896000540070758 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 760462904 1250 760461654 760461671
    0x6040f03110117160306050904240908160f0803040503030a0612020f041532010c151a13020711010203210a0603060203090a030212031b090d120c0303 66
    0x440d2425061284040a107449002140000900c0000404c40c082c407840c0000c1c1075961a400a045520150f8080c1c0300400c00009512808100540e10440c3c0d5049001c180600c0e04d855031041940c0c1b0a840c0c0c00e102c0000000c1c0410100112105881c0d401c982100b0440d0701c0b401c107424000d40720384c070650303641d8140341ca807000001e0f004641d16030f02c0100340d800400210a651100c01404050b2a01d04034105123900d542a0200744d184a1400200c1507040700000d08403140d11402d1020080480d09411034107120100d0281000540c3d034207500c05800d40c0c1c0c03540114122903010080007071107020794562940100d04c00100c101c3c00b021a406012154090003510390486031003001661039104a501003441d0050800c4550103040c560341d5011f070004406840012640da80303841d42d80c01c071780040d5031aa03190340001c1e4446e0b003810b50420580c40c25080041110b0b01d18202a41648154800031803402051038000c940380c020360359901d4400b560641c00040300b001d0071a07110740041078842c041d0400ca011078940b04e400e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 760464154 1250 760462904 760462907
    0x30c0e06040902060d0218042c0304050a210602040b12060f06040501050f0906210c13060c030c15020306190803032e0e0a050708060a0b0d0b06040f031101 68
    0x804820030707006004136240c40e90068594000e0f41c80000e1010b020313440c0e0004100b40ba100da11411100160b034003c14540110284d84078510003225900d44100c96100b400140b02c02c1c0e94280041301141c40e44860865410b942081c90340301280354403000f030442ca1001c0b900160040c0d214000b8010720094241d050040e544540810074100030989a007900210284814840c1d5401000184052510400c900e030400903003200090050b800070350405140480710408200b1409004802038021401e00c0d0510308083c079038a110720508a2a01c118010003a0300c1c5106418507002d4100e100d403264002035852031044080300391301e010754415034009024107100d140030f420820800d164941900c1d0040c010318a10f490300c1120740c60005481405984104105c941d0000c00c0e01c050005900403c0d0056500300d0500d072001030813044800c000c20800a1180d24410020142d0f2100381040564461000a42d1200d0700d460880000f880d03400700c0c2603040340000a0206401100b41c01c0807080302e2203402e4400c08206d00313100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 760465404 1250 760464154 760464161
    0x70e010e09071701021b010e01060e040312182906041811010504182721120606030506040f0c0c060b0d060f05060103050702070b0409022101030c0e0604 67
    0x406a066420042091100304400e0298450003001c400000d82051a20340c214006e0a051b910100c00682d525004c00604020131700542000b400003e0501c2c00e0303407810f900e010b07240c078291860042c40303965550910b8000082a44440007a40e400c4002c0c17581d901440c034688078040403030750304224180c1100f40000b0058640750064802c8460758003101d010701006580e038400d0f00c140c07000c0305505001c428480030400711188a081c1e40700403030f01640818814000b4111080c1e0324000a0245040162101e080b030200c1c040306803840c01c0200d4107004e001c02480039030b812a00400c40300b280e521101e06006000644560541045000b0181203030100015003c03002c01030112100a8198004202003000120100b14154080940488090020004040e40d980e4540841d61410070410805948409014540d641072180c168400880c0c001018654100240d4491900130b620600c400301c1e80019801c1d500b4241c2071000c1c0c40d0702c0202d070b5400b10556142d240801d5444007500031260f00d491900c0006016103010301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 760466654 1250 760465404 760465411
    0x10903080c03240a1a130b040b0406200714030f01022505030d091a0f0705031b0702030d050318060f070c02120a0c0906050609090c070c08060702070e010e 68
    0x58030445000d41004a442804141161254851426100000c4015003174003e0b580e5001c1c1020080d54500d903a0483c03d40e074400c41d0300720018240c8180005c8c800441c00c9011070302650002d04128a6003020310740345036206801c58101302c20034005c542c0b00190000c090010031300c07891070890544110032070a90b50740d403c038041c184100034217001c02e9618000310908080d21200d80c0340550252440c00302d0b00c00200c001e80304001d104841c01c011a03c07200b20154003a0f0101500019251188002800d110f00014100d0202802c080b1300250b0240803503500e851480c2c2246e407210303406026200e0800c6041c00240160b00101d40c402c9071808901e41040309590041945442a544016095100d40700c1d60011a000d81c00383c0b000300d0300050005c000303c00c500020030150001030710032050704182c03d0508a0081c00d4a149078460360241c101400002281c3d1f40c0d182c0c0f80340e032000d04040d1190b2901c1d080d007040e030800a0b03103911801082c000c0e001440350003607001c00d512090703039140c4106040d143d903500101c001c02035048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 760467904 1250 760466654 760466671
    0x2010c0c0b040f1406010f15030e0c130b040504050304080c0130140a0c0f02011104030f0809092d060f0103111b030c0d081e04050a0602030702010903080c03 69
    0xd01c005030015190080d40c4182c5030140c0185a4403020703082d0000e1920300d00b83c1104a100c5100602044060800003ea05100f0303064a410300400540c00c1030560780741a0000081c1c45503010b0715902ea03440701c2c26488000440401003041c005030403e411f141c0c0e181d9100f030042c49242d0003245d280c4030441d40a03042e100c0341490890b109104903882c2540540c808004510000c50301515507011041c03002d07010303808900030740d50840001408501120080c203400070791845201503906000244424904400070703242240d4008451254040d080d2900400d00d1180402d03040c0c2c00f0030403106108480b106020101c1c4205080148040c5c100b850b948030202840040b6040c581c0413024610130320103540b03c0c0d00080a01c0000914840c188540c05140c840301420100300c0e01c5136588045040c0c000c5040812440d100d802140c10000341a0400314112880340d1401d0140c2d04100402001140030402c8c10010744004a800000440d12406c000300002d01a154800c01540000d4402e0301042800d2210030440e8050a0341 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 760469154 1250 760467904 760467923
    0xb0f010507020315041e200108010b120402120a030f0908060c0d0f0b03010c050901080109050624040803120916061b060b1306030b10060909050916090b0102010c0c 72
    0x394083c031110b51001041200c05c001b07440c40d840300140c40c01c14609003440c42040205184200c000c0403001c4080400e10a50401001c2e40041108200850881d0420450890760b52803d0ba6079001046480c1c0a208541030944150420b250030b15510900008030306038a07580e07059801c2e682d25a069600c1a041d40c0610f14004104040d004c07017601036000c042e6071406404041070940d45840000d08689111555001043c0d0010f4a15070969001503034038090110000f0400c52414400003280190050b420059071509213580c89030b07a41c05528040d0703001420200c0880341c0d0f8490850b540b5000441c2903440040b10700c54441c0f01d41e45c0041c04580f010039a03000da610300c21030640148080a1001c0d000506456040d40e80b08034140030786500e010106029562030001c2031141c550314090311044001052070340000c16282051040760b40c0701a1210884180f44000f20b44d0361203540810341801081514080b03500701d40c840009241c14650003d07680b889090b0000c00c03c004028500340c50550300b20a005100010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 760470404 1250 760469154 760469173
    0x90607110a092315030703060f0b0102060f010e0c280f021b1512040b060f01020d0e130e0604050705090c040f031205040815010905063f0a060b0f0105070203 69
    0x41600010b0784038202c3d1348900c00031010200881d00344800f503007090740c0554840c42c1c000300c40728041c042c4954008003840101380c2880c161110440224042c01245e40d070594020101e081103d01c2400e54000000c854224580c810f10341012144503210405404041b404400818181d2400480e4400c42c0103221035940032401922000c00c0010040c12480303400310380050001051580b0201d02d440c2c0308078465000913685e414448100001c1c0400328906c07604550001c4000a14917900140c030081c00c22094036810b518003a006c00c507002600303803122900118459031040105101000400404135076050b82c110b0b0091701c03070155203000c600c00ca0180c109403200020301000000d003451401044210a4946103040645034a01b041c00c042c0c030f00b11101c0400c1d60b400d005001400803485030a403c403904807100c2c2a41000070405800d001c2001c0203050080d9080a07000c07050400d400c01c40c40780c01c20b141041d1403a000071898040d0080c40044901401840e5a110080c8d403540504103d036111a001001803a0860 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 760471654 1250 760470404 760470461
    0x50910020a120506040e0307050705120109050a03030903020c09190e060105010507140312040b090d020c1026070215010f03020325030b10050f0904111005090607110a09 74
    0x3c060500d81d01700f5907800035804007a0b41800039050b1503201d81c4c05000e8140c40c0c08104140040a80d41100c110303450420a10300140000681400b419070500b008241d09125080030303030500b4842000c50350800f24200c00c100740d01c4103400700d00e00f202c00b05040c00c000c00d040103184243d4400d4240160303070114004001003404107944035002d480c0400d024044a01d4200608a0042400c50650302207510b00000800c4c080300c801c00b4010121980c1a0744001d0180302c40c00d10028950340310ba03001030806d00a1198900c2d5101280103104031071071440101203481401c01900083da52040821110520170782c4e100049503410561040004807500100140030f004070383c6915000015482801200c0651019400400510713042174641c861168142500301140c582010712040540c9101c0301440781885c40200400031304041840360040702c003a10120082c040030034081daa58440d1290550740300001144510401c01610480e0070403600a07a5030500e060b03583d400300c100380c9010000c020244000c0c00891035514 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 760472904 1250 760471654 760471661
    0x60103020108181e060106170f06060c0102092d1203040b030c040f09090c081f020d0209030316110d051c1209030f030b010513030602030705120a050910020a12 70
    0x50000c001503505040342074490413400308a10404c81815003020b00100111a0800c00c6112004012200d1440e1032601c1d20340e9a002d81801410750f442890b000c02d8020726017800f541640c501c8400a000200c0d00c000d18040381c0102c0041c43c00c0c1103c03800100405404508008040d562135810000085080605282200c1e86c1038000512968021006100001d4246500a000001081f141800044624690400c0e000189064000d400b6550041800c40341500700308210f00054640c4143c01038560590b10b518174041d100e40000c06500d4031001c1200700403024068010600390303110f04280203000e000c950601516a00d00000503200780c01c441001d44102462a801c1d0b40300800c20314048414038600120542210a01d0600750300182c00c489140e0341040d010f02c201d0030fa0b00000d0901a0503e000e80058a951501c54000200744507004404114401d0180d000e0f50395406200424880515007250800d00034001280d829245224901218618000c5407085481041040d40c03242c0c0d0703000c81101c1c680c014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 760474154 1250 760472904 760472941
    0x403060209030109170c16051f0201110409050a0f06060203071101090302060f03100915061115181c050706090201020708070f09050606120613090501020d021b060103020108 76
    0x242d5220082e00d00021540030501c115140c1034040d1940380d007150320611f8030700800c860302c401d00c1034111503091200d9039848030340c2412056503281c2c03a50054140c40040740075041c0d640ca00c40d0304600106e00400c02c100d094011074451040c80c10204030409005903003400b9203142e48030340700140e00100a80703404283c0d500c0c40700b8402c0c1c42c181080c0c10240e41e00d0b80813403100d0340080000c9400c080c01100f0300000c2e25010483c2c1004004100d42400070041c003480020041425114241c1442203203000346200043c1800105000000b03109440b0b454504603c104c070b042d0480d50b82c0d45a00d80140b48900b0b5621098040e48408034100340e541c141030280b01c2c0e541000600000d48264107500c5910000070b1000020041e95016194014030218201d140407200c1f015102d000d8000c9d4801da00030710030070030568182d4001c02d601180848482400f003015000c00d00c0200009030b030260155000158030100d40506800a1200181c80c5100c0c17140721000031000c544850f001e000081c00624000049120348000d030b40c50419 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 760475404 1250 760474154 760474159
    0x10e04020108280903031b0e040e01061205010b090906040b13080d05070f0201200d15031b060906050c12031806180d0903030504210821060a030302030403060209 71
    0x4400a14004900100000801c0f001150303480742141d50400da0326018603100c5580c1c7c072000c540d04500c0c04401130008419500303180e004a64841181008a1094115a0081645007001d00d400021400d100c2e0103010107402c0b850040c0e6200c0003107548403400003803540c0f107260002d41c01c078502c1d16003c060326080c1030402001d0710801d41c03d02c04031070240440c0c807c0b54003c0419461743c5512038100c5402a0a65141d06654505140c2c4554490442c050302402c9804900c005400000d0304e040018820b502042c8640000c0d14081c58a204c5410f2144000350354020b84005403200782c200c0c0d030b64000031a054810142144039035080841d00d100801c559101454018000c401180d0000d0380260046107000c1c01101c0e00710752210590001c08800c03d0900c40480da09009150042c03816085440c041d11621603480390960f102c9524064120401c0245812084180d01280241d2780c0d00c01c40740108851000107801501c1d00003410302003601c1e8509250101b0840354142c010354103051440d2141002034004d815200d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 760476654 1250 760475404 760475431
    0x6081608150f041d1908160311030304080301060810080a02010c0305091504030c062604050312090105090d020102090a051504030611031603060303140d0f0501080a0614010e04020108 80
    0x41d215a41c81c021282109002c0480c0c0c184186100c90f05807170100e2003082000180d550030075400100c0e0504003104d444580e00452069041d400780b504441c01800500d105031180404014842040b01742d800850495910b9a6414016100c0c0c40f45100d0304040340c0306001d130395486211144015401003a081159501034141942483e0215010410801200c03442415004001409008214010003903c0141c0074034908040c0380c262500c0000c0540780604119410340d0b4a040000d0b0412000300100c650b640c1e500d91543c101410700000040c0030300000e5400300c4a42c0078400c1c110044520510070755091060003042599814604014400e088146100a11a1640420011010600c40d0003408400d61120821540d0f03807030404400c00300342008411400402d410024108086640a070240c000074103403564060740c84202007070040040100042100d4a5402d04000085074100803581103901800364409000150301c90401c00d9015100b401069080800e0307201050242d40300d1044103500c101d20443c4034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 760477904 1250 760476654 760476679
    0x602070b0405280f030501060b25050f1209011704020105190c0501020c06060a140303040504240303030614030a1707052a130b10050c0a020d05070608160815 69
    0x410165000d13421100070402d0f002c03410000c0110034407071240200b50004415081c03006054042420001c15100314090b84001264201404400d0008048050101c402c13102413420a030b5848203030390031411410780407811100159010880c2052a1072156a0581d1500d241042106070780e1441068014500104481c04400c41c000a1b42440185480c8030b95070020440e0346032060030020754120b9500a80f1145600c0d6a13501280d86000065074140c4004580105403081518480341d80445d03204072000c05605850000414160540d10500c01e841c07c600b030f40706003800040185a81c031611054024207604d01d01d80841030401e03503140a4003000d840f40041d185007011041503240040700403404144400d5041c400350312613180c400c400d41c000c2140b040060203400c0403200010901008a03a2038001c2c800d001400000e101401e001035201503034000c00111140c900303801d0096488181c2d0040c0d202142c410008944002c0c848416007445c0c0c0400d50303514036540e8598501e014018582e2401c1904500fa2501a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 760479154 1250 760477904 760477969
    0x20a0b07120332040b060a030f08070227010504200904050907050a0605090a090e030306010c111005030910060320130606121514061b01050c070506010602070b0405 72
    0x84140d100c86030306005a83c0d007080d0400b00741559000c0c06140c45200450403c0000980714842c004003560081602500c42c03400c0c0c008159500c10300c001618442080001c80101703021642c20310350580e04256001c0280c00409400480303050f020700c00d00c2c040ba94003801445614541600000e501016020580b6242d90366140800c00102140d04003a002c00d40106441d4181d06003000e81c0c400400001c041801455003980f1815260300c00a82000c4c100020b111001084c080b1102c020001038401420010800c0740550000341140c20a403100c0c0c05074050748101c01480980c501908003601c0c3c02c03208404d0418143c1140b940d103042c100511941004116854801a1032607100780c00c01440e1f1500c41d10250b070705200c003420071201000b070304503200e064942040c00b00101d042c501d44030fa00002e0301c01c10341d250304c104001c0d501f400601e04502420360030301040040b5032400c1d4000c0c05203030f0f101e10304035081030740c840d0341c00c0c0d840d44032900821300481414441003141d85004880c00e60f14ed0400c0160441509150f5103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 760480404 1250 760479154 760479221
    0x6030204021201060f090b040b1614010e060a0204150f020c1003051509100501110c04060306060315021914221d060d060c020f0613020a0b071203 64
    0x3090008402d0340004115141c0c00003240848205245850802942090103030452402a8010310903003103000b08102d0800c4403a00c40e0f080c00260011700d000d088910214510b07020f0001103010720000d00621000c03450f51503a90094030203580b41c1070100a18490f0742c02040301d0407041c01e40104214840c0c20000c40035600c0e04201c03003800c0f400b2079402186924000c0100c01c0d10401d680c0d4130b0b5004038581020410b400c0600410001550300274600041028125500b5074030301004400500e91041c40c25a0010411455510203001c480c40758448120004a00c40d44004034003c48074540d08405c03803500c0c3c94042e54410746c4040d0030304c1004180c02c0c0c1024000c03080346a002e00341e0b17121141c10109544081c40401e40c40028100d42420681003124a440c082d000b08004e05201500142010f8813041c2101f0f40034001d2005c001e80120340400c84075113240071142081d0000002100303900481d415003010a800302c500003122040c07600550000aa044070710301c01c034014501e007040f200d41800340320b4000401c21a0700c0b9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 760481654 1250 760480404 760480417
    0x31c0302031e150f090f010510180e0f010b0a0813080c030c060105090c391902040b060a05031302060405060d0504020a0f080709090305040902070f03030b01030b0f0d060603020402 79
    0x10003541c003e44140144250b40002c1c070340c030305c0c8100010720400101141500d0503d06440b015a14500040800d0340705950501c0c11600b11b00384040000b1001c02c0f00b0344171301d6056210b051301903020038040c5d9036440c0d602c105121b8801c040e00020960000520b02c407841c00c00240442c1c0c480d040d41c0f0715001c44850300d0f41c02c641004810301455005900100f00d24038090301c02c150041ea003a281e8a241040c43c04000b4680300088488065418040c042e0920380a10010300c141e05008a005030b4074070038003401003000024141c5a0481c422440c0103091240740c200b4500f65441d0500720703110309e07280d9160080c0b01c030180c41221138100d0340407804002c04141600c44074060080c0c003001540c041490300b464810403860401c1600100600c003412070040050200001d400402c85020307031000a40c00d001800c0032140c074403554010040c600d00008269007000150301216900300e010755010850412501e0044040c0c0f9840c00126620040410b0842c0c8a8030701f107581e880c8014440d1400062042e506d03404030781681c002c5d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 760482904 1250 760481654 760481671
    0x2060409090c050909030702012307050f0f0a0b06060903010b0406081b0d030519020a0c030f05010f0c020c040216050a21020f0a0308060d0f060507020c031c0302031e 73
    0x14039221041007840d04601c0c01408040b03404c10068030b08220450360382e0040f0702c03000c1c1c1040354010281028001140c0303d12070780035007a02076a6450001c3c5c00c1040c1d46840e15032102400d840b03200c21020845001041c09494a64481c1000c0719030b031207180070011560401490382d0360655807940480400e0340e80d440707840d00400021000d01040e45154232008108210785158074011002180c1c0440004c0c0c0c00780c100c85648aa041c0d5405c20007200036012850101d00c1c3c80000c00c29192840c001c800c0c84140c150500074244508028072401080c1d442000c01d031031600c005400540d2248450300c081b80307420b4000d402d160004802d60141820f16403035503440e01c040d07031506450303090050325013083c840001001450084814001004c80c0e08030700d6802c035625845610003a0811401402081e00c40d90303480c1038907401075001015036070601054188940100b9081d035500740503104041c0407004604001c00c000250002d00460741271000b0055000b54044d51004200c8030b00d10000d0000d80000c840e8440b406030144064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 760484154 1250 760482904 760482911
    0xc120c01030c05070b06060a0c1502120a14010b0c0a06020d0606140a05040302013f0b030a08090918030d060312030b0d0f082b14100b03100302060409 66
    0x140000903044441000b040c1d000c1000400a000101c2e41c1d070300c201c030707042001503070a16516059000100c951514141c0c00805c254088800d103001c10620b60040e01e1800c5446020b030b20b4544038040c14804403698480002da0352115240100805581e0801403c4040b40344401d4550244681c2d9801049031710801490400a5540c242400240e40c0440007020800c602c1e40414a1309414050250842c00395201c002d0422228980202242c041400040380c001c4d45403804c02c0a00d0844040402c0302018050070b070040c41d280041c90209864005404140079810182d440e10704076041091080720312000340500c500c040208456048100304000402c2403560305800040e01301c0c20351901c01351981c0d40402c8802007504184a20403a039440e9035414480640c031448506140d0034518100120b4001c0c0c25026241c003a084158040c0320007056440c054200c2c581c0c0c0b00b04039039050000c02500b80d01040d50b03540301446401e407003441280000d00c001d541141c07402e01002e1301d00795a507002a010750300641000600e41e48 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 760485404 1250 760484154 760484173
    0xc09030f0b04150e0f0601080d090b0c01060b0a02011d0613030804050a0209010b0c1b060406030b010c0503041404060f24141902010e01050426120901150605030709170c12 75
    0x2e121b0580500410b0000e40f142c8000a20000c06010703650041592398440025420030000c802d5000750000c14400c110b00d80c880781c490303034081d0003020701004003015081c00981440340d400001c00c00c180306080042c80e081e261015070302c0c103d0b140c0200500884582c410b14154401590b0355003400f600900b086800c40740e68461010307600c7e040c03070158680348504282c0e13540c070501585d8401d0140e0b81601c49a140009a149031840125561207000c0d9001d03095010000300400c02d407104402c4150301c404281d40a03c0510ba6032003e41c0d02c070311a188078001a0b00080800604c40d2110700340241d190782094605007a0540309002038050940c8401c210514091a00302c03281101ca4080c0075003400701c5982d60003040380e442e264481500d10302004070b55261612802e543c12003410501c00680b0150080305014014514003015003a008210031342c03500c2c0012000041c0020b10a10440c112442002c0342c0c1e9a64a005140c0103aa01d10221810f500300280c0c01035a5401c115911089201d100300c880b1200100481d04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 760486654 1250 760485404 760485433
    0x40e0103051513020f060d11031005030f070504150905070e0906030a0213021c0906020a03060506070c03110609060d060f06260919050708010c09030f0b04150e 70
    0x20241c8041c441410300340b010884001040e4150700700ba1a01070b148020174000c060300103851403207220811602e040ca0007001002c1c2101c440040c521131110104100101030720351301015a240e82d40c0c04800e980742d018403014801d908207604002d01c41c606040c6086000c0341c03511144010380c0c404035907950000781403c00e07040c80c9190400c1c0d01500501c0550192104041c10340100b0617040441d40c480004980010701004000d03008001084601500b0b54208400c550741c1c03a040d0040c1d480495a280080e0400b40d0205d59440d0203c22205080d90090191500f10b20710354421010780b099442043e40a0300c00d00c0b25242d40e80f181c1000f0415503001e0540018424140400c02c507503c9801c0d0002c1c0200071070004165000d04540d4181a403003540c084032240c0e030750313070340300e815883d1044541c94088160440c10083d01000b1002402c901641c4004009010360205d0402c05c6a0903038045c80040c00740c070004080003012803030300306040d50071a000b041a90040b0f01298103003c02d8034071200c10090030360300c01c400951000307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 760487904 1250 760486654 760486663
    0x2073014070602030322031707091a0c1c0c060b040603200a0812071e0c0602031201050f130e010b0913030e03031833040e0a1e09020a0506040e010305 66
    0x40c1c1c46da6415544072442d01c004100c04803038902041c1e485122008960703014002d61101008007845016800c00102024800440d0b42003001804964803402d0741032600c500742c007408100b40c41c05955a940036004603864031800b0f02080c40c911900075603070b040080081550f4004264a105120b0044205075440303c0510609200c258000342403500841d04001510443c2801c403800181c01490b28015070b107968007243d03005000820300811a03001030b140001e2441d00070018164009a16003e07104581c0d0f20740030b111480e0580d032256513101d01c1001d824030b94001c7c664420025000203e0001618407042e4011441c41031058030440400c4a10f080c03c3e20030140e004001108001e0103402640c182604009489980b0030000d0545120718201445d070f51106940c5007139280350341c0014244441000e00844582020303880381c011880c42d0b4007204009110801c8038051070486403501d802141d04821042e005000074001110102d91101c21140005650f544440190000e0035010f252680f25514510304540350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 760489154 1250 760487904 760487941
    0x51908011d06100309050705060a1e0309030f0f021009140f28170d09060c0503040203070306150515091903080909180609060601020730140706020303 66
    0x41140c00080181586a074400c1d081c0b0503c40d82004140e2282d03d151541c202001c5401c000d42024010034180c00b07d0b0340c080300e4440d551610080c20f176082402903000700e0542d11140e9000e0049020329803192503082c42040703516600007040c070664141c03040c584103240a0b03880014050b1404109010702d000300c0742c13050207810501daa00c00014480184400c0b22100c280c41c0c40c401c024854040f084040c000c0c020b0400c020012a030100358199540c0c000e41c1e550000901c0924820f03101c80f0b15010822505602980840340165002002042070b1840e641e00c44000e40115034a002d043d07552041e0004031600c03248048005111102c04080d00c414588040c00540100d5108141001800b11400c0010540d030204036056510143c80c50348003580c4000202c10925050301000e40e07540b003041c04200c0780c1003000c02c13030500412099003581c1099595000c1c045035a109003400d80b02c1d521848041c4903440061441002e503051080b0003500c580f0001c581c8e26814069198007200140c3c100208100c2c000000c1d4401044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 760490404 1250 760489154 760489199
    0x70201020424020309030703210c0503030a1d030403060e0118030512060a0f0e0601030e0c010e041d0d23041203030c0311042c010303020c1005190801 66
    0x50500d00780030b112400d6000450220300003042c005502c450b40c400e204890b1a07000c040c0c00c54007030607a00d14041400080d10360904004500320400710102512481d40c04c10125040340003541181c4803004107000824490800c0381c0700f44c48240700d80100c8041030000d00b0081d406840c0009040b1451801c5d1401c3d5821031403101d070092045a2403c000035007120540b54078940c03000440f1034a030354107c0482d007558955000321039a00e02140001880640d0009014846e00e400e036400d10450031521010303075480f040c0105050100320407844202d01d44c2010344c02800700028142601d149030050081c082c0c10040e24001000c0002c9042d890101e29901b01d219983c01d50301401121803505140c0710080c01940c01c1044010105a160f82c60342c480346120b60800e0010f4580304140598032a034401642d0180141c1d0b120580c40f0880070140c4440750420017803c1c904883c0c26070041e0035800518000c0108001c01800044140300051090092652441c501582564102d45845180354148440010703013003048414103c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 760491654 1250 760490404 760490407
    0x201080a090f15200403060e07050f120a060e0a020907020d080403081f080303060f010801050f04110c0607261603050702010b220510030c0b030a090b0405070e07020102 74
    0x4001600c902d000b080440e0071010a401184803040034402a004010000380003030300503414166100d0040000b071044a00c14801044094041c240032a254101d52103401e5100e10003140008203410908a111a10344083c01030300c2d6600aa507845030b0032600c507904d03111003680c071803800501181883d01c0e86e5a040b14960009003004070740b000c0c000741301e020014401001c000701d0340b002ca042c8101c80c8010b5204504020010300c080c689880e0807540c0d0f078104603004e0b0b100703103606015929154003134268075062b500c000e000300400300c040308103120151401c2010492040c00070802c04010b820148a6a4041e03543d9035101d0b500005278a4880101e1a41c01c003142c04640c81039410701086240010311900c9075005800c006c82c0360340d500d5005900420101089980110b408032220104010050104ca04011441c0307080040d03131504420440106144d0000500601000001303122190061007d1076220b01545404a401c11090b0345850810302c041d28210307010346c010380c42480a01c180417640c6034403809910003103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 760492904 1250 760491654 760491671
    0x10b22091a0d20010e0918010f0207021e0604050919050601030209030a0b19020d0203090f011103070c020a090e01051618060c0501090501052d010f06050d09050105130201080a 77
    0x43c00703060103042940c0781c4016a10340300d42c0143d004800c48840c0d444002c0640800d072502024100700300420032480e0215529283c160361404019201b9030780f916802074061b0003040076043c1a498401c2c41c0780882035020f034041c000000c0079a16203039050700c030b121507101003c0007880d24010700003a82c4006d0700b030341d042c14010300c00c035070f5103442c00107420240076041084a0029150070020800c02c1c42440c40a00c1c40500000b10650040d10f203400440c041c0105000700c50007108034107000ba08a4001c80d0491121000030000314079924882e44411a200d030004121810741c07551101d608048070030703240c4e41d0b1019946400070007442c0300c210000d181c25481c040c10a500110611021180b40894a0040f28284a4844488018440c0951100e080c0350f510800800c110b08104141c6041422182c415807200c44003580d04607603410185803203a04890710310000c5000541006c4003074a1035005041080041640c0d80fa1000200c0c9090145a009410081403140d03110303058000107100090080c860070106c1c0c20980301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 760494154 1250 760492904 760492913
    0x20909070e101502070e0a020306040b03060c0403050f0705010c08130b0d3801120902060a08191b05030a15150306140f040203040201120603050d030e0c09010b22091a0d 74
    0x12a1f4842c0741000c0040c1e0303959800c40028020a0a07002107600351055900300001c1d118610001c10580f4010030032a1a040382c0c002c0750964600310b9004003400582c59001d590001840380002d00020408880d10141c020740719028440241c0102045100c4580c5406100b18100c0d0000406a9a00d8215409078031200c14600c0c4140d420210b4964141000f201c1410b00c1c220060940c444d0040544c02001c030b541e140d54040c8001d1204600791401141a0002c2680014800e80351040c00440c0294400000314651115070a860940008003942c0c50541c840141300340c0b0518040c48132001e01645150112444031440d0300404950b02c40e000011482c3c034901c4280700c241d40c0c0480c40302250350108d81c0543d403540c40d2b20040759002d9482d8600c0052074282080401003020216202d03601c0305442d03804010f031102c0126069030f5495007203102c0341c0144900c801440500303041e1000380350340c110011151b1619200846410302e0448283d0200200319655541c02400c0440c0c10002290380404882014a9a40d0360720f5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 760495404 1250 760494154 760494179
    0xd1b0c0303080a15090b090105090915040c120c06090b07080d05341e0e010f051b03030a0e030c1b03100c03020721020a020909070e10150207 62
    0x8090284110b8000194160003c0c1c4c2042201010100d10014416920342501000d07290183c10144101c440d41d002040d60b0510030a1144074411180040c400c03c409020360704140c0002410a8494420a00010800d040c030010111041885a010795a4591404030002c0100e905604100d6803001e04004010201d010300c0309942c820003136994000344e6a12004419046c3e46850007045070b040c06000ba00f0500741d140095941e0a080440e12080d1448040342c2001e110150020508030108250300c0100210754891041840c03041020f050051500d448001c4c030762482c035030040458440303038000000c01c4050305241c080d070550f130701c0410015800c04110816407501ea04062440d1189000080444a403030303030341000300044d11070b150801003000c00d60341e10008001c0e40c000101907420020301d035040c26002c4a07400410810b604030707070301a0040c0302e11030342003210486002d04007148a100349000030a58a64154015000b80140800d448085140240c00801d01d2544003200c0259041504108100c142004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 760496654 1250 760495404 760495409
    0x5091518100f050c0c030a050a030201050606120c091908011e02040b030c071506090203010e10050303031b0d111306021501050d1416050a0b0403120825020d1b0c 71
    0x500300d858110900303600e46402e292074805c9625109582c9000144000800e80c198880c0c0683d00920903580c0d40c500b40100c40c807a8150301c00c0e44104400008440b103003110054142808002c0c0640c80042d10406002440b074110742100440d43d41d944501904c9500521003400b600000d82e40c00c3d818075251840c801c81c41d000040881c0c1d0f18076000600001001b54038140c842d41d03200360700400c1003600d0b00c880c1e5040003500240604050303801c1050210744001c21051015041758001001140b070b42e515084c05d42081160344155624404050042c075082d56260f00402082c80319003180345407506030b0118030503540c6d80158845415900512200c5201c000c2907801d0f5419a034050780c021805c84014584046c01c0c450b50304504800b80034000300f481c99603c40544000c120743c411110400c45ca5120b452001e140d200341d12008142c0c1c22610b1440320200d00030081c86603c030140c0400e414550421842402e50440c50403440b50040c4c0103600542c56264000031092414482050450031300e40403660b5601d080f08030350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 760497904 1250 760496654 760496657
    0x22020d03030e03040308030a020301260d0509040b09042012070618150e032e1a22180201020d08150a03060608060c030f0a0c05091518100f 61
    0x1d400000b6402800c0046500079588101e101e5500c0c43c3c200640002500280580c00c2c101d850440c50043d0010481d10745804800074402802032a403000e1070a690552000f001e241d00305e0f4032a561443c2c0c0c0e545000724507104a0040120b1040281d2131403854102017101c0c110355100d0b5250040d071300c801c007600044a0094511504002035040c283c0d120a841542c241e52000004238030240c560900c86034084075801c031500080e01120289001c03030b0030f4403007400b41c10450100b00e40e02020004c0d55100b51a0400702a500000007250310300e15005000c505031007a0400c501d000910000c41c0007004002500c114041c00c503121181013860011a40000d480e01070034045c141c10070080401080c2000d40301500b6541c130070001000440055501d00e01180a0070f001e100301c4115000310303400280d90500b074404991103078011554905042e541c00520100424901301c94604108061007000d0440d01d0701c904000d04003c1841c0320603241c1c03010310410003800d140a01d000b406400144030800d446508080380b41d5802001d07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 760499154 1250 760497904 760497911
    0x80102180415090e0a0b04060b10032904140c0a091d040605060f100f02010f050906071101060503060c0405090a0b0f0f030a0503131805071b050a020a0801020322020d0303 75
    0x2d03614554035117560603d0250548403a002131008210455105140c1c0c420261f0301100440d030407000a0f030803601110255075600700c1080000c951180c04044400a96000810002d00b0b004240d40d0224480c50031901c0c0c0c680762100040ea0880c030340d00b1211200080140074a070b0000c0e012100124407041d00701400051a054903030000c00c015031365211080c0e43c21200680380600001280000510500a04030f01e48007652800b0404281e5000c0d03400342c240704d14140347c002c000700c1e12a190115511098001c03081c0381550398650129143d80e09001b0140a07840c000c103101e443d582440e041090010015003c41055440c01c218101641c0340c1c1c0700700d00d8006100b128012415607200c00801c0c2800074580004006020005002a42c154484210000d80340340761004049130f54000000000ca0380c05031040d4011503a60700b902010041820164041e80e1702c12010785525115a81c081142120107800c5840142d40200800c2602006a00752030750001c035402d5104030103890381d00441c40007004a0400f0702010344 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 760500404 1250 760499154 760499171
    0xa0506030402130c020106090f0501050a06200f0703060e011b0302090d0605090f060f1012061803031a03070f030b0a061502010c0801050d0302060703050a1508010218041509 76
    0xf0703503001100b007618080109110031080410024002c144500075581040d24000c883c5442d08041e215090580700d01400c2c1c4407055060590035142c1c000c031042c0100c144c039400d0304112403080c000d000c0c20241001440c01401d07a01d0039440e0000541d50080007841c0386a15090040c003076000144100c41c503592507410016078401070300011130000710001d0b1001d44002e045c0414088900c00026491407404000c9060700c03181c1d101e040c40f15117004401d4030100c000301122a03060040400d0f4444100445110f000c0c00106403003c200c5192613409102029808640d6031900c00b103a060703000c502c9150584089014011050805298121500c000c0c040903002210303250001d003c1082030360085001c1c0081784d18520b207400031840024081d20443c980d80c000a444000001201d0130880c51040d01ca83d4941c01600c1569145a421402084000c6c5080412901c1d03c0e07803011a2040c0d20900c0014180300b00001d45c0e81e0180102240d0503904140322140a1072800d981c0819a0040c1c03803407103095508441010800a6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 760501654 1250 760500404 760500409
    0x140c0616140a0815090c180402071e1209050307090f060323010b010516060c020c1c031b05030a0c030c06051801241502030f040b0306120a020a0506030402 68
    0x2049030503803a034003001c001000342406821200040c4121303414180c03070403c40022400c0c440a04000e9074140400b0b0030034400024141140e851140c2c0c198005000142030103455240c00c2080da0410f0507013a140450800e004c0c042c40380c04010034003003040d00e09088420070b02d81000f0a584114500c03652003820f59038100e08031021800c1c1c01c214019030704400612140e0f4101030001111102c2c240c10041c1030b40c64032414035001e502810940b031500e019003130703100501109919040f01810212807000e0441c040c1007801c0d0b0f4907030b417200501c0c034038001000807140396408a0314001e00024898031107074900000031500500050000401c43d81042e0316032416800700030f25490301f40c1d00c1c00030380400104901d007004200a100d0041400c9052440d0030b000c002e1200f400e0074614a00c44500d00703080800c20001001e0180312600040359030714840c022510403203192062000186000c3c0d0400c2d009442d540a001061042500c2c14444601c00b145084000d170015031400e5000500840700b0b4441c8a001d140040001420356 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 760502904 1250 760501654 760501667
    0x51005010507170f04050315010b030402010305060301021b030c0f0a081b190f0b0705070c1a070f050c12030307020601061206150801060f051806070609021e01140c0616 74
    0x207449400d55403a103842054004c0c2c160080d0154600a2280c1e410100c061b01403041c0f064100c8404800c46851520b503600110090040204003e03050764007008018260080d59000b4501600c00704051909d4042c880c1c1c040c0c0c1000d0410020303849076407280103510082803444080303135140360301d405280c2605070080e00a5810680384050044009250070031110605c038520340c003001c80e64417400c5000c04656901005440c940201c0380b010303241200410003840000b500014001c0003a060184e0341d0f090031110798403648061141c8004640942210100d044182425102411800d10050286d4154500610003c0d5070304014400c4408202c060764080c952488240d0019014044042001c01d403030b0141c00c000f8096034400c2c0724140014180e1050180100d1040040e1803400c6e852401d05940c1c00f140004022030f40d00104d0040c1d407032550720340740900140c2d43c00f402d2266401800401c0c6103501a1800003400010015100c1c59428008200c0060032031000b1403440d83c0000c1050f40300e17030032000c0810122402d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 760504154 1250 760502904 760502933
    0xf0c09060109170a0203390f0a0902070605100302010507081e0c011506050307020c042705070303230301090509101e1b080c0f0c060a0519051005010507 67
    0x51041c582900c007054030f40031548081c81c900a13000c41d0000d1685111100c068900c13044070001e031000c1c6491031030300c0020448004000c3c500081c25901503045000000702d8050256202e2011154000351043c200310301d6029103a400201540c2c100307591882c41d000a003891052080003041e2020000321100280e0092054034144909000550b4480000543c11402800c040b198200c01404440000555a200d00112071088201e030b405452214096411300000c1e082040002040034200f070072082c3d0700001e04140750340180c050030050000714510f05015100d00c418801c0b6141403104141e00720502403105080b01e044034002400040c1c680d0701c411116040c040005d495000c080d0600c4190f1880d5044c4081600c1000319410081110b5000d94100f824121a0b0300b03c100081130340800002d017807110740d40203000c01c130b424a8030680c51310456184030b1307003060b0085496a40c2d02d0354070070074406240310128450040000203201002103003003180b0480500ea8186c400c1904018000855808008207071108601 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 760505404 1250 760504154 760504169
    0x4050f010603080306010e030609031c020408030d0c08010e33041407020c0a03022b06060303021005010902091e04020f07050c1c1101030c1407110a080f0c09060109 72
    0x1180d500c03840d00510f02e6100b9142540000e2143c1070700c0c0c2e06440c0100700c0714000d4144074015803a100d20100c0211140118500340091290b00707000005101704184010645028100070005040c94914805000b404068212404031a010010480042c002503d01c0840d5110042c1103040c7d60b40c01107081ca031714541050401c3d00a800c0c540700c04070060040785014000d80244d02170740c1203044440144500780040384000b03540410103141d000c8143e100d003000c076541d4114070700f03103602a4002501c80c0307400c0c4d484682c000c80c01684480310000d82d1061520640307001d03140940c4154980b2088100040b4000d450120307d0f10ba0240741c684041d907507079440d0b04641451081d00300c1da036204d1525090141d118541d00e500f0350300034603c0822086c062204940c2e43c1041c0d50780440780e450140c12803030044001300180240c83c02800a41045024401c3c3d0940c007a01c042481104850620035000c018009480080e81c0710212980c89204030300075920001c1a0000032140c103940c040f002e0f503242001242c1c0300c0d401c0d921004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 760506654 1250 760505404 760505411
    0x81207081303121107120b0402100201110301060503041a01050f0415051801051206060117040c031515080706020304091a06070804140105040609060c0609061811060301030b0f04050f01 81
    0x844a80c000001601e09000903040d2007090340e45a800075414030112800070081103100c800240189058034510f2103440d012f100004980840300c0305c1c00d12580c0280c010601017030f0f0100410040080c040082840c00005601ca0380c12540341901050403031030002004d603c61515085022000311000307400780c0c000c10f0000c02c0120100d0304c03161101747c040401e0240310700640361940d203514110300000e40b903400382c40103a40e82000410b8541d0072099521000d08210382d03004042e00c001001c610311403008243d900450800050040500c140142b02903101c3d480000543c019a0013008000e4012081da400c643c821040442c0340503182406010b01b04120040756804180030502e10103010035807001d001600e0b0000c1c018418039a24500640f614000c47c0715505c00102c04c00000d00c05140b04110302c0034054800c8101241310203003965841d040c0e41184401c03548a40d5041c01000c284003000da04074402c060196207241c6103504503150326804040c000d00c0e00c00160184008203013084803c0021240c2c07002c43c10b0081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 760507904 1250 760506654 760506683
    0x412050c09070315050f062a060414060f04022112071101091e0303112406010f0804211701060e0405091b090c071406040606081207081303 61
    0xa801440403000c4402c00fa90500300c08103140c100411b2a0214a00c020162420482041c030740f41c0003070b2195101403202401c4100e4041c07a0319001c01051f030080d4410000c0440c0c40d0640c0c48801d00c0d00b100202030445400c101e805003c00b680320702e02c15400c042c0045400300d0302c00301d11503a05440d21100c14201e550341c0320001039072420311034141e000f582c180c80241e07542000c10b503032500c2201c495a200b1461380e030752480c2288200700003800b50846040030035039502500c000100805c0160a204405842000d22090400400050b50782c0b0110481f42c2e511541480310050034540c0b00d4500b00c07140c5001c00d40074882c81d0301074442061300415504c1c3e19202d1101011580307603181e15004001100d00c0848501513400d00d00814811030004c10030544009100d40060b00d02d0900314204014104080c160312124101005104041560520054100801d07030f001881c2c181080d01c0c00310b04603400d03684180c1d03068001a8001804040c200211103101d908250820386641d41c1c00f824044260443d88000c0802c41c0c00300c02c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 760509154 1250 760507904 760507907
    0x14030304020f100c0f0b0a05010e04051f0f0f060906060c0b16020f0f0706090f0302030604020d110301090f2a0e0403050d0c030c0306090516051e211b0412050c0907 72
    0x44507c228410b500a206c240d99500c00f080c0789030403d9074003c07d81d401010300300a510300904d0b070040128110706808115030a21039000d03012038100c030140758945034803014180080c80540c0a83e034010300d0076251002400040d9140e0701032050000c0c0c40b0f440c203121a0003a076802d15108100e40191500704500f507440e007107099103890303503150307410f1180101050850381b001401001003802c0b00b08594014010301000c2e69583e00308a0a12a113540c00c580f00300d001000d5140a4409105000c1c0281c4505180402e6241c2030420004d00201501201e03141c81043c04008000021040d4000031111004004616525140b40c182e030325000310031104411900d05840b01e801140c0c950402150a4699101040038545802104056920895404c081100c40100e40480342c0e10800050900c5548285004080c03a080002001d00341d1104802c0c842d175a085294401c218100f07810000e8100c2086d0843c5202c500589841440342e00591080070319807940120343c1e0302406414480089140070050040c610ba1030003000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 760510404 1250 760509154 760509173
    0xc110609180405070b070f03030b03160801091b05181806040c1d101202040b090c0306130605030703120201090f150c030b1507021f050714030304020f100c0f 69
    0x1016150f6200301c0c90300241801c0340b8800ca860369500104115442141901c3c294040c1c080c00503c40e8040c841d40040c10942c01411039554040c0152200120b1710091a04224110303002c2c00642c20300704175070000704020540c1c480014003105544d80076031250715960403c0f02c000011000074030304218000c4908010410000c40c603104107585035079103403d0400800c0700704a000c039142180c034040805000c00051200e4181000c030304400074030092010a00d419040003248a02c0070a65103044000004003e104c01894010404148400c0981003080001c2c0303041c0019076250350520001c1e025185100011030388034400c3d0408612180c11548041c0041101c0c43d004590000b8022111182072030030a842d60601c1c4240180d20f2241c05c0100703100311a10100503201e20940c0640d030201e03031015002802d40c501d48452000b5880d01c401c6901d5090300d800060130a4a06245014840092a001002000010f030794076424110b00c04025903540b480b10b4802101030716440d28050014111000400d41c03001040070945 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 760511654 1250 760510404 760510411
    0x1803030527060105090c07020f1507050a1103011d03090f011b050a0b160819150806010602011a090a0506060f0c011b0201110304080f0d0509030d05160c11060918 71
    0x50300c1c5130481d5144012024203011f072480096101c9801030031002c00d032a12903290454500308160f828030340016542c6041c83c01451490854040032038250140580c6028030440c1c03491364149444008203903030000c1450300d901c22014030900c2a0380002d40b881c00c3d039214104400b52088403090070400e0b000107051060380c0c0c420400c4103c070320041000c0001c4522494803944004c607981070f16007802c252601714002c4c41802c040b10040e1800c0741d6540c0e5a000001c8a03910840040c03203080054187e079410007100a088d2040750486111080c0c0740701000e80070741c0b100c210a50380b108180d8000100d0b0341b50030300058008d2082c1110701a05c0d4034003154405440c00194064a1f070f14101c20545180ca0b0032241c0c060b42a0358413049034030b4941c40d061000030045461003009080f450030340c40300b052070030b400c2062800480d102500e58500991022a4104504040d032003025040541c0c0d03007503402c041340410f074014022420050003d0440104007940403203178031000140c411201e07004214402c00e172aa10b00c019807080088 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 760512904 1250 760511654 760511659
    0x10c080d0f02040b0913021306112b180605030c0c012a0e03010b0312071a01170d02012c0f031204050706030b0f0d02010e030d050d060501031803030527060105 70
    0x8a00c4c00003810081c0b08a0b1036555802c234034026030034580703202958510800e081d140101d00401c5a002c442c001804958440d00544455030b50191500c0a00104588020301c801a01d400c84e00d0803c2c0300141c0c010060f00d50003039502d0700b21982c0f8281c50224501620b0307051310104201d40090b21010180c1080c400700c1e101e103017041c2c0c0c5d90b0b0241003c00d01014280d0701700e06400c1d83c2640148550389e9102d06001c0040c035803540280c040281280148610450b01c603001d9210940200000b00c180131001c40c02d000718010042039100078403204091100c00054050113881c0341042c50404810207509403000c1c020301595200349000d0725151603088004d036010510441e0700310313464040c0c420040340d024000c2c458004005009000b80140b2281e8006001c10014007a009a0600c0038112a80304140c0e8100480d104003482c9645154980d403007054071109888140d040349050604041c000b901070200181c110300b4040d010b10b008607041d1561034441c9200d2512050001448950100c00f030303c00140010028100c8005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 760514154 1250 760512904 760512919
    0x60b040b0a120f0f080a05031501020a0b2a12010302030c120304060c020d0b150a0906030b06210a030e090a110306091b3105010c080d0f02040b09 64
    0x12508014880780540034420001c4004107440000c0b80d030303411003030540611030314074030594507400e8843c09100c1e0450f0900c2c0d40020000010001d07220645e000d101004c0c0300078001000202016a50410300c040c00070301000c0e0910700011003482054030840c82511440711100d046031b9079002c0016400b90151b09010690091103450840015402d1041c0410001403414000d0350a103130030b006045486c8110102c0070703a4070036020f486140215010ba901c5034041d60724100111310841600c018032041740241d500030711900c2e2511004001017001c00d421030794444811503202c802c145504128143c005018000742c2c0035441454001420960450210003000c01c00f242d40681c0c03560b40184c1c2c807003030b03c0407034406944d04801403010400b103003000d076a202d401c50440c0b0b018080940300400008115006000c0740c800c88094031080d08000310454002031842e0360528507100303540b0700303140006c1c101c0944620001c0c4a062300107444040b1008581c0b1200780d20210203400e650340c560318030b5045440d4110f488120f204200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 760515404 1250 760514154 760514171
    0x3100f0b0a0306060f1a031902090a060216171e03070b010e0a050a1503060905011b030605040e1b0105070501090c060f08060420180a1217070515150d060b04 69
    0x62070183c0081c8120b60000661441e03071a901d40b0304000da202d81d480d25001c0c9d02400b07501d09a58510308900c010b4001c90f401800400d0340380d821402038040e243e20019103000035070741084203400049002c0060308103814001d081c010402c0d00c814910b20400c17001800c40001c000000c541101e58880342c60144032845010320154440400410480d0900510755090308112401040010310390307041074007007078050000094001c0207418004100280042640b0000755280c00c2488140b88c10310035412103010b5140102000d002c0003002849652421456178144580032800c8401c10800350002c6807455800030441c11502c2c4c2e106000782501e490242d2410105a94600140701410035104101340d44c2185180310314010110103210010b5400800590301d0200b0103880348400b80c91f50201b80d00106041d00d060b07010080c00e400c0074020301181c1c0341c6000c0710b00b00410110f0003164000a0314202d0b21030252001000f6200c0c110402000b03119501480e070041040c4070444144400b60780004014071080d64240a00381c0e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 760516654 1250 760515404 760515419
    0x10801141501081611070b04060908060c0d15030c0b031e040b0f10230a06020a08040b1b010f24050d060b01140d06060909020903100f0b0a0306060f 65
    0x201c020340c040d400070341c690300010313075404204c0c65000e0400002c0c246021311090707081c5082c0c02d088250b0840b0005900003d420000258440c02e23100c010640d0101138003807804d0000c01880c0501c46c80c5000d0120585840000c5500c2004e6900170004550000d403044020b9501d02402400d0303001222543c100150b9040a01c000d101500d80c001d1041d588100c100340160b1f600068a1858803010301110708480c010341001c01d2080c0360362240d03101c240748950b11548581184041104481c095042070701117401c0f00c01c13001c0c0002c050a05070350a5800c0c104003587c89140e4100d09240d81c146c1c02c0e01c0802958203060301c0f444c1144940d40010102825066404805001d6410702e903c00282d503c94240c028290703018000101c0c80e543d00030382220360305250010721064128030b10700c103d40200080790301c200d0b0766110412900c0d4102100c0fa00400d8141c3d420340c14001010b001a0711206040200300495480760123040d6441d0305c80c0d118011760400203200150b0961681046002803e11707014100015409030f2021031000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 760517904 1250 760516654 760516681
    0x2060709051f0c080405120715020c0108180c091e01050418022103040605040e1f030219030212030904061205071e050d08031f15051b0601080114 64
    0x181122080c2c2c02404102031070480d151428004213481c20310081c4030100d03041d90b0b20219178aa0345081b01c01401001d0500f44580c2d9440043c031101d00556005515a00c8566000b0024550040100c21540e0051103c0c200840c04c0c07080c80c1d031405500011580c02c10800800041403000a45040c5030000c000ba80c8074802c1c0412182004841d083d84401441d10600500d411b21f0400740d6048aa04a80c0b18034018000451564009800480200b100881e040c01030002c0d6507440ca601c208660382e0040404601141c150300b8020b1404080c0c00b40040900d00b925542d03410f02424001c503070107040e90781c00242201c50b031a201e4100d00035262242d4105280054200a0083d0115105412802800500345003551050310703403080124007006c50b540c00000044581d112498034001c18029103c8950b01c2c03414210300c60412061420200e10004006020f000340c24000840104a5080713081c032503681c42281c42040c155002403685004988940750002c20300f01c6040d00041c4503006452541c0c50030343c0703031945d00c0680b6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 760519154 1250 760517904 760517929
    0xe101a0f030c1c021201240e0103032601061806020c0603060f0d06050a0f110a020d05030c0408010207050a06050c1c050613020a1110060609050d03020708030a0206070905 75
    0x10390100c041c0c04070602e000a2421003c0e0368840280d00a06400c2c3e0204144003051807000c50541d5503152841040300503082d01d022191242c0540614203400d00c01c4e41d05000606003c09020410814540c2d001010101010a03015648031240369082d1381d40d0320020280c050080696005020340310000030b0183c00091100800d00c002000d0609560710102403010701d00d4038401c3c00740d0224003c0c0c1e00b20040b800c9442180d000e991008d8001c184042881007101c1038a0364001d00c501c4d03101d01000b5203420650301190310f41c0c00080030710b05550781b031300c8400e181c907842d00898012501c294800503504081200000308142e55034450f0406012603910030640340f00d180101d50004481e101c0012800090800f01d600566200c030004100841c0d0071748035078201c0101d800191101010450030304204070b07080c9003081a22101c070302d103001c240440c600f0410020010038141c0b00301c601502640003600d04041c024840280903098090441e512082081c0c002583c0b524161905404200f1404020a01d42001e4066121 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 760520404 1250 760519154 760519159
    0x60702120c250522051b0316091a0304060c020a080d020705070e010e060a082a030a02090f070f140a1d1201020409110406020618010e101a0f 62
    0x80e45002d80c00604204400809044005144503a002c6200e640e003c00300350354450701c400d5807600304c2c020702a0003040350400791001540b1444440c0806a007220802100d9001c43c9440d818441072070320010668211105421460001c070f40c4514200c180041d003005035100300d00601c018030005403203c1c004d07030312a403002502414400d010489007000142c203030020101c4a06c1801180c0b40d0301e503607019040f40003100ba003010440030110800d004107490110701342000750558002901c41d22800c0744003501d16100840f080c1d07102070006d9250a000e41d400703011401c0402d402030032080341c61030034212000b401701f42200da0202041010004044043c03017011265a4071004640291814115078010380f00c06074601214003035903054001c900050780700d4007100c00c0088603590000d80c40b00e082a4122007501c06404156603441c50070b200400215a0001d0b500c3d401142c0c4080318a001c4d01e50844544c003502400503006680d07c1002580e131003c2801d50704c00b003404e04200c4800c42d0031114500c200403036041034009265 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 760521654 1250 760520404 760520413
    0x414070e0118050d030507020f15030a110403060504080403050f030c03120c090a08030406020c1f051e1909050306190e070503061e0105090118110405040e060702120c 73
    0xa41540640c500e41d54610202c0091106280d6072400039000c1d0030480310440c0022004510b10301141080421403a00c0700d401c94107500880b034003210089041c0401440c49030000c0d01d90400300091030000c8201c40140d40c0106040c0f00915041c00c01d404140d0003848200c6140c800c146520300204408003d841d1901040400f0310700c1d14501d021700914101d405451040300d1881048140840d640b00160a4020484640610740b0303140ba043c800387c1081d8107203000a01a10413001c10200d41e4441401030800000e16050281d1581e1842e0750550081d04016424800c2850003c0d403e082c4030203500c0c00d101415101d641d1030004c00c3d20b42c814151141000d480c494160000005081420320881c0c1055040d48080d07030440e0141c42da101c000034a0320b9802c0c0e5208882a080b200801803030f18660486501519040e01d08610b1549014a40403a960244490314184c9580360200004000c110781210006c1100a00610a0140c03058484d5100c003400c3e950303440540714089007000d110800c1c8055034840700002c5c2c040c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 760522904 1250 760521654 760521677
    0x6081207080924030f0a0f06031505040507030b15030d0f02030315060f04061d01020a0305040b1c090b09010507031803050c24090f0a020901170c100e041407 69
    0x30702d0043c03070b1500100c0c004020740c3c040c0060610018502c20f03620a400100e9600700103052404581d80c4003003400c9590704184050022500d03400d51a141c81481c0d000009213503485050040c1445116000106108102c0c0c0030301586c5200c01c6144070002800300d0a8882e0414206000d80350b07011001c0810003d0f80003440001c01c942070b1100001582000030b0111407424004445100150380140c009201003050317203034058010380f901005002051420700040901c44140d03200600103001d140324040032101c000540079940121403141d480006032050f4180721052061030101074a80003124080c4081d03107003e00140c0301512a01600007100011a80e40150082d240c030304460356400215104c00f20300c0f625940a00b65900701b00c4900703603518a07801003401810540c040e107082c25113000b981962680610380e010003503520f0a42a81c1107403211044202040c00e031030303803007810021f1100c03000b58400b031141080d0b01129080103448150000446080112186805c00310000d0001070321070720005121500f54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 760524154 1250 760522904 760522909
    0x105150108040f03090302091f12170d09060c03050f0708100b07080c030403050f0d020312071115042d05150403050d090c03020406090c0e040c03020903060a060812070809 75
    0x2011034040c2c588085e0301078594002c14040f0209840d200101c00032080c59800441028a5280140132428050010788400340c885408180241e120088004c6002448040d0010103030f0198a100e42d0007402800881c03060740c0c0140040008450f54020000301d003000404c080d1046800714421001564800040c40c14854018a56000301c441141c064100f00040100581d0400140005501c00e000074010b03606c40895950800e540e0021501c290340c010300c14a151008130b01411944003442e03140c41d0502000e400d015038604400c001c0d40394a050411070600090001202401003480240c4141510b030004040c54540107081c860000b030415000013200d92071131054001095041400380c90b125041131844000203003224210101151b144059110400031401e1034040c0e40c00801c0c22240400ca280445040609950000c20101d44103655940504002a01a6040e180c6105d0040c00302c85c00741c41d0000303051005101c58003a842540c401c6c80019100e4564280c00c40e508280d001e8011420200407106 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 760525404 1250 760524154 760524173
    0x1206021201050f0d061e0509030307030e16090c050d021308060c0403050703020904020604081c080708070c11030715050d15050a0b090411030403020307200d020d1a0c0c010515010804 80
    0xa1104c60250611b05002d041650041c0c81c01041e03014080d40e900d040c0f8031000b17401c9940340080d8000c0c83d000440781c15a032035491907040c001c6440e0880e000c50700c050050012601440345000c1104032a1000c50600807200d54101c401d41550141d2044a503071352240a1a201c0c0360056102c0200b056200c00400d20041c10036142154205201602c180d0925440e8a0200d00b0150b0343d15441c20500c2220f0500420070b544841e9a40e001805810000e00900303228000605c0c0c1500110090484189901450015241000b460004001d43c00c40c2807c8010705c03050051141c0c2c05000d864281905000c8405500f100d0408070310107d42000307140380b07030151030038555072244d03040a00800d0b8032907602d01081c940754000300000d5200368880d50180da0760b03d141d850b110700c0b0703078080d180c00740d0039048500715400b140e440d08c8141e16003583e0100d542000020035468200c1c0c151040100709a0310120390424030102d002c0000c003911041100340006d11007a034580103001d0020b18030340b101e00e00246208010801140384d006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 760526654 1250 760525404 760525421
    0x20c03030f1c020a0507050106090603122006070201150801050c0406110c040c210b010f0c0204090f23060601020a0839010605030616050309071206021201050f0d06 72
    0x10384840d01c02640d0b2051400c0742c120084820210b0000103030030781000000e10444001d00300c000c0c01000114159101c04803010541c441840620120403c041e1103824400b407040011000c03002103882514207081c00074040c2524113130f20480c0030250039011801c010107000309440f90680c060400e0400b40307081d20450300307454220040c2500340034166408840b0780340d50050a44181060300c5401075042c1d09000c2940c1d800c600440e400c8060f1500c030030700c04a40e038800b01e8161014004d00e86101141254000203000706000b80300201040d03681000b80c002c00401201e0145041d032039042c41201da031444004a51590401c035000f5005070010b4141c13900054416000d49a041245200400c1660707000c8540141035140000d118403045011815180c1940b090003610094001074000c1c200b10b052100c50502c044d07910f882600188100403000031032129003000044001c016108803e03d01481c5820408000e602618001f10f0035910f80002040a061010b8107400e10480a0204d140b2103003507840e01d50081c120030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 760527904 1250 760526654 760526677
    0xc011d03060703240905240901091a030303090607020d050313030810080129030a030804110f030d080a0c0c05060a0e0c0303040308130e3c0a02030403030507020c03030f 74
    0x281d130000a00326100ca0820150059800010765410300b03048420b203960920300300040086103c51980b1007915903032079a0f41101d44400010411501041c2d82d041c28810b124100b94151002104101c044c00e4005900c50003510b59400351b40702c80d00d281d1400c403141d10044544080011003000380030002486a01550341c440c620581c640c0e1041e840380c400a0030345652106055410341140701c0b62703400c0e028040806600f100100c0082004040316038001d400c120b0010070150462040c04103001e80da855898082c101030000038140c1c1c8445441801c0500703c1c20062703810004513441c0550003880c05009040b001d04094010000740020340d01c2c80007080142403d6403030b801082c0510324042015031010000341000c0d502c240d02842d241d540e695480d400c0c82c00340e60b2000301011280d07005d10181044090001c0400090a005034034040444004402020390b0a10340d421501c52800c03c100103910b20b54086e500a6100303039820303c015120074000701c3c0d4404450866581c160010000e0900510025008100042c0d04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 760529154 1250 760527904 760527941
    0x10111207150912090807060e12010f1826071e021002070504050906130215160803010503060a0506060919030c09020a1101150312050d0e0c011d03060703 67
    0x9501d42001694110320003103d401c0c00000b9070002e02034200e03520001501c401c80040815a00e030010080042c1a02454940a444040703601c50b2012001c0d0803014441103000b0041c00b004840c10307281011160003075800c0d80c00301c1505001c0021803650000107040341050005071410000705845000d88103600180000d54140c0348102000140c03607100124240721100d801034200c140c9800140000e441c0014512003594000d001000400001c19041c02141030301074480008407002d0300791081d6036104001d100c2210820402d20641006034100095060b190250146c0b10503807200071603101a19070903030300e00368002030600801440b401e06144461501901c0c01d0302c4009280d481e1146403c1200b10f400175080d140d0001085000f207604004111100001400200604200c1a08680c1d9000a5000c0109a07008200003240a40d100d1029034954a8030503008101c107011070038000380d0343c111140c1d416010034816444400e2803030614020121190010300580013a030340c5c0ba20704500030403803403180c4400d00e0390 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 760530404 1250 760529154 760529183
    0x10f09060e060a2c0f03010e0a0305301e1003021302091203070302060907031e1103030d090302010605010e091f03080a020d031a010c0b07091a03040210111207 70
    0xc0302416034140d10802a0030340e001d0f070380c020900010003051710a941c0283c1c107003000c1c89000600041d108110342c0c0c16140070b03a124a01c05064040c500300000c0b442d80344a068140e1500c104d007000d01c13200d014040d04032010b0b0351602c800d140c00d00032030b0f411109100803443c0813404101509020400701d030f5240e00150010319084010001546038407407012b00c910964800701c0c2030401c1580402010390411604001007411520359910440026120580c00e030240000c03400d050308001c80603403403646840000b01602e44502c120310f10b040007000410000e030b00540c24200c0000b030a500401780c0681d514030180c000ba1160352070404001901000c541c2488103819000c4002000c0743c0c900b000340403030500d250b010701140481c8100040950302800031084e101d820b1283c0004042c0e0700b040d103100f070517907100060040c0d076600c044061b45c00c101d0641c030003100504990b04c1640418900c40086100700e100303c501a25404940c9012642c00b0402e45214034603601070301e071808010100601031300940f80f051401c2c0340400c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 760531654 1250 760530404 760530437
    0x2417060111190308150904020334080a0209010b040807050f060708070804181b202d0705180a0609021b0f1203180a0c030c05010f09060e060a 62
    0x21455090700018110400e210760b080110f0890005d006045038450854105070700021344413001e4090b111411048580003449444600c04414810070fa14408054940d40d06d005460f121204400120b10484000b8004108640a0b0040c1d40a031a110001000c8140c00c10b401c0c0001e4110315211143c0c02030307040c0710110000f800500242180f510070791a0f15110380c9000301c400c50101c903842910144600302940e95601d401d50040b1480404203c0c9400030381001114031111040f402a1001c4e9070500408004c280c40180703900d08000c04007609080005440010b442d05615040240251544078071001c104e614025120302000b80c11846210002900aa87e40f036054102c4e445921980210040310808540c2c0c110305100c009a419490300103885074101a03043d5000521005150480103c60403200094100081055680d2250320600403544951a81080c0344980001d04c00c01c1c2c00640c00d25144001540706000449c21510140c4a1420350070566041004540000380050200b004241d80c3e5284107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 760532904 1250 760531654 760531693
    0x61002030408061f140d0602091c060213050d02031002071e060605090606090901030b0a090501020c030309010e0a0b040303020a05220503060601030b030601050913020a2417060111 79
    0x12132043c1c181010303a4000d105000082d16140d030000c80e44c0300b00001c0c1041c1c10b07211100d07403004140d405440145c0da201e001001622122a1201c062134090750b02c0600c804000140d802082007641c2940c2c1c3c803120607610700400030654018440250141c0281110312554282074000d0140359214441d80710010360000c1060924215501c0d0980d61030351203003400c2046041600190342c00c8041500d52900c2c0c5291a4041204050180b0004095510410001d164081a5481070456980c08802590740702074150a40343d0b80d420070358001c00b89520300100c0b0000c0000004600e03000951149480d101c42c1e4071394a05030001d4002d0040f2909005040144150040c6a6000d0b007100c81c00841c4071448503403c1c4414946014130050446041c18503018043e0642c4e81d001503114111081160709003d1507036000140300c0c060b145940004d420042241002c5a00b0081c800c00c0c2c03078101d130b44402c240300c641d884a808807070700c0b0902020b0080303500f40e08011038141c0d4403070811700d00104002d00c1102c1811182c0501d0009030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 760534154 1250 760532904 760532911
    0x1201050901050a06080d7511030304050402070812090309010c0609021801170114091915021b060c030c0a03150b03010b0901020601050406050102060f0714190f0305070806100203040806 81
    0x1041f00d086000000000244c11210071944011244d1010840c14400d85020188200c4041d02d02c40070303a82c1704192035800308101c401402c8090400c2d51140294a4805644d0300400003c018001c510300010307048400c000181d8503000c0050f505c046d00d284541e1a094000c20303034004141c1c3c001180c240703000e24079007170035484600810366941003220313078602a000e02c1c0c21500705041c040230340311503c001d00408000c0001c0b4154860300142c0c058084110618244c00c6100d5502c0100003030500114400070007102211000410300d000d07100750750303150b901d4008040a87c0300884049a440c0003c2c0706c1f0b61849886940701c0400203038034418003014a034880141d100716030000d92042e8480c0d10b000940c1c5041d540d040c82403d005000070f45040c054a418000042c0d22503800504c95400c1d00d05841c00191664070810072084012000092569102c5d400350b49506210040f02001020a5580122000c0c40340301c0d100c0d1034403684035680d1b40e105940783c22041102c00d00c01e03141001e0841c03000344404035400005000d281d02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 760535404 1250 760534154 760534277
    0x180b09101d06060109060e10050c071509081603080a03140406052406220b0a03051021140129191a091201050901050a06080d 55
    0xc01c41160500507140c03100060101d4100b0911600c2001083d4100c1c0d0190f0b0031081c02c8030501111002c5600441d1140140103114106210305c880000748105041e04081602c2c5403a0b030f41c20100340d121001196122030742d881c0b40d21800300c0300c4401c102080200020b00003280c250725000c1410000c00ca03640005d01c00c203590a4520590b280107000f00c07002d24a003420f00f003203450a80d00b501401b984e40010024050800c6049a03144c2d000280219400407a038064003402c1510f0344d40307032a080c02c1c6400400428084030205800d4220707041c0442c050b002c1c0c15400806041d080120307400b0f1042981c40398100ca0000e8030a07a10742d92503e0140f11800b00c0070741542c3c0303540c0542200f806038102c0031003000010001c448031000d0801f948a070034040046034103400f014001c040c00c44550f0b1000d00001203401d4800d640e2000c8001d52801052007103e074010f40150340030b4071003503105002e034944401036642c90742d0400b240240461405500300b0704030006405280d5030740c00d0a0740c071075509200c0c00d0894040301d0080040e424 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 760536654 1250 760535404 760535441
    0xf06150b0d230f01140f011e090503100e0105071407060903030b060f1918030605130807050102030712021c110403051f051f170a060c0f0e04180b0910 66
    0x140a0002034024101081b10100c1c101d80c01a000a40fa85100400910390040301c890901c3c0301e01e00404034400108000380440d40c2c40c3c0100a60a0000c0000e52038038180c55080401052949110b400c1000030600041c031075603d0401c40e50399030001015000d0046013416101c80c030440310340c0d81d2070001c0c00c52540f0002c6aa9a60302c0c1d21a140141d080000704074000b484080d0306c0018400301003030303081410340390f00c01c000103040e80f0344402c594001605a10300400c034000028000c4e0030072006402850083d541900d40b06504241c0f04034035810380c0907180200e10749003203103103882203581000d41103160140c0c1080300380c600d0281c60741c84590405020710303038a0b2201880e038242e1104502242c440c00d64030194a04d0386070805440a101e001d40140688200b06032440601c0e41a250f0311012701c0801300b5503034007100402c0340d080902e501030b05504000f416013001c205820920343e04d9092034000e000001c3d12a0001441482c0695240403091401521040d04c0b4400c1c2c00408036044282c1c0b1440c5442124841520b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 760537904 1250 760536654 760536659
    0x1b0408010e01180b0c070c0503010207080c0d0906020d20100912032a05130f060f02010504050606040e0708160f0b09090121050105040f06150b0d230f01 67
    0x940c203403030000b0800f84001051a003008041808010030507005101c0c4500c41d60b882e00300d4104005c02100a42165600d548001035840c20005548002c0c41030038942381c103a074a20401c1c080207850060040c0b2414025130825000000490300c20743e910b00e140c40c0305042c4e079158000ea2810051400d00c1c00c4804206150b80c03540b4290501118030400d000e0f49542c0e00d01846041d41025845002403002c10030010350120f00703141940c0050140040d1060f19800100106515903a41c2c820707450105144102c80229040038008401d091040c01054031440e0000e00400340754032080c080c000102440003075408180034442c008504032500703000cad40340303080c4034000e0f2003948a09281c4d03001c007075505660010110407420490826242c81c2c0381041e17030440f10041c00e03500801c0d42d0041d14801e82c0d48038490041c555441c0908000c1002140d20350076203094001c035810409541c00001980510300380b4014000b4070581401004029203944e0055001d000c046100151607590003401a0340c0f87c2c500fa102e01422040c2d03440107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 760539154 1250 760537904 760537931
    0x61804111c080403111f142506060617041101051908010807050f100c020114040305060f0a090b010b0901031d0f0114070504170a051905010b04090209010e1b040801 72
    0x80c05903400c800c0751180c25106d99a0694481070407005013071020302500b207c46441c01703c840001d40301c3c0c840c00c042c46030407502c442c04449098400000d2084800c0d0f07160010124005210741e1410807036940419549007191110345840318800c0d4518101410000c00b04604d01d06c1c00c0011851241c2220399840c0e0403441e5060610440c00c5c0311440e00003d0040089500300c0c1035594584074980148030107400c1c900c0c0700415034001220030301c1c0f1180b040301c45228001800410410b00042e0a440b8540868441c031598940751880800e0341c4032140701038034910064005000d084010002402d02980505000410030440710030040541088240210f00e41c2100e400e20340c040100b800350071340d030304116040700c0003928010b28050000e0041c4c3c041c0310b883e03490b003a0808071032020800c50840c0075900174003111461032000702150100c104040003120a5424040817100c2420300d40603181d2219401491400c8503030900019010032407004103504001100e812803c02051104401030016011007000071580300c84400d034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 760540404 1250 760539154 760539173
    0x213091506060e100302090f0a060c05190203030403030818070e1f08030d090c1706040c080c090f040614100512070f03260d14061804111c080403 64
    0x4024400446200d0801382d560801603480030f880c9040040e112200704001c62902481020140c3c4c01404080022943d1034006119a54041c4108100c0c0c2403000a201154541e460661000750168418081800020300030030300c00354040d0240700c002e591059148003013071030132655510810405010405112140740301e0481c06000b52080c0c00e01810030740c0780010b943e9a07480f0305400e054005540b0071801c804c12810a040740c0c0180001c4e500c214041280f110b2184e113800d0281c034202c030790350444000012460004604020844402883c0c08a6071381c644100084400c40104102d484a59411007542c00712001c01d0164021000300385c1000341e0500b0507052012080d0f8104525102d07500c00700081007510866503040080e40d0f404403000d020340151405140c0454000358402608a41c0440c0c02010440168000000918180e03524145912405c0610100c0b01d402e00301c03001407842c114005070100300202207001d03440801429010032507113181d01d19072541101e45000c0780c082c180050704000744a014070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 760541654 1250 760540404 760540409
    0x1f0c030e030a090e070c06020f0301061806120203040f0816060e030405090c0c21091c050a0201031a040c080915100909080f03161101270213091506 65
    0x20041d860030003a4000070700090401d10441006900c1140059203680c815004c080c4016030040041d510380f48095200d003180e4109004180010f250b5100081800c0e610503140e108031000754413165840b030801c19015000c2c0d03000030025240307882c05440c8480020141d000410392405640b061520400042c5400c0c0180d594401100640340e005100c1485155208040c0a0304030103040f412030b9441007811481c41c00c20894024841444d9503007043c940440400100500c0c40c108200d40d80140070341208900072000c20200c801a02980c0800002c4005500943c0280c02c007000c2030203507480c2840350364002025a2032034000480000c00744000e005840001304030024000084030f00c000c145103810314210081d88203a2044024032600c0740207907002e11240804542c1c100c05440c22090f92490080542c3d0302195259035140002880c00b404003410240600c1128028010000050b8038015800e001d003030b540c103800600740e80c00340c5010441c10020041d0f110301c14201d07204200822405100c25203100840c1d40c6036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 760542904 1250 760541654 760541681
    0x3090c011805040e0a020405010f15020109080d050916080a061503030203032d0403080414071401050c0f070303080f070309020310051f0e2707050f031f0c03 69
    0x80200465101034510020507182d003543c0028000303c083c3d80b280e140c01000c0030040d410920385030010482d1814144103109503140c2824046440c565594100c0c200c031281c08018103041428000c8550321400c0c3d803c881c1c0c0000c40401140c4056100e041c00182a13400342d17100080d1584145880c00c1009454025010b40489902d50613220501d0364802035203034070000303003041904440101001040a03c60749040001100d00707032100401d14003032130b02802004d41601c042c2c80b0110002c50300e1014140026a41c0286c500d414105241030043c44010340301c6400074106251240600d6060310b610600402c41078000750701036583d1409508041000598110003d05160105824070030136070056100000e01c3d80c2e4081c42e00000081c03035950300028905c108500c00c2580003401502c2c030f00103110310707040e140c0d24002e0f00740750184004c0030190718201c541518810b0454029410450040050340b402a90780609404080c040d0307030740e5074a00322031a003885140c4d81192145941e124100c1b13803c161316100e100f00813040d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 760544154 1250 760542904 760542917
    0xf14060a0b0103150e160c0b0423010e0706111e0c010e0303030c0a0804060e010f150503070f0b070804080a05070e0601080402090f04170a0905090c0a17070915030203090c01 76
    0x1092100c50988800405c040c080c0c00400e03044072801c1f03101300d5000d0002904514120254201803071b0030340143e009803407880a1a0107044480071042410b1080550b504003103001051550300d8000150740313403210000f902a8a014540410762613190030032502d0946107400002d491002010000580641c01203200c007070181e80144208030400c0000412603080018030b00b00154150341c1c516203c80640301d000c4890080e5402d0240c840d28a021a03040301c02503502003185d030703a80192503005165843c0203901c52802100f19103d4104082601c9400a0801a0140a07110b1800da02c92103102d1810001c808210398592210384d041101603464030311590040340074a0a0706660400303400182ca007460150288104039025404a000c10220428107078841c1d1900c03208a8403400c00e40c5018051071020710540d8002c030000d0300060400301e6640205c801070b0045032991101d0311611a591100da110061001040c454400f00200ba03e0303092010131511500c1555000d80d6924161880500340b800301913034075060259 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 760545404 1250 760544154 760544159
    0x1103013e03010e2e030305070c14010909020d02130e430c06050705070c0e1b0c190b0a0b1012020f09190614030708040f14060a0b010315 60
    0x3c0d4006540c00c110410184000c14009001d0b503215084a0103814188511540740003003015081006401c1240c0511030350303d01c242da146501c0ca000410041c0302400078599801c180072424450703024058a01c070090005040c8604012405020071141c3c004004a040510401c4411000040102e01c00c0e01c0d0943c60110b1040d0701c05406410303c45001500b480907601441c541c882d0752054144240407904070718144480d0400001c05081584040402d07100107600c00d4000c100031400d400070a00403642c0c5c00d0b0400082030740c1112006580c118003900711450040200c2420088140f6801c9038115001c2c2c1c0c1c2d402401d041680f114011110600c103403600070810614124000b503007003042d02e4808111401c0160742c418591103851902e02c40d004c9e01687c804000c2d0030f0134034081d10001403442a58465160709110082c6900d10414502085410078000382c15440050000352158428940780c6205500003403400307045130120341c10710700c0845cbd2080c07000d5a100000d2403d9a81402980034108100034000340d882e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 760546654 1250 760545404 760545419
    0x90e06090a0f030f0309170310080105010b0906130801060602010b091f0608150d12020606010c08070206090d080a03090b150105030a0e0c030a0507050f04020f071103013e0301 77
    0x4150303031010b400c0c4140701c101c102507030340070b0f410130406d40d036002c20600c55202948803599095001601c0b50749002414680204204805210340e0381a107218500640c10107c0f14420424654807481410031415890500090040424040e0340c0240c100750300003041400304001844031030300c002455810a04284051180f4414407403002000b554841c0ca06800165030302c221610188050455458020301e00c400300105002d1070800182042126500340c4089460301d030011540d5081d00c2401804146042041c0001407500000410700c8280103007031403650601d99265407450750030005411006c80e8071440702c50b04101100c000c0725400340708000448810b0704501c0008000340801403260700e25507590202240712a41c1000095000e90004007254211540341ca0050388a214500c1068042c812412002078a807600b070093319101c2e44680c04e914100f05140d280c0e00941035808040e00d8155584001c00303810070810202d4074900048000d41c900c0b0300d400c44e0038001040550681c0f100803c120510042c800350b0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 760547904 1250 760546654 760546673
    0x815150603060f0301021e030a060603021309020901090312050c070603110a03050901060302090103030903050f0303041109150418032c0108040c051011010b0a0e0105010c0609020406090e06090a 85
    0x10b005882c8807074140c0040b408680248a101c50100501c20401c10944200c42c0c04c100461140300d02090910049030781d008250f00fa80950100000200c0104100f403050054036405440b440e08145010104c032a0b403a280e0084415080c5c1d101300c0006e40009101d240d41e0410440300d00100307114501000b05040028407404c05002e0400c50740101505c84d00422980002500700038003540d0001c042c80241e5959240180540700703a4403040320315025404050040c94808410350713200d80c0d0044000d81000e0841e0003088141b420080240e0280d005000000a068407144103031442440361481d17801400070182009480c8001041c0703071281072500c0d101c0c0085500c8071102114085402820039481d2612035260113015241190000c9420194075540086140c0d40001a162178100d0f440c0208099140c003024048002928020341e08410070711001000f4030351280c4a240111401814000f516107c141d0001e01511460790001030810340303540ca1036145a80a02ca1250044420070061860480325074500404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 760549154 1250 760547904 760547911
    0xc0807200109060606180608011d09010e06070e1306050604030f0f0803101d102d0305070e07081b0315090906070f140306100e06040815150603 63
    0x80401910280c00401801d400464403142d10190510240c1e0b101d00c0004d06800096104000f40c48100b03c0000701c3e60f000700b070042e060b102c0010b4411441101210080b04403140a01824015035881c6105003e91000388250741c024943d96487e02c0d04034400100300035076502d5101c005d00010b031600b00c081040380d40f40c008a604481c0c2c820042d0a80c101103080c480a40440040d01a0000b40000100401c410003446584141c601c0c502e1150805100340c0c1000360720200807200b0035007801e41c10b14140480501c5111343c000c02c5680f810903e03038a04d004480512032942a82c41159568801d41e030074460092141f40070b0394064042c0ca0201d2003480d0910547c8060100c1d145400d202c1c0d10000007141c4504500e003402c0100500207001d0485a0a200c2e080e15034400045504500040c03124840c020003610a0260004007a03640c828075086440300070402060012a01e00801402845140c011b10340c4c030b03808090402000030741b0160211000c0801e811408410080c8515000c81c2c0914000301d0f55a40d56050303a40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 760550404 1250 760549154 760549187
    0x270d0c02120a080703030603200d02121e06041509080a081e040510051503030706050c070c0e0907050105040605030412091a040303120c0906050c120f0c010c0807 71
    0x4814412603401e0781000003030600648031600002c1c3c03031000d05030035401c98011a485103e82d0ba50300880007203040300d42048074040c3c41d0711403800b040d1940503181c6a480803104202c0c039001d54035880b8404000e0040400300701140c003003e40000f42040140000c5500541c06080c64003420300c05895542d84028091207040c51140906c162000801d40704100120903074420b01c1e0800462800341000e06000b50746d00802c209002816003403100181c400354011840f0711113002e000d4011400c01082d070355110041e1074014440103140e001803200d0004a03190584903002811082000e280508003540010b041c900e00780c0004e41801800c004c00c212003a80320084035482500142070750119064108d0486002c00254420300c42d034102075039030030a1800d011000304101c0307101e80c03200302410035884005000d845000d50010049095548200001d40c09500200b00e0b080500040d1100100d001820300195001020240c100300c101081944100f03e00748220507003284a41081100d900c0c1c541070007404007840b00300780790 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 760551654 1250 760550404 760550419
    0xf05060706020409020a03060311040b0a090b0f030307080a02070f030c03060b0f100e1e06030a0203280b0112051006052b0c032927270d0c02 62
    0x1030501406078140c4000e0000550259030710300540b24000e014103c60300054642100d220000c0043d8030300751003011100d0030003404241d822880d10549100602000602c2d503040f10310803820303104640d01400140310141c4912980703900c030502c090009191107a1500154814450b64000340082907421031018200d907840400800d90415410208542001c09201b4a4000900c00014800d080c0c0043c50700001150036a2048020f514400d50400484420307040d040e00b004007000418446102500119800001c0c5280703403074454a02c0340c404070b481007003003c0c0b005810307581d0300d40b8421903034042142031075040040001d0001d814100080c0040481d980710707400c1806000220b1000a20414190280680008807201805503100110f140981070f10342e03080001910300b1480340c1c1c081014a00304095011880f903007800700380100c02031080d10742d0050302e054008020794859081c1c451007041582d10801c2144402d144902d8680c0b041d140b40e10a03100021829004003024801c000d511854404c042d40e0102c5114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 760552904 1250 760551654 760551667
    0x70c0f06060b160b06011b1707020d110102190b1614040b090f0d0c03081c06090b04110306220f050108070807060e1804060635070f0506 60
    0x9002030038541e124030b110b00b40209002e26120381082c040362505020351194800342c2d0314203004560b85102405144a2108406070340d0b4089400e0302c2d01c01c2d0344004140c02480c60015160001410703405009821502508800e207040901d50341407040904100070f4004100d45682556160701110a004188001100303105450103400e6103d0307210300c00508501032650b035446490310701c5403506900c00000350b03000d0700007032032805054281071240000440d0021046003da9046590349601076208042d0320b030510f6444c2e040040d00c4201d5202d00001403004407030004010b1000010300060350580d440c10410104148104106a05e8681816000410f111102c032403c05c4545c15110090501501c01c0104a142000104603400d0000e140410b9503200d00c100ca8009036684c0044904200b0900000d800c00e00d600f001c00040c10ba0150b0464106100304808102c00e515043d400c000310035001d102400503640002250501070400211400488a040c0a001624248a540e01c3c1200315481824068040028031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 760554154 1250 760552904 760552913
    0x36060109290d06030212030901210e120301030515010e0105060c030d060f1a0c03040b1b30030c37020601030b090c0102101e022709070c0f 61
    0x140c441030450075107007075207422600307984000400307031404124040d101121507100b020030000181c900c0031030169592000030100c40000e200e03070400201c11349071294840b4600075120f48144150584040410300c0c3c913807a5850341c180140b50802c015842900415030a005011510076000c1850564105590a86c0c0da40b000800f2107141d40314240d11070300d01901d88034002c5400b00038010420201c502e20181c41020711014140701c411441140f180c00c40d0380d0302c100700400254007060041c000300d04001c0028820b42a00c0d511781d501f40390301c946032821001001c03880241d400c0401c10600a020100c002d009040d0701c0d0081400c81c0d688146101c0820b0044115080d140c040c510b4020425844213201c104040d6000304030340603503035500a00003102c411955600240031400c00185500601c10705900400c1c0302940b50503ca0002c00e001e0303000c0c6640045074420303442041802d0005144040c50180e0f42c881035886040290717000d406844400c3e1140651006011110b036000100c6490142c001550b02c000320041d00e00b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 760555404 1250 760554154 760554209
    0xf0c0c1b0a030c030609060b0108071b02011103032a0f0405040906200a020d050304050c090a06090c0210060501090b070b13020d0b040309080105090d080a0b36060109 73
    0x200f0716100d10300080f040050a030841022035208190501484251a005580701c460485002000a51000414090f81400200c40380d603180181810385071225400805401d6500c100c40001142c214180512101e60290745500350b1240121003003803d004c412405442588103071b100d9144103c1c7c40d11500700a1061941c00b41481d0140c0b0341010821010900241006400803031041000d4084d4084818000c0d0040d0300700d902c034a6000014110030583c2c0c5081201c2603c01424000e400b6039165070200752a0514407400c40d100342642c004120045c81c3c600c8002c1560f0186d00b240e41000040d143c02c00404403214103031140c1962040c120701080c2d8031484055810810306c0d401075400080b42d9145424484942e40c81402240640d554540301c9498000d250300382c402c1508c40305100d901240515076101e100e1740400360801c000040c0072034a10a2040011009111130f209506181014840110188560480e0100718000303c0e0700d41e09649091400a00040000e00c40c19001039180780d07113620301010802 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 760556654 1250 760555404 760555409
    0x506060c03070f0507050409021c060e19051c0806090a0f0504120318020a1203030b0d08090a0f0602070902090402070b0f06040b060403150216050609060f0c0c1b0a 72
    0x80440340c0b50092030400000094481100744d45a0140c60400701d59401e283c0980c0c80c4940d006051440303840780e601e01d248400c0001150540f00d2543d2031a101f0020031052106290241e07540b602403003920a03504006003081002e40c4000c90041c01c0b00b42c140703401038004a00662081d0121201d0700d055480d0907802003c1c1050001a140552620080108100c03002509044100041d6070400445010040c4c003080400c45000c0694441c58802040201c5480b40c024000160300c40e20700410319500c0d49010070300403841c103c421124100003040d102c802c0d040504c4250010301030b4038900e0402c1c51500034040c1d1110300e603002d000342c229000907107210b00b625a0780450362030941c81045002c05103000d040420031941d041d10341501c1a420201d10210a26081081c0c0d800c2d260441c8681d8511204900a94025030103202143e161010001c95180030540600c0150b218601950280030705103003a0824202c0381c1030046c0060b00e00c0006104490010600041d2070407d2180010000031090701c96001862101099 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 760557904 1250 760556654 760556677
    0x4020d0b06011e18060f0c08090a090e070501020d170402060306120f07140a1409040507030c0b0306011701030b160e030f03120a02160f0606051e03060106050a050409050606 76
    0x10f000d083e41c4940c1c4a055101050400d0111080c0d0f0780d1540c200702c0380c903980c03c5008000030321040c40180124006800501e000c4a0090880384d8003036503003203200305071401e100042840c2c1d001041e042025507014031a520764981a0319203400e40f4004020040140c66000d000640101d40c0400041c4040d08c1d801107100c1d422000e40201c44410b42c0300d85040d5034980c0540111408504d007410066001d040041100090380c1c5900400f61b038450440041c4007e90600030302c01d41e0a480340b03000c000b010440184144000d0702040181c0c0f82d032850150f00140c0040744c0c0c40300440d500c0c42c4040042003c244c503003000315008a40441d03640741040352910222031014146840550600407100c40c04040f06001000b81318181200850b0401c550f1080d0912081b406130554012400643e07150b04800510302d00d161300581807059000213401e540300c10101e48a280c05004c00301e50a80707050031003034046c0303000c02500d401030002d40b8050b46032240d0b42000408070b002c0d9100d0228150707201e5000c144113541c0e80054400b01d1801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 760559154 1250 760557904 760557947
    0x1505040302030f120612010519090f0f0f11030a0804090b04151214010c0203070210030f020d02040305010e010524041107030302040f0b0306030330090d140304020d0b0601 75
    0x411400524131031040d40d4940c814002811300d0740307400d10306025552244280d50488001e54440ea4a008080c01000104036045005040c400c000104940800f1340002d010f41d1100c401211305140c00c2d415400075085942c481d82c041c6107100001443c04048078192070b020a0b0220b030801030100400e020303040ca20b0b00c0064203c40300c8808620040b544910507902401003220306408440c100c1c0e102d0895115140ca500160020810342015080881c407181c0451910301c3c002a00d0202c4d40c0b03040080b40c100c0212005195000141003041c00400d01800398005400c000800c03d40c240b00f140c00030f000c002c00340b1400c03280300b0884281c40b066960b070340100c6007144803045041c2d84651910b0014025403081c01070401c06281c105000c00c0581c0742809032882100b000e4011440c0c205211520212004541003000d8940032025141b154070b45c400a455000303c0400d4014100f00040703000141c03410b00c0741c1c00003800300e040910408c005030781ca86141c1201150001050790300c5495200040301c140036564141101600e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 760560404 1250 760559154 760559167
    0x1002091305071e050903070b13031703010f080105090a031101060b04240903031403180d11010f1404020d06180b04171606150f060509040f0203041505040302030f 71
    0x8111820355654900c0351000e003c081d26011003903c0c20301a2400e40c0e80c0690150f4001d01c20407009178014a0142e00c8211105a030300c0ea6990b0300311400c9503c450440300348101200400941c01d00781e00042c043c000c038000030711083c0340402d581ca46c0d4110641000c2c0400c00c0314030707110311f04000a41c4150007501d500d4126a5031a0b44400d64041100e12203018408456540a45c3c141d94501c580951003e480d4159183d400c2e204030403162360042e0304082e002d217801a4450541c0c0000000230003980b07a600400b52031781c1c82d00e00c040d903c00c0fa0840c0e000101c0c114803182070031150310140d8042c40c070b0b0541c07060303044481c01c0c801d07803e6041c07103c014207411003030f4004c0783c0d124a02c02061150945007075100c0ea200e000034204010602c15030204600540c4942c0c211483c0e61107001002903401d410130544101307100c0c1500d20140c2d0301c600001b00d0180b04c0e44503102144002a548500d1b08283c0100c00d00445024030a500c1c41c00d00b6501e14202c0201503c510301c62a80c2c41011408041c4240110b814031800201355540340c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 760561654 1250 760560404 760560407
    0x607051c052b020f180f0418062711150903191a01170105100e060d062d0e0a0c031b050607060212061f0e010504050901080106050111010b03100209130507 68
    0x205c0101c9a101c0c000c0c43c40e24564030700e000d01450400d1440c0250780c10703c20100b03980d50300c042d10600800f03040c0f00c1c100080080da40c0003800c116007012402000c02d1900400f889041c0680186a0070394045201c0302088500a5505e00044005109014410009a500c00c5040c8800918950201c040407034034a8400000d10311b02c4048003421070050703e402000941c0b03400d1100200c0c10168440c0f0f03041d0b0084e00300098201d28100c240310440034090790700401d2050310041058040c2104848002083c040c8014404030703011f0070f206892045540000508802385161240401c1a200703100040c01102c4428260850400444103500242400750000e52900481e141c400701a41014131500500800b20000404a2520182d10b0141e42280741c9004503501c5400710499030040f580d0b8815040c01020840020941c8404103c1402060761000000e421410680010100c040301800c1c1445a0b051003440340007940c02141d400181864004010703030740c03c818004070b2020107035071a649142914003000c202c1c000d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 760562904 1250 760561654 760561687
    0x7140d030516080402090705030c070b07110d020604080d0e030d0501080706030e011802061806030c0c0601060810090507030902040e060703051b25020607051c052b020f 74
    0x104440c180a0500540203a400c444103c4100c2d00a50700881c1c50000c2407005020300e004540100d00750072060715204560303e5281c3e07800c0040e184480020761a28000200010030b12410254040902c0548580e0410fa151080c850081c0845121400c2ea640d4105000071820070848c0c48482544c907061000e507030340305441c81c1c03036040071310036140464201902c0c035480304c0046c8902401300a514241c160044c841da000c0c000103401c10b615800c9504e100607141c0c803560740c4500145219040240003980e45942034507200d41030070f1060f0b20600c180b01e941c1080c0180301d1504104003054a4141c80006001c4d954500304401130010000003035001490306026607903012000c500c041c4a040191400e00450b1100100c82140c0203408900742c914500510090915080080303881c2400d01040200d2445412990001085903105440803100d550000c2034150b40b92004220034004200325040c02d605084d0b16414a20031030306012a2010b4145040d0041c095401c0325605660f024030308540101d445006011a54014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 760564154 1250 760562904 760562911
    0x1021305040c090321021c0507060b06130e040c08010207080d0510030b13051506061602060912070e061504060c0c0f1421070e0a090f03080a0e060702060c07140d0305 73
    0x1809200890b08204000340c4d1b1f151076840c00c560b20b540c9400140d0703c91034010080319071041e60200b003c1107020010503103080200d02a000303003109950242403034034140004040c50707032000380701c0d900601240c0045165101590040c090411000c01c0d1583c03810a02c135a0388050b0741004146e0f1085000f44408440c802c5484070070148100202c4410004c0c400c4564013046085503407aa114400f082100c8403121035418040000d40b0140ca00744c1031049a6000071048110340b40d0911096011080030881403110f030a445070821000ea900407001c41c220301c00b400052003240604414403944013144010003d05c0341468000f480d007210403400b051744903844042d842040d60081c511800190300c00c495403141919103410070301c00a000070040f031480c251050319000e8004102080a03990b0303040550102d441451040903003482503950054a1402c0c24082c401c40ea10054504000d0380301070204005c0030b0f00040c0c01a002005444047d48601040ca0f102481c200c0000a030142405010440c59030641c264000500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 760565404 1250 760564154 760564157
    0xd200c09220209041223031603110304030c030212030c030f07020c040908031006020712030e0102030c07030c0504060e060312180604090905070b1e09040608030703020604031101021305040c090321 86
    0x11092800c180801e403040c104086c004803071078200b01090344c001d440c0c0d040c0d1801c1e81003424041900c1100144102c80c54008440c2034000c104044108020964180446000107015046c00390545c240803220403207601000781102c80c0f80140c100405e0b0018020440200301110052003840014003901d0140c1141c0c10030741e8000c04450201c500480d01030300204102068804114140383d01c400c007a01c0441d010400503908a055000c20420514614000c1c000d00010b1401241d440702042d00c0c020511007118510343c803820244050b4002e00c03000d9a8040362309880002400c0066403a1206440e4000c002140350030590f41c408400a800a00c410042d0080c60181c2d0250301650340c9141c0c0d40565403d5413082e01007031100d0001c03c010b082e0640498001802a629001d040001c19941b59078400c0c0c070710f600081e026400b40e03002c0c0c0200010558446d0390342c49256810701c002c0d400e00d19a6040c10300302900d24010b40380710740d45800c030300321503e0701c070340490f200030760300803404401510720101c8204820380c02801190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 760566654 1250 760565404 760565417
    0x140703140a0b0306130c030206040303030c0f0807021c0504090905100e0105060123120406050a0b030c0f150f1b0118020a030f03020f0d200c092202090412 68
    0x29203a229a02c204441804081e014054030354492101e0400f03c9006982264403d41c0b401c00031000d07071654400751021754820340340000c0500700280702070040500d4554080c1003008001c104013007181d000c40c9140c40301501d80d001c108254401c60301501c0358003a580000c600d15150600308000d00c100041d0108082c422640c0410401c07401c2500c043c240c1d1411902103012442d0303202c00c0a84c1114060b03604044c00801ca80046c20b101429070010107080c0e0030342c1c080d1811500c400a002200d201d62281502c030007001c070700504000e0401c1010504d03900301c00d04210b01c40c0c801c90b1481c400c0151013204580c44813010800035a92032100129940d005500001d891075650f1030084507800c40c0c10b041002019842d001024115902c0c5995200c210a102d184821030842c010b468003415100380420122400c40f40e1a1621140c006406070030801e8412103440d4405183e015008084241d11031184082d08201040800c00e2440702ca5424400c907854582002034114081070100820b01441862182c4540840d54400c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 760567904 1250 760566654 760566661
    0x5100e0d0e03210319110c16062016150206220602160b10060e27040f0804060306050f0f1f0207050d0506060a0816060507030314070314 60
    0x26607146040c401d80303d582140702080c003030710b05102c0000e150720a0300b401e401d20042808020320010303954034122008000d2008070f50720b02ca50206010342ca0058680070703110790034603182c908001d041c501c4003945a2040c0d03400311000011103100b44250134420581804d014070b0300340d03180c0d916148103450214000040c0280f40216141e00300314080344c0010001d8008083c2c2c81401c644500000b54400003030030707021049a840301800954440c44491196115411101200d46049009000200f104107120b1040d40388803c03504121407151b40104800351000201c8070240d0b0781d85805041009841400340606d01d0204000840e04d60503048102076070015901c09201c0d00003201881003246e11001c0c034560094a080c0c000e240c0115040683d00349924034812280d90b144d40d040842e2800440d003400340c8943d0440c0c002c0001b181031140782c0000412081004082a06d041800da00e102d61007805450208003002801c0018140309412402405210300203400e114200081e0103002460f0300f0201002d03108544000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 760569154 1250 760567904 760567909
    0x1218050304032604180f09050106050f03010c0c0b070507051b010f0e030d030b0a1d0615090a140103110a0e0111031e03190914011a010c060905100e0d0e 67
    0x600350111110f5196030070030b82070500b03061040c1040744c1840415a540c000501440d5198043c02c201d560080d400001d0960800061158250000c0b402c68007a2381091401c44440e540007201008260704250004035039105c1c50b03422109480b9100e4003a00502c1031050922610458103e6051000401d0701c0d00340010b528040140d4814190f102c0b0694190000c41d16014658002d0708500b022000c001d00100c1c50741c2d21250070002d44c0610022414800b0034081c10810941080b52110420042090800342410421b00014807810641c1c010184696500c4004421603401f03500f20140005542071410384811042d00014450b00002c00e10500041100186015902010089540318100d9240400c440c010950040310240c0c400340c4985030b89074810b0303200309aa050f00d00c19050f01610030584c00141d100585242400c1d254900412041040c250841c142260703045213040132160340c04640400e0041c403500b003a60800c1704203540c03c2c2007581040300c0f0030344414002c43d10000c200c00c2c2e511801d622903e50001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 760570404 1250 760569154 760569203
    0x30504060f17010311030a05010606020c03010b060408030f0a1704060e0d0903030e01030911060301060f080c030c0a140705011b18050a05010e22021206010302070209040201121805030403 82
    0x809101e0b924081c01400407a40400500030b105002038200ea00540b51640c40d542100c1c500c2d888880140c10414140d140d5180a006140950004850490400d400d0090258491084008003207496100103034068400740102c10240007001c52415425151a250614034050103030003d040000d4007a00307000f044264010008082504c1d0540d8030010704441140041d40100b511580075101c555880c5e50901090703954034000e601130111541d0702d10803042500d01c013406042c0e000d010110141c1007441000381800740c900a0352146403030f0386480c3d1210a9032200e150b4143c4a034a801821a500b024909042d58060524004e01d25210b5139603002c160311803141003242d040f1540103035584214140000c0003150710038034100305100030003010070007c41c0000040902a01c401c00e0300e00300c940c7d000704003400c1028010354031503400902820150310b8001e495002400d2180c000348000c1c14001d8100348004c00b14600d6100c0c90240070301c6c44405d262000d05040890b62034000d40b104849203043c00c8402075071030b8062034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 760571654 1250 760570404 760570427
    0x10b03071b110f060d1b260403030b12010c02010e0613020108010e090114070c021e22200304120c050a0f060b100e0415230319030504060f 61
    0x29030880709400300300608000a5040c180c0c2c0082c0c10702560100c1c5c2082c0c810818040c205003031500d4000103400018000d1002d0f6080451751512100d180d00d02d0042d80d074201d0750b016615181c000b5070051030a000400010406074104665842c0042c2200b82e00d80560200c404d43c00302c13400b11800c2c2e58411300d502602c00d40842009001504000042010107101c00b0100d400003402000410054142c44040440b020112007940016900d031008030705600340343d52a82508035058440301e041601d000c0106151613030350016030110640c0c60f0f81300800c07902c85500040708150b12000d03610300c114400c8000652070704161400c4d200d184000300100030f0740f8002c21004094030751040140489940540f00c40341d602800e0442a140780d620b460a000c020354440f1203101c500802c81e100c0984c0340c1480000d0000312840c0031703a20304600303000306e206001d113001082260141111080403008001c0ca680302103400d02032060078040b030644006030001b08042d0400060820f898540d950201e40e01032282040354403882c0c62 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 760572904 1250 760571654 760571663
    0x50703120201090c1509170c040e0f250905041707050f03030705070308090303160c290108100c0801180b0301020d1b0e13050402030c0a18240b21010b03071b 69
    0x4902441509080c0c026401c103c1e040000d031080c25030a2841a400d10f4826084211188180703000300cd4504044002c17070000d8401c26108000c4c13490203540e4a05059030340000291072840224038a0200f00c2c3c104031501000c0a80d000340da8503414913000142c0982c02c0200d003180801c0382c040009214400010569109200101000300203030b1115034141c4141c00c440409440030f400d070990001c80081d08001070311055040032400880c82d8074040010341450040e070000c4820a007004d10200707109600a20080c1900c0085000d6081074001da0303030480c014040c108180c0d4040d400850b854018284a51110005940c001314036040703902d01200485107076540e0b4091961010b42049800f5007a0f56503407086a10074406800c50340c840904074000740d004100c0b44c2c410585440820314541c2c00b01c016029a5a4401c5090032884241080c1111300e0640d4220b40216456108007140d0103018950459480103903066000c8960800c0d43c403180c1410441c0e00c100d40300c0c00460b01712506801205041c0e81d82c2001036070030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 760574154 1250 760572904 760572913
    0x50f16140402191412090606090718030308100806010b0304170a021b0607020d0f050715090e071b0809010206240d14010213090c0804050703120201090c150917 70
    0x1000000d481810707516000601c07130002400b2560000c090142d8240c00b480d40c2c0001082c203860445c040114041c8001d0860042140381c6818845102944510f442079940c18180101940e940820741010035009030720100680c440ca500005460070302070000d601850042c201c001690000c82c0c50380d14940314602803500180d0120250000340541c100c035103510b035840200020314142c215000518615002c44050b24082c21100f0f602d030802c801000140014075071a00600f2029403074100260002d001c034824580c0d0b00c01d44000040d003091059440500c100040b909003c0f5130b81d480d091280d042d030002c0d88800c1c05440b40c94082440300b036191031300303000c001d4101c0c048441c2110480141304d84513030506000c440106000c20fa15250a00c00e00103450032007605000440494544540e079401c1e214020080424080c80c3d1003840045400031030750105598020700e4192003004004812401411a420060a442c1e00303410b02107101d00e2107043c00070001c907042c3c1d10803000750303211225014104051691880643e01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 760575404 1250 760574154 760574197
    0x81006030504060f020712091e17010f1119140904020a022a1c17031b3c0910091805060306180d0c050f16140402 50
    0xc290490790340709224007000b0602a95004024040e07030002901154407242130065000d90343c1e400400000100800c0080c00a18025005100104c2c9014080e490421340d110500003145042500400c0c252643c180342040745100102c0b4814103070f00051140c0c3c2d01c40d8503c0d00c0345a80c40d0311038015400c011940884c2c0750315240008003040020750004c1491000d600602141114800c0134629120494020324990040b840c402402c005203088803c400200e50950303c4c1030080403a00003007944c20000c03251074a050b81c2c0d854180d121081c05a850421003010180001d00c13541c0303400419540c40031504109418030001224040b8098841501c4403411003820003400340154928040603e0300141815091000065403242100d01da8030000c40103400000b62204280f140d90b00f001c003d4158080c604040344040150101c08140c1c49444000462003000f00d042c6041d000e000b4148400114000000b08940951030800f1207110920384500c2030f4948030944000e03510340c40c00d00d402290807888024120303031622074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 760576654 1250 760575404 760575407
    0x2070507060507150e030a021203010807090e10020706090c0e1303031a060d021e0406080a0c1103030a06050a080d050f0d09051b03070501030b0d03031a10090e07081006 74
    0x4000f100c0641e5900c1003100340c1200a030140c4100401810040d0181d0b03907406495401070f18000e012661003001940404c0100425000810403100795040c064011580407515441075261003004400c01022510004010b010441c0603403200c1c0e030092244814041040d5203803c142907070703a0b00f100d003021664001714113440028403030f900848a800b03d08401c030b000c0300c1484001c50071940001803600e0400c1c2d0700065251140d5410740c000c0328240400d4440b503103400d0511b040204052009450350380101d0300d60303000351502d40c004c0780c0c107486000d204001c481d1245001c1a4007000b4010300d110b1035003d00c50000000c00d0030340000c550089007101c6030705ca0038a4071079441010b6110368044443e940b00c1c40d0340d503d01e00c4d0008038103010700040d035649650320300311a103114400c250420907103602030b6040c940781c061007220544072020907103019900350500041e842c1144e01e01d8210140c002d0111540441c05214080505070005008010345070b0140b110245640d139000c0070f071501c0c2c0c400e0b621040c140c83c18480410030300e0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 760577904 1250 760576654 760576657
    0xa1217060a0b0a111009050304082125171903060506120402180403020a03080a0603020a051309060203090d1d420301051309110609060418050105090703020705070605 73
    0x5032803a1044131510500305d8184000c5468454007100e20b5040083d0400505204004010081214040540d2200b90160204686205000801c40c884030141081900e120070b0700c0c044403130b040d0898038038042044130750320300240c1e036001900340280b0080c41c80018035041d100c1c0c8113410030f849c40640014941011625008501900180f080b68040901d4820b0341844203048140e5003d503100e82c0050110050500d0090400d5500514199049142400070070160b0350318080300c0304580080d12115040e5884130285005400c5020000e00294000414000030081c0050745446d502e1066403041821400c28806c895617030003041031254002c0e010201001840610311003400d40040805440d2800400c0b00741d2802580e5240d03510007000440480100f01034103143d0783e0000700011140307040014880340d5541c40e2103540f01c0c004150240754041400b203a1030f00c030281120040c180450414000e60241c903030304005003409000f103d001d040e1803804580c03218000d009903100c039580040a05035050815404462a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 760579154 1250 760577904 760577927
    0x1020118050709110c030d020304140a02180405030c0d050406180506071106041d070908061e06060d0e030c240105150712030603050f210a020a1217060a0b0a 69
    0xa94200305c00d031a122010030050074a030282401c0540c503031900b402d241c1d55580d102119100d5a070410000c050050751040384164008880c4a00c264450702c460501d14518000c410301d2054910a9201c640b40c1c950b017060203070048030100d64440700b600c581c5142514041655100700380d044081481100d00080d4040e90518134100007503da40d0400703a80d09401e0364a160060400317a4402120024080c0460348080600d01401c03410340200410b0410b9030410035001100302e00701c04513502603c046043c40d0f4645d8111003800040d01818800088074020b0907849a0040d61405501c0c40303103220b1400b801c0050207061025240840480381c603603203048140412160b03201f1081407107600070082040060440f64908150f83c0040d5400901d0905610300310386440315a890090040d0700400103078914501048807851200307410000c80362074034a0744030b05920744a41a90700130070340b035401440381500340c1d0301c00d0045500700010b020300e110613103c10742401106081402183c030b0242003040b40301d8001d402910318404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 760580404 1250 760579154 760579181
    0xd0c0810020f07080a032034020d03180e0a0501080706090e04020303070b04080a030f110a030b060409060b0a02010f0b09040f0309080706110c030c091902070b0705070201020118050709 81
    0x40446100c5002182d01c0d00e41f489200d03410b08046600c07181c4154035108a4403090300303a4004030100c005203c0e00c80c01040c4429000707101d0301402d89800d04051182035100084442060003010f195210000c0e0003843c8800c40f129180310b49880b000181c1c1440008025007221402c1d150850b6a6061030000d0150450040050360944400c101000000f08060740c1107100794014210a0348405400c4401400c0d16080d0003824411070601920600c0080c0d82c000700d80c8510358500f4006481e41c980350100307541c0d000315405041d146140800020b1501400402003a40043c0d5034020003603180d000640c8000c503803c0c07401e1550050482000180010b0541c5046012071f4024204044456560809a4030309401500868006200410346280c0d0400c10801040c102c5400c5025240c40c0c00600c01241010400424141e004081d5110f90100c03650780d61704a0311403e4000561001034541190050b190354030502c800c038015840c1c2000308034090081d5101e0303000346600001410700c00c0d00c4c1501440c00f91400626401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 760581654 1250 760580404 760580411
    0xd0e1c0206252102010c050306100e040e060126060f07030228030c110a0b040f050a060c0e01110c1909020d0614090f010b0310050d0c0810020f07080a03 67
    0x30895a5050b48032485440340181c1d00e030b032640c10002c00c140507100c5003c190075a810202030764800c4d42c00900b600e034400c400382c1e860024900c103030750b04581082d03854a445400c145070050010030b00301c012071303214142c0da207841b039440200082000c1d0701206181504140710540109011508406404d64003030340006c1d040c5000343c00e01d10701d24200c64a01301e80401d00c4817030741e0802c8000c242d1030740c250248070500107160070440405091001c415407140540c1c00000c00700200c03000020108604141a2000c1640240458400765014502803004000300401035002c1401c4440c0403510f5842800314046070320b402c4015141c10200c0c80103010b000c440001800f8040d03200c4250100c3c1c0344026101600c0540d0740aa0b0114241d80b8054034031921002840145001c1e550404c10005030b081020303142c60450701d0480c0725a80e01d030b40342c54400c03540c10701b6504180e92040540403003009002c0030310b03030203001d546200c803d83e10032400080b4418221710034402d030f0050001062182c0c0b004a441000a0700c00c824080c103011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 760582904 1250 760581654 760581697
    0xf08030a0e060a27080d020c03030409050a1d01020406021b030c04050403120c0302030109051e0c0a0c02120a02030c0103330305070f081b06040b180901080d0e1c0206 73
    0x43e0844c041c03800342401c000103641048120b004000046440c0040e001030a50100d40c4000b00b510f0340320740d0081c0348544c0d4480c4e01040342c860ba158810b11610300010580c02180b102e214030f0a01030361003480f604006119264110203400c188003c0d904049030010020100c200c00c4030148405000000c200f80c0c240890000804001c44082c003810340d850403140e0780180d596041448201c2101c90241118250741401c6210101112001007100e8200c01c482c25501d0315176204420488450b41c0500c8000d410102c0c001104001c45400101a948031744202c0c140c7e080c00600000443c21101c0c41e409500021910141d0f25810020110001507402000c681400ba441d49035240c0c0c034602903650303200c1c2e41c0c2940b0b00d040c00c1241503c2030285802d40300c0c414000441c6091034900080080c01240030304209c1c00f0000907400640c0040f41c010304c030003034405000781440d50381d01e07090541c8070002e1070b81100105d10040c0c100c2140c1e1501501d40760302c0385103900d5107030711001d00f40c2c007480203940000d980255046e4600c5a10f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 760584154 1250 760582904 760582937
    0x61909051008060114090403080901061d240a1406090405070f1101090305031603022106150f0a03050c0d0e030403120f0914010309080409060f08030a0e060a 69
    0x1514481c01841c450307442082e00d0440c2c403514081050744078492001c42c10707070310400980c0c80c1c4403059002901440c08292944400003142d0040406600c0124855152180c44002030a0107412a10440c00041c03043c0c082442042040c004000c94403025074404d0107400b05000c224203007a000c44500e08050304040c1084600d0700460122141622441c01260034100081d0220340d02110400004009000900c6804215030f40038041d03000203400d10808561803040d51409510a0f8141c400d003400d14515542c54090b04d9070144a87d07582501c0c280e001c1c05d2806c80d800003598455040700c0c0124002c40c40c281c80d003032504004400520010f014038400803070401110a0303000c1d050181184108034038025554452071407402c1e04c008042d404145c024810124001c0b4403081e04038070600c0c01c549200310340038510120000124010650640000c0000c1008030700401c980c05c00e41d1151007070300c1c801200007120641340c482d030325540e01071000d010300015918400b010300d40c02d03d44081c08a100c89414900710044620310b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 760585404 1250 760584154 760584161
    0x6160204021204120513210503072a03020f0f0a051003060509070305011211032401080d02010231030b07030905060604150902071401060b04030623061909 68
    0x442c40c80304114081c031084c4104441d2610007000a0306002d440c06a21081070f20003400103100d00680c005251221401110754200d8801009520800790381d9101ca2a2800c3c0004c000b0301040c0040309070fa17078070707454150000c1c110190007a00d4008203d0700b130469042c8100840901d1811483c0d800038018500000d441e240e44086000c8194251008100507080406001400d140100400b0030942020010000014140303051041d41e508142c0c0b001c5060358500105e407600c031102824008070344890301e00e400740900f40031602d41a11840410f0798003805a620040b400d03801502c0c01048031622890354058001402d51a007468020840c08080c5425620707165011074107405c03980340c404241c950480708204a81800b44950014003104c0800c68122540d4801e500b90076240180140c1541c005020001c0c840741480c01040000e002c0006d2000795281e450f440d4994000b4403080310702500309505025110a094002c2900b0020f1812240c1c05903120020410100c14031a00000e00001c500da0100c2c07003185500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 760586654 1250 760585404 760585417
    0x1050109080a0b10170d0815090f0901141003020108011a0f030a0e0106060c060b0d0c060e030c27090c1021060603061e120206070507170d111b0616020402 68
    0x700901002c1810b803030060180040101021b42401300031a5500c5550340789d1040c0e40e0041c0840c3c840200380c0d99a842c40500601c044203a800c000e20340c6034100207107000c0f40e4004c1070039240300381c3c0d4040090742e81c0c1c1000f14407080341c982c2524101000740401d803015001c0b0301c060755001c0d07140003004c101241588105404c6404a42010001648050020301440040d00803c21010070564010021424588511460841078000c810030804501c00f21145540c0c20425035848610083c111880100403080d04824901c072140180c40b0414202d000410303004c004606c0f5101000c010342030084101c94070401b2141c040c1080641560000b0045120003042c0542c8245400740050b40c400062950030080d038004044980c1280d4190404590300a00a6620301484c20000a9042e10740d01d44442085c90054100081500201e510f0407200388844d44450001070a40e010740b03c1615006035407486400c50300d4980140c140c8040f4004490050401942810002400f94510820045040e00055400141a03a120b031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 760587904 1250 760586654 760586699
    0x906011202030406021306020f10051302041b020f1504030e01090315051b07150f0e24010e0402090601232205060301121e12120501050109080a0b10 65
    0x10502c6e43d00c2c0b1000901c40300c082c0240340010110b004a5003402e0f55550f0070400d034100304a0b00c60002c100001c58000c5248030312070780100180054034a003542040200280701e00e0100602c13656542e2140c214010070040c0090780d500e640803085907100d8806039094031f0b0305070050b81003000d102d2001002c20444580707002c441c4541c071004159400e21b000d140380c420070300720707070064100404000c030b50001003401c00030001c8070f985503c0c0801c545403140f9450340100b0320030594110310f000c3d0700540c1090101495090742e0f0011040c041ca110760b600c5030791080301d41a00300c5e0000e42100072007000c01d04560050124188024240c040200ea00001807051020ba401041e07000b0303100442c0e6102100c58044140113600900300680b0110304661400b450703480d240c0d0384814040d111500304840c0040410052503050f8189130890304c800e503007014200d4010407002a070151903041900d004008280340d84540441d108507820680245040856070f1220f501f9a140602501118a1900e00000d00c01c8103811100c80e0354100e8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 760589154 1250 760587904 760587907
    0x12050c0312090f12040605040e040503162a0e07030203131704050307090b09041e020303160b0f0105010f0e180c1c110403030e040915050a06060c050c090601120203040602 75
    0x310343c50f035454000c0b0850010308014081c0401c3c440c8035801000d50701200c10700032999149881d1420310368154480c050350704661118120304401840710306c0c0c003007052000004106034250251241c01c000803407110b0242e04203240c048408180541e10a030007642e000203454034403081c0e01c512540e902c80003465000c050707621444c010508101501d401c1c4001d00c02860401c50500140c11020f0006101040080006002c1c06c2500c49041c1e001c1d2103d440c0f035141c103034003804032581e03a4561149035410345000c003400c5605480700d00003d030301c0100004003181216410784650f95080503401d002c1e46c09240d0300720103d4003c4c2a803045031442e038440d4405280254041c040a41c2d03600d4000403181500c284450780320980c02e0401d039160245042e0030302220100c03601450f140b000011200002400707040015000303406002c0290f4000c810b5041980040c0c010810b0010400034a0344d111000e44148510100c00350080d00038120280305810142c12040d0300000514007107004e0882000214200d070825141682d1041c1e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 760590404 1250 760589154 760589173
    0x121d0a1403010e0609120c121c060b1603030b060c01020304120807020601060e1519120b100e060901020f060702030903071a0a030b0312070501020711040912050c031209 74
    0x1820303c5148215211a000780c001c500d4581c981c0c5d56910f07505e400320075101c1c5000540303100846d41448081403074941e901c140d1b503607625000c109044550784c12003945860fa1900000044518a1100721810541440c0303070718107080a951015001004401c01080d0000c200f00505140c01d40300384001d40c0b089103e6109079512205010005158150081a10043d58000c10041c0034042c2c00c041061603030310040b148040210a1b6403850103842c014416150313607144c0420b0041400d540c00100100c501b00280208100c1c41342010100100c4008240303580b004103185482c92081703800c00c400100f01850040c0100e5048000c2104a1440d10600b00e8030900141c00c041064155468140440f400600840201802600c20100d54014611524101d00181503403040c0311089500d00b48000d403850034801d00034036142c03001400c0c428041d50282c001120301390030040180c01c4034a0a0f1095101c8103412020b01030003c521294140d40c40d6000065130388040c4014001c80c07464180c050441442181d003100038249109 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 760591654 1250 760590404 760590409
    0x402040e0a060f140601090b090d02040c020a0311071a0f042111091603090f050709150b0a020d1206031506080625031e051e070c121d0a14 61
    0x4c06840074160b40818100c00c1c02043d030b910020b510b00746e4000c0c1c8009503a0b03d08081c0000c120a4088030000e400034242148015426000319121403010702a4071485a9010303055101031700d642941c09062660400f0040030440111000060402442c0c8044282d00d010b8403000c010450b41c180300d80c07440c10343c4c02c4c0f203038200204038402c604460303500340c11b40f40912035043c510803603120241440f006c0820542e40f0030100d02809250718044040c16089410703038607400e4548001c400545500b6100c505d04044034807000a001560200710744100c1540d6000d0606041c8180085aa41d6000000d055440707850b1040440030405040c1042403600a40800043d02454941418200724004160510700e0701000c1e11440098440582407180340c21500d0005100c0040380303149151002c1c5800045c03003013480c0400b00120440d4035085541110500ea0709601343d5500c12108660841030500300500d0840b1400d5480c460034001d900c1c2c3c0c4a0481c042300d45c0c607074100c001400300d007101a969101920304203a901690b4440d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 760592904 1250 760591654 760591661
    0xf12011502060426130902031501090b1605070f090c030e0309010918021b0105040b01051002100c050705030d0b090705070f110f130605010f05071a0402040e0a060f 72
    0x200c8030360000c0c02c101c1c40d040e10f665107032140d40c5010040b030b040f0b5000150311060806040341c4108201c4d81c150f0f0806034a800007100203400840d09540c80020722080070350b00358010b02e409801c54402c4190b803841c00c900d8200740d419403a02144103d40038420350402007008001c59007000050600f00c6c50010720030071410001425186154800740441c2c0080029009591b4031400080545554110b01c04250000c91076000c024070481d0140032054001c403525151868040d00454040da010b03902140469881e1020000c04026074400c20025034064131031000c0640c429007001c2000c141e1418100d00344140340d100d0341e09550141900d112519a03c582205083c50b103440901d40040546c03400a061182c1e030f0b91400325804101e20043e007100800d0000090365510440503109102000e0f240c11001010030000704064450f0f0b00640c5e01194803c065030116601c0b840a070f0301026044000c100300344000c82a01202d8140150040c0e821a403a61000071800c4000c00444080c64070808001070499140140e09044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 760594154 1250 760592904 760592939
    0x330d0c080f100f022d09030109060e0c011e080403210c1409010e04090c031b0801061a1206120f16051009060f0c050d050405120d080c0904020f1201 65
    0x1001d2040c0000155581121501170164520309400750341d01c00c00d40940e401030f01030080c401d9490340c2042d031a281041926001903040b0030600c4d01b156280b000c0c1c500103441c100181c400d0140b0728840300b10f600305118412800c2507081800380c14054a0107052003550500f02d40d500c1c0804410684800a410b26598030910100c00c100e0090020741c00c4c03100c060300080884001e09151881641c85420324030a01101031413081c02180c0c400308041803c044002100400b50103807084099a5182000004580d6403c40320341148200d981c4500c0d2a1a002010414040001400e807640142d0004800d4803c1401008013040301910900181187c0c40341140040c4600d4403608102e002e05e02d100a1a270240b48c01180c44400d8031703039909001002c00980481250039100c1c0c014040c3c514810b08040d01c0126801c200240142d80094920002e00e0344c1c05900e480c0d03070f42d491001002c009115032000496081080d00a09084d2000034009898411a05115090f80e00f0580000c0c2c00d04079404010000728044050b41d448 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 760595404 1250 760594154 760594181
    0x30d020c150c030106210617060703050c0405130b0301050c0306041a0310020f070515040c1202030c0603090111030a060509010f0b0d09080403120206330d0c080f10 72
    0x8440c074120190084a020600c03510080c00700c2d480030310f42441002410143c81c00010f000c10001e81d995001c2464040d03400c404408ea003401008007043c00144a070240700c0c480d4110f1f4030b036540360510304014130648502c190205900c1da03945200f80003a560b001c3c01030380d0282c2c5140c10a280c8a081a00c104000c480780151048a00c000c51146100d903a1800304404468503001301340140c581c401d2146412940c8144440181107000f00c0400c040b414020301c0c031450050340074410002c06151542c0b00d010050f691124041c3d07055101c10381692403460600700071540000c04100104415440707280d606415001910350052054031a002888a81041c1c081c45004042d51500d05104920b03080f01d03a041d900c60204541040360b210145142408200800c6174011a4041c50400c2c050101c00c000a4a800c0f0903107107194882004620249414028040d012010041e241031001d09110402000003045211070111003843c01400c001518280900c8000001844a4060a0000075801b00e0070304548428161b40c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 760596654 1250 760595404 760595443
    0x32d2e0207050316060612030c0807020a0b0403030305010305100603050a020f280312050a1704080912030c070b04051005090d050a0f110409170c0a0c08030d061208070f060e030d020c 80
    0xa0119902009809e5203a4005800302c4d0b580042d400418037440141e00400002880040d000040550680c07000341220b02480030b441040780342d502c140f0280c850038070002d0001d5000c40701040142c41c2074108854407160040507251030406000d6804024107900500c1050148110f80810a219040c070014084c1c1e8007915105180014103030340a090900b40c16240c4040d41e00c8400001c080010500480d03580e141c00601c0f108400111580550784d0368422172200c5a1405254030010300900030909a500b40d55000f0702d94181c0c00003803241101c00d80c012402e415440000c584030000032440071b01031803608a014040804a07420981030000c10f003030030080164007851400c0d0f20078020034404001c030211341440480d419600d491640c00c0515250301e02d60040d002c00b52100700000c11040000040c121104100d20a001d82c51b0781c2d81c40140b103002c5021010b030000c0410000b080000d10404d4003898040d00c1009e000400743c00b10390441d80355400c1084c1000c0a07640c002072441c40c1c0030f03040000c41407001000c0400c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 760597904 1250 760596654 760596689
    0xb0a06201c09140d0f0b090708100f0c0e100f020a080403050109030f090b0f0904291311090103111603080601080a0504030c140c032d2e02070503160606 67
    0xb00c07400b84030f10300085c0090301d040f008540d2601c0240709007002800414210380210b110ac030707003280c014180c9500b00c14101e8501494003a400c0d00a02c1c66000c450001000348194510810054030380c0d50300c0140d8401107001d0b00d00040c00003003042011384051070003100005030054cd64075010b8103007280003402c00c09011840c04100403804d204402c4407609000540325580b149500d9001c41c01802c225030111030002c811840c0074508a400c0181420b2840003145c06200729a6109020b00448000118845054404120500c92035000f60000d90f081124041d00710302c0c0c00b00c0c00d03041d00910307100d0034012070004d04c0e0078040c02000e41e8010482504100c65002c02c006c030b401c1a6a014114a00304200105050b241d5075126800070010300c1291740c4484060251280410b0540064150090700c149507441c0c1054030416102d1007200103681b08041ca02c1a0603880b480c3c074030585000443c2c2500810160b10303a0208440d0703001881c00d0002e0100e060b403030f2540700a43c2d0203c1c0340910584000390800e021010041014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 760599154 1250 760597904 760597913
    0xb03120c1203091c0311071a0c0a09150e090103081801090e0a050a1d03190c05061305031306230f1206031603080d0b0a06201c09140d 59
    0x8501c1340940d03c81c8201c002d44c4041d0b003036002e130070315038100d0780c01c1c2c040825030340d0030b100e4410840e615031542e0481c2d0100c199120b82e07c414160280c401a8400a00410b005214186540b40c50039200000390410480040d0041c0018500007002d8004503107601000c0342e0b600d040d100081d0240704640302424815501400c11381303903180d660002481035400d1915a00814204900c8e50f1201c00c54804990782005800c0c1d10344001c80d501d510140a40a96420301d40440b41002d01ca203031003d03491980180035140584905a0803102c402c40000107861354001007051041031680e40c00b9a0000f080c0d25101c0b0103010b040c1b0400d401d0f0800340000d51001ca400100403220500e000c0070115103c81c800140002d00799100e007000709142c058500c4a809900071690400b1045c00b840d50060079010030361304000d200318a0203609002901065215140100740003030650040004410048841c51641c1011920001160103140c446503540400940104902e008140074000840c501e801d080e08059030161001081c0b543c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 760600404 1250 760599154 760599163
    0xa05041d071d150c0106080606150a081506040909050d080108060a0c1803050601170a0c23041b02210d150e040b0f0603010b030606040b03010b03120c120309 69
    0x400003441901104110b00303603103003e810b8881018140c80c59032104002d4000d41c0c0208024028102d440c4580000212207282038021440004210070045090003000c102c10f4600072400b41c0002000e24160b0344400e8581c6075000a0300003043c0c40000030450001605040d820118400e444204001d0001c0c014005a40e000460341d412616a42e000910052410022662241862008010b05030301d80320004c18860000f6443c0d06952090300740600c280c1807841440d43d56081c21400510340509071a0030000303200604180c01e11833102e2440180d108c3c40410020b011640703042c501d00304000c001c10380c001d0301e66410041401034015000c1240030030034012502c00140c0c00340c02140c40c41203483d582c040c00000d145040b003034018850805092041c0c00d09140400c0303c040220341c40380c0312145481c0000c05074941401055000c1d43d003d0043d103816102c00c01072001804014000e01e800d0740d00c40c1c00c11400c94801304040650b03008c4400c003c42d2a902601601360a196040b02900010401807042c0140c0c40000700303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 760601654 1250 760600404 760600427
    0x110307110a0506280609020301081c0f030f0905030304062405031c110706020304061206061709010615030b120f100905072402060606211b0a05041d07 66
    0x83e070b0a0383c01c2030081301d0601080e580a00ca4491074180a00081ca0034410340145050782ea00c1003d40d902a4401e00a04c3c5019141d1040c0c03400081200c80c5001c501c5000c0e60210a16103c00c034004541807900e5142ca80c034503030058804450b1079540c4c02617141d201078882641801d440c0290b0140c03d601e0725200000e69039861a40300601c4415080c840e0807400c5001e0144d0004000824095a00341955140080e4903900302d0701c15100414042e01510b944008184101c41c144d0f101a1030f01d01c900c00502c0310b59605103000800315100e1350351700c12001ca1040c034664540500c421447d503020460140c031780c003440300326020720340301e0001640500aa40d1030600302145a02601712401c0c4005a4018103040c5145400c80c00d42c03100740c03d010111954403558254000c0c00d03004042903001c481003074a641307040c07018038403c18491480c0c040744443c0d00542101c100c800c454216203482003410350b007000350300c51081ca82d206282034070216074009420844903c605403000010810300c0380410f0140340128000c0e08440444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 760602904 1250 760601654 760601671
    0x4060f06030f090203160305060604050c04060e010905040e03090a211202070f06050705010c1103220905180d03020301150302030a2301080115050f01030b060d110307110a0506 77
    0xa0b5095082042283e00c0040002e4004003121400b4003034000352503483d6078a0106079521300403680050142d08060241502880d20400114a4103141c21000c0f609201465081810010b15540001303680d0b03650b000703000310a46880040c6176503031a07040c100424144582d0140703580400300305143c44c00a0111560104094100e500c500402e42e24500803420034507190842040040e0352000400c0e102e92020180201521500007005550380014003503412015203140344010b54410807c4818101100c088004082d50340111240d0f003580f1180900300390303401255900c0c110700070003d9800540344104a0b150747c0100e6410114915410243c508002018a034400d4040c11b4001011401402e03071580100c0300062004060240c4801e485010954940284151130344c640c00d00000c14060403124031030f20212070009010201c82d40c4e2510040d0080d05c0c0118065601940500410007551640e0240ba030000c101c00040f42e59078908940081c000c0c10f241103618246900031009100050703000075915800a14a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 760604154 1250 760602904 760602911
    0x7060309120f120c17070206091e1203090c150406080112021c05013303060e070807120b0a09020607060b04020f0a02010b0f03152a0c030a080604060f0603 68
    0x200c102c01d075119601e01c1c11842e081864085a84072041c2d100710708a0144074800d400059640f1002e00490350356030b042c1c894200d02d8021041d908a080b840b2100c201590480209075980342008100076440d60700125000503031a04884520403281ca0032208100398590512072150034541000d10050040f07505005011807084000741e10015540d40d44d1486020b0001d600002d0400e00981c40d0030360203000300300182c0940201c844e422150504c110942c280d501000b15100812107032854452002400d903000005166008010020179030300320a01800d009020614411074094500c4d15208080c060020600005c1a18010403203006944403c01c0740c602507040fa4002c5140d079002d00024000740700d096201c050400e030003d4520041c44c1c040d0014848a001100d4112100c401c041c107154650080680a0402c4114070340042c0003011040742400000e002c801c4000d85110001480d00784a501050540c68a070384040303a210001036000c080702c0d621080950b41840714038030b080074103402820107003d0fa2051586 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 760605404 1250 760604154 760604177
    0x403030e011a0a0503030a080c21041b050a14040f020c060117060702060106090302102709050a05011a070501110304030903111005160813031a09010c0801030210020309210706030912 80
    0x12ba010141540c440c5040e1481041d041601d01242081d00d05803400c02d810071820400140e919200701c40c0c00441c6d540032030016802140350300b04001021255501a02c0650074442c081c00c8030400c0181601904000b01c0407004c40b40e059031007910f4036400801200440d4841c2c001800f81c9a88144441c003101e0303064030501102129240d007aa0541d0305030305402c8060748040080800380d4240ca00c0b220031285802030400664840341003e4003070310400d01942194040d64203060750b4044c1040010030342c00b0b0180000045200152520b6403907030340152815400140040c0e014030500c102d90a01d40c3d0000710840303101d914040100d0000e801c40c02552541e042e5414410940c00900c101c00c4203c0e11030b060700f9101d01c820181c0782d1038400302030795881254901c803001c100000b841c07800c0c2c14840e0424518035603c2d00c2c10240e20716820007070981c8001c00c91104600080c044c208080e04d403009078506c22486d80b0f20b03d04908901300000f920b0a40303560f020004040c10011240301240d4602031a5010384481d2074100e90040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 760606654 1250 760605404 760605427
    0x11011803050705301c08040f08092d04050a1416020102090303030a14010b0a050405060a0c06050703050405060618190207081b0c1f080403030e011a0a0503030a080c 72
    0x9041c1303032100288543e0104c07a00e2901000c00d1000c82034000d5802e05e059908411411507031098210750003403652440030022030209244402402e80504000d00c01d58007020028070a610900d41c40850715508817560810042900c0c140c026150b00852080d820070804544038030081e207910340505600321003c05100c845000354800c1d01112103250010302140da80b82803681c0c0c401c0040820180011101350300c44004070b42c2e000307500110703480840c085c0c0e146800d017400d08041001540c0071201090511400c518a200052414010588a00126100002d00c5e180500342a400c2c170800030038052240e0310070505081f003010f4100b82103801038045003030b201d1505d001c101c10400a01c14208060300c200804116041c0751000c02c09548a503419000035600100321000902110550031440d4107800001e5007041500b0790300c140b154560207070007440e001c2070460881a07400d00b140c2c0711540c20140903001c40029080c90400500d4030004000540c011031030001c0d4031034010080c00c4040d1000003000b030001201031042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 760607904 1250 760606654 760606699
    0x3090108090327030f161802090904030806031605012141040f260c0a05070e0408030f04030527040c020109050309010302131211011803050705 63
    0x201c82c5448a18650009426902040070030a156109114005c034000c0400c1020400c052098251141404c1c400d0038410203010203500c0614420746a6400c0c009505155180c03923100340503d000b601c4024050900700181402d040d010b0301040394030951504108500d0364011800391090811031a07800301d80c0048000c0402400b118030040d41c5423809a00c1c2080d4850106070300070010749688018161200409551002030701044402401042c103206400000c1881c01009040c11032603411720b24644162120581e800340c101000e1001d040d4880104002001404c1000c140a0400300d901a01030340f07001e60b00c503440340c40003c201151a15079480481c00301401541684c9440c00c070183c9900e491075512011086200c8910341041c880c0303042490044445006201d140005a001406140340c01c145400540103540b00340070510742552030460001345190700c2500307145260f03c98031300f12103000d400c8000108a2240180351480b1400c40250400006600185840445e0011784603050b1504c044511114107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 760609154 1250 760607904 760607917
    0x8010605130e010305240603030d110915130801051302060a0c0501050a1506080712051009090503030912040b03071d06030405070f09020c061f080a06061a070302030901080903 77
    0x102c26110001000704400820081c10304000c2120121101e0300314240d00b05c1d036503410f4a00035050b8204001da001c0350340d49600040540010700072054030340004c0e0b90100300900000095800d1420011901c640c490203804002002400007400074000c5041c204200e26031280c40040c000c3c40303814000344030700e5018000c00c0d82408484e0000003c11507440e15041c80c0c00600b5068107001c031000c82c4014046082406904aa0302540b510341e109135445040303c2d40b9600421025149551500d402c1000040903041c90044030400341c0f08001544d01c1e41004e0700a03a10340510b0f8002483c1c26442400148810005c0c802625405000e0740b4000700c05003802400584000591542550400000030070070050220018401044554101602c928560b03181803800c02c90044074080c0c001074001300c011030b0300d90504020b501200e1000500f6590007640d50407000b4038054520100321072150f2203c0e010003440c400c6000300c1c10086122550180791903a19034009440344240424039052004480c0481ca0001c01041560503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 760610404 1250 760609154 760609169
    0xe011209020406050a230406060e12160b1209010b01120209010309060501170c010f020709090510090b071d0a05010819050c0705010b0a060e0607140328030c0801060513 74
    0x21030507107560610700b00c5104005105131060a06c801c10400d828a44111000c844240c0c0e641d401c62100365040200c003020780200d007440e9100d41204d2016902e010514a801040f034441059500c1d1032250082c12400401001003451b2b915141c9240303110303600400208d07403d205041005944151390801070f401002e210304d000d4002803902c00007145030007612038402c400d0010041155581c0d40c0020044a081120200740c03401a000420100207112442d0400840b082c401d0065603902c03048102b02108446807280c0c155014261802400b00b031680240404c07003001038540341d450700c4402c0040840d907d2151889542e0401c000c400c0050010301c0100403071000803807165420b00c11400c0c0802065803d800030740c01540c5a501c0c2c8540d441140c9401d014502c121400d544808814403481800c00c4001c0d0004001501c8882045290300300c4154240020030145d141c80340c0c1042c6418000440040340240400840141032902001c1c0c60426000162a81100c086143c59591030546840040700610560b02802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 760611510 1106 760610404 760610419
    0x110f03010b011d010210051611030306062b0f0e07050f09040f03181e0504091113060305100b040b030303220f02030d020a0302010c0e01120902040605 66
    0x51440b10140107848222003006c8802d42034a408807501c001c5200500c00b40790210703421442a99244c01000011030441c40c018022648910885c8842040a00b00c880081070f5031003200c41c0420601c81c0e21406104440180f010030300070300b10001241daa140103260b030200c0d581c140350404854841001700490302e241c0361a2610804206940000e07000c001c01c1281c0c9124104212184134020200007503a5003100c5104113680c644070b00140c004c50b12842c1030545a40200e500140041c026000485d8001054415240310318018038407544010300078003502c45080511403840c0c0c00705442c41010381d0140050303106001007680744d02c0201e82d14807442202d00140190348030304c0d10103030f03441c01c0c07050600200c0c00b20305400091812001e041ca807001a400382030b68104041d0b080c01081c40d00082818005080703c18800080c11b001603100d0604206996080712405655407504504000e14000d000300 = true := by decide +kernel

theorem cover : BRFrame.Cov 760431654 760611510 := by
  have h0 := BRFrame.cov_init 760431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 760431654 ≤ n) (h2 : n < 760611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
