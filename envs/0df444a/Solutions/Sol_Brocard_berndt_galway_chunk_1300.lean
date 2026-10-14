-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1300
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:15:18.42352+00:00
-- url     : https://prove2.me/submissions/919f1f8b-8235-4426-a479-886f0635b572

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 233633093 ≤ n < 233812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 233634343 1250 233633093 233633119
    0x1081c0201020f0c0a0c0803090d08071502072a060c060b010c050f0f060a09021c030e1f12140a0b12030301090b240409020313020a060e030106080615 66
    0x640203004240d900100150f00140c407000c0d504000c12440325080c402c2c0880c0d00c4684e1201e60b155642d002710300340c0b10740000070741d40003001040b03051010f000740a200d9254102540310103a03020050383c02500c0304403001190b8030031100141c01c05070a52980c0c90b0a01825522041c50b00d000104007016018001d01180d17500c5c101d0280d141d00c140c60f03c8101036042002c0f60300d484040d0f080166510310214206e156402250b000c100d00d00401e00a0800700398008004680409480c0340090100400090480611128080c440019169406020b203009800003070208010303200b070006000d0813205954003e100345040a081100340b160700700e045d00032030101c100203501d40e580ba02285506011482e1841c01d44004400080c141c0f02a4000c1078104074243c030f10754140503000440c04940c98a200a00020001c01d00c414494803c541e4083d41d8059010070030300500034119000306118050640282c3c0001d1800603088140d418240a40001030498038014400d41c50900c0d10306240c5504198400d1003800303881c40130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 233635593 1250 233634343 233634347
    0x21060406091b06050a0e040b031e03040e0a060e07030903020d1b0204020706270c030201230711090702030703020715020a05030301080f010b041802131b080405011401081c 75
    0x11124802c1c2c00035070781c00b1592107800c080c0054120030015400109110315212403420107000d41c8906c000040c00074800700d203914290044040ea070940c4001181b1051200082d45c4005c0c07d0080d02900030310b800042c0c03d83c2081440040c0100c010490003c0c18208910000006d500280a86500701c0c20b00c0c01c8415500418480310204500c0c8001a62150011a50b45d0900001d0703800042460051040004d20450f0142424035a11340c01002424528040b0010009540104035030b446400381c4a14002d240c0b0000c00002c02c0d035030402c580596405c0364a040c000b09a0808001858016019000031814404107942c001e6036224180180c44c08241d0103d08103065500801c00d29040c641d20100b56a120340e124944a6035400c02c09580f1546903090000000144c2060b101e40c10152442c041408503013040c036002e000500709040c401140590303603103581070300d51416811300c0c00c403030510f41d901e00485051505006095039050113100c01c1e00c0d4540703c0108032a240004482010507200c0c0d10f8204284610041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 233636843 1250 233635593 233635613
    0x506010c11041d15090a210c02131401090e0705040209030c0d14070b0307121d0607032a0905090a0207050a0c0e1018090f06140103022106040609 64
    0xd003668421082c0000b100318040401c0328a50250300f56000c030510395492200703d54510002c0b101a00c2001c010301401003005070000f1200403100ca5040c00c0309001d00944c0490b24041d007521080040c50350b680400c00300145004bc485005000e00d05c81845030703a0840f950340f42c1316040c6200e090b1050f980041c100380252000e0112102080e002007070034100a009043c5409099004071a2041381d014880001c0348060540003a40e00410107036a91510f102c02d0009803000a000d21801e504448003401400701c03011204215203071240c0042e980101e180c0c5104040030742c415030440388010810b081c400b10800d100703501a44410880320103c5054505807562035621f4028820300e0b42c0035209000d80715010090110f1310596000f11450706511a40703568030361524421700c1c2c145010381102e90040c0f80f403822300030103e0b400140c40580240025202c15425035100011a42c0581e0002080614034004100390326180c2e120710184c0417440c0c03a4206800c103c040242e00e0344401007008000c00c0d42d880c1d1020910032030840c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 233638093 1250 233636843 233636861
    0x623011a09220b130e0709090510050702030904060b2508070807080415080f0711010f18030e0105070317040f0f05010b090901060803040b1e04030c0f06030506010c1104 74
    0x1207615140c1d500b0b10000c10180140d0070f0000d0090030b01040b116022806480380d43c281034200c0c000340900d181460f01c140042c21510009651501c41d10000528101d898410103005020783d03001140d0302e12203402444255a0140e001078034071b89091105000e41d60250ba803040c05d2085000a404102166251249280c0a2940302070201400801c4403010400003100410645520104881503041c00d03000c111800c0c0d4044882100424046000ca51070a0103010f88613003440d045800499200341c50341c16070013100c103921079820814441f6a042c0040c1500701051190318002031070010300e00501c589000d402603604141c0404000c0201c1700041c140082c0c160b42c50005544280000340c540070a040c954041c001100c000340c071039203181000ca290703840c0c14801c40040340d5404e405141032500d000380d81d0580d0b07041170f1040c00704010003000401058103184010005107114080a925880c14604140d8900840741c000700c042c1807800042c41003da800900c07100d86140d110800c50280e0308140d000c00c000c0c0103801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 233639343 1250 233638093 233638129
    0xa0207031202010c020c0a03020616060b120a0b060105040b030c0306130c0c0c080f0c040509010b191a0a0c060c020a02060a030e0609070e070c03020c0d0623011a09 72
    0x210312018402da06400140e0a41007942c200c0341307208400802c00401504c0f51000035808901044440034031400d43c44141501c0d03004041c0014020944400308411840c10410052140c0104554500704004e641c12035400500070b182147c2041e00f002041c01e298070001e400c03021040300200001d021603461034009407005080c40c0042c010071000c000b0152420385042411101c540c41042c01280c40e000c00602101c4020020740108100301d6403400780030003884084d181035045d54840500b00460b423120f41d6524180c1008844a503502ca28110400710100000c1005100c514800c21071409556030002c05d0003842604010001142203809805a2070968072030b100a400c10008102e0201d01d903090303842080d1801c0520162407890307071190209a201c1240b070241c1c4003d2400340d00454400d40c8540c00103005d20f03100e801100c11054050f40098010340386494111101d42d169180604060008110505c00084124911440b9410010088580c00c00e0807180004000c0110b88854541c1d610366180340c480c4020303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 233640593 1250 233639343 233639363
    0x7050111030c01091203200a0e0a0509090a02090c09180c0c010f05060109050603060d0b0612010f150509060a090c02010b06030c0a080c0a12090c15020610050a0b0d020a020703 77
    0x6203000e10403002045c040b00040391824003480500103400d0441010074035410312542c0b820301e82000603141c0f2500041400e41000d0b0a40c008241398941d03051080c016800300c8010102da1381144104007101c0d90007004003490140501450400d0b442c2d100d0034501001c021800b00080b035941c00c0718a1194000da401c2c40c04c2a47c20285401c03032102540d445280109020790352078003000e03216001c4c00321a22096944a80090045003450b0118406070b01d841d400c000300401100c040c006449030a401e4481030152030200b20f43d1000c19426038408943d420740244829199440c82d440c0c0800045c0a425941c07280110441d105c801c0d03442858800c1d44104495603000b00810303101e00300030520f50301682106803040045125540881c04000500f000c0e210007485e00d40d5060324001c00710a02c03202422004004450091818a001c1941d07184900050070508450b030043c205407800000325030203461154001d0b030180d41415400d200c0443c4502c00c68070300e21003c89000d40d450501d440100d2a2144030b50001c0c08103141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 233641843 1250 233640593 233640611
    0x807030525110102070603060602060610031d07060909050f0a0e1c050c0d091a13030c030f110402191d090f0f01050613090c03060308030c042607050111030c01 70
    0x98100b240318402070382185d801984800096007110713214090b0740050790244000609501e03090b0802d8004090604c0c01080d42c25809141e001d0000c0c2c8248092003a4105103c140a900e6120884a0090190220900590a1801e0342451144014000c840c00c2c94981542e10001c01c0100880b14007035411140f403001b130400c000b4004103aa009102841d200d40101c1d209019558441c40610090721001f5101c100d0000c003001400745158080f8400d0050003103100b00000101c1d140200c442c0085001e00340d401000c100900d071a08461442d4060b1601c500c0c810f000301210315039141d00c0c3c15640b10103820510b000040030000760001789500c5000c2903111640d0020020441c00e43c9024034060340340e9405240c2c41d6601c0d00204a201d02408440e2a1000c001c3d40c0100141a1513070041e010020150900044e825129284c100302c5034400c481080e580300300000e0804c003064002c55900945003401146403240ca50405d542912425a8230a072410081000c864a11594083c4201c03040c15a210f002003143d1b0711 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 233643093 1250 233641843 233641853
    0x90c15020a03081f050616050618010b0d03050d0e010618091b120b0c0c060406150608010308040302090603030d02070f022e030203070c0f05010222030807030525 71
    0xc074421040300000c50300c80c0880c000403e415400c2c030210b004401103802c1181010705000d00c54018aa4401e07407948030650200204100703001d858003400c0d650300031207203a2600000260941e041013421038007510b10088000701081e441802d076804040850b50108039294041100d9025003240e1300302414041001e542d2104040c601d900c510340043c0714250310311441c0a0b00e0314680010540340705142842142e080301d0300010300500c0c04d081e801020301c800c0c6801c004c00c0303141c101d1a000d0308480031110349a81d07020001c0305c4100d42007528001c00355450604032030340c110381d0b40340f000c0e00491100038020015103001c035905035070074802d4403404100c1240c00c64903010030f800d14074034070b800b20381040c0c3c09a001e00c4100d4009500c1040308412042e4500a54014007030701d07480c120000d500092070402000380680011000800070360001c610303e030280e0000b5854030800580e0204c0e80341c030080440341910340c0f00707070820000c0c000c0002e4540140c0c0500b459a245c1001480b0420490401d015141251611044a0040003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 233644343 1250 233643093 233643103
    0x7030614061801030803070c02060c010c0e030f120708090a051009090516081501030e0a0309090b0603060a0303180e0906040606051e270709080f120d090c1502 70
    0x70100c4454440d90401c0d040941c0944082c040030740207400c1000000e09181c003c80c1c0c13202c420b603c00740c02181b601111004c01400c69a091920b040000c03100800041d081c5001c10030010241030130000f8001100c0354048640c1e152203041c0740105000340c0401d00048036920029920002d00b0040d100300ba01c1311035200d00a24100407800f036151914902030105802610070048034288a5040c0ca41446507101d001d03007188050f4103c0402810152200780e401078141c424002a181107120b5100c0381d904600740740035a000e403904060184d0082005008024030f41c0d8540c00d1410480341c00d810403005c1e425500c0d20513601081c0d2038000c0d915140e02e000c00e2003498080001c20350b1041c0e0080e00c04101598680c42089240312100c41c1082000485c60034030055032a108102c1102c000c524503c1003181c0da06078105c00c0301c00c1c10840b00140401c40c1e0400411140c1414000016800e80c02006844a924203010350040c0c1d000c0d036070080d000c895480d01d035181081000b00754003000c1d0600c0707c40c40500500c4003800940d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 233645593 1250 233644343 233644351
    0x4021504360c081905060d14280201112b1202072a0321090503010507020309090c0703120f020c01140118060305030403030c02061209010603140a0b1807030614 70
    0x44ea2290611034103428003403140c2c1d4020580104446102c80340c58545004055003a4135054081c00789030707112460300d400c2044810100354803017054416902c039800007509030101041d00c040650400e03c50542c10703a40010020700e0701c00110000c2d51881401c5a804c90741c0c1071503001c200540070300c001400001e001c01d10340da0040d008015000105038040b450400b07011a041440010301c00f100a061030120103090701500385103800782d440c4c000406aa9140081d094034400d40b140c00258000141030b288a0030700d00300c490ba004901450a42c40d003400c0e1f940003458400c2d50004501d0340d550382e141d404640803103901100d0b00d21400c40001e0082c1d520400001ea242c060a2140d544804003030301041c52405000e0085000300c0b038101c405107003030514503102900d00f404841310882c0d00ca40c1c02c01081c3e801602000342ea40c041c1407800000201030781940761540001c99000c00b084525403250740c03548000f40c6000c8801c9e43c030100040c41034084030340c5149007038904030560f01300600c154242020384000346140c1283d40d05ca = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 233646843 1250 233645593 233645611
    0x6060905040614010c06112b1d06061e030d0206070807020a1e06090f05030705011a0f10090b0706021c0c08010317070c0b0304021504360c08 62
    0x50181c1d80c2256a915801c0140001c1c0840e203130403a0310000c51b28541c48144002101c142e00c5103002005c001024014620207561804040c402c61000d1460a841c0705d01600c1c0c0015034401105522001402a50f5040c010407131485401400c079445c41d071568010b40c4403003012014044804030300f21203c0207074444904031038540000d040100042c100b03510004d00501c10390380100009103030890341c03e04250890441c90095917000e85400c4030780e001900c3c2d07040d0040b58a0054014503203405207841d085003903032207440c03820750b640280d503250340c0d016507840300b5410f400e60382200d030740b0700c011a42070082e5007540e0141d00000d140003002c82c032101485650b030000e151043d110b42d0f014103440c3d48401d0f2001224800d840400002e281c110060000484941035841c0c0384101c1c004d450306103c0c00341c1e50f005144d01c50350003191484202005100441c1401c01e111700b1140264851242090300b400d0760060001d910100c01c0c0e0302c0c500086141c950724115001d0441904108001c2804041701c220b6001d02050415100000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 233648093 1250 233646843 233646851
    0x406091703010801050906070e0d0212010209060a0f0e09190c02010b060d0b12070b040303050f09031006080606150d0b0607050303071701120809010e030c090a0518031306050307020a05010606090504 87
    0x81c003c9e1013410b40c9042810001c0c201d003c180d01503000d200b100d41000c0d03000840c4e50b500304160306480d0349070806010412025a00d1500c0e01d4410321000301020800c5840a019260b01d2041c13181c01d070907117180b00e40440d14100b400a803442108200701d008d0b115042849400407400208002c0140e40c036005521000402d4a661850320840a000759450a00d4810a06140020710040c40081d22500040c000700c01c1c140c84503420242800700103410451450740008055990b1902000307814001d0150f0b5900040c12103a541c000d02c4100f03812400b901c42d480e40c61140683d14481d508030740e030700d0343c0c10f50304915044001c8944a1500031809443c0c034100c4101030415101c0c0100005501c04104100c000303050380800d0650600c00100015103032412100e01d819814061000314600e65211403002603c0380015040100e4542810498040042080000d0510702c2c6c004001c40c408071005c01c0d110340115031142c50020b070360350380c1d14400300d0404081c1e560041055003403c07800500c4590008100703090b120100d030104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 233649343 1250 233648093 233648101
    0x606080105100903050312071808030d060e04030207141c08090a080307030512040c0519050a0902040303050f1b1204080d2c22020d0e06010b030406091703010801050906 74
    0x80c400c1c0d030b0b042c8001050780e4030811420308103240207107100d6000f58180c14945040c0c891945449c01c003050a41241406902c081030b002c6140c801400380301c00800150340e444500c2d090a4034002d48507600c500030369408140c44481005151550114005445412038014a01190300c3ca00000c00340d001d020a28802e4000750804515010003100721402180d15846462521600c51b4060880c0407000300103071006040ca40000815454007990045a002104442500542010100034005030b058200c5400c032481440f040c00020b8112044808400d400c610b41c1c0c3e2610380ca201d401c03440c1c9640700d09244240c0200010304da820711f4420013070010b40340294195840a4082c81040b200880e0200c100c032104c0c40003049580303104080b030700060403040026005107040000e490300d13240d1103c0500d04c204503165000030440041e50451141281c0c108110026180e5545840009241d9010203000684500c0c4d592400d4000c000607a0074807040074015a40340ca45a69440f0320316030080004881010650003180002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 233650593 1250 233649343 233649347
    0x501050601021f0507031b030e0f030313031803050106182003011502100c170609010807053d031505030601090b01051b0606030d02010e07060c020d0204060608010510 73
    0x104810f0742c010052840002e6111005800b42a0141a4806240e40c40d500c20400d005d45200018002c500b90700c02141007040408007038580704c0d00f0302d00310078513400500521030784000081030030720000e030140341c0003080340088000c4203290046684024800c1d0701c1d000c070000e00c920007803c900c5000002c8420400c540c0462a02075084007032074100780c8180714420070051088409540840311074500a104a6008605941c0000308a17a040311018011400026502c030b040c119641095a009030140c07031080d215490504859030f40c1d1154001c0364401c5885c414101d0180401c442d41e0340d080c43c0449020480c0b11030f400d03c111501850418400c000030304005445250b030802c500030b1030441e0070181c000c1200e0303881d0206900050918016050401208012122055061309034100e1414030403409881107082240c200341c501030603246400156410160010808240130488408485803070030316000501551000404624403458000d50080c82c002021443c1c0e940009558180c0e11300340c0340050344188180003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 233651843 1250 233650593 233650603
    0x108060601120e0c0a29090d020405040f1a060406050102031804020a030605060d020a0e0315040b0406060e0a1505040e0a020d020607120e030601060e0d1709060d09050105060102 78
    0x1003940440c01401450180029941c0400d07200f403456030a49039080104000180206071a41c080c000720842c86035040d6240340000c181c0051202990b00041c6072007a85004200f507030311100d00103403080340d55000090a004962007600c00c0e0075031000a80310030000012820194140517078070380340100c3c40c0c03100108030340d40000110f0b039040849410002c07291200000f003202a5010400b54810107031242d80c00a040d4651034007130310030264407007809615849600340082004070b4000007103100750b00c081e44020103004d03034144040d002034010010011940c0c40d03080c550301038072440d405011000d020f00300304285a41c00e0382c0010908154146032264560b5900e08002c01d4501d069015149600700c1c10138200185864685076005038400b9003814284101d9480e4107203401c41c440c10710404214000101001d1746414450540500080d007000c5003541c107540081800c2d0090183c0040c1140ca42041c0c03017419920b150103451501c000100301d81d5450490040cac0c0d801514101500b105d0660a120108030740c4d41c00458 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 233653093 1250 233651843 233651851
    0xf060e06060a081c0207091419090803150117040b07020d0216051212190809150a0c090504050c0d0f0204060e100903050304060e090f16031a06041d010806 68
    0x401041c045020851048034a104d8162480179407294100002d07150845000d4034801d0103206541590782d190581001103501402a050001c0500d000c0400000030042c00689401a4090402504e0b841d800401a07501d800c0030400c410050680030704110070062130303084091040c071040d070030754400700e01c10801a41c3d1510301c10b0304a030302400382940c10303c114100228036400e11907825049074030349140e6588240c403950103045540d01624030074442c6910241c10201c0d203900b000c074410003013411031090700e914840c01b04041d09076030711142c90303501c100036042c032401038103015040091040100d0304000d981d44035a42d221440840b0014140f034491428441c4a10a6034201e0700b1a481d42420030200408001a101d40c1814801c20710880c002c010010036402c00141c0b000e090305403101488440040c00308a41c03004000c1c81c0408061034042004540c4403210b058044154590801190384101c030035048203030b000030308081500000081000241c40300068900121801000d040c20001d91b00d8681701d54648100312 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 233654343 1250 233653093 233653109
    0x10020312040f080d05042001020c0f030c0409050105181c0f1707020106060e040b0f0105070c171b041e0e0708102a0207050108040602090405190506030a20030a0f060e06060a 76
    0x20505500e043ca42c00c614bc01a80c001c083d1240f901e031400c0054125103680340c1c183c415a55850810a56140103495444a003000341d008180e1b07440c4ad03110401c0d1801c0d03003054280802c039016081d241e10358024007201032140d44c5000305180302e01d04440000d008204510075940000c444080803012070416119010040d08050302d60f246c080050401520540d00c002001c81c0c07448a008070029411001c0859034062503283d0005d0b0980400c0404801c200e00c581443d0170344510714280c94101407600e6034140d4031120042101c0803d040740102d10031030814246601a01541c010f80114003a83c0c00190300070114144207220741c40d9100010604840c648490301018000b50780491402e22583d0f0060b501c040e4030078400d61015240030b1030800420151081030700c1d154208c500094040442c1c640c14050705501900030b41c003c00380f03a0905e803590745c40c40c2030036210f00d40480e0610544810a8400f4005103c1603504150080201581840c2120081611a200549a019079804101e0525100c60b042e02124042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 233655593 1250 233654343 233654353
    0x121b0b060d08160521180d0305040b1c0f090b13050a060905030a0f2a06020c0607050415090b0708031e0109060303030b10020312040f080d0504200102 66
    0xc0010322207a840c0d00795064502c010240811004420070f42c8446035654030901c0a0801240c50400d404003001c81084c044550040600a4040c140c0c00d480c045007141c501103824000074030700c0e03081c10703105446550414207803900300040c0c10345402d02008810004074900703881080340c1000c2340450340c00c840c07070003400070146400500824000d4131080d081c20005401901641e03080c1c016542c500c004c44448000445841c1c1010030003144464001491040070b80f11400c0103100c0d041c2030480040c0c0c00e6960008410441d40d080a00001d02115606031190b900c85813048500d1390500120141480c0c0041c850822800201000300081d10310881006c000ca4001410290074144e01766108000382d00001c1c0080400382c18007540a0304562025045402481a5034001410f541141001000e81e00c0c0004040d004203c00e201703681d134007036000040b0745c20140c081202e02c50986852404610490280030301500c1044007050540880e91107501440c041c0340300d41101d00c681c2ca403061980d001001c854104601503080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 233656843 1250 233655593 233655601
    0x80103021012020403030e180721090501060807030203160f09181709010210050c03070f02150103080a0e010c20040e060c0a0e0108040506072a121b0b 66
    0x1c1180541207040003400d00802d8201001442d00490300309a00650004041f000328005608041528010680248461003020701e4400009450310700360403071a0074901c40040e19803014002661154005a910a000303200141d0744440c0c5558442a50000768440d0185e0381e81d0303503068914146c44000300d52502c0c40c401880b5207800005801054001102200020000001c00020300c1d11000700610a0305030341d0b4035841e0000780000a00c0c003031465a5984100e80b034001070003111041071040e281d2001a91800d916520700103c4101c1c14903070f03010f42d510500948040080308001d50350001c0e10079814a6541e80c005050518011525140030034800780012805050315401da503030303c4420005a040140000c11206c03c22003809140000c1140c0b8035a03070703000100c0c0c3d03840302c15840354000c03000c032a0034238040e905402c0686959813a41005005c03601401010313801440c09200041070b000c11404503142e03902c5c6030b000c01d0802604c0000c4400d860070000b002c0708a038075038407801d483c0880401e03a08034200d412503075a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 233658093 1250 233656843 233656849
    0x315100608040c05041803031b09050d06021e030103170a0c02040b120307080405040f0207030807050d06150507111914181e0f040b06010c0c0e0915011508010302 71
    0x160290080d070b031200b40e183c0041040e8989009010303c2171111544500c1d100b00604006040f1004035941101a503800c8103550810356100b010b000c182c800446590b0401080742c94440028401d10044900003040300804a0b0301c042000060f6040383d000d01c3c20200c074010404050720f01440b48010280200c1d20030b8034650054180b0764012004c51802070680602812240001482c540001004030760001c4009428000d50130940196055040c006105504218031542c02a040c144018148020024042514200c0c50984d420030300007007040d05140340584008083c02803140e840b090041e80c03984408090311059041810361100c0d600702c0c03c1c505010683c140f8800700c20704c2c6110700440e40e0090181c40290190300c2c1703015100c0e0064403886c03030420400710b411103448a0000f0040c1803013030844100c0c08000103d041300ea03101b60311050034a0006180340302480c001e003a50031560001180c201840003040101000020603000304e0950001c8003940383c1c1d880c296441003454400030140003036404401040141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 233659343 1250 233658093 233658107
    0x30c0c040f0b312703020106030501020408070512010501140d0c1d06040b01110613030e0901060504080708070303050702130e0a0309061d130b01022e051f0312180806040203151006 79
    0x10b4406d1001042443da203450305420398103e80c1040441e0380104078100301c41e18242c240d05450344010b000900256141c0070400c0707a001d0307444405500074a0130055000c2040b001c0061000582402c00c3c0880302103002c81c8400044135030440f03a06004910b03108110750030390b0048041d0000826458000c4c515503a610f124801910b141c00c20840a0110200151260341e8401020a000e8003182c0e43d80780e1928540201d69162824035801072203280c00c118018408294040e00b01c030aa550150f4400007038074100c8040c078000b000014100d00715070013040c0e04402059400f102400c2190041d541c1e00c000c0300660680200780b806801030306540402d0000c2d03101103030407103600b04603180c00c814010b403070210102d0070110310710ba111079201b10203142d0301903001038980306d491048581020915210a0f1510b00c105c0b001e03551030b0071031301010300442640c41d103020140d446420700110140204404075030140c0d40c0c003107503a5102d81c1503070224420300ae00d40c10b03e09184c2c080c04403648508949603044000392b141080c1a82c01c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 233660593 1250 233659343 233659421
    0xf04020c07030b0103050d0807050c0714010c1a0f0901060b190207030206280f0509040e070f03081c02030402031b0d140303070e0102030c0c040f0b31 66
    0xd01500c071000010802c0141c1190081d40650003515140303611150003081c1c040001c0280050001c28400166000c80004507032058424800c03460380800003240041c0d848106800000b04440035400203040ca00120f100c000f400340c18a03140c03002581c0c440125103420307543d4602901024100520030303400040241c80c5403002d0340526006641b81c032034a90b0049421540040e006840301812440d000f8103600c0b114181103041085d0340f07060303014040c0b07100005001c1d10034090807a10847d211404d80805000070b01c44240103000c01d48401c9941e0755203141030300d1550400c5251080b24a41000a511140c07654000c5a21503640100501019a10b500c150030246100c043d107c0e40001409890301c0c00600c020300c00b42c000300c00220007561280391150008141c03111840416045400a001005000e800011821403c801c1220b000c1042015240c0410040000c1c40d503c41d407202c1c003038075a400401031100c6c140c0400725040b000041d0b00b9180f00014010f071004140050f0440c80121503071600503034824446142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 233661843 1250 233660593 233660617
    0x20d050904020c0a050a140105040201090e07140418050609011d0a020f0307050414120607031e0f020a0206130f06020c030c071e09050906011e0306060603020702010311090f0402 78
    0xc00d100e1043c041e01e03122441c08100e4003517004415440c2408001c500c0614014401781c000e0255140c0355000815201082c49905021030440d80410b120f6401040302c004003c04603140b8680301c03503440703640c0001c5210700811184003e00d4040410700e242082c01c10385060310152100c00d0402c00015007100901200205152a580c0d0300703000c1e4500a40240c0300450003041e0980c0d41c15259400c15501c10144001c41a00600c0340302c0c404c0c440c400c0000c010a00c0f45e80550203003000250764402c00041303050700d403440502c0a10706140c040040c1c40c03030210703074040d2204c0d000e25030840d040d6954144a0f08102c00d00d8a00c050030900402043c400000c00c079800a1030030480340010f070303070815040e40000d902c1d1141c2500a4406221000031030307003805036000310301c2000340900c0c4010701c504c2c240030400a8944906006140a1180b822858185942039100300d00003964807141c00c024455035050020000c1d0000e02c0b080380080e080410154428064500343d41c0241d00040909505804900400c0001c0d13108064105c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 233663093 1250 233661843 233661847
    0x2060f040308030703050103142e0e0303010b07060501050d150f140a1d0a020d17070b010801060614310504021218190f06290a09020406020d05090402 66
    0x30016100b02d01071801240c2c10b0b1000b0a11354103502e04a880800303900460760045d801920056618520098551800240703c0c4503000100700030300e04400940f10180c05c4440c00e10002000145801c1e03150001c04882d40286020889a601e940407c00f80c0720903c000909280400c144400382c6403050b500444011080e1400001e40d503c7c0389400c2102100704517405c21410b1f9071a801d2a2015504500c0840000e00050141000307a00070b0f40086c2c0d00110303460002d4001111030f07203040305201502c01103400320b80e08601c0c660b06030b6958410050190001340502e04c0018001da4091003403d042c04103650b110049059481400405e260304030042800340c0f41c540a8a560304280003480e502d5502c0244500302489505001a00e0011180022104494505641a84800c496480510402e8600da1078654807103901c0801c3e200c3c50420001034403034001c1c14043c1c0070342030703260b62000d090340462003001c800151800f41440d552941d01c1ca049002d14403951000d41c218054020b9014480c00c0140303d81480100014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 233664343 1250 233663093 233663099
    0x8071707090c0c11010201020f0417031e04060f0504030b04030315090c0e03190b01050d031103040f1e032a180204050a080f030f0313050607021015080a02060f04 71
    0x4001c1d07031020b0729101c0c0442c60107003014090000d0712119038030881c3e0a000a5203410a641d000881920032032040590004140c0c0303048040329020700807910016a94031400c030040710704011145a503440b40c030a500105035505d040306001030041080d141203d401004640c2155110b403401d6018151401805c80404180000424000700b5407080070007548155844000c000690810325142c03101000e03c403042208440502c40004145890182c1542e100f40c40c14001d8990924080d10354043c1400540303400c1c00080b401041445017105290300707c0b07a40c203d40d416030140301907107152401540e0101500707005154410368100403214100c040181800d03500001000c1d950303070034041004101d038941001a034000030200706900d460007136600030780b14072406400c501c0000300a1703903601e02c2406452040d6101c040001800708080c4050b0042143c0c10100b07642c50341ca4451002919a000510060442c624003c81008150a02d10214095444c1c0310028444075115400b0440d03250000c0821281d0048100004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 233665593 1250 233664343 233664359
    0x4020f1003020408010c021606050717040909020f01080609150604080a150b060c0d0c06021c050a0e03210a021902070305070e0403052d07050a0b06030708071707 71
    0x100c031064015900141c03035a081007442d03800e4895400024045521454165095213440301d104030450b01c0d2414903c4e0703141490b203001d0852107100f04000c4801400447c00142c240c159421001d0220310032242c1590491041d001076401c42c1c82a51219040001440000c0e0704090050fa48800260028555814181d076200b010745400311440c0e0448061240d8158003a403c078045c0950309000c941260342e24104000072482ca96192603010002040000c01d21407030041c803005a04803854803802d20780c040c0142c000700307509a0240c40c0643e20b100c1110710700045010a60408401d03200104804042c0c0065100e41100344910270070081c00750362524ad400c01002c800c042026480301d513100c8103034014242c0c0c82d2842c02c141d814103503154001040802c0100800001903440f80440343c5d40ca500c14864801c106440d00740000611410300c66240d07141001440c2d00501c0000142d00b0221480b503031410f90180e4548060545071303802d600c0303441610703440030320144a85412400c2c480c40480340340d401c6411442d6201c0407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 233666843 1250 233665593 233665609
    0xe0c161104110d0c2c0406090204031202120301080304050d1104050f010602060906070509060c010b090901021b0c010503010b28050d0507030c09060e0a0e07050c07080703020f0904020f 81
    0x994003982d40e0015200c40d2820301030003080030096090030000c4000c0c400040c00043e0800d0140350000d04000440c100f440e50b41c4c0da921250140906143c2152166103a1411841d03070344441502d0f2001d489054a404000d10082d005c8074181c1e60070501a5050600e02801e10541c0100003038129009404040100096100d40c400c03a403003802e800d0700142c00c0d54034096010b0b0802c04003a0561302c050700800c00b0003195035008012110003810a03100950358601c0d10540a00401c83d0040140c1e00101c0c420a0103050b582c15005403042c8a180e01901546001c2c010480381d5405c0e100c1c4905004c208184010448201404040d05044480d40a440964001c0280c0b01415402141b11807012540120b0340c0d039407001140c81102e40c00801818204800d4000c02c0c80500480c0c0e8034413440f002c001e03c840030007803d0b80ba900c105c84003c00111803000c0580c103003c04080c080d81c010942e442c02d1842907550024403c04005503182c1241c0e00948180510250f00d414403040c00c2e07009005076048602c1841c543c1c25500e80c041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 233668093 1250 233666843 233666861
    0x501060b0f0304021302071a060f0a080d0e0d0b040308220b071124072a14160306050c07050f1c0306061220030103030504080105010e0c161104 63
    0x7405996440c051042004010000880b050914410b1040320001208201400c0710055110040401d07a60341c0c4c000100608494901543c01c40916031001841601c0010a11a03442c050b851300c1c55400e040c0340a0241e13001d8007160141402103061f0200f0f001c64007402415030400000e4001024080849801507130b84070544208030ba0201410040005e040d40c046100051005c6d2180a0014403020340c222070704441810404207c4481d810300850051801103180164821400320404505100180d80c40e41442401c0001e80391400201034102e151540807400e51440704080c1114200d26040d81c6810009280080a07150903040070481540451400c100c030b402c9086050004104c4495000e200d615200c00811342c1f01d00385410420244000da400803c10780c245c14903a800002c131010072200001d4007103501761090080b9031000001100381988000140b05032101e800081c400303a641c941045100480071036010000050a0051035001940200041c285034043c5521242411074800014105e0b0760540d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 233669343 1250 233668093 233668117
    0xf0d0b01030b010501050c151f080f0705030706020316062a030608010506030a060b062101090e0c011e0905150d1a100f1809050a0e060615070501060b 66
    0x100100b00d006514540548020720f006814403429510300c507980d00c0070b140604000794000c1d00040031442c85c80d68000d112004080b0145c01681d480155540b10f0b0b004001030422805040c1011032242400500e00040380c61560003589031008071b81040c50854000f80c0704445003602d680d95241c101075240c5400c1b155840d09818540506960311025045a50303562140040d40d06100400c032255502043d40e01c11107400c11400310f0103201c20350024000d841484905d004007000b0103440303c2410f80c1d40c0442c0741651b001a001300845078280d4400e654a45c8000c4074035000030900143c0156554070002c41220045040c1050000c16440300d002490314101000201d6803030744040b681d8084284a03004200b00c00c00c0c0c604000128540380d074003080d2018074070440310381402001c030981400302c5e10400408092451604c440405a515040d02c1c0001d03100c191142500a1304042c0c0d00b10000c0f40c049602405004001c0c941121308c0004150f601c0c00e80c01010341134a155503078590000e44485031100505a010302d207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 233670593 1250 233669343 233669363
    0x10603050126070612060e0406020309062a070305070b0109051e010f050d05101802010905040b01230d1b030c0504060c02060d0608030a020106080106060c0b0f060f0d 73
    0x201504144581050002d8401c0507404800d010304001c0100b05401a1007903407030300c28003401d48101c03440b01802035648402c0c81000000c0803c42440303200d074040d6000c0c0050707105840c10345e06c50700c03041c1e4051800010258000c1c0c034604040c400f0850028010500386201e402c103035040c2441c9440e0030040035000d91109514a0300c490820142d131004101e200914284403e46001e1941407440c81e0242018034060240140940e8428605120741000341d0705c8003c19403502842495409581ea51020307035841740807408035121880c045500c0c50305015034038460206958008400f009049440d9130b096940e800c034190300038200411a00c108103070086604205840203c1590380303004017001801c4a00d00c4006800f08123050200340001a800344000c140c454048074003a8031509000c0e8060020301c8158842e151a11002a690ba645501900420301721003074032000700080d030f0340d41c1c4042e5085070b08114001c003c6104140016048144001c8440d0000c10207409040394915080c00308480d4040813100340c8000c0700c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 233671843 1250 233670593 233670599
    0xb030a0f0227060708030f070c0210030c0806090906040f140a0506062107061d06030711210a08100e0405030c0601060201090804050618151e0c0a0b0702070506030106030501 76
    0x250400041c0b2810190788161424031070f0340b0707208000e0001404425109500030049140c00b80f0071001e910102d90010801d0103c410450000340062988451050100b005c0100240c02480c00016161042d2071803405001503950b1075480314803103100302d002240d1820301417007126040c400401c0310a0307889202d10000c01481c28904200310070340f00c4407101d0044c00b400c144250340300c5010105a02b0b04484585c2014001c0b260016565641e81d070f10710500e40d0301300318040304004001c0d900c010401c0340307115880c003a51084140d83d4440301403002080b5035880c243d001084030311181c03449040e045920901d0365155403080d90b2a190000c151031010359080d1040d500c0410740018224051004900401d100c0c0020440408a6680c412444c0034512805100d00001f00f00710030749050105a10001013402440c03084a030441d1015101c0c69040780001084286800404540500010049a903001c0d8028000c0c07010801c141d494015102c1b0007088481103000d0b0603000583c548030715015501074115900c01268640c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 233673093 1250 233671843 233671897
    0x1b030605161803030f0c0302070e0a0204060e010e0f0f0406030804080a0507170601030308090f0f0d030c020a02130510122009040f170f040f050a0e01030c0b030a0f02 73
    0x3410229402d6801c05085080000030f07004514190f034020b19040003041012141000da0504a0b1030344050240100c00f420441204410350041094917115202c0b0309001400e18011034502440c9000d494120100700011211403a05124005c440761000b44085030031074903036503a4582c50300254840c05013030b4030a0800350100b1900f40a4031000e00302d101c7c45403030007894a98a40e0f540c0da07070600c00074040c0511800882c44050f414092030740c00400d56812940c211486606090b0360b060a880e01e000060700d801868484244041100304180b07400401056004220009882c0184009410b07010302060031100040c01c070103590301c0d10040d07038020600340c6d5564490800c02f4100145422071140301d48010f5040200140c7c0030060801600d802c00c10440351030101001e512180c0c0f01300e04a0002c5140046000a031402a048052003641c2060b90070650700c90741c90481e065504001c8c04010285030048806101002910000c0d5501502c0e80e41c5c04184440320304082d00483c2c0c400c28042c2628000342141200c612 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 233674343 1250 233673093 233673107
    0x60801051e040b04080708040806041b060201020405210a0b1e01052e03180803010305210d091b08060a060b180d330b040b0a031b03060516 61
    0x844000020801d80c9400d944010100c0c02c002c00c0245590030108114007440356200640f00600f0421088030301e282000c1c00c1030428590b000c228011601962600800ca0030310600a0302d040b98005400c20f80c0e02c12282c103205071007a200704d00d140214450340d160600401e08200905015210b6100c2c2204150082c5132142e0400c1c8050f04491b0240c0c02002c0c2c591075141e10039004410402d500c0461004071030381071408030041e00316152a6503d1a800110b400140182c03440214101d80c459001c80c2d0400d40382c24240c11008080c4520314005020034480c2c08840d141e2030300030f2411540b103004c1880007202080300102e462603190304090400d0788940304000400d030a40c0300d1007002e400d0010000341045580100001c50315a4031050768001e003424000e1104101c00d2a0300c0e00400702c0c12295148407418144800c040c540300d0b03001500c0c0520b041484e190881e0425206a0b01d5100b406000062880d065848000c1c2d80c90481880c118080401c01000001c0360051003501c1c042e002000c100b008152211000400300303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 233675593 1250 233674343 233674381
    0x111040f03060e1b0d111005090909011104063605010f0305220201020a0b04030c03080f0c03010b090d02100210060501050c07060e01050712020717060412110a0606080105 75
    0x10740e12042c4200c42848041039a512213030000c0340d900d03041c2c4c041c80c9405400080041d0f0311075013018a1201c1c920242c0d401c0006002d80d01d4042e600d82c40a65034003c00703142620020810702c40020000c00042c00054422080c2180100b016000103110700b0081c00b600c00c0d404010801c40800d00e0b001c0c0c0c3c0a01c00b40d0b038040d00e03800c3c0e1940c05180612650411803c00c82c25115000100300003080815010003c590091100c1800203030401c4100101d842c041c107001e451940c1000c000c9001444070f50010300c0f001c0001010a000d411000410703800c3d603007460b480c5074060f0310260341e0b1944180c50403085001a924aa400c22542e1110b0b4040c1c20100f2581c0c4006007990b0b450b030455410710070217000c441c44509000800b0011070b40645000341c2c0c2240c1c41d8005071007901c41d0560184c043c0300080c00ba54402500001e0140407200c174050100c82000544040c95101c04041d10020f010301704060102c00511321900600c103114244405540c0d08500d15560001190506d42c40b41155035194000c12445004400e0040b0007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 233676843 1250 233675593 233675621
    0xb03040b0705091e0f13060806070f0804122a0b0112080d020d06031707021003020909040f05160602010e06060103150608150a060512070905010f0804050111040f0306 73
    0x10812641d0001d084061650b0204103103010460418880313030f0745d282c0103102c0000f010f400880c0c3c04410340c03e69000b41c5054014401c040c480c03140403c2c0005e11504e90314070100480d0b41c0c0c9082c15165a41c50700c200c52001043c60041001e5580300c2000101e00000c0c0d4116240780c0760417040750746024600803505407416408002035100c00c000490210f4058005c840300c136103000100507550300344041002c000b4034203a00f02911707a45103010041c40b81e0141900820300745000b1110180f09889400084041c2d10555901c990040501c40104000444500040c0c8060b4070400556444654058400c000a0300c2d5511420060303469100d100c10780101442000d4002d40203180a00c209120108111019649440b4840c2082203190000d444603201c0e0b4a11003511400070030a004580d0f80300c4c401410b68202e80e0f400e84103401000301048059000701c43c0300c0d04607841a11615800b6120b00c000781e491f03010040042e0703039a54a42d18444901d03003007034009201401c518400d174400b050945c1080d0044404145040348 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 233678093 1250 233676843 233676847
    0x504020f0f0312071401050403050c061014130615050405120d020a152309010f05011a07021c1410020304031e050d05010326030f040204110408070b03040b0705 70
    0x10722a200820004608403195194664840f010325101080d5900240b043d100c551900d41440100340e40f0100400008128001726545502e400300b490040c502248510410040e80724148809030401c0303941a160346022150000c0c84036628425040c100c0390215201000440001c0c09112902d00b4a4910101c0d05402c402072808034041d41000e5580c0d810000c001c1e1040700110191044000c1c02d07003140d0104034452046070340321401c3c44242a01c840098400f80c2040d420169140215401445528100e0f0b910020002c3c24103054050001194009002071760010311480305c08910f00b00140f800d241c100c1c841d080180c1021454814142044a0b00180e50320b014010024800030981c40003803001900c001160090360448c2180f0309603264410007100c00102c0d420703c07000206106000012710101c40024240481040100c003000b68103100c02c841d02c01c0c2e0441014089000760400764058014081c0240d503841c5415100c5030150f180210a070b2003001000000002c00080101d01904940c001103d400e08174 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 233679343 1250 233678093 233678119
    0x2030604200d020c070f0902030a060806070e06031905010b0306010e09040b041b090c09080d02030f0f090111070f1d0105030c090405100f050103060c0207030203062d0106030504020f 80
    0xd54030344607090710903044540104500811319000e01409000300411411107000caa50740e04c0c40720194008940380d00e0040d203004800580c004002c10074501ca0307240c680d50304600500210400c14940c101800104003581e8000b4215101e40e114070807a4080e1480c07072041d54070f038a030182c001030140e468241c103c6e00074055903080c080000c000a42658125a01106204540190036050b207080310103503004e99221030401d208501101c2c0c0102c2068241c600c2002541c0034240345400690b56032240f0450140c9000042001c41990020400507140c1160145004000e0781c1c6c5060400d890f19985401c41000a0703c081f004114a1003051800708a035028400b54010b15031410b00065250008034200d24090301014001508001052080030001c038820401000903190340d40c540402008240001c840e0280f9200d40b0045090001039180102d941c001c0c014211959026100c009231580000415200321141241c00c0c1801e400d0040c0c0e601030891070b9800140c2d031416004210040d2240c1001d6030007090030310f07840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 233680593 1250 233679343 233679401
    0x31403070f0b040501020f12070e0303090a0b0c011d0f0d17011202150c0a02150304050309011b120512060406080d0c0f0c03030810080f070501031a030703030302030604 74
    0x2040705030740114048925a4031801c2403406481240000c008a800c00190440303001e45a0389018040c00e030595072001c10181c00e0b81410f56034030400b90030780d6000428500c10405811000300030400c4100d028004100441d05101114111246400b89000e58000c0350282c0c214942c10840389081c03240c5860b1888500500d201002c44088040c010103c86c41d01030f107010001d54070b59101003442e14000d8a03000c1c1d60749185c0d00c01540c541c100701104070710602070102d141c101d03017800c001540c1c09250040041d40c41d03d004c5070b00542d503012046180c5c09040108804a00210b40310820b050716000c041d0700c4480d5203160800f04440c510100a082500c664981b03d0240410300000620650002090508031821003c40c18491518000d1800080048245510202c01c045d0301c00c121500620344401d5024045803901c110a8440c25003c030114910703172002004000d01d41c401d400810710b00d0408610304e00703c160a04046030900b19a42c2068011980010501c0103d0405202d50040e080060002d540c036021410300d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 233681843 1250 233680593 233680613
    0x2100503042f0f0414011e0e0c0405041d01020706150b07050601051903061a010f0519081306020c010c1407020112021b06070806040c0e010f030f02040f080703140307 73
    0x449805075400c10003c031540d8030b407540100000c0c3d4110090000661392601d4903a24000d0300800d100320031040302070002d100c000307440c1198000c202038500c13036041030300700343c1030100920340c410f00c1031080b0252540f01441c0003000c0c4000c0c010385010704400300301034400000b40500070405034442d90300c040c000c0011710302144010031801c4c1034843c100d9940c1c200d607085068030030000e09180c10140001e882c0c0040c1403416201c1c3c124802e48800e003038a40f01c99200503500142e42c1d501440c1e01f06255180032000408245214030200ca520040103829120841c40913200c0801301e0b0030500540140d603550300d040c41c01c61500a410000e201c10715485051606103290b0000300309034940ca00b201d021980205110040070402d400e100382d0980280201c500d10716102d440185141410f41d00c1902480c5446410614244100b042a20589043e111841c0181103160210300034920682e240350a5076007402702140401000c8000d9005000100050030624118100110303041c0c289000f904060f030003004880001040750320307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 233683093 1250 233681843 233681933
    0x70e0f0a0f021306050903070611150402010302210906090708070501200114011e0e070f03060f0b0d0e06150d05030c1603120206011a090d0210050304 66
    0x404116000c903520707220301034020190682e030346902684001ca078096114000c0d18240608070200c40203070369224000d442c5031200800309256500803450300e03d5800e074042081c9e9009071041c90300600d000130200002d102e0b080300106516585080038140804010304104407500185a40301400d400340c07415080c83d40c0c44406114480c1403008250f40c90840e10810aa0f40003a041030600a103d040ca0640003003103404000d011b807585405100c80300c50b0140d04042c04920640700840b032042c0c820748500300156a001c0c98004103004164440308045441c07074a00c1003c80080038081e419a0700c1d0030b90011031409541c00307900c0c4900c060b41708500f0400c5c01e00c000b45024400603010356500e0350440180c1400c504600c200090003040d40700700f41c42a5032100c0343d03100280480e405440301400d03050148504903202ea0081c464130703600c94107000000c1d0340d8240003030040406d400010000071081c4103581c0403415140d0600e20b0140418000b008010600c025410901c00300c00c020221046800d040d12080c081510f1042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 233684343 1250 233683093 233683111
    0xb03010b010f0c0317010b030f0c07080306010804060b040e070515120112050a080309100605030a020d060b04020c0a050102030f13120c0c1e03050c06040509010e07030b10030905070e0f 81
    0x383c2e0310080c94000e09002c00c0c003603903e1140c4003035581c40348489001d40d4400c3e41c0c0084500b07042c000081c00b05454800b540c81a6034400c1c5018030316210300c001100c0d6a20044c0c02910060741d0f4000600503569980300d5054580c00a001500c8420310301404c100c801007803600c0b2a241480c080003482450317020702504a055401408603d0404a8141882850203025020003080004000107000030040c0004500e030203600454402c0c00204d45034801d0649802640f50020341044600f664280001d400f604501140d4001070320050034040c04001c1d252901d095a201a42d0036540001400001468080ca1a610090030039442102c03100076541c7c000c00d990440303084000c200c4c0010817001044850420140140580800c03441d81901a4407a10441442488201c50a00c140f56a82200742000030940f0100c860080c0300c40c10907881d0460011000d440202050100340d52150384c65055078460720b007802c09180c6540d000904920034607002d850f000f119046101003041043c104000e528100c2c1c2040c0c0d11503154 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 233685593 1250 233684343 233684357
    0x904060e0109020622060c051506060c1504110405130b0402030c090712060905060a0b0702040f0504080c0709020906070312090506070f080a020f07080f040302060304150b03010b010f 80
    0x1142006006110b1140025445000040c030849101041d5551130b03002601c100340300d090565140f40079680c64402c1c410051040d00244210350401d105811959806100681007914248036921202d0034010300b612001e0b2400240014007007401940418031644074425074080095050104d003100c89201d00520041c0300c650668001405c54500340203d028954000e8104200c1e400c10314030241542a84089061560346003450010302c9860500455020b082c01800a6131420704002d8061010b900400d010b9803c01c1c0c0310941c0c094002d1151081e1480b0718020f0b0440da480e00040c0d45228100503d650010714054018400451540d485404803503034a64141446000c1c540781c001290050002400c5c040c000e402030504101c0b051750000b540080020480c0d45010306036542d9a04c0703d00f02c1c000d44050b000a4003083c4030706030000300c81100401a25080460341401d003582e960018200340d00445080703d40700040309008002011030300409030101c0084000380010303101100002d100d002c003109004c00300005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 233686843 1250 233685593 233685611
    0x41d0406021201030c090506031c0f0207030803010f05120615010302030a0e010e030316080f010b0f0f070c0501110c0f130603140706020c0114040b0307110d0806040c090302090406 79
    0x140364102c9142c0500714010030320941c1d4034104200c0c0702c072080c426002d140741450001151803074042031480202942034054000200000012540390f10301ea180d68040d1b100e01540440858100d10103103008280190401903540d0510041c0f164807070b410b104080707141d8040010300002494402843c10812003c2c83c005880c1d0780c4404004001e01110058003035254a0300100c00e40c05400407006510070300005500b1106250382400894034154111080c206184201c001440216400001003807641c0d4030190003418810062411300f0070741e0100200315611564013400f0001c550b000b903a403a038507a00e1030016050000f50075010a500c4050040f01d244607035100001c420314a10194446005142c0280840182d0111700d00d0345503803500d25018110240c420406510002d62058669016030102e0300e694505282c60440070000301c1c0c00107028182402950343c810701c030b685070800c040b07940032041c0c0d03544045c41e0401c3c60a1104880383e5650360010400d05000502c0540ca03030f01103480d00160301020001d04000b03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 233688093 1250 233686843 233686853
    0x2e140d02060d1a0109080304050306190902100c0605011a07060c0219060b09060901121b181e02090303070201081e0c0703390c050a0920041d04 63
    0x20550700100c20b0746241c281040307001c1c903c1c1d0210400e100300030f8880e0303c1d40303070f440e400c2c0c2c0c0707a403801244503031a45580302c000021881d4040c10b04c1000001e20848020032903910f00c1c0d0001e031440340d6602c0f0000c0043c03052001c02d0103000d0a8060300e80140502c0241240700c00807407060960301d01c121000a807107c1d845075141c41c400c0d031003000400c000805000300581c520f146454294043c01c5041030300341c444c030451404110a403804021b618101d40074124080b00310540e0382d03101c0041e100364255034007441e200c0080008980701c0b00402011070041c2d0540019101001e40040b41041f100040d4a0507842c0c03041c4541041174800108a4885a40900f04401d95a0341c1034240345140341440d1303526884c1000041401800d2014401500d0960301c01c2d124a01445003602080802541c5030707548040c2400b0441c2c411051002e081c511f48401c3d40100580322400e921040442d1485c0781c540d014190143d5038981c40300000280d44141144081008112032030513103040a04901d400c0c002c0c08148850020f6408242041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 233689343 1250 233688093 233688097
    0x90b0105010e032b180e040b0907090218030609070b0a120213081c0c08120604021608040f12020604090506030a05011b12090b0f0603152e140d0206 65
    0x95007003400c44d100c0c06120981c9a1500a00c1da078000007258100428140002d01d111a50303041d1411404010f4550781c2d43e0b01d072031f414510040c0c0141ca0300e0140c5140456400a2030005101100c0b440c10100c00300b22580003418030301038000b00701060980200505122400006040b1201c080040c945406c81280e660345c0d0000a11820b988150900c90418001400841c01301d00c0c180d2100400c0700030042e4050015040d034000802e200020500c0c1800c1001ea544010036805640d002040030300700508215100c0306980a041001e81d0944100c0c2002c40c003080001c0c83d440009024140d08401810b5259165003c168140503501400e01150f44482c001a41c5880c20400754698a402c24001c1c0440d03c00400d02e26403904070150380c03900141c0f4192400029030b68500805141a0f4400007405541d500e0381e00140d00080c024040b5071b414056050b00ca41c1e03581e0501c6a09002d40c00482441c94000d0303a290080d4800c10b120b5641c2480100381c4c0b2010400c2882900c241ca0100801795055030042410b84000b030001c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 233690593 1250 233689343 233689363
    0x1e0a050406120201030e0708120d060302060d050103110f0f0904050f0a0303060303030b0105030c1821010605040c0e010801030f0203100603030f0909270c090606050a0210090b0105010e03 82
    0x152615078001100990101c0b8051214000c1e21308000e50411513800503125501c41c0585d41481c3e0000006108448005004080c92101c0c90750006000d500ca034006000e5601c0030001c03550f440d440388018000d0044408a80140c058201c890820341c031700708230102354010460400306100710013440014062200510800c25410711200a8400d00c07142e618019006120601055000a10b045c0b9440160b50046003101d0140c07180e042c40c00c0c00c01030154001164550710800d05a040361a03911031001ba0844203800c1a240701d070200000c983c0310f00340010720080fa22810b4100042003840c0403503a115076001110710b8152504007078034028045071800030910b840b2210b082e01d44480d150600010515034000d40ca82000d504c2907480c8008155aa112902660703e403c500403d40d8001103100c4050b40c01c0c031b0044400c0b59124100440e4001d0f0742c1d0380360300200c50312980700707001050000550307040c111350500c94214078108a500c104159102910b03000b0000030140552418812052500c05040d0b40c104010541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 233691843 1250 233690593 233690599
    0x90b0a2306101b062901020c010e091503010501080102091e0f06160f0b041a0f0a0b0f041802131802120a0c0609060224070e1302070c140306061e0a05 66
    0x610250103074076840058031702c0c031030180302c145e40d03503083e1550320110754040c1c2080141c0d2072882c0e44c51040100212400060700c0f0b4031103c248084511b0158900780a03d900800c070400005841c3c1c0c007940244040480e000484018081c8158050b03440740d0340344440340b14108000c1d1005500c40041c1119046034400d80300019108180401d68039003040b0b02140d40c0c520681c403412800c20f03d4500048039500c1e0020581d20369000c0904803000a6128440ea401140100d01c01090703005c800c0c181e400403404a550020f00107510441d205103120560501c2903840640160204081000042021411030041e0318041e00074415070058840c0c480202e0108010b401003a000321310072803410754503180175000495500c0f070603005d80194807041c03202a12006c90341e000105003c0b00400150b039584411648154494500740c0d001d43c0200c002a003e51551020340714a6105403140300001d03080c441309903c802d071481d082c0752003980704404001c2c213600d41080140f01c6802c01426140c42c2c10b80070000072035140140d0011a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 233693093 1250 233691843 233691851
    0x3060e0703061e060b0307120b0f1507061413030507061410150f080610110a080307090510020c09060609030a0b041a0f040f0501090b0a2306101b06 65
    0xc0703c110010a100301d00e00c5044030801c059541c0304018400c500007211000040b60226a11051030f0802d50080c4c000b07100024a02c025a08142c80040c0e000204d10590403030a940205141c02040000c1c8603c3c40b060a42880241641c505010400f1a080c0c2c100c1c0000d0030000e01103003007010400190860506070350442c2c4ca8401502c0c11410a1075065403500c20610303a42101c0c0c900201d52405501e40b104502e6966403020031070b41d900310512440c07103042810002002600522210108803d12800003030600c160190b83e5030741840780b80100741032420b40100303200c5e401c1002c050703010300c1d0006081c1050342d030241c0704440700317030344d50000110580030780002203406d80903482c05e490403c4508030420b4440c5110f00714000880c50b0001002041490441340100b20700103020215010484241498941511a00020880f400706503584440044103880c803c8030203131a526a950185130820303001c45011402030801580303280a00000c3c03400f221640b40701b0309100c0300c013490142d00110003d03d51186174105800388 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 233694343 1250 233693093 233693111
    0x15050f03070c060c14090618041e0b03030301060512100305032214030303010611030708070b2208040b0901050c0f06100b0306131d1b0111070b0403060e070306 70
    0x140c002806040b007111020300d0000c80d0b0356010f0052407428503024403184803504000d420405c2c84000c0d4030084043d080e002c003a1002554994441c024000c6008003a03051007407403403200d5054400d442800c11800d1181d001480180318807540082070b02ea52021666145415803104280b5643c1208550005041c500001030908a0000403030311809540701d486002c0180e8070794a010405000205c0d2034800d505030404c0004010180c4070b0342280420f500e41d001a82d140100940c3c88a115511000c1c0460b200c0c081c0c40208000110412407000704210201140c403411542c60395050130034400c40c0030b10f00c410307100401c0500d40d0b80d12481c166004804200c01b2152110480394081d9501c4d00c08940d0f008440101e05004100b40156000b503a000d601c024103c3c000141d4400d0001c00070307200f05114032400081d1611044001507003040450710407410101e003d0140700440000400740c103c001869030103030307104401c10004201d12400312000c60350402c5000510612104102e424164940d00142c849400d0210740 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 233695593 1250 233694343 233694347
    0x70c0302060636190905030901180f0816050306040c090c1701081c020703050c06031e07090611031219020f040e1e0103030c060e0c04180b07031515050f0307 69
    0x1660242c008401350075002d8078903241080684810410052543d082407016070030720350041d48000c006c1c0c0c100418404883d616501ca114000c40705510141d525400324040c0c1d1001c2d10100101c8001e031509901601c1623103499100e40308600f12920842e10550755506140801c1d84c81107950f4a401c0308003030b0b03a046007565500102c07551840c00b8420300086403e102d80c0c40d0481390000488030200da50000c042d1100071594800c01000360070003411a0804038502c1800f001c0411140c510034401c42c0a07032900c0c1d2a590801000400e91201c0c020310107560b5000700450f03118941000e554075480100d5203140e110800c55586028081d0240420030119844046804140301441141d60340c802c01e0021015100a200812943d0b500c1c0c1b400e01c0054007140e0360a2400001c107032a0b8001d004220310010444014440703a0010804540c0302c03001440c00c03819810601ca003000325008420760018030902d0140034040c400b4650440c103207564458001c4002d00503280548043c000c0c42940e2400e80480001600d91400d0741d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 233696843 1250 233695593 233695699
    0x813030e060c01020c15070903030806040f020c01022a1905030c060f04030f170112062909150108070f11070b0a08161407080c0604030e0306070c03020606 68
    0x303691003c0c001c0480364140061805146c6101d44002d0390b400108a14584055400d040058100fa0300280c036682450042e10090000700000c4107110001640c40c0a0070840d0001c0ba040d0030365181d0701c1c0c4650315800c60741480009408030703000015181e107807000308a86080c0d82f035403050b1035050310349004400070404115003503100c0a02c10340c003d440b80d102c0840d140504441600d8507580041c00c100043c0c0060040307051800092003072a00c511000681c00490a0360310840e1480e0504090ba001c04c0d02c5851809401c10203007082d007100301d03001c0d4114030310702900001e404d0101c0200400d041120b07601e2050181446000d070100924103000541d08016192a607408a130b0340141e503050080f400441c00f01d050b0080c41c0c034008440500c140d0f500c49101d90709104600301c035484402d0590b4500d0080c408021660824001c490150f4801d884011140e10031000341420f000c001481c038814040c1030791051003c40c0d00811a00ea110f9004c442268011002003000f0300a80d200311340e106108521824180c1420911400d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 233698093 1250 233696843 233696857
    0x2070513021308010e1009030c0b09010c090603020c0a0809060d02040b0706110903150601180f080712050a030311191805100c08031b07050115150813030e060c0102 72
    0x140710b00703602d610b0700b0780359098a500241000460307019520b0701e400a0402c0c0d00910000d4828540302550b5040c50300c9941a1080540319880c0f5655100b122940f0280c0100f40000145201e050030f5091000c40c03c0c40ca92101101000030303000e42c00000d071049549e980c0200f21004000858000c42d200d03526403110040d207400c07648044401c1c03450102c0310f0010414030003d44554120040c01042d202c00350f0100700050a80c080e019a05120b00720340b07a00c81050170210090050052001c3c80c04001d40b03421082c03440d00059038401904024095000b2020a6000c28003561942d010706011900300707140b2030b450350740740709501c8804c8000ea14640240141c9a014540d001407100640800d00711545460801801e05928032005008c220428042c000181003480610b50010100c03440d8803071101c0c4032003001d086a2210100711040d964540d8051812948801c1140140000f003050341c40d0424100c5000d06100005086044000002403410003010320407450400c402401502c0c5030340717941200d070101d8080d41004c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 233699343 1250 233698093 233698117
    0x2011107060f0501051c0f03030b03340e0f10030c06020c04051627030210110106090213061b02211902060319092f1f0509010207051302 60
    0x2000000d020724103030b1203a0014544200780840b48050031f40c0c829045000c0e40e6001c4051584411109104d65814048d00c1c0d000011200e101448105a03403420300c3d14000d1251801c200ca440b4441400700103caa0802644041c0c803101c2500540c80701d0303c1c2500008400d17400104401402000415240c3d4040f84c80d50340b02a055406214503200d40c0402c41030001c1d95087c1000069a02840c503c1482450b40040ec004100510f0b0003480c54494011610b00090740c501040418802000b030001d00c8824405d0301e008150b261411030030102c0c0d0820f0044025030510aa00400c8000c2050540284418030b0f07010180e54000c3c209040790f00139030b86203401e40c00c40c140d80700d24502401500110102d00c041101404a0340200854030316039a0550f001d4242c0d40c01c0380024160f27983e8008840c00603a5110b041000000307080c00c8140790406803011005540c00303605185005c0c1c100c0e814000e6000e01d821180e1541d0209a08045403154180030040b45424419402070350b0012460314808040c4c0840c0e40107141c481d080c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 233700593 1250 233699343 233699351
    0x150206090706021b1507050c130207031407140f0c10090b0406031805060c0316180b0d11030414010506010906080412110114061c05060a050702011107060f 68
    0x41040192560524814940942c2190070441c3c41d41c13a000c0e0501c01c0c9900000c0060000f840c40c4030052541d80c210400c111225485030202d140140740c0b59036615901a1400d0b025440c02406075401032404010603c442940707840419500200000d0084582001c2030310411a500b01a69a061a079600b22108081d070103681100319001c03030340e44685640b000352540d100080d8035091825100301c00411500070070364032041410302d4a10001d001804218002c00c81480040d4aa0034910001c1e0348940d60110f440f0706200400c000708104009542d4200c1c221076001032455103500c8010031840c094100500c400c0c10459000041008012503811448101301040c0020005650359000544143c6c84902840d00440c21010000f0000740300c80c03207840000c4603540382003444564a101034500395214482041151813182003041a1810000e221001c024499400c003505442107443c3d07540c880d400505030070b044540b02c40001c1c501e28000d4008031504020701d1a440d5842525040400040001a000011442c20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 233701843 1250 233700593 233700601
    0xb040b0301090507060e04090308060f01021507020d030501090614042a050c0609030423010215040f061104121b050907080103140c010e04150b0301090e0609030a171906150206 77
    0x2234801c400c51a0f40c1030300c400f00e050300c4040030032020401d800342450441c8100640d882440024010305401218140c00030070014a0091026060f40e205801150700d007032400404003e00c0710702200c03551114400781d40001e2104061601c84110380b65030600310301c0c1400f1b5100103503855a0f004000f440300030751942c20750f292911181c038910b03220721441c0b00d002446140242e100c4071840341d02445a0a003081401141c3d180c8542003200c0100c00c038100c2c1e06451004054448400b444120300400240d07000707e1543e14079180c1054007154001d080c00314054101c41500d0240200750302000101c0700903000050a0040c1843c01b400e00a1400380c0c01d00003122501807000700040089800140130a83d642e051711400314001901040c03000405c0f4042c552181c22400e0000020300030243c80040d80a00140400810460b4408040c5807030108040c1604156a2041001c2c003415075000794140e600f07500c102c0c0d58500c00d0303c600000b2400320000044070000b645c6080c00000c1c1d084100038180142032099000c0d110303140e071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 233703093 1250 233701843 233701849
    0x12050c0901060e130204090f0902040b12071202060d0f020910030509030f0a020c130b1c1a1015030501140102030901020d0311070501020c030d0b120d030b040b0301090507060e 77
    0x240a100c0c14000c10715030304110f40149402020740601c80765a030401130601d40e40e070b2281c1c425225944031071416196940061000e60810b170095054200003902c41707840081c180c502042d42e0303149030b1080035420030700d4003152411580c4090465002c1e1440500c103111070a0440c50a100940c0214052442076018900e0b04503124024001c141c4500250800b45060510546c065242c03503002d001e0200c11800399101d00105592080e11924054120a400041d40d40c04032061090000200072129400c4502e4580c450024002e2070b0952000b40c03110528400544640c110035a1010300d0750001001080e1900b18405d005501d070340414100c65155103074256840b49500103a880b48626200390f40140c02049002c002c450182d0004a20a48180546484c2043d41e4603014226040038800700500d410016203148115900d00031740080b800220750724442c241505003060750703038400d03040044185929200b00c00415651640000c1c209000a002803200c802d030362411a4035026140218004141400c801c0c40141c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 233704343 1250 233703093 233703109
    0x190609060f29030a0b120a06061d04060c030b031207020a0504050103030813050c060c1c050406050403030f201507080601050702012d05180f06030103020f0103060f12050c 75
    0x144003100b19940c1c0449a01d070342c040b5500c010510684240c13601000380580d180d8151080c4a400041c02804251840c0d18004040d01c0150340005081244010290301d02010219120740044c1d01c160300041c0c3c60401007054020301403034140f0603414003e05c010448181c4460005100151089616400c141d41795030070442150001e0101500240c010400100111030140c05040074901500031100d410105100040343c5a02c50a06000e1304d401c20140c0030541c1e451002c3e0745034860201d0800c01e0605081070001405030140d84809401c100301c1c0d030031881d14140268001520100035220311701c1e91000114245d45c0e110300ca24140500440464000350703070b20b80319440300d5015200582d40c843c0b41817820f07001100c506064031040c03074040c181aa014041d0428a0084003041041601c8413030310781000b12402d03202d290041d03182c0390180140d21296402d69982504480c10340b641191015402038004004034000e080302e0300704600640243c10081f421841d41e030802609140b01380c0c100c2d240c4043c0c8105000401d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 233705593 1250 233704343 233704379
    0x3090602060c0f0309010b04061e05030a020f1003060503060a021c110d1d0d020607170405060c1b1b030c0411030406020708210115020105040b01050108190609060f 72
    0x81d100500c0f0603012101460025908207209a0000c1007506407540040c04866069001540105440340b01441c1c60307585803418070080800300d015188483c00c030340220301e00d1710072600e206115070520a84401002d00a0303000e407010340750150850f03103140341c91200304000b0350100a50000101000e074a0300c0030344d030036409040700708140040002c0c04c254003030340c48101500708103980c1441d1700c80c0c0205186403203004100030050180207034010b143ea130900400181c070064182d00b00c1207121058108010100d080050815004000246055642d448040010401e10b403500744d0660240540e04c0e1401052a00010303c0c40403543c114141c810000c02c1000708411a0008403800c03803004003d000040c0852259030103400301601031443d541c6404101c55012000981001180980010200050040c5210100140108819400200b1582c10942c440030801d9505101c0d0a041124000004004111043c0321141c000c01005d024841d150300e9800038809041140142c540700c1e034521600246100001594402c0e13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 233706843 1250 233705593 233705611
    0x220f080c092a130308070605011d131211030a0210050a0204120b07020106120b0106020712020f0f01020f010c12110405090109091113020d0c050309071206060801020f0301030309060206 81
    0x108a0b90500c4900740d0b8000d110301049901180c1400030100b21803030020480e03d07116800010b0070750704010350a032041c0000302003078080e0000c050420404101e00081003200e2900806082181c000f00e407811140b203004c029091321076020110380700d1216500000c9080880b00446810f05c880da0704c1c1079504d41240218810307e05143e00000d41040401c00c0c0c805116040700c03941c0300209174980c90303800c043c1608800407000c0f5a400300980040245c6503041c0712210241100065942e0032006603000a0209042101094031500e1144501c0010b60300030007800302e25101400090021402c0031001800c458900f000800001d0b090035421402008039034100c505613140144403440990a024800f4000d1200d01d50444515400002110003959080000d455502c0082e401680d180008203440c0151400020004244030050044c0103140c040440c4100580300096095901803440d4109900a48029440304003254400182015914910401903050b2406500d9101980e5901c0e0f40c200d03503c41d811110084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 233708093 1250 233706843 233706901
    0x504020909121c24030b06010f1418090c0a1b051e01021608030a230c0f070c030c060f0206040b06010804050f1b1c0206220f080c09 58
    0x10070b8440c04000c841032580050781c0001d03900281301000300790300303420042c41e200c1c1000760804000300074001c0f4030154040401c0ca82810082010140a0204034010259540d0890007141c0034100580640400e680d01400410002e05400c007060341b5001540000344550003c2c0c411001d00070320108000e0303443d0b51158864004c00c1b111000c01908038103035400d102100c40c50354080114000c4042030030174942e04103000707100c51962030a11091030000c03611fa4a0036600c004210003c1001c101e4180101a9070045079903c20550301d103000d0814100b00c1c4150b8400a020a01c00d1030702000f07009903406200c040e241e00351912802000c0417138083e41e860400315001000c0552030700026646500c1112907503082849407003128080c07402c0b401600d050184c0291481ea90002d0081600300c0380ca018021910305001c802441c022824450b004620f15120702080c40e94155115a51848580c03560307001c010013040302003002030600f51181c04403600c4450ba503889a104100340c402061b01080d20141d0404801b81024400d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 233709343 1250 233708093 233708107
    0x314010b062a071a12071e050a350c070f0611040b0a0206070201050106030e0304030b060616030305010315020c0c130608012c0d09060804022101050402090912 70
    0x800c10404a40b2004268010000e00040b0300384460748410754000101d503040e4070340c600c440c0c200b03038001d000400d0b1808204e07140418501c0407504200c220500141441e20703a0382d841c1c411800391825039002c3c42c3c0d8070b501c204c2c42c404103280682241e0f5410b41c0242002c1f4003103e83e266490048200d001d11030700904032043d21840080021b841c0c1e44141d5505240ae50220708140d03644802e2900c5400070500c41016800030320420000c3c030350a01c07846000d014107003410095400c20811440c0e803800b550000401982c5c0003800302d00fa65480b00d0a682201c8104c0b495080802620720303008015001c20300c402c42d0200d00304009503c0031035807402503880c0c089030700c00180002042c40e001c1080c0c11079440030702000e103513850a0105d0040820b0144024098443c03038400c0448412200100c02280c504d20341405540150b11751007071050348604514100c40c0549400101611540000356182d001e094001518005c8540d900e003011a040d000240700b14000c0703c5510856030f890407056100d001840d566803402c807080040d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 233710593 1250 233709343 233709397
    0x20a050f09030a0b090604020301050c0a0f1809060b18010c0206092106010909050c06190f09091e050a1a01050c0f060106020f06100b0f0906090a0314010b06 69
    0x2800d61041c00808a5882484503161132003da641503e07851215003100e0104419820240a1140c01050201e0241e01d88410f4100040c036050340421010200541c1e181072001c1e9000c01c26a500160000a00400142d0341d40d0b48142c10542c44101c9642003035101c417030884c007150301a5962403051500584600e1400708000d003001120900c0c2031102070070840b9013801c00c03100d1008000d40f80c00b0b048110800a404c0302d1a0821618144c4005482c9110f510300300314185820042040100c0304401908040030320340c03441501a03400403442c0d00030b030000619014204c03c6507800500e62a5951600c1e400401050301c90070350341010395210005074800301a2488031000700794070540040515a0a04041c0c5d1984aa1885042e082c10005c2e88058010f0b40310b0b9a0020386072000b0f0151340e4110041600ca030b004189000b10500060013403003403210300513002284085c0c8540704c00d02200c508810007400d4003403003512403500e12410803c10490110940c640079004005081220448900d10b05007403100748154410145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 233711843 1250 233710593 233710597
    0xd0503040f0c090b0f04021602040c11010f0605010f031803181a07031103041202100c050303090604030207080c180402060f04060e0f1c0f0c15030605030f01020a050f 73
    0x22030720764030011804408104180800005880c80c400b022510340000010403222440c01521541304601c1001400744001a200700064225070580d000b1404d0100020207840410341c02410740c54950070720761041d80d80141980071030142c4409881741c3c00c0b40e441d500802c8003100c0d1500e08856002030746501d03441c0840d0056456002d1f80700480d440c4014203882d401c03248069583e105c0800d5103a000840c4440c2050307044000003c0c4042c4a8000310700f014503024a080030b0303121240000e070040f601e01c003010b10050711400d144030300c2d2a0000700310780e603900307040b03045a6451604407002c3c2c005008003140030402240104030703254642d10007828242e0200031003002800c59a00500204da0058081060000045041c1d000d080100965103480342c45080120601c900c0180000340c4900c00c0e0003521035034507000744001d40b100c04035030803145180e208402403401c0c1d41084529005041180c0c0d092036030300d40543d895040340c1c00b500e2090302643c418030101c2e00c40034284d01890b80c2c10b10105400b400420384184200300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 233713093 1250 233711843 233711851
    0x3110903101a03030a020304030215190f120513020109080d0f030f0b090906040b01081f0b01020a0501060803130b13061b0b0712050f04020f0402070c170a0c0b0c0d0503 74
    0x41c0c0c2440803025900044c3c907680c440c1c00c1850160b0400f0404005514005407400e56600c18440785c980381411007109004500d8011120206011070781d0544840c541c855041e01d074a01000035010400d80c1407000c40007129602d51401280003841e05100400c01c4100858510702281031610b51840c40f0500140980280000a00300301e0781581d01c001c0203400d9a5190b005500a54030303c80501943d040030b042c800005079050700b0000d110307481030600c1030300741000004440c4444031100c80000d42c6490080105d0a100c0b814078050650341c24450301040043d0080b00410084054001f0f42c40541c0c1e030f41e900c0440c1070040c5800d002810300c8410f0100000303030150800c580400c280c840c58016104103940e07050081e9100740e0301c400c00648041c0e04038003e02468418a500181c01a68910040c84c0c240e0004203020044003020303000e550042512020060000144005401c581c1c400d071920500659002d980c9400410b420b030707000204a640000d0004140e8111083c141911018214000041c1e1013078030184c0c4090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 233714343 1250 233713093 233713121
    0x12010e0c010e280819020109140402070f0605060f0f03120c150906061e0a0303050f04030515090d0f08040b18030a030b0109060215040b04050712060c0311090310 71
    0x202d9207081c420742c0d4185400240a40e82000e550328100140545880c128040f000c26202403990740c1c034091f0fa00060844201d4034003800740007504440c58045006030003201c40042000f0618000d01c2e0400c001500564415542644c0e058a408501010440d030f0000030041c0c15050380040400c1c40c1440b501c0c0005141c0d0712134010448030072840e4510710601814044074045d42d941c1040b000d10000f843c14110502d0314035000e8000c00b41c10b0b0384001c00121280041d00c8020180000052070101c041a482c05031002150414161041c03800008106401030004507440c00c858020f80003041d00c001d014990040412902c0c0e03030303951401c3e0341e141c0d600034500d2405403a106028020424481000c001000104040c1c601640c0120300344420100140ca10041c5400c15030654125801803da5107409014240d406508420034511980348d07420001e091101542180704410040c6190205101c256000060341d051030f070381d0400000342016034002c0140100303400075905410080041c611080346402c08001d0101385 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 233715593 1250 233714343 233714359
    0x60902010c080304030309150e1e12040f140909030301061103122706010b270402030c0316020a0320010b1914030102030411090a02090d0c0512010e0c010e 68
    0x1030b49a480c02a00f04940c02c8000a45480c90942084403040141c00138121549040c01107500d4840142d403180704030907094102e10310800c40300c240500200510103110744d1070004a030350380e40c0780c00142102c4c6640c2e01030110000a41142c07854a0300740320890a20a02c0305101850641e400d001c022100c07910b800b100f00082d44000d100e0850b0b43c42815503074502508410004d4011040f517100604c40341c4030600340005942d003200e001000403540c104c0864480b4030b000c21407186100c029844a9844140c0034000070f803c103202008004110003410000c500800d00030001519902050100300d0b40c07030719070500060026041001281d06502c610040e0781c12a04070000204049441c0b0707001c21402e407514041d400b07011017101801c11100e0a0a0348411007201c0035802513103149800d458030034122031250800c41c024880c110001c4c00c8102158140c4414000061205c01d00d5192424034401071502401143c1c4200c1c10072584459810052050000c00c10344013000d012885019001540c00c4c2d0389422078a03070800701d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 233716843 1250 233715593 233715617
    0x6030c0d060504110306100309020a050d02180108070812040531110a0306050a0305060c0307090806130311030310031113050c13120b15061902010c030b0a1206090201 73
    0x640d00030040c407410384d030035810349910700a0704214a01505401340414513141846040c05610340f810300101356030090740c8126090307026202151880c14009030828544084000101e0219000300e00c130401c8490841c01c8a00710a40e050321010140304030b118013039101094014540440715400000b0308200391940700440121940c881c01c00c00d0300c241c04070142c2c03550030006420080c42d17007501c42d0001901c42541c10714442403c6a540c5070f550702010303003418000b00b0b010000a0040e40709169a5024003085401ea44207070030a591401c06941c4160300490201310703500c0e2469a1040d002091b030f4070501c0950017070844039185840305203807904413441c1c00350088980d1411400803821409024002d0fa8008a05941c403005003100e601c0d01e2001e50081d4440c08142d13841c0790089650002c0064111200610000381c103940c10001500900ca41d0b42020040c1d01d0700d03241c041c003194044d03000b4980d400580c2c4007807009002d88001c00a0310032260040500441c00c10860102003103640c1c0c44410850702c103041c10454110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 233718093 1250 233716843 233716849
    0x30a0f08060a05040e060103170a05070b0402030c1801050102010f1e1e1107050d030905030f09041b0503150405010510030b06160c03051b010516020a050a06111b06030c0d0605 77
    0xf41c2c40c560100176034081d500410411000e2500c00c08010900d10249090040000f801480c1e44646034014118514148c04503040d50717000d01102c9418040180681c030043e00d103481101000600748600c60155182c04080140141070b401005000001c00100e00d0b820f092000081c401410032400440c1c004201e00d070070400ca0913031f501c6158a000500c03018a9180d02c0d02d031510700c2c50808040c038040209405e0103410340010340000113541c808140c41140755100c1c0b5403100420b0003420300c4000708289403825020514030300e81110003107000345100300c83c0f003a01c91120030502090318801c0c03080d16045041da102c2c0c0b2204a00c039a0004000920050580345488801c4100308e440b405c032000155141030103c40200208402044a0945c4050203000741030319080900000c1c04e18001d9044001c00480560b202c5400c550700c83c4080c2d4007504000b0700a0800e19240e5000a00400c030340303000302803c0d12421020354054a0340215242104800034246c07841d5589107021071850ba00490031816495480b10008a02c5036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 233719343 1250 233718093 233718101
    0x3032e03120e03010b0604030b0609090f070b180a05150f0f0301080d1101050f01050d060b10030218030304030f030f02031303150c110d030209122d030a0f08060a0504 73
    0x91642e40c1c0420980b4050300b050700311840c602240b0720400c010041000080c0d07040d072104c2d50040c4100c40360409540c807807050a0a01c0c0c040585900c0500880c2008203c100594010b8228130300f00150f5410080c081c0000c0c48242c6003180185a4020b1102512440c1e50002400130300d180301c640b4141d2402d0203a040e40b402070a8000b038108141d1500401814a00158420380780c40b43c03c0c081400a00c4107042a032000b00300c50340d0600450740500c2270408290140540394005004a0300e0140c0600f08000c69540000e0080d08001c0705202ca80c1181307980604646000015170781540d4000c83d0340c185294940da0103941800c05d9114150a600003400900c43c241e80c840b201c03000850103901c1d40c03d120034407060703c02d0441d03005220030001e210800030b01040349000042c0c4404210058240181c1d030320403247c00504810403000d800c40c05840b5458001b51208040000781d802101c2c214079410480640300f50f0203031a4054010541c0c0041d82d03c44222010701d00c030b012096080340003d401921825160000308041d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 233720593 1250 233719343 233719373
    0x6150d02150316180b0d06030b04140f030c12072402071109070f080910020724050c120c090a150e01030219140c030c07090b0303032e03 60
    0x1400703002c8100491500b030200b810140741010700d0003e0040d0b4042102d266130195a01541c24030b030901084600221079140d2012000c0c42d0408164200ca2a1034602035a140c0450310100e286402a00c541d40d0414400100703882c007541c1c00e2000380c0141840e4101040503604001d80c292280d4200514036806403070034245004d43c15018520160340c82c9828280380c010304043ca4609270042d49c0e55401c000045902105030b220b654003a15000c0c48548a5608441c501070100000c215060710000b80d100822211042c996083d41244403940d40d0107050401c1f040840e84100d80d070300440310f0f04110121070481c4800e03045502000392540c6034100001c00b0f01286030300c07903242c1002c0e42915000c41d21503826501b051030b043d185082441e0a5103080c0b8003115510382032149400700700501141103c80411070748180c0c19a40780e2400842240d40391140440d60a949400501c162868036181010440310342c180841201d21406015030450548280c2071440b44203201b2102c81c00002d1601d4900100009528100502e94 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 233721843 1250 233720593 233720629
    0x7031e021f08010e0103080405090403110304180e0102030f010b0a2705190f090b03011806090b070e1e1f02060916030b180f030403030203130b030906150d02 69
    0x110258080024000b002d040e0801956880c440c001007001402280480e130540d813041d10203c1540c2c85030318082e00c82103000001c1c0f400c035010214004c203c00c0100031104024003150001440a11921a00b85080b0310003a1540d8203000f10600040c4044401c107002004544000c1c80c0207203003c800c00c03407c0c020505401c00c5110700f548208001300064038055600750050001403160100d182e02d0018402c1c089081441000e0a1580b115010705e800d641c20b5000c610840c81c00340d607a10500c0450320300b482c010603440d04201d45103040d50010071080c030700c0340721000f101800c094070f0040000704000e441d0805440c10f111842e40a003038240c1d40315070880c031511080c0b0585c605e50014125803c09241d01804c0c920984116041e0141008040001c542c000e640140c12680b8200d0400d98050005011814042480c000b010b03503110000b00002055400801084a5905501064892515810888403c1c40b00ba1624000c0b44c1c0800042000300c090310b0b18000d4454001051040a10b01c95804610070014640740000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 233723093 1250 233721843 233721889
    0x30b010c170d0f05060102060415061a2101120230010b030105070f09170c0604080c0312070506070f0e040f020304060c05030603070b0c010f110702031c0207031e02 72
    0x11400c2454043d6103003034403601006100c58030b490b100003903071100c006001038110814a004113041e02025841000070708100d0300002c0c2458240030001c4180e42c00780003101d101182004248407203518041406050f900c0c501910840351344d150702000006c544119011a0680b80f1000124440302c6003501d00800c040b410f1300202c0e044003041c04040c2103d50050404c0140151400c2c02c1d44815801201001a900b4001c0b0286d10480c4071807040745021041a05507400070000100030400b0340c03001415258040003101241d4845500707003006d1003d80540038005002d0f0348200c0110ba40e4074000c05070700c0d290398458986400c00d803141d08001425030308140303401c100340c9a000007884140400c501400803082140c0c10401d1541c00c0110100c0d990f140c4a202e5031071541030119811020740e00c2900550b070140c550103814410440e048068a000340d1050804034440d02c25441c0e0102c405004051485507140e035600507144461854940118200d00302034020302c0241a840c42500681d164000d1818481c40d032001c4179 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 233724343 1250 233723093 233723107
    0xc07090609090b1501121a090702031b0a031706010e03011b12020702091311090403030e160f0611010902032509051b0d090b15130b0d03030b010c17 65
    0x2103e11020b0b003800d40315002c5a5040003181d80101e0074110300311500c08005403041070754200702c440003000b1841c194442c0d2601c061250b07603940000541808808010052a18142448069503500340d01c0c80060105007034071801c8180c0c081c8032003034540c80720f010b04007519283e442d03400003801c440c4c201000c00051080c0b050101078169200341c058aa0384914031086103002d42640028a007920001c2042c00e40c0c0c00310a9002d001c006411012408913180640039904078242490060040c00c1c05140c5018640b081141e0b403046501500796034400c0782d81c240c4040040714203105c8201d0341800408908100b664880d8255030050310100f14012070040c019000452000e49001681d03132203040c503030014810714106000d11452801084003100c2815030040010b0780d4507400c1d140e000c068241000003410071080f460070443c1d68031000c43c035400c00d8030048412604c800c00200d5698100c80380da080803600307c49880c1a050000703009a00c405e81c0c002c01410401881e01a030342d51440c00d07582444800c03103801d03000700d066 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 233725593 1250 233724343 233724353
    0x50c1e0f0607050417031e070510020409020d05060621070207080304290a0504060c030c0506040606030212010e071703040b03010b072306060108101d04120306030302060406020c0709060909 83
    0x1010405c003024524060309034000c0580304080e0407600c030780482d0020b46a030400008000c0c058400c0d9541000703546480da9130005100a40000840461450030800000c0c0700d41b52605c111440c5100081c94100d02d14503151524500450081c42d4006520a64501058030442000640300601e4015005801c1880c1c00d4911042c0d101110086481004c00340840754031584c0044c181ca09a64141c5000d490f4441035050407214000c040d08050310b2030045405000610504e9084281503900a55a420380d80e4198000365081710f007000340f51030306600a030005010448590019416020041040302c2c10b060b10f81d05450041e9000b071b4060500354200041c1c80d01004807040d011041c02c1c0010203580b07035080000c10035680301e400041025041114000025802406180c101800752290b41c0090a8800c80d404082509401c1590241c07801980164801c410724424000d000c20383e03505901615541d104d607070300d00d000303500081c0320043c03280140c030b6000c0780f1000188140d0004148110002c50848014101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 233726843 1250 233725593 233725619
    0x706090314121e01151809020c0f01140910051806182517010905010608160509130f0c03020d0b04120305060f010e04090206030406140106050c1e0f06070504 69
    0x81250520f00d40700041160003034095111241c801c1a00300441c0c03591241000101490242e00031581c86840410040140e210001c3c00401940c000002084421219003c10385024000c8803244100c0d44100a81e00b04c41c440381d08115088844014100c50fa8448940c0c900c0c24524101e4800e040d0320040c0045800201040150740c148116184580d642003d01410050541d21036024841030b452000000040958003503011b030b00500c1d0004020080a52a401540c0e2500b080540015a030b5040d2240460076240c0789110a003d2095500e18090440e000e503180c4a10061490007a03034014035083c0000003680707070590944035407840b40f0b800d003500780b0f0144bd0034616600b45034840d6041520b07150401c4641d0306c8009640300710440c00d003812900001140001030241640c244025001a004020700c4208043c503000b1494103510311203100420b80c1c03a2f001c1180c0078000e0880d4102260b00c04440030303008a090759650819058404151641c41e4071002c080307450704409440c01c900140c1c0c0010100240c940d0b85031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 233728093 1250 233726843 233726881
    0x4090501081c0e090103060504020d021009140402040b030a09020d050d0e040e030901020c09060409080c01020d06050102030a050708030c0403022e030908041a0c0706020c010e0103050705070609031412 88
    0x100101c00841e02c0f008160072080501000305415560b201007000d55969001c60000b40f64000d02c41c04600c0e03402c020041081000d0320460000b04426081c41c0d600b80b41030700948065031b408044042c150395815020174064260901d06036001840808502c0100d94140401d00b00308000c0c4e22050645d0f044002840200c2d80c0d40b6907040c090750024401d10640303030380c08034004010703d404580580c103907100d100000f00101542c0c170000704a0300001500c02c0740d00c2019000340180d140303504c0040155544d170b41c005984a11581c0c60071000540d040190304000f1305158059030704182084502800c064580d80407a82c034044004046030410205004010000034109a0080c405e04070f180034130010a880c0d8402e04103024501845040b035030380a81417503a41d14140180c841c000904022990600d42d00c0340040e44408414944c2800103030804100300d015400703406002d00a601554500d80307051402d484281c001c100d04c24080382006941c42410700940040e00240100100941d002002c1d8242a01804030350107600b0b03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 233729343 1250 233728093 233728097
    0xc04050d1412070c05091018090503070210180b091c0203010e0109120f0503100308070c09110903100b100507111c03020c040b03030a0f0504090501081c 67
    0x44144040e0311640c00c80310815501c44103095001c1e9074004118245480540280061207011030000306004085550204407541a620700105803905003c002c69100c0ba0700039040c0e40c40d103910140640c1c010540c89150740500940c1501d0a041c0c5070750020701100c800002e15000107005e81c21765240d070b110750781c04075006041c0f044a2038607003040c1c10042001050380468010311000103101103000d42d2801c1d0051000010070300001c001c50b180b149003191034200105c0700100085d12610035009407501980481c0c2c05003a0030140781c141c4030300e140d80e03010300707070b030104004645410035514001520310460044d10195075000791035503180d003a0002072600e000e080c004082040c0f030400c0030820301078595400d40d040b04581498050b66406250825084403640011516081a08400d200c40300307036501d90403004224460b6007a03421f807221110400c41034a4016984680c5600b08100791107445004028038840e00b0054141181426a540300c8002220000da02040c0150000100c2c00080a5814504101a1958 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 233730593 1250 233729343 233729347
    0x303041110020703121d400203270607020c0f030f010f02180102070f0603050c120702010b1e0f060d0f09051501050603010b07060209010c050d0903030201050117061614130e0c 77
    0x9805e605c03401f0000c02e403200e219030050071042c1c40c0b618840400602c488181c0704065640c0e0906040c40740b07150240101130032280c0c01210b040d4084050110703000c1d004100741c0d80100714440341c0c8400c001c0d0113600d044d251641445101c0e000c8002400c00e020380c01c24000c03480d100607221244007a10400711194990414119009100107021040562090205862080c40c3c00a419074940701e0b12640d900c12580c107500c0000d408410006a03542c150031071620700e00291a0310070703e00c0e04420700e41c006403088001e031030f400b01e2204075841c0541000e002420008100f40c5011a2241c0b0000c3c5074821546280c0d0146c505030040030303d00030b401b42e8917a51680141015103081e0300d1580b502d843c0003010700686400400a070380000e50400d90341c1c0304041e0b8444503a00401034412450a44501500900c1217100841c05542007400010340c1803d00000341190352507103c040e1819076600002c0340220030400c03030307400141b000103081c041e41244140082c1240c41c1c0c14043d02d2550500303000c59152000c00081c115208940c0c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 233731843 1250 233730593 233730619
    0xf080903040b03010b0c01020c060406020918010806040201030b04021608030406061e061404050a0e0f0702071d04050f2e060302150a031d0d110303041110020703121d 73
    0x900302c1102d04694a810045450302201e8801901902c41d9169805440c445e0006010030700407182e00500740540c048410701c000f4103030303001460302ca40d40034803800032250070000004025501a4021800c1800020b000504e00101045444d904580c101030564203800c0100400003004490b200b001c001d00480715210440389000d606420181c2c0090041c001002414644001184014000c2d60b01400b002042c6815a5032074240f10503400340102c510000c2031100d003004c00c94482c000f00340c80e42682d0414418042400394a40881070070340000d8000c540c14403440d040240c4139141130041034100000380752070054070524120340f4500c00c0c0c0902c100203040303440c0503400c200503903401c020108032010050025031513180d00407040e001482100820301c0d0003032040031040e40c00b00300480d9800840c0050307103401d900d402040c03039071554034001100e004201008102510015182c44030641e0841c41961044690003526540c5030020080d564000c0d070086008aa50325110111100c04410404e005450440d02420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 233733093 1250 233731843 233731859
    0xc040b030d050f070503030109051e1006140c01050906160f0207060f17010311030f0115170307080c0601030b0c07050d0e0109030c0b030a0b0d0b010e060d0209070f08090304 76
    0x6041040781c18071070005070444404440005032030f0a41d4010056a8407580e680060f0809460300b01c800b40720026101c8003e11120f542e1420150090410594841800f82841e50544440070107900c2c3c159095410300085501820034041c2512507040d45003e0110303800d20f684002802c3d0318583e00081846001d402e001ca0035a0300141c1d41e411074040745004009500140010b640c152010910495041200400030043c1714440e4403490074400142d0841308188075031400a400c83c0c49400d400f014141d8001e00420818070740c800070b4840b030360720042964500b01c281d94135504564041501d096458102c200100f0034801c0d00d074070295210f08442c1c4414540505a83c1b07071511445040c0300c450511010014100091f44a040d140e40510f500c543c1c80c1e020181c40d050a000e8980040358049202400c14002038180c2c1401d8200d00642c03070713000c540c820f41a402e00500c1080030724010001904030404c0b512510144e99501c0c80c2c07034010a030940791501070b000d2b182710003001c10800420000d2140e0040008010a80f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 233734343 1250 233733093 233733103
    0x150118030b130305090d0b0912090d060908120a06050f040608102a0302070c0f051809010f020315040501050603091504050309031c0f030c0909021e0a0906020c040b03 73
    0x4111410b404081c40e1442e054509009882107150003601c0420000100002070304028000c1203160100d07010034000c5103a05600388508001c0a4100d5605031034000003d070180c1203a41618032440c604c03401c2a0003480f194560b04021207180450980f507403000c0219007080c100511030a00261801e020342d40c01c00144036a00c41c0144c1d0180140d594403441c1480402249014280591001c9000d004040e2038800c0103001c3d400944003034403021107030f09000038040300d239070000022220041c0500c084821880064030303100000070031480c15952115280700003406288005c3d40304402450609141581c101c0c244001c840058000c0c1e4012042001841006d0100048500220400c001c4070111940e5918010307041d0b000c2c1d0030040f501440703072103172450040205080185069116645d43c01301e1f240c1c0000103d041d01d891580030710108142c400207001150954005280e181166110714840300840c54140509038080d0907020005245030f20148041503052041d501411412503083c40040c0768140029151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 233735593 1250 233734343 233734351
    0xc0303180b060f0d02100201021c090201091806120309060e0102010b1c03091502010902180402060d0b031c020f010606140f091801030506040b070341150118030b 71
    0x204103072404011280c0d201402c03044d03240da025211151a4a040300040c0c080e410005032a9403200060040007200700301803152030903298050791484005480c090700891000d0405540000c255181e17480030130882901070060325901c0c400d07a03e850807249409030080c01c408601880904590412264404554415540d6000e41004200f400f42c19901c5250940f4646aa548070040c007442c81103400413250703010340c0454030850007601c1500c110303420191100507558044800a510a005201c11004a00540d010640d0210040d007120800200c01485000c100c407920000c60050f40411a0350b0f0103080d0a008220040140c0d0070220b8082c004040c0c00c58260003000c0641c02d11140120380242d1a50b0b4402c20880b4580399504400506e503120b060154480d01c04a50603603025041801040395a80700b0312030200e000c182c9000803000070003c2030419601070ba9045070f4047c100c8010a580c65410301d400d0b0582d01400412601040008060001400301c40c0b84c03105010002092400810100b51170000c441d0388 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 233736843 1250 233735593 233735599
    0x40315020901140a0306050310090b18060703021e030406051803090105070b0606120903370f0e1e040e0a08071707060e0c0102060604021603050906190c0303180b06 72
    0x2602d104d01021002051158040356261040003481091121107920224000d070040b2003c44c51581c0300b071054580101661a414001e900900010360311920030340c003030103014142c4038800d104440e01c00c4d0105203d804c107070f6050b903e841e5a103080c0844820000b2180c031201c100c0c040070b1803c0c00c50039000a0001d018031100030700001c003450300042840c2c0d0f4680c201e03264481c0e241000001410800c01c20755898014009820852101d40c010700d802d00305000e6210744081c204c2c0c0304000014401781d002c030380d4a0441103070502841700208050145650f04145102100011038480386501c0c1c801c0b00b00402e80707110300c0300311a19030841490b076130200c1c410760115003010f038101e500c0c041c69005050034406640708089000c0e0140b031408502240842005c2050301204509030308130750b9036480318010842284203207421841101c150850080000e40540007418200e00014030142c01c01800580301d0710060400e003560400100c50010080030582c0600c29a002003c032101482044215603641c41c8002c0005449544 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 233738093 1250 233736843 233736847
    0x306020d0605030a12090806010e18010f020f0c0c0d080a080c0706060f060e0f1f0201020903031b16061209110414060a080c090106030b03030408060c04031502090114 73
    0x811250010001018040c081328824503490800710400794105000000040d10301d1070000d00c481c40012218184c07800040000e0b07071500c805400b441d8195810780c12165070354a071503010603065a98409400c400c40d5201c2d01c2541c5a403003002032030170101000c0120f07104000c618410000300b0a6a02030b51110320544c00c144000d6107480b40070404500075040003d0600d42000c0c400300e05002807490280440d0800d80701d5a00c0d0000c0c82d01005110000303c18800c2e0080300040c0d81444801103040d1210040c1128000146440c1040d40800c4c11540030305020071032000c201c900f07044500810401030703e080c141c1d2020840600d0a0210003815103110506041d800f40d2144d101e0000c1c44030100018419038002803080114584d506224050a001160a0f0f803095444040000307401a000c5114800341d0f400034001c142c960301705401a002804440b0310143c1500c030501020540d01c40c10030402d4051550011080c0c0c03203d00e140790a8201ca00c0c85420105210b0040c000d0b80e403907076000240d8004001046043d65 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 233739343 1250 233738093 233738107
    0x30c03091205010204030b07030b1005090a0b0d09031b0f11180a0b0907020a0309150c02031e0c0d021f02011506110d020105060a0b030604110f0c1510030602 69
    0x458040311508211404140101c145040140550041c41104e2091188032026582d118042d82101c4080c0a41600501800603401101d4829002000ca030030000b041441e1071503c49050480503049001c08010070356855508509050f0030403414104901c40003840c602c81d2456507104284a46402c6000b002100508040c02d442d07610030b000d84540f1072011542ca480c0e0b242c41c21841d4060a0101c46090007910030b140480c101c24030201d40c1c50307048c0c0d4058651054151074a24501d40d182c080890020070806100c001000694091103032a03440b0150301c40212460100700c05082c148018610141c0c480c1ca015041c0b0030042c0c44940d81030a0940004c20220f52000b200301040c2d01401e50f18180307220ba040340040c00f09200d5080340b00c00c0d07030703000ea64802c541c0040d0b030006059080f154185d40f9981d0000d8814020030412245a00840e400781b0007400200d10420b1081c140003180d040f11a00c004d07006404210180c50000030404814420401004800345003040f502020200d101c501003e01110340020f490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 233740593 1250 233739343 233739347
    0x8010b24070f11011107050a0b090301230a0f09110d02030a060f140a06260f03030103030815030705010e1c120f080903031501270f05040f020412030c03 67
    0x51510035401501d5900c44100c54504400c440e6010f1004a0100d40704900b404030060001070722005503a00900038590a5003010701400320350704402e6195600d90b40300c621103080310844100180c410008001000c2c40b50401c0b6000c2020f440c110808480810b28200b6418082101051003118030703403056a02c0002c1101d6400422705013a80080e010303207410304101e2010300c5003625920542940f40c603018130004c0354072a1000740c03081d5091413188800c2c016680d20f080d600100d103031400c6401030100e081100c645102000d07895045400982c001d80116900302c0030450380000250031541c6c030000c1200945115410b000c00641201d9159500c0e40c041d030201c40759802c00c52001d00700f10142d1a009240d88500c030914083c000c25807100d4810380c80000f14500041401d905001040d00d00510040b040240c2001e00d1500464452281d19080c0c00050741000203841e11a41c9668844051304060740c1c0707010041c0c02c100900003601c8400240f0a9942d1040104014050760b5541150a00d949031074490345441c014101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 233741843 1250 233740593 233740597
    0x70501050c0a06110a1b020604050f1804080a030609020903070b130801060b0d1407080610030236010509030a060b0d020913060506090103020303030711030f0703051308010b24 77
    0x10140d40c903000c90001042425030181c66880c17020780c0e9400c15080d02c004100012000c0030002508440300b804103200525215500d88100540907004a0714860444880c42d070801e0150790940c1c02020000707486007610b6050181c2409842503071b4043d86404000303070100e40d8800c840d20441504e00f201040700e9020149000072200140f503c4d00081c000300e91525605140b6600c20003031b0030b100c00d1410f0250102e000025140a10a4215480341d000d29501c003c140300e20104242031034010035508011480d850001042800d000c140707084000004880c032140880c0004649544040c18418144041a465600025a822010b9100001007566003607a4045502650030000c002d5200411030200200b0400142d00e003200715016000900c00c584503942846061071007800081e405800400010301071074090304181c00c181130381034112071070700444140b009015001941c08070f0001d0301c0029040c0201180c04049006030903250001c220724100340c00054003030750191800f07042c0340a405803400c01030f0000c041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 233743093 1250 233741843 233741863
    0xb0703030f0608030c070504061205100c020a0213050702060c0f0a0c06060512032701050702011803060510180c1b03090504050703050a0c08041502180628050a02070501050c 76
    0x1044949401c2208601502c1b4042030003454003d51610a00044c1c4014100071b180da250781200103810300d403400c5042080900120000e001c2075102e103401d2030006880341d052090302e6006800c1c2c000ba0314109000000e0415501814908410400f0300071100490b00043c100c1d44001000e042030000501a46071481c00340085030311840d4040c0000c83c13400e0400002000030b10445080350200c2c82d02c140307900301120030761411034209030000d0010b0041500550040008034240288010120140c0f80d0741d6540c0302c141c0300115070601c3e811505407801c1200b4004035806000700c0020400901000c207040e000149000c4c031420b604c1405001c0312007402c3c00e16000e80e220002400c0090018080b0b840d001c034025010703041c20340d20301d4500b034a042400000244990003070341c0501d901001c80d4020040003141640a90441d4241c040d6085080d40d402800303542d00002030010114101480d0b0100d00d9481c8004007800c0c520012405000c010844808103aa0115540040d07800c01d08120f0f40f40c2d0190154a460154a44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 233744343 1250 233743093 233743109
    0x5070503031207020d090b030604050718091e051e1b030f011502010b01081f0503030403110118030309050d031416140d080f040501140a050702060c040b0703030f06 72
    0xb4180248041000506201d10240c0e001c0351454084550110344e08900fa00c03071a1300d080c20600c041031881c940fa410068010080b07181c060340148801556010b5100d040d03100c84075003640c41e04440030241400c0501b038074000c81d6500402840c0382071410071121000000182032100040030020f501d540000214040d580d0044040d5601d0345002450040ca107482801000e442c0c211025178201c0203417050045401c02e51060752011841d482d0f100540b0640028148107000b031000c268000704150702c0810180000310300480d644c1c10f100310b00700000740c000c202c0700b00846c440c110840d105101194201031228121030064039007403c40c2c036217800c08540030b00450135040381c9004001101000760000c80101c9849134000c050404200c03026001d032640c3e6a2148404202241900700000c100074004034080c0d078810700031400414095248000744804010455100c4c203401d40d06d500b071009203641001020340c0700c5030003092517103001c3c00c01c2074080b91400703480402420591120040110001144c209800410f5a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 233745593 1250 233744343 233744347
    0x100f09050a090b07090e0a020403030215060f0301090605060a080115180207020d0807140106060f050c250905060402030c0d020a090506190314060109030305130302130501030605090a1104090507050303 88
    0x184020f01113180e5206d008000d9160902040ba20342a9100300d60480f40d050b00100504400503c090149030401004145d0050041c004410151400c0c000c241c000c3d4455580055a45440302c100081c0c00101d420655140e072600c910700789410107070103042050380c101d0258190400342403050200644501d580003500b012400c2a10010400350202a0101d50311902c2a9060f2070710158405003200c1c031520a0710002982006043c80050042000b0400200348205440000100246070524411102c4448551400c80c110402012905100300780e0022000c03107007940fa5080440d8400603a016150705044c0c820346c0060301000c241d000e256810700810007d000c0a4541000d0001340c01c1061300000e40f480440d042c406100240c0c180441420f00c44d8005840b0f03041b2581c10b5440445458101d030a8036000300c19810408005652036081501c0e14100014001c00c0350760552800c9015200064901200d40c1d00c075030300e2107002400c045031500320410b050360000350743c03403080c01d029140451580c00b0a0b094040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 233746843 1250 233745593 233745601
    0xb0f0a1b120e0a0b0c0d021b030306100903030e0105210f0a0f0608060c1c06030c03030e010c0b0610170a230c0d050711160806100f09050a090b 63
    0xc0101e5000d0055012000c010b42e1910300c2c206903c4040c95200200134929100014100001050141c501c2c0448a80c0060500d8090301e00d0fa88003205000c200c0b40194004001c010040c40c2c00301031400d11401c6031900c5004580785076005403050100a61880c140803002c0382e4486101002c03401c0e00c0c440c1c400e41d0790315401814418072082d1280416507405a0080c1049440410b101141c00307030404075403c0000909156070b44a1610409400280e01300030051000c02041c0800883d42c0502c0000d0b6002e00184290f0074510b00e0041e02c400b0060764210305105040b200c0c1d40116039100c0b1115803000040c1c5042c00d41c90411038049078007440000c502401048500280084140e0035404100d042102c0c0d510490400350f4040c0e4240082411501c4c0d549801d000c02000d0a003000c142c01840d0400c0c944c0c189202c01c0c100c2402c500d07040c05007008100303007041c24600c0d040040c0c0f04200a07141e00660216a6000814100000b000c800020341c0518021030780c48a01041400d0620b0303002680c250b400840030707405410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 233748093 1250 233746843 233746847
    0x30f070f02130c0e0d0803061203040305161818030c06021e0903070b271c031d01110706030509240103030207050118030204051503100e010e07030b0f0a1b 68
    0x8202110f00d00103100450301074a1401c1800c0805c8a083e00501500d0850340e81108224404000207205003e60006020000002c1c0040100f8122041c0b6844000d40280c10a4081d141c0c10000e0301e504038246040c1303500d5100e03682d000d0300700034145501454190f4004003242031941c081c0c801c452066510021050009908140c4540505603039041101652141e44d07449650103280c0c0a181118030b40380184598a0f8400140c0c3c0b00d40701410032010340040341200c41c0700516181154201000d5010401e041c00304865101c2400304c0101111090030101403910060484030b5480c0d4442c001e09060623518070201d41038005c100104000b00b100700700c43d46003850842c5124a8005c2013031004901610500b0b01c08a040e6004803e02404017240080071101e50389160204400b50801503d80001851b06480790b0407039443c14440e502120a40d0a804200030404400d03241c21628040b00244243c0c0096030b041c4006800d84440a800c0720610108868a4690817031020041c1405e54a011203540c2c01d41c03c24004507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 233749343 1250 233748093 233748101
    0x6220803041d060a17070f030b0a0e0a05060112051c0c0b0a0506010e041d0604080c070501020a0b0f3d0e090a140109020405010801060302120f030f070f0213 69
    0x81028801c03100c003500b0b655122416140a480c503a900050520061203e4030102d030240078111400742c111400301c0ea58010b424032a9809420503105500840b0400c241d00185020390703098808610b00400342000d46880b02a2603600600401c00c802d1302400040b4203014040000d48403400860924500a03101241d019200e410415000c030364a28014000907114100c51213824441c58040c0c540a241c0d82507801044010000d1410741840e840c000c00700010100020003034503208500c541820b030356580c20501003074501a9290700c100c5c115032015010a00086030810756680003d45440b0f150b90545070840d0010007201044654402c0c0121560305c90700340c00124044084150204100d0340d0f883c0d441d0001e8152034042201c1e01d028030b6111800b01e500080a0866490b0340071806000003071030100301e90000303041c5d071070a138028103a5039140c02e814420f61800c0140c2c24008200e40e0010468030b1481091940c03a8062540c1d091410040410f00509001584400d10f01141d402041e5682e4940b1030b043d0003000b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 233750593 1250 233749343 233749349
    0x1f0b090102070e40060c110d0c051b130905071a0d061203020a020f06042111010201020901020613050a02060a03051f08030702130204030f050a030206091b0622080304 73
    0x14400418a070010faaa0b00d1002c0c60701c12060441d00c1a078034070360340302c01c1e01a011292018042010300c1c440e0f00701160f0223015080060a8a903030ba80c11009981c1000c034500295a2501041c102d80400c2003d16543c070320948040c145401040404c6e40034160505600302107942c0d1003010307002080c0422400d1142420000c4c42c9102c0c068000304690b5890348500c0b5982e102c602c8000b005a48148803440152424540d007c0c40075500814581c505900c58010440c00481126a0018005840814010414000203800e801d103c28402141800841e01c0003d540f00d80190100001d030010504c200140300c0c050180782003003600940304541da884124401001800101d0314040c4c096070442030a0345c06509481490b089480705401075003031190725001c00191002e080c5090041a41c20040000050480b20f40d11000c9409280039250b600954100a800d1050003401c2401c1908042906a101b0341034030419003010038195403803a02c3c0c02064800e03040800b01c11007880490500d43d500081c0300b00d0000010815 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 233751843 1250 233750593 233750641
    0x1e0c040e01150801080d0905040e010e070f0306050a0504020f090c07080f0a030510050603070311041809020118180b040902030715020c091605030603120406030903081f0b090102070e 80
    0x1e0b9a03a20b00305e80303840d0f100001408000411401c820011480d103a0444c454940803500001045d271a2200d009141c0180c0f94000701c0000c80c540c2c81042440400c0c880c0c10307449607214005020900d0198000b8204100b11440c00740b1501d0064081900b00b00c111080ea1003079030344001c2960b565001c59650f04144d400540349034001030f0412000070302d503044040c3c07203900319900a40700341e04540b82c8850a4000e00031442c6040185a800c1c8400035158070a2100c9808141c0c3c40e40e8001203001060000500035890b0074020a50f1151000e020458240940040b000b90250701c1c178000307185203d0b400000d002e0414203c001e076140c42007031400b1900322085c00141c1c000c0b03003da408495000f80c14609001c20202c0499891410000c1041d43c041650b000e00b00440c3d00038001415038441160701e948062007600560444800a60303100c40300300426811042c1540c00880c0340c080d55941601158448419003214040e58210300c1c00402c82c1c48591f4000c00490002d448010164020362812405810745403080400e9008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 233753093 1250 233751843 233751857
    0x501090b04020f0f030a030f2a110919020a0909140702011a030705100c0f0605090607051204020d03030f020c0322030209070c0f1709011202031e0c040e0115 69
    0x990310b805110070251384c501a024002c16102501c3c1a900c0003840001d20342031011030030703034145410035000c100d03074000e450b55031030320501800d50800000c034141980c10180104900c50503c034024541400483c25420080009030b0380d820185421514035480d5032042540364107240f51014061440703110b05200b003c0e10b60080080c1400e03e0f038505107405030a034071107800d6000f00d04c00740240c0c24490101c0302c1e451105c8c1072104592283d0360310f085403106405000d0341d20960321000d00441c5081800343c1d81d080203241c50b100f42480d2001015640d0f01a0150000f4490740e003c4980c80c00b052301903007103c405d68224603021900c9003003564005440e41c1c003080100c00207681540d24072031104200e070400c5043e6900070b4030117000ca42d1030400580740310f0718681c1d007a01c48a0300c509601d00000d0300550031b0203244420314801600c8942602c0050141040d00051865290041c0200401c802240a16068140a0f02e14000071616203040c0c04015108940006829582c55000400c031001602a500c03414225541c07404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 233754343 1250 233753093 233753119
    0x16020606040203060d020f03030f030903040e090a021503130606060c17040b0304030c030e1009050102063907050d091802070c0509151e0102010c020f060402100c0501090b0402 77
    0x407080344421191301c1d620042c0c1d05858005404c084014018610740a01120b01d005041c01810000c0d0f041102c1d0300319180e0000409200c0b0710300602038180c0000c8050001c1c03174507074a59800124070400c2c50800310780024000c40000e0712103031031500c0c62101581000b4100002502e42070010608140220141d0b1074140c1040d510500b17013a141c08880841701c402044500716111558120740720070141809a0400c07100710f5846890350b8922140c0c081c244040d446840c1d0891520300003906250004000312500c0c90501e0411100d5080128511202c1d042a501c2160300030300c003610050703540560070020f4014424260302c2c2a885821010708000c0d14103481400e0711421070304041000f40e1061079001814211184030410a500341408020340103007210804580d02c0f88641c01150311585080b102407004c06074160300c28102e513028400c60050b4082b51001e801048095101c29644200181c002401411429000d60396039201d4401074a40b65031050092150b04074030300300360000e204203903000d07449800b00880342 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 233755593 1250 233754343 233754349
    0xb04210504030f11180c030403030c0f020a03141b0f01050108030f09010e04020403060e0a060f0b150c1e010c09060504080d0806041d1c0f020a0b07030b0916020606 72
    0x36400700c0c0c0c2c0c081404030720109183d031413400c454845000c05400c1212280403070703100b04486406601c00e411045505440785068200142a251804020b0040c00391060484c084035501103a00401160103040c0302c86941320703000c03407a2003d100720b0741c000300442d1211480641c4001c0101d144440c41c0c80c00d0f00280309070390700c42c14465181d1207a402d0104940204110f60078695000300c02042600d42c008000608069480d25886c06a480f11b0710601c0c3c242c1c00202160003040b60600c900c50034581c4010f800c0001d0036010340850030081d00303a81c02140c51000440c80b01903508042001110011002010386003019203c034a07079020b4030651150001150070346d0000305d0403a209505641c121100540201109a1030001c2581d4a40d409802c054100351200c030211178046000d280352425030003c40050808010301a4522805500c40502e8820800112000b60702d107540081da1186030340c1c00c5500640d02d03442e1110254010040b42c05101c0e040a045000c21a048021000215252960b42c09072801e646e144020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 233756843 1250 233755593 233755597
    0x40506060901050a0f090b0f0702030601061107050d1b03140709020304150504060f060b0a03060902040b040b0d180b071805061606090602030a0504020a1208090d050a0b042105 77
    0x21180020000e11a04c034a03103101d620545d20503001400d045a8098071501c001c19682e0040b07a003030386070480005660046007000c000545c01071120345480300b038082e03401140030b4440456201d420711030040241170005006c10600f00100c0c03118401e1001e0314056a038a0308583c1148000c4002040d030052000c0040c1e0003400317000710380c80745900001d03501031030040302d0400004100c007410540d4a242d84542140183c85584034032009480746c8180e0b15144c1020b8040103055541e04c1d089484418014001082611401c4d0203a8003501c800344915a1205610100c4100514911400500590594003458203001c1c043c20018003c24290303489650820350010528080c041e24860f040d00f0400401450521446003808500c5403441303281c000c10200529140c000070380e0030035240c4d000016520018401146840005440106401d40ca00100d81e0000d482c1c4030310f54020041040d014544031004d0340108002031122100c841d6110820820608041c20034070950b0b13081e203010014001d0030010b5003200500643c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 233758093 1250 233756843 233756857
    0x8150303041214010501030309080708010b0a05012001050f0609150d030509041d061005030607090e04020604030524060d0c0b1b1c0206060603071704020a050409030203030604050606 80
    0x10040d85041d1500c05180941802c0b40303000d40758600030300820b0980880a000b102e00842c043d030b5a40080600b0081c2e032508146103503100c0a0960b24040503061240c84084d41c81017219824280342d145903281c40d10031420000180c000c03044551a2000704060300420544480c0a8107064551760165039500840d141a401310700c011300d600c240e41c0c11074400041d120300c0082c641394402800c00702e10345011070f030b00c03104801a20010f40d080d0340000040000e0100ca1450260040c001140189040e09000328050705503d60360048603110b034010030000e001c1d5150700e02140c0085034080c080343c84444482155107207954003859801c511141e40307004106185419800300403681c1e001840400c10070b2800d00101130340d603c403240d64400380000d2040e0340072080050100b50541001856154441000c4120090a0440c01010940708038018002c0c000419480030740700002d81c40300500c0a11580303a90000130f21105003507111a61141c24100c024040541c04805075000b00002d032018811501d658007048070034000c0740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 233759343 1250 233758093 233758099
    0x6180515070e030d17060105210603071802030711010516051c0e060a0606050301150e01030902100309060b0604030f080d0b0d0c0e09010b0a090c090506030a05070815 73
    0x1100c400100041108103541144181c100750100038800e0340401e050a40700c40c02c64003c42c00c034001d52500c54107120001584400246009850601142c0104944040c612804002c6000100000e00651401c010080c050816031070601802c80a61406201039402294083c00185c204000c0344801c030014011b0782d00848032042842c0200c05210021201a040307013007045105465604178200c0c1030344511524001407a0440070340310070b26011503c0c01c16a0702d06d9000c1c0701040340403c01003090401d079082040390b100d941e20300420440b00395030040303025055150010f540301885151001100e0381541c040040e15100f50002d020070b1072040c041051038040c500c03001d082480005007000000c1e61b1440103001d2030322404d400291007030b000004034605800a03001100d5042c0714460502c0079541d2340049690044441c4005d00203c552100484c031078240c14441c40b480c490321822420707051805100d406010f080043c2c521502c2c0d10305030740240007038401500c1c44000300703601201040c1d000c1c1c903c1001d140740074400307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 233760593 1250 233759343 233759353
    0x807030c1809030e0f0a0b030f0708090d0e0108090a0c0b090a06031509050603030c0105070203030a05010e070f081504020304081b061012020f03030340060c0c0f0c03061805 76
    0x1080500c4030340c01c0e000000f40c1e031080349040c0c041090002c14014501410b49d042d00311046241822000c0c1c491500500f8202542d071090010031042903204040049914080ca080b40d510b8880060709e600c1c1c0810201c0003400c140c1040303004254076403580007400b0403100407915a50283c1e03445000390116035501242d00c100049102052001115540046400000c0541142d182035810650103086a03010b459000040e04001b060190385012401085e0161071a9000c00140781003204001c1d103008001e40c60302c0103114208000130650440200640440c250180c0195036a140c60b240803012507011108070300ea082d4040070016030074100020414811650302d001d0150703641c00d06c4004075400d424503008030703400784039484070b0004c40e103082c80a140242114400c1092400ca0041c3c00c151016803000110011001c156001c00752043c20340c20341c0310287c3c00c4680040c440f481010125103404141c4c40c0a8080050301701d6100030403070390307601304400c0320b0150300b080094105030441024840c83c0c031580a401540700b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 233761843 1250 233760593 233760617
    0xa15150215070e030f0703021f08040201080603010e070b0409060b030c0708090301060906030803060f030309030a081e130305010e0604030906030c0e0a080f0c0607050319090807030c180903 83
    0x1009001c0c1d03081242410300c0c3c40442400000280381081c10551100541c0180d1004c01c1141020460880d04100d0503401d5840041e84880003003c00c60300920181c100309040c80414101e48084d0b20901d645070080727064400705a11900118015402480740700c945034a8600000740c3c00c4095410369004403d50300d4030501d402890f8991031021b4000e2101d40b54507558900002a0007141449010011849880d0050312407410004110780c90402080703480c041d410801000501d81d0f00404d10945082d840080c179501e403002d40050314901c01c0701100009000c000013807811490000031001c0000c80c1d1080c0000c0c8142c00501c080c4c1500c801c01030314024040b0f82d0001003440b2190090b0004e40d048000e41c50010404448a80021060203035680407010a412801c8644281602070013907842000c0300f6142c0302d1030030400d5683c00e5520f100300c2c10b50b0342c6078480503004000402c0c4920385550040500d4011134031610749030b007480603562000c0d218688035854002c910f02011441809000780554141d110003a000720 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 233763093 1250 233761843 233761873
    0x127060e0c0d06080714040b12031e04030b0421030612030f020c0301090809040b0a1a0a05041d0f130201021507030930050313030e04090501050a151502 67
    0x10105040650303265480440c021302c0402c0003c00500c043c4440c055580011420300040303906601c5010300891080b030302120b4600c1c00004603903124100c501543c411025a16030012a4080d507000141070040b840c0600c4103100380408040d8540c0000d181c0145004003800003941114483d01c00c2100c0c0030302900d0104040380c011207929000000e1401581d071803800010010b821542c02a608982a1601250b16a51820584924810680141c820040c81401c040340c107040000412030300c443c50140054100c207a140302d4020750300101503868041505c1030a082c140514441d007221b15105001004000440711181001000700440e01a005005500041401d960300818010055001e00d5211401c8000088000c40c0b1011224803e500350250309090035200e061000750950904100441482030104800748041c0d10a070317050b403508015103411052400b24002c6c01c00342501a201e5480d001c20000c1d41503c42d00302c07804101f0310200e68051030384c03903d141e9084a0000d42e52900180d00c070395280d0280d07003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 233764343 1250 233763093 233763097
    0xf051807140f04150801050c1201050d050a0f060207110a05090a0509070b0d020c1605011205061809010905060601030c09030f23100f0605090723030127060e0c 70
    0x201c000341601211545140105042e611001240c100d01203031395104010070741080c07064607000032846414034505014044911080320043c0901481001d040c405003040200030407002c9980c2e584100c500c281d034103031424054029004140b090b00e02e000c5a68005c2c44914000e02c44405413a4003c0c2081595102c54180b44000d1030b0061020b403d501c507491011a050280724064000002da0b041e0269031100d441c41010f0410707601c05080705415141c03080511403a0f0300008201d0034070424150009550351000d000802e29006076801c1c10910440b0010700c20504019001319030082d0140c021130702d240d01c60200460440e5100740c04540018542c101c280f000544804071021450b0080580202c1c01350403104500040d0b40720b2004040030f5100c282d0112507034102c1d0003a00030b014200201000102d15160115001900040020007080002c1400b0810b00360b080d05a00b116110300b0804a4503903845007000d0f18030415414101130300d528000100310900c4460301400064440804c96083d082e143c4c800391500d50b0f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 233765593 1250 233764343 233764379
    0x20313081e0309030a17070519020102040b04180b09060a05060904020403080307050901140309120a051c0203070e0604030c090c021002120f01050d0b0c13050604090f051807 76
    0x7442000035040003070891a0103540100c80c07481c0659591020000040c09100d115200320002c15540f0302044020794002042c2c482c01d02e00703407411426621050504038020312035500500c03445e841c04500400c2c0c01c440440c016030f449070300c000d040000b030201c2800c0248041c0f003107850f9a800001503001b4440c6060101c09400d80200191015003002d071079030385c3c581c500d4104488050008001190313040d03856070f0054a03010804030020b4840c0c51410314410494a400d54803440c400d110000103904c24017503209a04541210300c41c103c0c14030400300c4d5121450069842500c01c400012420500c203083f42c41c06104850440c1d0780054a130145514100450000e8940d0500110a41c0500343d28038003180145c0c0010043da6101c49034a41c803d00c3c0c41151485510410380010340030728401400040001d00032050361703400002150b0f5490310f070b032258160005d1445403608415000032012800040b03040b11a00b1114803241c070344d1028007840e034450a0746015a042044013840e1944070b104100303d8200041903407021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 233766843 1250 233765593 233765617
    0x81509041202240f060105180d03200f0c01030605030c1c020604080a020414060618030f0106030813060e030303010303031107020405070c050c0307080703030809010e121c02031308 79
    0xc00012071510800d084022241c00c3d0b10f5901d8401007100c64034040001e00d521460900b40766040540d050499040040719404060050b500700440b40b0626015203001c8242d40b468100070841c03075400c00f10264a44003c00c211500031f02c208e0012481541c0a07001d0b510a80da006001011218041c004102c480421031019640118905001602503154000200043c002e0403004201010051040c842190103008a04004507a1402401b15580e1203108a55400725141c1000300c087c48048002403c100c810400b1601d03942c80e141c2d00000b0840d820000e03050320965117000541e199a00c2405481c10054440203e915410030401400007a000c1d45c400340c070488074204543c6c18003600b81d020404483c0180c580d640800c80c0c80300d145003000000c001e41c4d40c1200e0300750040e01ca4507240c480d04a40d01c09a03400000c5c240a0b01c440054003d070000d600084085a0841c116072102c64a440704004661005203004103102c860070440180282034000c4a0264041940f035001e461f101f5107c0c041160440000002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 233768093 1250 233766843 233766853
    0x503210d061203051c060605030103120e121e0a0215030c09040204030c093b010e01020406030921020304050402070615081006050f18060d05010c050901081509041202 73
    0x1020b00880388212030080c441d0716143d0f964056240005140b04000420f20051030800c00d09100d070319888020703241120707880700701640440c41200d0183e60740449005140e8000503000405911880d00041c11002e0703c03401c0ea2100c2e862a8010b110985451881d10043e400450350783d0b05503800e10b00d020045500c030021428080c1004840703170014050b40c0c000d620649120b00b0b0294140840d0760203100750154803100d031003070101840c50b0340301109500d2181c2032065100d107440c0d6070065508000b90000072031405940001c66550b0785454001d001443c0051003911951001040e8030800e918038862a10034044e01d400a5091502d44010170019520240c4122030361510341c650649517000030100b80002e0140c01c0003400001d40715200301d01c11501a94800c1d445440c404640000c11344503500b8041103031248181400055540d4004030f03004c04c900640c000c040303610745441003c01d10303401806450300010998950666494a181d8681503e4008000c544d01c460610f003c600012011504031701980050b0040d15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 233769343 1250 233768093 233768099
    0x2060f1f08030a1d01110706050f070605180c030f0a060b06220e0901020703090308250c090b0d1e0212030a0c060c050307080114030c0409060e0105010503210d06 71
    0x80c0c115004401c801d80410f2003071841c22074208130343c50b0b1000010400c0c40d040d00007650349140c4585e03d1002e0700c50303c1c050000000300d080120140404640c400740d0410000e20250901c0f05900a660b0b00801c2e0008150242c4684582280b80105c0c1419068040d40c004214000c1941c0740c1000410034041125401042005646042c070b280042448217680c0d1b44407035450740c42ca0f00c0301402d401c4d074005190b01c0c0617910402040340000d070003500c2ca6081d2900420700d141c44881d5a0004061040649100c458100c030501104081292454208080d21440e5500380a10504201800f50903051000010160000000603a000e00c00b95604016031500051000101e541114161411075000c4043d11000400b0750311800c00340030a5000300d4641c0083c605c1c1503403441c64842c400408d0f141040c059020341c40507040c0d8402c81990b00300000700640100400c10000240185044002040a85945481942050000107061401140c9410b01c0100c0d00040c005003040c5a020264591008241d40140383d9104404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 233770593 1250 233769343 233769359
    0x3051803070302090414390a0b042403060b03010506070609080a0c0c050a0602060106080912030f0103061b0509010f091707061d0f0616051204090c02060f1f 69
    0x4c0340528040c00202c3c2142000c082010708050302c200c1281c5080c0440c03141320f603030f48a00020030501641c00368101e91440030014006251000c07550700c00702d0040c1000c00c0114000c80864081203401c400301d01d441c25500b110400980035110705200f048003801043c001009241010340091154511507440042c1e114025681c111042e00700000582c0000c2c0742031813642c20054035810700d40240404441c1c100f07905290960095981c5814001e160403c008000841d0801c1001c0085000001c101c2c45900e0b00d901e045040d518074550248820743d030082c2001021008034803c902d0641036400140c1c0c40b189020440801911090040c002460412080550008180e01051201e400c5403000c40040c2c040c01d031a11030f000740214441c005221082c44620b0a0640780ea46005003400c603840c05940302510b0b05103114902211951a00740541180220f80102920030f5100c0020300940d100f1410070082001c1201c0100d0b9070700412502031011840e024013203444c40c1000c151040c019079103000342032110340e00d501345 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 233771843 1250 233770593 233770609
    0x323010f050c0406020708120702150403080d0b0406171b0d020904060605010f11152509050a060905031f1d010c0801091406010804061b0c0b011203051803070302 71
    0x200c1031a0040380502060b0380c144480e00040c403440000301001c4580c0d2380f0507451442800710080c8208030b078454100e2070341c5800094800540c1c214481e192207044040b8000050600c3d1a06503204a20304200480c1d880381c0c1102440402d4900802040010364450b40c04201044c81502a94490515004400143d98510301c00740703d14420792000c103099161a001408401121030682c09101624070789102c0380400161b02a0171042c642d0400456444405483c0c0180d40c0d18040302d0303103041220325102e000c1904819a8002c130740b0166081a5420750f13400d0201e030b05651500805038990007842d100e04100e8210540c014144801100000e040ca03d0400718851420f41e2007158002651120311010f403a50700820b00c51300404000350180704071080c00b0741c2c0540f280001030015050100341c074045000d000490307208800108504d40c20103030b1551307140c0b40030742000315910080700d4801e041000401d0155211000c01e91055050b2243c605216005540300c80080588820303035014420403000202680c0c840072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 233773093 1250 233771843 233771851
    0x5010c12110f010c0914060702090f06011b030309050f0f0c0d050f0f072d1503091e02090108031312080702041107140d050a0f1b030215010f0323010f05 67
    0xd075507460038034018041040d07407180d001187c4a0031091100c14050b855183c0b81e80c1d4801190b81071110aa59403c00580c2d08810280d41c034105115080003820403d0b401d50701400304180144100d405c10240501e0042e95503100d10600d5000d60041d60032a00681044c1040801c050f11460907248031300d600d00d00302480c0047e8501a0030259100100030030030403018546455003201101c0d81c011425844100308001d1080521420100d6180300201910151081d400070045903800280c1a207a20081d007544800138020710320070303032060203e0000001d8445c1e0010840300d083c2c12094056001910f000c03070300000c84111034803c1e00c808030100301c99401030350b070740c803404040c15400c801a6441d001e45040243c0200003020403460264004040c5100c00d5401805a44402401d89003610f0950b0300400101c5d001c0400c640301c0c0b074060794120096401c250b0003141042d05090055402450360b03913191160766100000d88005400e4448a40e226000f0a08084052085804003000440e500404070a40c0c81141e008036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 233774343 1250 233773093 233773097
    0x1005070906140c0d021f0b010512070c05060a020a020f03030609010e0615030a090c3f06020d0525080a020307090b07140709090201050d0506040b220605010c12110f010c 74
    0x40c6c10040312000d008043d0503281000f24200f08110341c10b030010b402482403181200845694100042a052040043e0001707554001e02755400b608001c0c900c403010b500030200141c0580140c1d02040340310580042980d100c0d5000034440100c80c1d1902c0a00e1038501c0d000b5090980086003203480f24801203103c401107004040800000807104011300b8807403113016241e0003621100c5280120045850140200e14203050103080c03140c1c203c0c0c0c140a07030b5809800c00080c401072401d400440c420b00c400c0034990103184204001c1c040c5034401c101030b100707021030134441f0100c443c0441d22520102e4044801540655882040c0e0b0070030703101c40780d02c4025032015900702e10340c101e40c00a40d1994842004505000312001811407820a100c12680e660010f40a4001e40744a00c0c0481d59034000251183e50b079800c8a20481d001401444190080c2c1404268414096a424100c0c4c0c1c2801000511940b00754019000b00c0d4010400810369101c00320100d503401040e2030155220b2207011165406842e00b0720071000c03142025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 233775593 1250 233774343 233774353
    0x50313080a03090e010e07031a0d050307020a050406030215030a09021203070c0e1b0c101401090b0a12060b03120f0409051003080405061e1201081005070906140c0d02 73
    0x680b8000b4150305041d00181000c00101e001003110310580080290400344500f40490321055070f0070a6a01303801041764082c1d011481041c01c0b018014080014404180203650501c4000c4e2140280015600c941c0b0000303400031442c2c1c1f448000340710f0301e4014542052021401050004103500041c50380356126580c0c290300e0b000010b14504008500e5241d500908001c1c0480245150560032030303944181d0800c0b14001030300005501183c0e200113008072081814411400c00941128907204400d02500f400f0b015009407030040864414a0050381c000211440d12140301f614030801d03500d0030701400b91000307000c0d01489445031150349201c580000e410a010305607403a41d102d81c54661014141c581c003901203580c0103032044062012420308002c03102030342c60a8031590b0380c40483c60000780e020458908074684c406404240f491416206c00d081504841e0300f2000c407002e8092907582e44040362002c0c2d80d010081390b440030341007040c1c0d070140101552503400c0d03e903418249840c2c3c00c0100d0800760000c400400503040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 233776843 1250 233775593 233775613
    0x2030303010e0f0603150601050903030d020a030204080d050c06040627060213092c0708010608011a180a0b01020309031005040201031407120f0902030a1a010501031505090405031308 80
    0x211030206076004c0411801040b120020503c0c4c0c194241024000a04001000601d801607450400880355a2000320310304550320b00d1440c400a0094110340944c42c03c030702600b205a40f51314401e006a80300c407405140580082c0d00d50b60380788001800d15094101e004803010f803651369103070300c48921721181c0d0f0f002c1d0b0f0015030717254280308440c0070401c46074104e041d0491401030720f003064041d4448403408040011010321130904030600490319008a980c024601c81d828400089600d80045d00b240c4d03c0206060907010520a81a04120020680c00d0490040461a00001c0e003034500a42114601540c180152072a1a914038042414404542e80c81d51078580c80e030062000310359061044242c03201e406040324007a401c042000400c0703000f25142c24001143c959840c03030b90042003070340060800355000341165122002850f05104c1c145175090701800d00c40700040000740c80c0d40603000700a00d11481c449507a041e64101000c1004000c00078005403581e100901c0f05450340d80c61200f503c1d000d003184000401c800c1c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 233778093 1250 233776843 233776861
    0x3060a0810090308090a0b01090b030703020a062708061302040e010f051906081213170f0f0105060307030f060207061d01180c05010804030e0a06210c2a02030303010e 73
    0x13401400ba14501e6011403506c44c01704036420b00003415220350820118001c01c1100000346411001c1e00082d504c10b908000c0020f5464000c071003610100109024084c2010344038003c90074000c4a8860121945c00030f400158070700500e6003492541d0351004000081d000a80d80c0c40e1421a01c4030001c03850107030b54400a0111f941902840c4504d80d045040b0f0910a482c20103018685a880781d2900000b05480403801035a840407030610640541400642480c104050040d00b41e9a020f034416414498015000c1084141106000e450720684024004204a900d035648802c4101c4c0e00d01010f848259007807042400140303050090420302c828081d00c041070151030980301c031f086803070207801d54203024802d4040d180003a2007010b15030115182400d10115580e81d6040c11340c1d05001d0f5802041e4003d0001a004c103c161704400c1c05181d030340e600c0c4450884040c0c44252401150b000c041c0314008102604180c82030152118012160803034000c4c3c041502c0e03800fa9000c285160001c0c0c008401c071420705010404400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 233779343 1250 233778093 233778107
    0x90f010c0e1906051b01060806040821060a060c031734080406020c0307140303070219050318120a0302010b090f16050c0a0b010e0403021c090b03060a08100903 70
    0x10714030000a42c51803c1e4020345148183d610741d42140c0741003c0d081d42d4506013075014100070041c0c5000e540c01c51821340340c002040d5201300d48201c04107900107030000c06400020754451103244040c0c03040c44030a0030444247d1b40140c00e210128100480701415401820006000c24010790b8403010030704d6a084148000034483c0b20f803100001240070360040c01e107d62944141190381050f000100143e9403411006142d0440c07003107040207090150b120250f8422400004000d6214002582c01e641035080f8048030800d40c142441c501a00c203a00500500000c0408401c007244403150080001d0800d240494159040a1194006030301503503407010120703258209454511782c0300011011200c61403500d404460b0001c1000c44442040101c0480c5249640360104040710609400c0440c01d0000e60b5503922500034020308840c21401401600e0103c46074980c5000c200782c62780b145480d404841410441c0340009900000e01880e404a05040002a240424045101c19801040000ca500345150030084d18207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 233780593 1250 233779343 233779369
    0x80a03080f070f0f12090c0510091235030a0c0905010f0e0103020d1d0c0f090f040206040e010b090109060e060f03061504121205030f040308090f010c0e 67
    0x301c000100100e082e03001036801d000e98200c0c10300a20144003150111803401000c03000c1c029182c54441803c062103100e000690890300120780390440c40d41c01d104110381d035a41c1032042600b1b0b00c000980140c006000b1004401601c444082c4000c51b00d8140554000150044007030301a031050000300b402048403480c0030b40710074880241040e0400350300c4c20000070000c1010101c030310108541c0d08414200d5078482d070100c444140c0050710500c00c6580c1e950f1250401d148000f558103081c40f80c0f030380c00d400908001040309030a0900504a4105d5590380940030441e8000a10403680108100000b041003040807005074060102c00311025210744515001400d905c840e50440f100f13110400d505004c1c140d131144216082551410880740e04d94840c400030030b8818203006540c0301818004540824104460b103a007010550094800c40d00075481460151203501c415500580400c190714001004a40a8a4030320340100c9881c0441c0c0002c3c401c60318084c00c54038036245c40030014035003412080c02460900c00c44294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 233781843 1250 233780593 233780611
    0x15021b0d031404060e0f0f07061b0c030f05030706051e13020306180c0301060b0a02060705130302010c1401050a0b0a050a0f1401050f03091f02090f060c070f080a0308 73
    0x200105000504030080b2005000a05241e00c50020340803d0303c040c481c849030300c000c0c90301300c4082c024108079450b102d800c140941000624480b107600008504035440041440c5c11a060140d8603085880305644031181c2c0c00e09684034442048104001038540c4144d038440c901302202d03174000c140009190072811201400d00107441c50081c090501503500030810ba9040f0201440e000e1161b0f103040106420300c000c10148641c9946000c90025030180c40328000d0a2a14041e4241c400c1550703201070075107071406910030000310303441030b0a0180015401400c200301c80d280904003841503600c65803003150035100c045840401213a100d040444150403c03c10301005804100c400e4a02641421408035004d4103910803100003d0708824030740807690258044a008035040103400360340b8038140840c2940c800d4880c2c80d0b0120b6400d070721031036030308443e4501c00c1d141c034440700903c08145205814100704490b04a6800d14403940114500010b21381101d4402d00b00410005c00942111035040c1400707407245900403c5550 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 233783093 1250 233781843 233781851
    0x12060f0d020310020a0903021305102103050f1606151203080435092407020405060a170a02040b0a06080403080415050112260405060715021b0d03 64
    0x581d000f04109080010343c200041e1280100d05017141c401c151640041d4000a68600200c022611504054403481000100755425542d8a11065140e00c02d030f90781280700520405080d0000b4400e00040c083c0307005051803a828011507000440c04c2404c8020103c0301c0d141c0d01d07020780101401c44420174005005640e9014840461524003819501c802080103051500c280303080000d055407651507003800205000c45502e40ca00306260368950350300040a00d485445a8070b240c1001c154012038034000d1070038468500d8104400c075424400a841c4c0905032941c401c152400209000304070000540c80c3d21030750401800c001071540103000c01c8031000c240b414001c512844007030022a401c185000d80065052034880b07107996071400c00c891120141801c981185042900004460044403d0b0344250f0703000380c0d800403503030300403285042c1c1d255038985c0516042c2e1010300082050b0718085014010306030081201a5038065190240310883c5e022010483c08003d4140785e0541c000c4003002940b11500440c28104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 233784343 1250 233783093 233783119
    0x40c050406090e04080c0a050607180302060a05090406030222150f0513090219080c01080108060118090501090f1a10050d05190533040602070804080312060f 69
    0x30b0602e8802d00030103840032800f90103e402c010034401210b16240351b40d81561a00b85042c904184c4800064460310000340a150400c000000700c0321134001181e60050409140c68071520043d1000e410589215900c5580c0d8000000943c6031440401c00f9100c07031a48101414200c036820504039902c80780c0d82400c190754920301b4040341c00c501100000352081290655119141c130900613014250f5110029000795050307010286040b0b40c4e0740300c6010703181428140e0340307260705070310044814000911940b507150307025030010006030b14240c4400e0a994510440403a10400d82e4882c5400e50310300780d00880b0000c0010b52a4010300a1003c50782500080da207000c603085081050580103010254010503201d081115000801c2260401160264580c80c0e202c1441c41442c40c2019034071160b0384500a504914180320000400f01c40000400320240d814002094030707115601d44000a4100410885410b40c041001107205c440030000b86c078408000310036900e41e510707007801404081410140d4030343c0a034180c06400303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 233785593 1250 233784343 233784347
    0x815130212153403051009150e0105010314061207090e030306011116030206030703020702040f0e010b0604030c0e040c03080c030408100b010804030c020312040b070209070809062d01060e040c050406 87
    0x44a600002c03440d011a1701c0c1c0350f00384841c00c0d003009540b084030f1461800e40d062003190400507200e01100e489640340f185e1a0380e00d100643c1038800b01035200c03000c15a0700700094150f2a110b090341901d40d24400071100e82035102c0c1d1130070003103541790200e03640154404410001e5540e8031150210030b104402024140030b06100441e01c5402c41c850100038890b050120004400c14441c2d41a500180d030024410b0146418010b2094020726185000c44225401c02030901214280681250201c0764080c800804441c0317031006c107a6051401420807203500380c900400102060004000d03106644402020b141d40b14603148070f0615040ca80e0300ca4205c69420725800b03012584c1c008161300d034881d416003828010100c05100017401d000070011031311050784000c0350200d100402e0201500c6d0240c4282c6034140d00e5200c0031410b441d170f4001210f070b00b0680d82c03210b00042c0c0d03680d41d6280600301c514207808000c02d40d100781151500070729000360028000150718a4030882146402e002d9200d4600540c181645050f00381840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 233786843 1250 233785593 233785681
    0x40501060f02030f09030a1a0a0c0513060815030102070308010f060306060509040b0414070210051f0510030207020a03080a080f06091602030c03040308090307081513021215 76
    0x20b811311802021540c0806900c0c00d000c0a90300c554804071502c10000041c0ca12100000260b4241c0052480c0c40e4480b40c4850150b421250001c412240d124461850b140c402c0b07401703c00c010201a05c0604840521110351424005080c0c0103110791585002981003103c400704000c42030f8008001c040c20088200030349500320080b034954003011b603400300300c403928200820044c0a914450301440500c54040002c003030703800304045098602110003409503842c1d0040401c0e503100c0c2d42103681c010b10302d455020800751424003c511007240e030034100907003840501d400040e18000103a02c1a907486200003460403099a00c00c400551106200ca1171a18509024010a1861754020b05c0b2074081d03803541d001680d006000300242d034010001d1004595485450f8070700141c007504041e9529011348100c640c080703803040c0d0200c0c1d1421030741204162260303299920710910b8260980c5600903a081080d83c85100d0b0f030140103020304801440c00218400550414550b40e20410748000079400080940044030000406590300c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 233788093 1250 233786843 233786857
    0x311030f0d0b06160809030c031203010519150e010e01030c080613020c070902130f0e0624120f0106020f03030a0c030e0f0109030206150f3a02040501060f0203 70
    0x107070009185002c800403410a1040018410070b415100240804018a4800030310081000b5020703107504128000a040c0d64100c400c840342140c00f0b003440107010a013454407469151000d1408a050060358a8036004c20942c20a084000011510035048000d0b50b004210b04441100a00c0c04018140e1102c030014110301c0c1c050b03c01e9104680d06070b41d1000c03888290301511800103502065031049030b6184176001c025130061070f061302c5c1b981c0702d840001281c04070005000e0480b050401840041d50341c40041040c3e500090803a000e41400003091340c005948010098600701c803524014140d0350070010b10540c50030105074024411940981d00c461821076001c0152078000617910f10100394000081010741c06000346284c0d61190303200381c02115049140540280190600907002d940c41c1d030b25041000700404614416240d00941c46010b00c6445044c01d02d6150b182800d00c100b041d281036800200104400020f903484402005c0070142070040d4a460310800e4010302842c02c002031190400c510182d26401030305 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 233789343 1250 233788093 233788117
    0x203060606030c03060d080c0714090708010303020607050306040621020a09020a05070303021b0f03120f0c030c07050f03031305060105271b0d05160305072c04050f040311030f 77
    0x83ca080061f04000d82e1843c017040e000b0381e2981500d4002c0f82e0518119154a80e2060300030030041135034140980e01e1641a030b03416038054041c641e1081401c0e112a400a00070b81c4d00260b640400283c089564a16003281c0400c40381e50003440100d600420042c0d000d640c00a1440b80d1040004081160700482264112a0705050160b182c1c90010508200c0d41010340780c08810740507200307184102500220040c079030b554140100c22500d80b11201040d00040c0101c80044050b401080070801c2030b003142d000750134810301c00d4007200c07400e42c40f042c0c0490954109407414002a41e02103044e0041040a106c910b0141400b80c51030f0040400580018442e00e08141d000183e0113403007008078864445038841c1d03a0308504d0040344290340701f900301141c0c07004020403950b010003540c0e06048010414480e00903f4011807c0f6074a40c00300c4865450004d0401003000c5040c441c41c038100715100100d454030b000b0144140c0b9200c1c0a107010b031070103080141014807182d42a82c0503030010042007540d6405031040d140c0c4500a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 233790593 1250 233789343 233789359
    0x1020f2a0415081e0c150d2a021b030d03020306030a06060e0a050708040c0510020f060c09031606090902030a0e2515050f0a0302070c030b01030203060606030c0306 72
    0x40d00219009010420ba14002480c0000c40400c607000300080c2164a070f03c80d42d05046109034840d2010f0703100c030f1040200301c2e446084a40a03c50302030104000d4801c45c0003418000694006e02d11001d131105103003801e58038141d151a12a800020740511400307603046031403d007009046a49800294075013412900c601c00303241d03011001c11a240c80401080e002e941d0700c40020041c81f0303142c0c2da0f11800400304940d002441c600f024006020a445034288034040c03503120780aa80154104001c00c143d8401c032490b408110301c54501e15402060003002003e000300386102001e5940c0d011a410f01d41080020038921000310f1842030304028090303102060f2021030f091a03c00503102e407149010301c4054002501d203d0b40318420755500303034040c8100524129114059003140c1114a59889c0340035400045000071401282050010035482006a0020100d100091030014a40001580c54020038009508203a5039021280018402c6042c100309480d00701c5000c0710030074118903110b0b00b001c1091000420850140c07442c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 233791843 1250 233790593 233790673
    0x100b0403110603090705030a05010209091003050a0b0c2b06060306061b0f020d11040608060601020a03030509120c030712030515010309020118080a1104112d031501020f 74
    0x306000100185c440181903400d23184290410340e020350400050507205101410210700e0b03600d00d551085041300c2d441409403041c003070203480322182d00e2002403040784450020440940d00d504003585c030050000280e50b15080f28203100300803e0468845400201c01e05240c00030074018141c101c480f030b07d07031080b407503864070b201000c64503110807103502d00c42c0d00075005920308400100b007145e0040c6480041009486c104021a0f4404e54242d403640165440c41c056004141200d012034841d4100550101a220880f80c0e51214103449d0680766000250600c1940c00c04100d4100b004010b20040c4c10406c15440c00b401181050083c41e0356480d50741516605140e603070442c03641103901540725050458942e811002005030381b503802684a09803110100c58103401c43c201400ba61529200d80c407090030483c16a2030804400a0f8100314010500800745c20402000c012901d10320782520013580710301c800c44c0304600c00452210019142801d00546111190003505d001c402c03802101683c4400c1c0c5810301080c03092040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 233793093 1250 233791843 233791861
    0x308040807152d050103030807110703050f01050f09060903042c01060e010e0103091119030f030903020a151d01200109021c0c15030f090605100b0403110603 69
    0x6410040300035124100402d5a0303180c00b1403084000207030420841603000c443ca01c240c01e012a40700b400010089100503001ca8129071040c0c104c41e0700d824500084038001910394481c02e242c07401e51034844940d0307911032003042850784030380d9501500710314014010419420189890f90f01ea00032030044464080f90251705040a041c0d0f88880e1032040d020358142c40c2c443d61500310080010302091002130204408145210481d40300e80700d004001034010401c4e041e4042c3c0e907410802400c1e95005c5401303102403024404400b0482c64600d4a064034403a403079003007440386540705200680480782e0210303440c8402011040240f40e08601c4580c4418810110030340d01401110060340ca05140807032540840d040c03620b10b5241000150312051001d4000c98044010107040c241e1500c0c2c1509412004184600d800e8041020003016030301030362031460506010580007002c00e40c0e10110b0301092410b039925070310b550600559017624012007014010000b40f40d0728190468440c0c5880c059503c248a008800010006250348 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 233794343 1250 233793093 233793113
    0x30614190f06050405040b0718080a0f020609060d0905061006020d0c03261e0601120b032a010306090b030c0d0206120c04060e0f1c0f0501020a030f0f090308040807 72
    0x30052003000503003481d08043c5821f54045a8203800b049881d40088c5201c461590400222000d6100410900042d9500d10000722113100e000c0360442c005200000390341e900da4018107401402d036a0700180d000528144149440c070b010308481f040c0d07001032200740442940800c903400e00c1e0302c1c0781c01d24904008003450304550010300c0b6058448000d4004001c00e289403141c6001a0084600c10404031900034620451200d041069954502066088070840d40032485504841441080101a10030a00e002c0f042060b009862a414203003403104880446050760300361240a0103050b61581c10480c082011000c40d50710740038030700c0307051084d244903010004540c0e40f83d0031038031055000c11303110165003849071302c2d240b00e40c015005240200740d5094255041d420405105031203820000c2c240443c03c542c1a18158500c0c0111030203498201412038804003041e401d000412a0f40d5803541e00141a200081206040740c5420001c10072150902d00c0c604042580003070303c0c07908107802c6a182541ea20300c2c0c2c82c0c108110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 233795593 1250 233794343 233794349
    0x405070306060b0a1214070c05010b060409090312060e0604110906070b2205030a05030a0213060806010e0f03060a02090118090501180903080c0d021b07030614190f06 73
    0xe542011400700f0405100800780035210a141c072064000a803903070050056940c0d4042c150300846940000403022440381003807120142c00745000040d21814113000c2042c80e445604014241340d155000034003010360148500c00c0c18000c4d101d00304056400c114bc440084c1c88080c0ca190f100310780b50708a00c071400100c481111303240c13040103219540d104000c0c600314003011801c494503d070030554020f600e40311000000040300c0711039022002e50320f001200310055440e604040d20034501641d0034802d48030041010506c00c00a021541c0f00c1d40400c3c5482c2000422003034030145800c0c02054000303008950303610000350f00303a081002e940f0096161030940004035030320103a03500f07010342020f0010b0b0005004545988910b040c4c0761000c0224030121000d00451060320442c1030700a000440e040001101915600040c000d58103003481e01500c0c1140010030680b80101d0240c40350226040882c007001049250320a000120071291040052850b00e03281050b00ea007070070b1200c041100d40328805101075000c40c2d4451006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 233796843 1250 233795593 233795603
    0x140d0303020912071205010506060a140a030b0d0506040501050106030e070504020a0e0d060b03010f0506011706220e070501020d050406050307030204030609120f03180215191e0c08030f04050703 85
    0x13903070b41e5020382100d00c100880b041d00c013540303014003148007030030520115001000240c4400304003a208a00b6500301d6800003200038101035407007201c42001e0391414046101503010b640203090038182802c0c40d03800c548040c3d10000500d440c1800b0b040842402103601000c40300200c0e4010b07101c0d1203040b02035440711090015154170a9052401004111107544841d4804400b60000c00c81c40b502520f1000c11650306603071103400b08901e11035018021660403911540b06a000e8103082009001c84440d9500802c0030320404180d540b0790807051010035080011500401092009003401110f910003d442c0748120300a11007007120000004680ca4020b1b0103c500840e4001c0082003005450b05003000c201742d20006890000e0300f407001600402e8417a00a00c4690385a903041544100801d508001d2456001000c825020f40306200b143c69400d544203003400d0640680d02c1e0402c444000f4031844406000310b00d0610140b21540743c2c41404110040243c0758410040c065150150301c40b810031a14002c0300d6800201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 233798093 1250 233796843 233796853
    0x3070620010b0a1511121207200c01030b0306010509040b28020705010c03052203030e0a050f0d0f05030114010324050a050301020304050d390309140d0303020912 71
    0xc0c401d0b04d0507007a5800300c4031580c4490700800d12850b590b882e803001c540504030154050045224031502e46c0304264011005d0309018007445070040c80200d03658841e59030740d00a6001045022203030350b00b5004032803900c04114003410306903050500040b010340014201070000906071000030300d007012114030303201d001d41c00c0314100540c5101c1c900c1c00000307580121000c0382c0715401c01040d602e0541c042d006460040c100060380c0b02c00402011072a0140d074840c2d00b000c1e41050b440f0480c0040c0ea04052000312441402000645682c4104400a6107044400c003010800c005420041c228901d6209059034151180650404951301c800c3c401200605080d1064180407110110110012080e80404804441041d28040f4034250340e070081500302d0004550282c056008180c441c0c14451050046210303020403d08041504481c50003010100000c9160074044006416804c20038582c2040100c0000c1102c0c00582c2414a10b00002c00d5041076100d80085c18140c020901241941d5040001e400181c000c1007150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 233799343 1250 233798093 233798099
    0x1704030309030c08070f060f0c0c0b0a0b0a0830070209060a090e100608010903210204030c03150b10020c09101e050a0f0510082206050f0603070620010b0a 68
    0x7001d61580482c100c030740c50300d051078201c200d8023a8096044182c2d22034650004440d41038441c446041801008124400d99800041d00943d41e2001000e0103031420800030450390f4000c040102907500064030812003540740c080c040301100790602c00c40d402c02c1d5060300c0e81411500e1b8040458460001038001d500150704103182c41d10000710000300c10448200d1903c0a1126907030b03d0598508031211810301900081000d9800901000d455010300340c40308080900524189d0303242c40d1407a0700680b5070400c803441900040390503070b0316240340070304900e07800708070f83d1a54400754200c8040c0d0b4415501c40814028001800000d10011039242c07150018411140c1d4405a411245400d00e04000c29020b0540b10340340c80207000c901c6510b44800003081d0b440c060b00201040c448400d040d2492040104150741031200390003600d021410526500860512070080850142440703005181003c0300209071500942c825081002010f6005984d20201d0a101c2c81d014031f40b00c5e2410680340503028400749a508411165000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 233800593 1250 233799343 233799353
    0x160b210a0504030311130303081302030a291003020409030c0507090c0801084c020d05090d0905040f0204120308040203070803042306070609211704030309030c0807 72
    0x2482c40b6510903035080044120101c6000060f020702c40c007075405880e0140007840007a00906400e5040128081c0d040003403289a80040c1c90706403281800c0300c035000313400c0c001c0316254240c00a00d001d184560380341707010340c0c5084000d001d042182448041e120742d40b564118000d06009072603548001d504a0300f5143c056880700b0707500d00a4103820003588009006d6100001e40c00b200424800152103013600c0c1650b0740c1c020108901c061480701c0f85101d0011840d003142d62544040154002c20000c0d03040805a01c0d001010801e0302213950060080750f842d000320700e558914a5224520714160342c02200c00081303241100880710000c2c003942d080f4141840f84c44240740d091540100d0264402d034800c904986189849802490701c034020703440781e8600c0c403c1d08005580580942e801c0030701d0151018201a040807561f48a10094401c0e001c0181c80c46103c10862928541d47d03102061840405418031062a4001ca10380ea1803445000300058201940d0748410420144940b18880c02c0c07035001808661148074600304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 233801843 1250 233800593 233800601
    0x7030f2414010f0e1611120c160902130303180b130527010b2b0b0a0b25170d0e0105160c1b09021605060108160b210a 52
    0x240f000340041d00c80001500080082e2080d11441610b888034059600c0c510b0255480c0d0000318003103407203004580c50355103c10100409402d00c044040018489221071001c2d8940c22501608202c06003401000b10b410400c003070504100071640d040c80c0c040b0440e140746044040a180641051541036000900103003a0910400306000360750301290300d04080513045880880342e1a030b08a0038a0260003010040000034285805898580b10503507001c100d030050460418448022003081c81c002940d00d04650360303075050810242d8040d110041200380341100091088040301c0b140a1140022038400311308000b00303c4c40025601031507950100b102c2d10303043c80e80e046601078011108015aa9860580040c4e540310b5440c4082c070001c02e86846040c60385c1090740380c04001c0c10341840e00c441d00e507504402c0050200d4452004040e8070b0f0200309061902c1c031031403034401e04101041e800800c00f60b20080c40300b0800d03500080007800300c444c034560441e03650346000780705800d841c56040201e4403040e9040030405500c2d01030300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 233803093 1250 233801843 233801849
    0x20070801020705060703060302130504020310050702150703052206200d050a02030f190e2d160b25060b0f3a02060f0c0f07030f241401 59
    0xf0913100e241d038584104400300c03500e07403001071f51003403e003800401c6080c100d9001d503800500180c25504034008400700032060780c905846c288010ba00038102c00d40d41c0c29401c4c0716150030a010703190034001803c0c042010750040241c0080910300a880e070400c00104049940310070080d901e003180302403010000d841140300e560000c0045038202e0303051200041c0004158030889100e84041c50043c103090300d50248110307000240c0203c625116940780003261089000304080210a50b820801c13000b42520421401c50002074032440c0c480c283d10640d00107406d040724803504810b50781c484108545403442e00074603801c82840d4410030342c0c00904c8904102c0601540b07070806040300400782c0d07548084100301400d110080140c2480c1a8610741041d01e90309200c5007030211910084188909000442482d40001d4030b45d43c0300841d210442d003000158909800824403603401c003100003030b01134241760f451078550345a041401000202148180c0c1c107031410415a51070900c20015403004100b046402c420205808600280 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 233804343 1250 233803093 233803103
    0x1005091c05060a020c1b011409040213030c080d0c11122a0f030c0a05010806040e0f0d0f090f06032304030201060608090703020d110402090603070306030c15080403200708010207 78
    0xda0340004103580e480e56188446d01030b07441c1685039000ba6009100303904001c07080c0da071054081046101c4055038400040140d4060405001c0c2c592500309481d1800b800c140e0403000b40103c080c48080812a854005d10160405076213540602110210484c101480424803c0c002c207401400041004108003900c40c00800607569505002040808c1680e100c824010956105060301c50500c50755204100c403940002c00904085000e01326a03a00c0343c00c041c1c00ba50440c000740c1c00300c50b56040c81c5074450f4030350050b001c6e1414809030704e80c1011002c1c4044500c81c0140303c2850303141c0d0300890105030b107200e80290001e0655040411400c180c54020b02800541c40ba0078001620742c004200d0703ea502141d580b003100c0d40180a0790103242d0b43d544035060030f14402e907140e510950070311102200d51240340003107116507020340e800a4070500358038040d40d2030350181d00003403040c151060310110703440d400468031030b00a0f800d401d010503040320011000c000302199000c120214062031400151008054008d050b0140c450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 233805593 1250 233804343 233804353
    0x1201050333180a030207062607140c0106030b04020a09050103030c060b03070906081005010b0301081b0402091908060726100b0d0c031406030a0f1e0b090c1005091c05060a020c 77
    0x700c0c0c6001d62301d60801c0e00b41d000d2036188020452407801003a0b0700b100d1811602145091041c003c00c1c03d400c490860344103485205000c0b00b00411442d01b03072800d5002e840c4501c2c0400265042d45c40041c54451000c00040055950b0040d070301c43c0b41e90030418900107044054060203520344070074907181c50741c41d5a0110300300c4504000000c20300304031003c1624141d03480280103008061441c1181c01d44402240c0140342c01c1582001800c41d95100e00c8402c2d2a030121841c44184d51074130346500e40b45007000007031070001040420f0200c1a444001c458451007060540015140780742c68140480360b111020f54000c0130701510001310488007124503000110140f185460801603031401002207000a4800c80b4059855006010703c1d0380010342c0002c8203030380240a00b80101d420b40706015a64500c01043c038007a0f905c001c003075040108001013000302e80722034141981c511203410b03600c410180c010302503109203610609030008501000c0d5005014500c015800c07104903061400e000804800940c060007102c1c030f0900035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 233806843 1250 233805593 233805617
    0x22060507110406060206060f0d0606060e010f030e150405030909070e03010c0306030809040e0304120606210f08090f060708030403090503070f031b09021201050333180a03020706 78
    0x10703100fa030085441a03005011a0f96580d010000c0302000c154100b64040182418000812802d2148034081c0080d6100c1d01600001c50340050704a046800701d002c04c060400d4030b01004001d01280a0480f46c594a08002640d21989802400e60203080710f012b420207a403004100b540f44c0d02856031800e11a0540c001c120b9000c1d030040c00c03000d46800b800081c00d802c5c010030010301103081540c010041e146412050380d08080d101c8d1800c040d11070010070240c80294465405004140300701030090007a4440180100001105a0f40c42003c6d0780d030000c02074000c420110b00042581c4485420b58240517004140540e2140c1074581040e0542040d9000c0c3d001900c2a500491203081c00902417094445241100ca01c961560769004c00c00384034460781a517041000800007524905e1800540209120810080010341c10181814601100500141200b000c111100325001d114880b40c0b141c4c03c0100e15000840350745040b01521b000418048201041c440c00320000c003810780c049218403c0c3e1700e250b0b50340d08103040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 233808093 1250 233806843 233806849
    0x60503010218060906042c010609141002010b0406060305040b10030f080c2107110a0b070201081b1c06150512090705220b12060403052206050711 64
    0x40d031040d5a110b4080882800101c2ca003050180c10115001019246065140d50150340c050680e9001e1562102c6104c42210100d0f40080d0f2003800341c4524507044840324501540c0305c814440f190300c094002e00851400c4010240300b03400281e0206806030041c8491076030f51038000d000b044100c805070f0304924080046002c1c1102000b11000300c0c0e41101455083c00815151100694040040942148030f0066034601080c1044240d00324400d4085001d0703220700150411840141c82e03102c54038410300186506000c035000150a2792442902803070140003503980d0300101201d1400c038003800c000542000c1065029035508420003014106012810311100396210f56610a00c408140c003280451401d212040c03100034241c1100d0f03840702c0d84204032907601d50381e400401c10700c0940c00840c500721407011070002000e01c060301890003644400d4404c45d0030b01c003120403c01e880360710141008040210005012601c103801c0305c0ca02a124021141e20044241e80e440050400d5000300c0e01114156406074501c01186 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 233809343 1250 233808093 233808097
    0xc07080303070818100c05030f10260c060708070309080106050603010b1c0e0d0207120f030315090e010605270a02030a0f050103050d14030106021c111507030605030102 74
    0x10b459207030781511340100c00c005111034626000d01c28485c2c103452920661940c0622141d0440c140c0340c0d0f9942e810041c06400c10142e00805c59024900070440800003001040c1c1d203010b4180401c000d0880883d01500628109a5107036042d81d4014404a40002800700d20002003ca141c441d032100700d03609645040450a0303d20318032034968050800d000400c56508488002c0c00301c40325003001d41c0310002640d150700381250003000480c42980d00000300070240b0342d010400c0e10058181080d006103001c01c240d949480c9007180c0388000341015161780e414035210120f9001080a010b80120500040c50404901c0d0300a1400c1c0c4901c5100c0c03800012201d2403420903032940000180b81c541c482c1c00700e0b80c8003e406c0f006540301601c520245070345ca0000a0180006100729800b962041010707202c15400182c0c018079082010551b15a52081000104440d680005034855200b255000c400c00900324404140c5190070f1410280340b02d40034400c240c80382400b41c2014603100d0718a58804000c51130701c40041c1400c034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 233810593 1250 233809343 233809351
    0x411010c0b040b090d180303120908030406140a0b15090103090503030a05041e02010f0809070b070503070c06050906030106032d0213080f070e180a050a060506060a08130614010b0c07080303 83
    0x30341e04140302880809d00c1184410120004020089000085030b69441001d40c0101d4040d907446582c0e03040c09003411008110710741c000042d02e40c1840b0300c00342140082e1642c80e42040407446800c1c0082c000c00946d0207a00301d101c02a8000e03090700e03124a000c044040240404607802c4a00700c00617801d100b81d01601030012694079070180d45428032210241800e0300c50602c090040b4401c0d12a02c500011403010540041140500c660b010310b485080b240b4140015060b103400200921800340502c0300e064403080240ca0460348580703008a40140e00c210740d041c1c880400020040e401a01c041040305005140c1c000b00302090507000d007441c9490303540c8035054440c18004c1d031402e2503802009042201d401480d410f250480c451280c043c100d1b04003040c10500e441180c540c2120b0a03001007040d02c00f030099501c80c039944100c05171400352405100950040040d10010407800c0d800ea035100000003800020341c40b0f00c821980b5000381c141c031961680c1b901c0510350884914211580301c0d65a01244012020040d41d0013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 233811843 1250 233810593 233810627
    0xa1202030d0509060c0d0f0e030a03090b01050d110d0f02030607030b01020c01020a0201020d030c0e030102040e010e0f100509151305013204020307020a1b0303080f040b0411010c0b040b090d 83
    0x2c09402e09100401f910107450310301070240d225031140507408000d000403c100c0145440c001030505091800f41d041441c140d00080c80350300684540b40c08078642c000c0e403050003101103c1042c08017840e441c02c1440c061100e1400b139014402e0301d042003451a0107900c10354020500740c0864a641d071484004a80e114082231000b40140c101850458849000fa0040214900282012b000b90a1041e002c01d0072a04076034000c09550340d02c0c070010071100003242c1d9029080072006100c40301e6880d00e540a6403640e0304070701c200fa02454008001520300349074920300c01010140204082d012586000391000513050038002c5a00c0b401e0006c1703284110440d00318480d607101c40184d01e41e250b400c40c600104402904000c1241c000c0d8014040410001054800620028038041c01000c110b9070079802c0c02050030f2001821000c44c404100140404503403010281c81d0700c254021882001c41200c800105c5204141d0440100031003800350521040280d44a41c85104600d0ba10440f000448842001c6404201400741521 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 233812949 1106 233811843 233811847
    0x803120a11040b041203090b0705060f15010c020d1a010f0608060609011b031101020a0801030605151c17030903070213021306110a1202030d0509060c 66
    0x954403500803441d8101810040894003074880c901a034159072602c045000e08240c0318030606005410301c00f10462722041c451401c1507561030155407000c60a81d80e5400a09a0b0615080c0390840741c01c142d40d01da0b0010314980900030341e030a01401c2600c12081012540386a41d042401043c000e00c1e801c007244080c1c519144000b00b00d0240030346554032403e0704000d4100e0303680c0c0c005215400c0c0076911068840d001c100b8a0141c3d015000c0c0c0f02e100100354000301d0f244001c07a07000030219040b603024550500031991000f00d20080d4403451010389a2103001100c103034a108440140360000948500500488505180c1e0718103403a8004807504001e907400000e40c481113040030420009110103d110070350800d01c80640d0780c00a0300d15401140100011580c1c2e00d81e03c1b0320200000d10b04560404a0445a4148481c1c025269840040c603079255a0521000c1110f0060010740c6c00e10560792400780c58 = true := by decide +kernel

theorem cover : BRFrame.Cov 233633093 233812949 := by
  have h0 := BRFrame.cov_init 233633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 233633093 ≤ n) (h2 : n < 233812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
