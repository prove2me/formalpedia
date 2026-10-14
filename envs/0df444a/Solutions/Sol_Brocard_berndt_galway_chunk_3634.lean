-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3634
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:14:28.37302+00:00
-- url     : https://prove2.me/submissions/56a6d970-cb84-433f-8c71-62ad2de77cab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 653417266 ≤ n < 653597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 653418516 1250 653417266 653417273
    0xa0c140601141e030d0c0318060210021804050403200631050d020d0201060506070f080f07050f0304031203021611040b04020c0c0f030321180102070c0302091003 71
    0x5041214482c2501e002d40c00c02e0003055040c1040414001c02d81e4144119045035100d40d0307200340c24064142c82903507221918a620490101c500c000d6005000158107c4841440c1c500b4040e4007509800791081481c080d1115914003007012114140e0f8158009583c420096801d1503078111a5000ca4020324020a0241340046804e010300c03440105d1304500615548410070114124081c484440c3c4d004000d844520300092000707560f030f6a2b03804260015500b00780d40042e480c602034050712040c81e00302c4c2c48026402401e40e2024215404903500182c048024010007004c68020026810300e540050001d5942d0340c21403c0c08107d14190340701d0002018010400a03000c0513030311075188580e82c1d100340390301c3c00c241c0e038400010041c01013404050740140c0b0201d1740700f180d0100001c06580c040c0064640545a80781007062584a20078003983d400d10039003081d4000d40c00030030424030130391015642145030541c8100c4410142a640002001c0c0c808998591062007580391140f503144e00100310000c243c110505d1517a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 653419766 1250 653418516 653418539
    0x5040b071707060212060907050405030a060f0603050303100905151807020120040e0604090506041416061d0102010204060f0e04020f07150f0b1e040e030a0c140601 72
    0x30002841c0122200c404440406081c096811056204509548400381000154010501110007501c2035240c000400c0b6200c0c0220201d0301a40c0002d009480c0300401925400f025000b40c86a8030a400e90350100000440c2040c40614002c22003540001c00c868902f059480513a4001703000349091621009090403541e03590b08040400d6141c800540b43c0da5a03800c0016030050400e21266003442070216000150180e40340014020703184c401001c500c0c1605c802c02072100b00e880440c4010410b9018401040100f006c018111482c1c80d0207004440c2f0b1203540425034006e0881541c00480800d61a10005038000210028603818040a01c021800c0925100c03000740069202424001444103e81c490180c5031a41c0e0111010400c000c80707030781d0741c601491404000104220300000905807524079185040051070141d01e0348c08070b00801006121034492103c0000040030040d555001c1e990fa00c0d010b46d002070900141042030055100c441544003c2d04006041e040c00700d6007040640c000074014084010900f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 653421016 1250 653419766 653419777
    0x702101a012d02010c12091716021509030613030518060403080f0a120207051c2001150801090803010e07171611010b0f04050a02041e06020d05040b 65
    0x3441c2007481e2015002d41204052030391a26a00c40d040128041e03000b658054101c014541c0c803d40d10501801440c2c0308160848040071801000b08a650600820f4400070b03002074089100d25070054030500820744e002800141012441c220760003000b00e0100707840c1c5000c1c80b0165216241d00d1103170010324610b075801441480fa01001e0308032060001040c1c5e81c5c0340c0304d000648010b1a400701603150380d00b0704852007201c190404120b00f000510301c40c002070b85100f024020744141035403003002000e80c412074901018035032040b90202d030200710320701812201c180c4076095100411482580001418201442245111005031300041e04680c1441c204000064100382124111119002e1481058a40345011980b6102c0099500c9201051380309100c0c07905d507001e43d54421946680ca4031400240c06003c224282c400401403940d000300d482c01032030058242a008a94428540c1e54014601905d5030300f2000d80001c41c14280000e40c01e404170520000b0b404025200b411440c0381080c1c0d080604c0d21a15444d1031048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 653422266 1250 653421016 653421019
    0x403020d050d090209130c0b0a0c1104270201030c0c050a0b1806070906230304060b1f050d050609010e07050702060409050a1a09090d0e060d0203010e0702101a 70
    0x6a001e00ba4035865201c04103460b4001c1411134103042503040d55140402c20001510140d0590320700141c00342c0c00a00316000282c5989401503401510b032140514020400d80700790700b041d11812000200031400b08001d1712201808011040c0344081d000050071203a501103030340e007071102541c84013002c0750380055010f1070a68400c0c81e20501b40d860455400386854200110141486030200384040036801450390700c00d441c0305946183d8800e4041e0700c60121b814203220890002070302000400c0c00300d08240c002c2072421001900c010500e00255004270540d400c82600840080d9000c2240c00b0700821034014607030062400c96081c084d035410003088514030140a001d00f003d001c00010104110b44407041601e0040503c210100124500b0082c00c2d00a0459014203416003803040004035404d1600f00e81d92030140480301d0052042582100050742c600440c83d0380320354400710a0000d0540d190842c0000c50107889458607410141c2481107000e031901e1040151120a541488503016003040000b0300031581800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 653423516 1250 653422266 653422277
    0x90714070501060305030c06040b07090e0c03151201150e090c10022d0616021b0102070b0304050334080d020903061026120a092111090403020d 63
    0x340741480c010031043d800100a0f00011030f0103a03005001042091250340110f600d4801c0c1d07aa10801142d0101a0740140e00080c5805c0c00407810052001003c0d40c0d20244440a1408403132100000800d1807854141700401691a001700d2110400007200c00e1004002d0595410703443c1c1003900301583c41d80b1022400601031402a030282c290300d4170030010040102c180841007020b1202d40d6024464180c0209140000f900c00c220100346029418010200c1111240c1e005d0300c032901c1c04400420603280d00380c1c0c1550441c86007520101d003419168005600980c421001165a090038200d03038120b1841c00c0451201102d13124540295110b00c00c0b03141090141c1c0010210b0b50b40c200d82c900b0380001d0059200c0280c0511902081101d25611007038030509a85d404950060100e04891040100080105c8070990703c4d04807041c86102041d036880501291000781c2040d0007059207a44000c1c5020014a011201c08024a10103006000880c2d0074040e0000f400c2c0d90841d51361030035441c040c0d52000002a040200f01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 653424766 1250 653423516 653423527
    0xb09041104180c0b0a140c061503030c010509031909030809060304020103020c1f0b0604051807170a02270d03110c03100e060105040618110d0f090c05090714 69
    0x6160910b40110b554002c403008a80d54541101071340b5500002a640c02140d03080e021006400c3c4484141c0e00c9039090700004103110340c1d503460030500c881048502e0316050700c4240002529080b0a005443c4141d034684011907d130241460348040c580100b80f62a01401450103082c400718100104540c1c44c2ca4059540564030703191480101c00074826060014094000e00c40107100391030049100003a403460030f50050025684402c03c2240c00d1240384542d50b80b10303414071070f04480c0e90000c00f80b46034045081c1c103204488a60010a030740e44041c0844035049803503800111482042c4100120352280e10101852441101003403000c40c000c000c503a40050103200c8000e0004481c08000c0011080003440501500d45450051503030002614091621003158061349002080c0d07401c140c4075900480b80c1041907050880c883c02610300040002e0900741c1da1218007000b0741c0ca4840304c54010340c01c01001c0d03da00050200c820742000c1d0b80390025a04494403599611013030103043e541c8040c2d101c00c8040b0a50b01141c0d205c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 653426016 1250 653424766 653424791
    0x150e0a0c021207050a0209060103150513090506010303110d050304030e090402030705040c09171506100509030a0f0204233705090f0114240a03080301090b09041104 72
    0x40003519007811a0000c1c1140401031302081c000d00c858801d464401c0c164032124010340c19160080c8801c081900301c0381d810401d40c40d0580001e80f040c4401e0000054800464480034280042600b099022a02041e114000c000f010024403082803142c3ca0b1003800c500301503030018a041f203034005251081c0c00300d40100d420342d0f5052000d4401428014010400000001d0020346078018500c500c9040901d01c03c80351864101c0400c01c8600c00c502c030314020b102661450200082c1c401040154010000103001058481d1410405600b05601600b01250090103a204001c02d49402c6030350031108030228006042040c40350750105410070700701e200103001c890701c03041340d840320041e140b120301d801c00c581c000403958000551b445640a00030078419154040300b501c0000c0c2c01e98000c034880030036407003001c3c2c00035581342c0100800311004000e1901d02c20b22070300040005600c0506c5608186c98000c2c0010041000c400203100780442014140c5031280a0702d4591500703103021212125060280d515030b102440385 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 653427266 1250 653426016 653426023
    0xd0528051c18060e0103061211010f1407051507170402060c160938011803330b01050403021005041511121602220c12150e0a0c02 57
    0x18a500e20b0700c2000d0050343c84900529403122600854007107440e051000c07620000e41304a40e26103541210b4000864541d500c0111000200300c440075040203c03400b28401402035407001809094000c2c00142409200c000d6010243c087c040c191006100600e8268030540020030055944241c040318141d03207030134062807602e082c84950b01410001085251300810300300c0c01d55110613154009521030529402a1903031b96150741500701c2801e0340c441c5140c03019814940c8680d0345404100040060440c02d2036590740d90850301d81410b00303884030b086c00c6280072615030115a00e000050b9202444240020654040081d05c01c3c8298040a809080701705aa11030090103082100e004000000c0c4255440490340030003410304044400c0c00e451409000e003400c90080c548020f071070070712401c0000d03010092201c2d0b003003085d51a80c03131804000340c618507111950b21a016100f0700f5800c0d800c80c0c8030030104c46512044070040740c1640c10100070070041c54105105520142d80c3c8154021068030000441300002134050f442d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 653428516 1250 653427266 653427287
    0x6090e040b09031b0a1101020304031a06030109020904050109020108160e060f1306050c0d0201110301120609150905010605060301060f081b0307051b07080c0d030e0d0528051c 77
    0x1c100c4d016003007543ca200005da4049071070041d020a280300c2d60200049031a44104d11015041200c0c0300c01c800700428110700a00e400001c01000000d03561b060380d0110324150360031101036803140d555030000c0c000d550300107213030b00e0780217580b0602c85010150004024201c2d00c106101640201d8020404c0c0c0085030201c000c83e443c0380301c0d1840b050350007540c6400c014455440340c41d0018460190300d100030500e034014010784c80b2002c005201c09096030300300b0304c140030b4a80c0450f600369907403516811a000072601450701d000e0b09861403540404d4181503403c03d00d0944181c0da21160250008100400c107481c1d12004d48030850005240c07154540d151813805040703003160b43e500b40b01c0c0120f0000911440c41d8120008001e070002c68030102040d10744020540b42c8411552041d41e08a41107500c07644540d03d00b900d40c8142ca280300b814440b0070b0b101081c010950490050a04035045d0b484041c410201100c01804504440240c0352010034108059a4017a1151180701001980c180c0d988030110510f400350114a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 653429766 1250 653428516 653428537
    0x1050f121b1207140111010506090f0601021e060106090b0702090126070603020904050106021c03020c0f030c0a0303060b04060c02130e030a030903090b131404020405030a050604060606090e040b0903 87
    0x54516407503103c0480c151244203101404103546c0c2180000130304040c013640c0c0c4030f03200007050a08540d482c9420042e54440040c5014114012106484248504409004882c0c1c0100f4014162581091000380c41401541c001650300f803030600090005a803007801c002e0542d0001d802044907045c00801040c0f0300c088442821b03240d809510320110390640c0c19030240c070b8072400483e028000780e60f980c50b0603629000303900d003452a1084490700c921420f6001742c000380304502c000012210382100c0045100e0450300942455100c030781160f80071509040d4103001d000041c03d100c1038018a040d2400e8009461701140c40c1c0000d00510039000001d4003201154844100e80014000341c81d9a01c60000f0020000d00103290101d0125066480202e201c160210903600980010035030303445c095040c903540b00c44041a0030b04055009400700400303d110b0320709000c4404064031660091502c3d00b018908441915401d4000310100300c15050100000004c2222040e005504025140802c0d01d80903400c5080d88154081d02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 653431016 1250 653429766 653429773
    0x105090d0801060c0b152706040f050f1609080d020304080d02010510091e1d0d0e0d080c0a0f0b010f05010c1709040609061e0b0a020a030813050d050301050f121b12 72
    0x105c40f401f15241418030500c4101d4081046151a94851007100c3c0107039901e00007100c0c118001940c085000b141145065102d04010305001d660701843d600e840d141c00c1c03111005801c0810300302300c150b401f005841c908202d1800203101518040700d0101240010748602c0740700b10780365030403540080c084600c00b007032501d1849801d011081c0e1010303502c0070042030805030100c1032203040d48012116201c0c84040080131002440c0e1102509280c41b0703505907410261803101c65001d10b1251000103000d62030b280341510f2046240d4429585044070244503261075510250500448004440005402c158030b2400c0079055901c40c2d8441c490140802c0044c0181c1d00000c1c103d40ca800004100c981d5503596041445200b41002c039001c2c1d840e02d080304c07042d000b02070640b80942e00c51540200000c0c015507402e40e119a0303001e00c00e0380d00c910039258186040c16040d07140010500c000f00500c868100214600d511007010303038410300c960148a9003241d944c020390b844880c041c030b200c081903000c642c0d0b11400c2e121a41c0504088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 653432266 1250 653431016 653431069
    0x6060f1908060f0118090b12070806040b0702010c0207030602034201050f2b050c070b011e0312110312061008010305030406030203180105090d0801060c0b15 69
    0x80c10111090300c0c0c2c0707072084400084011040d8400c42115580591a103850070300301e45440340c0756001e0704089180941c042400d001402c007050040004c0d40081c00802c000b17110710f08050034400001680548501c0441e4144070f0303460034840d00020000704070780c2c1c0208010f030f50760307200c0c003820540420441c0040700000340f07485041152218454051301107140d1100342c8001800d01001541d592060028048020360103009898440c6015440c00c1c00e82817100d2405540104401c40140031900e044900032507044004c80c82030284039412284a000d84000c124459a5034100c0455400840d040e05c40141030318800504402d025104213065490000f4040882c0c6c0c65a130000021120a1401c581d040c3c0209101c0645500e03e030310540080d8120fa800c003019501e0507040c04000c034003030f40c402001e02c03074003070003a00b1549840b4000f40b040912858110b0702400080428080007800f0cc00c0603031081040124a0f004400070945c0b034038602c1e401c081c14a0a9a49118480c4045401000d5849078800c00042c00c504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 653433516 1250 653432266 653432317
    0x2070203160512190f051606180e0f1303020c060a0908212d040902031e070909091a0405030a08010f0e061c02041b0206060301020a0806060f 62
    0x11001d094030000c490b404801d103580c0d40c007a40e0320300c06001c1d0064502d42184803403001c18100550748486500a1044d0b070a0300b01044603410001e00d15034031480010315001310082221300346003805c1015081c007481010039418a182002d1103824050050010705420318092010940208640e451800700030b00741070f40f0b40703010120140c0341018603c03a00030a4000e005050410401603900710034080e855031074a50030542019801b040e0030000301070341440d0780e101d400c03500b07000340000010b4070082c40c00c210090703501d1614500c60803585000c08034155140d95a541480125500070386403034161840e020001505840508240910182110b0350b159010340c120305100610001100412010300c07191034070803180c1d98910300302c0030a100920481e100c1d042000d011030a1f902d030600241c00031a60800141c40201c8040d000102100d058058910442c403005580d035400d075405205003076120b0401c400843c02c5c00785814001c2c000701d90041c010f40c820240010a440d03100c2c8910f0a40324403001e003034506480c0543c2d110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 653434766 1250 653433516 653433553
    0x31d040606171303050f0c0f01020d1e0c05040b09130f020c1606050406080705071403030604060509061806010c15060f051207060e12011b08180303041502070203 71
    0x101840b019103100000b400d000d10380c41d450108154140ea48500d04498009204aa50480709041285009000a01c00c0e051400d0001e0700d10400701060008010802407450000110a944008005030030015880040782d00102074404803a5000f40c0c0700c4d5115080c00018600705001c2090140c03851070442000135070b601603400b401420984600300c40c0b05004901c01e41a00301c000c0d100c1c40c80043c4007080107001891180d030b22643c0025081c10440d0030001140d0310307503460724104000c0c03001e694004000c019079071401c1d0144800404041d196100c0b40d04004c0d02054544101c00070a07201d804000f80031800c2171348940c0e064800386811601d01c002150703a51840764050303d454410a8240340c1d0707010011826103003480c0280282c078642401003800c3c1d40f810b0400c0d030704405600f02c11030f8040039188111503079020030f002c0c541032083d030000d075150340e458035640250040f174024150700f4010301c28102c99182ca0500004480d0801d4001c00c1e00001410840200c0001e4828090000d415010381c14100140c1200032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 653436016 1250 653434766 653434787
    0x4141003020f0a1401180b0a021b0406120204090f0b10030b070509031e07121b0b04030c03031209082808070f1b060c0206101d04031d040606 62
    0x21102c007400c1e0400c01c0100140b941c2c1500400d42101e6060b03c01c080d0301d6004010040e1a07041c6c0040444034181d03654006901500403240b842c1c096001762203003903802a032945150442c00300c01c5a08001203410015010348121b6131110003401190365590803828803c00c02c2d4001d10301c6610081072050381c0703045c0c200c0081d022110f110407203101d003503000440e080340d000ba4261110104045d0003428610400780741d54182d114584880b00850003070070404195024a0303140268094001e0303408080c424400980700e00015015442101b80c103405000620006600900038412039030140b60215094101030901c3c070040076900b000804070040040c07442c03604180150799000b200d004000e03040003046410f0094502e03850032582500010407a1100c180402d024150864480c5108001d03100c140f4400e540700b00440c0c0304450f41401681c461010068010008400103000d00081030039813410002d25000005101c8010b040101440a0421240440040900180c00d180001401442929541c0102034a01200e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 653437266 1250 653436016 653436019
    0x7080f040f0f0e01030206160309051201020406261f0506040306062607180905070f0315090809091302031c0905041a06091201050403050a08240f0414100302 69
    0x88400010b140e589071201913040b00d4001c2c04103440c140c10001c80308201d500d0100101c0600444020101780e54840107044290260304400069036181402c40140c0200e141c1441c0e8210805040071000f0b04e40d9039415019000803c00e406003504a11920301d054500603650805600800702160000c1031040a4102004450000180204100400310b4207400101d050010141903441064100481801c2e02c80099020780540f000203000407041d5115418480c0540c01108184407000d0305005229641510403c0c1e0b10b24400100400041543d03001c07201d0080305481881103904000041c0c0b950032000711203101c03c5d030040c00e03a4102c104460728628640042510b04000179a502c00100d010b0070b2a00c60095413800c40d020950720504080c0402c01640d2004072a00d8000710b05a5107000400c07024054240124480d41b40c482d11101440d500400c00e801c01070000307e1580e4001c490702c902c60324146542e9200075041d00c030840024603540200d4041c0c19520b1114481400d03c50400841281071010791064a20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 653438516 1250 653437266 653437289
    0x3050a0c050901091403070e1006170405070e04020d0f05062403060606070323071106091027060c1e050303180106030807050d1716030207080f040f 65
    0x314400c0441d03550042c010310300d02145107200117100340c4c0c10000150071310403c0102121200f03510ba0460a0302050196400c08400700c0b10782050041d107402820150604010b11090062841d00341c4400303949551074412a07881c0ba0500340858250b468001103050200d40004105840040c1880c0090303840d0300803a130b4840071020000c01140c0303c001407904082000d00c020003d04141e1962004c0080c1c1c3c3d0b0122000700d081c0040c840100c50140034800c01c0c0c070165100e80311001e48424440c01d14902d08200084058401c0c0410020505556640c122613072646649150000501807500814032203000d80c1c0d0394100e078003640c11000080d115403014107106513500c42c1030790701c140114a04404200c1030708000001e00a400034400100600d130a06ea41d40100706e104400070079480d80d26190384515520501040d0343d40c3d04906040028140c0201c0c3c060230b00e00c0b02901c00c0e029480c2c112065800d00c420b41d004841090340014513101070001001c243c0302c1d0550344141c481c2c0d80e595aa4840100c064061055103050711 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 653439766 1250 653438516 653438531
    0x9040911040b09070c03030f020c010c080406060509061005310303020c0d080901210507030605090f0103020609130207020406150f020706082205070608150301090f12140a03050a 78
    0x4003c48814007890f46615148222034945d501a000b0f00030040d8039005041c0c3c2407101001c24030003401020900d50054558222a00302820702ca400d484060f00240d000e03101c1882440baaa4440d49255401a64589007803a240c10f0751241142c04004860001c1d41d451b01c0410404407250b21550025007240d200390200e070a1241090240052108808406008082c083c001503c01d5405108400034010354101010700010100e81c1c1f080480e80b003a00c8490000e0f5a0f58070500c072034284000c0d001d400405650b00381d88503614580c005500c0d80301d0762213218020704000481705c2010081b030701074a000d50390041092200c81d4881c105503000e4504842c66000080202030030035415400403d100042d20103560f6140c0c05541d500f0100c403100910a010500d030201c1448150000c41c2d01070020802400c52030340e45012074102040c10301064800381900740e01c26450629524002036450080501c00c0b64070880c00c4105108042081d5100c146500407207401c007000003805880b481c0d040d1300c81882402441d20401085 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 653441016 1250 653439766 653439769
    0xa030b060a1d042402040b1b0a2a0306021602041d06010e061809010902041518050903071a100617042402071b09050c1605010209040911040b 62
    0x840821000c40481c2c0441c1c0218010443c6149506200700151080110b10010fa94200d030407030340031394404009a2804a2004044050316010700e10640d20800241414500c40d00c03074040750307071000c005078584488170f00b4620f41d4103020085c264006c1d40c21070011522100307010b4240c000351480c0704040307129900d00300c010b88070314180350341400c480030324040144216800d143d21044010746c0030700143d500400c10789100010200a00b01d0714807401d4410300104070041d0742d20600069508a48042000980680d418800780100341c065600c104000040401e454444031002da00310302c20848050200750408010070900c510f40030a0318041c0c04c403100d1001e45603030756032411a40400d46005200c01d640c000004100851181502a208034500e1420f6101c800240744101c412680511401c644a920003092041e02da043d4200482c01461100028012403800c0c1803503c1841c410719510f045010b84a0000000740304003541034810f400c0026004006404050500551003e680e6442c42d2146003402d4500009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 653442266 1250 653441016 653441039
    0xb120f040b0a0207060f09030c05100618051911030f010f15080a470a12080c030d06080f0715050d150303110601060203030402010203070b070e0a030b060a 68
    0x140d5000500e550460b1220100c0c1c101960100c4030a403081038566408145031079241c46120401842a10382040310398040c6070650809105a81181c0740601d0090100721a82c0180707a6200303c003100d00c10020b4581d40f10041141c0703101d00c040c54216164907101000416a40c12002940154442c1401071210707a40d4150440c41107410380202d8022800c2c1200c0006e80e00c1c0508241600800140030106454440e0a24000010610340b00c03165404a0713503070b55032083d08a0105140b1085500d0180c1c07804036403082d01140c4501701c1d600c54048800480c9100c2c8080c80208425140201c02032429265908488540711000c0c0c00a4010200030780507001803014120302c00200141101d03602d1012440381d90300b910040d03072145c201c02c0800c1140382d00c81455035100c001640503a4003540c82904e0b03110803c094403041d00e180500c140c00500541d4000c00c20f00c000360f0303000001d481c911036000c40545002da030b542030301321250450003041c030b501300808610110401188101052003a18259118850541d9400c40d0001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 653443516 1250 653442266 653442271
    0x131a041a0109020a0c03050304140604050c040b0315150303071203052202090a0213090e0607020f1902090c09040507021b04020a1d03070e042609010f0807090b040b120f 74
    0x820381d00c1150794001b9000b03030040e55000d40103020914207060401c49081c241320045a0488003500000c0200416107424481c0c2d1140440903002000c130512042e0518006000103001400d800c185407480d6441c41e45c0410480c2c4409600540722440401081d03c00740c064101a51000903040e4a01991182c2c021103904c03400346103400418403440c503194030300300c4ca00940c004140013050001c2043c0c00300b030040c464040c00c01a42c503d80028540c510317148000a08103210707901d181001d50882c0141c6154560550801d242168044614200c162150740d4048828410341e0713581c035000b90600d001c1000701600440c0c845032004e034148440d22003480210400089110b40380c0c9601c007050442d1028005501582d40d080024070001e001c640b103072038444468261120f41240e007100c2d43c400400c184c09050107035800d8111080c031100012030070a0100d00c0068007100b4035032070010406c01d4080000c0c00c4140301c0c00c00f0300000e01d007100829035116120304581403550f100038220124180e02c40040740007210781c41c48aa1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 653444766 1250 653443516 653443537
    0x40207030f0309440309030304030e010903020a0b0c16050123040305120304050c0102120d02070f020603090a1b0807170a021c030e09070206131a041a010902 69
    0x554140d00000540080002d28400d450004094001d0b0000d00c2e20301c9040860130b030011148150980030b0306811002d240361070070603580c0c049050061000e84800003007947c0d0465450304202c949082e075040101c51030074240e40080c0d8803140503a030000b1a02101e000408016983c1d8043c2ca00d070f00281441c0700c1d000c001c28424280000c00d540b0701208019610714800c00d07603106010382145099580d854080c54060800d048882c0c0500010500c003c101702008082c60200080c0050f0845c001088188004e42c0241c983d02400307a0380020700d41c2c00308840400ca60095a03802404591617003000480a952031091903400c0710881d003040f004010b00340c0e2011039403084604c840010a44241020402081294600c10078045d07445404036441c0146da07141613150301210408120003074280c09040040c00050803020031400350b601da0080c844400d5020900390b80c48a046030014104452a29040e200551015001a48071170120240002c11540984242010503000385a00740c5036202c0e00320f07a04902c80c021000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 653446016 1250 653444766 653444777
    0x804062c01081906080d020106051009050a060507141b18101e080a1a0f060a0308030601020a080d090204050108030c0a120c12020f07090b03121b0a0f0b010504020703 73
    0x26501c012040d032a030424803c940d008070300c081d5154005454071034090380460142c0d45509040c00f90f401c2286d64074107a20703920300c0c2c650646450030020404290302030243c201000b100061150a02c02c481c0000c5103407801e948100c54900c00381004a491403045c0c00041c502c01c40000145000700050504600d01810120070b607411140c4c03609401c22800711060100e954500380790000016803c00520098004c54002c1107070035080d010900c0a580220b41c010310f604512a021010f00845480d141460300c01d90382c0c881400c039580c0d00d8540060f4a03000c82010018452000010440e00c140b03296000021503e00c240c40910071039880b1268146c07a401288030402c502e6014061980101d032043c0d4040c1602c82d040d00700030b2180700c0c00d07407502c81605020000080240c1d001031a10003440000300311040042c1f00070030b03080040050002c00251245403485120514010220700d41c0c800c0c0d204001c0880500030280708403402e15600346854537242c22950024bc40b807070105400000c0c01d003054002c070351544c2c0e4159101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 653447266 1250 653446016 653446021
    0xf03151501030603021008090d0f020c0f0102100609020904060b07050d2d080906090d09061413030515131a09070e070201021206030304050108010b070f0804062c0108 73
    0x1550342280304081854101921001c001005d601e620001e489640031030382d6030176030a15003992032031321701940f2511000c2000002440500b03810760100343d400d04514201e0301c0c540611403000c0101d2400b542c0c000850409803401000060300300d80b56000b4980340c0800d803014410180d554a43c0c5030140a1024054816005040d0400714140301e041c01c070403583c5030810381040d17a02000780700785500c0c21148040400b045006040c8040008200007031036002008000420910418000040c43c00843e03200d0074050003000362580c035941c90a181a40d00c100d50f0300c213840d0b04065680c00d141d95100c1d10880300c00c6480d030070600810032401030708642c0c100264025034080d810440079080c83c011100c004003007103068010b010002c5055620522400e006801590001d42c40d0b00e03800c0d411400d507800240005110380d001f04010405640c0145915044954441007140c4442d11801d21034000900320000410a40c80090007049254010134515581c14511580e42d03510f40080c04101035202985420310b01243e0207100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 653448516 1250 653447266 653447281
    0x10c050a1b03200f1c08090a05030901030f06050909030909010f0302011d04090b0703020406020d0903150b151615051e1b180108160519050c1b0f0315 66
    0x1052039109203202184c50f800c01c1400101d06003900c201c4454400e124020a85086581c0801aa50444c2015002e46404201c645c3c4080e52032183c1c414140c18540c89103e102d50715542640034500800028003149804d10306240401d440b80d000d10503592080046030008107070800000028030a9a81c180c6415042c00c074002b15131035020f1a21001c3c613038000c0c4c41302c25174000200320118107406902c0d240c40240e107030b41c203051003e4207004e60507114804000030303880108045801c600d40c050f111090010000364150174003002c10315011051800e40d404020004101c01d41443c092802148a400758003402d041000c40030401c0107844041e030301c2c400d5000c403c403eaa804200d4140e40c1503000f039403980710460082d580d50765800d0b950304002c00011428807a861008100d58018030800c1e884002a04100e00c2c82c2c3d12502d001d8030710301070103c1c810b503038a0540030b943c0c0c1c5440c002c100702c038080401c25048820310701d03584800c0081c01da46c210003240100c22210030203989003000282070082010141e501500d5558510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 653449766 1250 653448516 653448557
    0x92506020a0807170a080103020a14010c062f030114010305010513050702100f050f1b04060e010e0901080618010b01020703021311070803070305060108040f020f01030e010c050a1b03 80
    0x807030540e00d2038101d00c0e1541109841074014044440c040c1c0f11080d040d0708d503004211545055601c034841c0003d0303d042078030051382c0c80011000310a030300840025613509507102c0c0ca01c401444500e0307051031103004d010f03003140c4014100256040f1031381171480c064011001401101076420030b01c2410781010307848000003815849c40c0c01150b4000c1c000d00c1103a100410301c003103100640d0041d03035007584e2140d610024401e4044000c46029400322069440c0a03902d0608410340503070b03225900c01c070810402d044200048980c41040100c090940042c0002700c00e50b12012000d46500703090300c002c00d1030401040c11801c40b400600810300c901c00143c001d081d81c51f01c0c5400f40542d0f060095400c0fa1415654a210031a02c4003000240509502440c40682c2b24500401c028040b1031029080d181404203000800000a044d030f000f402ca110f038159110605180d4030300058010741400c0062440303950800403209034081d8440050a43c40d5610b68070300d58408603866075801000030980e4064001803501078505000c20114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 653451016 1250 653449766 653449777
    0xb0108030c06060f130207170d0e0c061e0a03020405040f051503060105010f110309060721080f16120501061112040e07082a040317160326092506020a08 67
    0xd11040d006010401181c03240c660200c27100034070403551400d009064840400004281c10703010740d486841c080c0342d0440725058074214144007419040c001002c10125200350165801843d000e84188000411138082101405049481c007080520100c01c841031407500007020380c120398040c1c5804086000e88401111804a60f4202c01104d12041015000c42e441d90700c000d003e1140180366a09014902c501d0907103400011894010400c40380000b8404862a0800416080180a80c1c40400c2c242a904203448020702549204140351500000181150300903468402424400701965503c070340808070a100c41c01a8028010114030b4980007803442c07801040c2140d00401c814515202c400703044c07907100703549c42882480010204d8011604004000c201c001c85120407041620381070500c01d001e1055200411443e1001d810401d0001a503803209107400c0d03a0311404d010080405040d881e00d101aa45d03109040309911104810941150120b074010051400544265901410580c11540c507082c1058015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 653452266 1250 653451016 653451023
    0xf02040f090b0c0d090506010b0c07120c09090c05040203270d080a0e03070807052b0f030c051b061609050a1701060e13030201060801060803160606030b0108030c06060f130207 77
    0xc0703500105c045102000000d009090741545681ea0380a821035450420090ba40012041c0701c1509440300013442103138003c001d03110f000400160203c29801c02d02d84510060380f006421074400014813540070710034001c45149225203202c000700f0025100303800759184400c945020024003250081a0b207800d070f54000c0101a00701d40c045a08004076522484415480365030700b211607501010b00203043d10030b2842d032102441e501c00049002c940440b80c0251680307000e00c1d684ac040590b20300001e61564007a1099610701c4150000d003034108032105200690701d0310159114180307400d84c1d01034061441c0c40b5103042c0060710000340c214a4180e15220f4040340100c4107641a601c203541318800840c07c10402c4c00d44a100b280d02130ba8281da11512414042e0031103144c1d07002983c4590410005000280000040300e85036502e02c0d94008066070756041c09070041c00140c000428501c2110000208040300102918002c200c0c40306440c03150711041704100408040020341c1e6040350f8080c4400c076140c0c0c055405031503d40c0c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 653453516 1250 653452266 653452271
    0x20303151908011103090606190b0313081b06151f02190303090b090105090619060509010801150e0403020a0303020a030f0603030f0906020105010b2a0106030f02040f090b0c0d 77
    0x1c850b181d150035212105001c0303000702004020424005810020141c101030265400d0000c015000d0621208207581e001311028200c0000c0031a074050400810308420b1a00003903c640c0740c004c0b1a2072422600750341004000f580c030644002c0394034952200403070141d00b100141302000c40003074003a5031481e1100c00b0707800c003040d030040f0708515400c000c8a8903008030080c4250350004011201c1d14040b890800f0142030002d8680c1f50001700002c500300000d006400120b2021140741c000b004c1c09611018261b25000303250054103403400083d1000d01500818600113881c81081c24280d11011100e01000c022280500164480c08001c00440d000e9401032030004254500402e0289221030310006a4083d035004400180c00820a007084640c131040303901c0a8801c51000740019413514510220078040d003a202c1214644c404202c07075001c643c5009585264000100078410309a0300c1c207040300c48500040d0181d02807801c00011002300d01e62032041e612482d03440040344019841c2d1815001144c1c008060b010981603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 653454766 1250 653453516 653453519
    0xc0d020a1701020d06150c170c070305060906060d08030402040203070507020418061b020703020909031e07020307050121050621010b03070e01050d080d060f150e010203031519 77
    0x1020003428909004003140056a104c241c0380f2180200c4801d540b041c0300210180e800070064591000000700e015400400150030201c1e10041e1203480d2180c2140035500744140302c2d001041140c00314002d80f04070555415562580d90b0030040c0b044501c042d04006050200401c0040c0051070603038080d6800100c64540a41043c00f164003240071161a0340000c81251003602224080160a004120611715650a549111851100c010359911050b010080c03140c540b50001800b680c80c1042902c2c1507205c7c688103180041450108142d1310313804800f090703001c1d00683c000801e0395406908428100188031007220701140e40d03441e016008100141140381c0c044175110b113402d1704000c20786090144040801c00007070a02000010140341c80e40c580e000c00a061004c0c0010043c40c0c0d50031409441d000d4005e400c0c1a0b1302c6906a980c54010102c2e5004880f111591031030102c0c504440c0740c0f132440c0405480e110006440e0204005a03038a010032076120452034014600403205003020b00032048003212081a02c0c4041c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 653456016 1250 653454766 653454779
    0x1c1a1302153408031e0106350106081f0f05010e040c0806091302150406120b030d0507030306081e060a0e060411030c12030a0e120c0d020a 61
    0x5030440c2240c80c50400110701e480c48000c03690401c1c10102400a080110780a40842003141c0040c2c800c405840d03008040000f03132502401c004100e6808003007001c21000741d84c441101500d14000c1c00012000211412082411458003111210000400c0c001608c85a864407804490314080141104141000185c00d420010007000501010b440d44a0412210b242401c000400116586415074807039810640695100703034002c82060b81040c010381c0d10015641c1c0e482000e128407000c03c00d000390800c00c4a0248000a1202009001aa010340e516800d01a00c03a500c620259140741501542c940c01000c0c0d10041640540e00a04505100b4140403030f505d6507800c141030404030001031000c107a12030040100000388040c007801ea48140407901c104155030481c0d038401c4d91340c0c074020402031050b0340710040c03807259603010401844402d0008102c2c14515202540301c5489030020025200854820403003030074285070903031504040031865801007940c0301e00f010170040c814807019014ac1c2c0042e1503641c0818071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 653457266 1250 653456016 653456029
    0x20904030c17092e0c0311060403020a060b06090906061c0509060105100f020307060510150c0b09070605030c0307090f0b181e04050405030412030e1c1a1302 69
    0x8480381c08400e602c81c40c41c10f05020482400d000c2e2210400300080c08245070040340c0722880140c4180d80307400c078039202d098a001c1d600d4080100e8131226a11441081100f0142d0015400080134400e2500340103a045260a221440c0100840c0a1b4008210380006235117040c4003016092040804c40701400e9802030302446011a00c080c3c4c3c0c0411aa049000140414142030f0210041800320b80340881d900da000c050000d440c3d000740d0708002c20713803912a0042007a0b08680c40985010300703001100388082e04060b440c00740002c2c2c2c80301e00c02c0396030751803900004021402c007003607502c1101c0b0280c07100c038039650342ca01800c03c1551000f0211014003610308004115201071180d00d0f000b400310803072015a902d01041c20021826016200c01d44175040c0c1c15800c0c24a1000d0410340710f001d00090710003003000c0d1518a40b450460181d504080c03038001030b452804046c1507000c807a404140f8020795600440809044090400d1407a4200107030040d50030794840074450004044066001c4456040105000320550009a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 653458516 1250 653457266 653457293
    0xc040c0509180103110a03080a0311090a1517090a0605060301060e0103050d021b01050a120b0402220b0301080c0603100e190b032107032304080601140a03020904030c 73
    0x3100c0710b001d00180108403801c0d443c0c0d21008000c07610070081c14a5599800901e10481c40c4260405440303410810f6194200f60580740e0758540100640c041c99142d118000803400c9050364800000c06000c9480c20020f03c080d2030f0350107141018041c001a90085d19044081e101c044c180580540d43e6034030010741a001c4c030102c2c41c0038500c154017914600031115802440c02540f07614501d0342042541240c107450f80c1140441e0300031007003410710094885a42d84e1041c018032404c19103030303005800014115089a1b00000120780700c03090924111065407195508515030109015088140c5c1c4002030010581c60034002540c0c0c4044c00003004a81c00791264104011060191107a600929082100d01e003080e007180039072051803409a00030710318484500c001d0041e06000a01d103070210840050003a05043c8100000201007840301700032032003042e2030b0701402181ea00920442c0d04138020350001064161144e0b103411044440100790f1030140c0c1c1540c00300400e041001c1c00480621007076150314000900014040754 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 653459766 1250 653458516 653458549
    0x1d040509010204081b090f060d1a06011404080303010308070f1a0402011d0f01140d02040f03020a061716050405120a020f0307030807120e1203041401110c040c0509 72
    0x50303c99160804c003c0c505032201c040360132010008840c000180c0c4030003000580c02000c0c84e50042d09038461f400481d41c10410010054510440e403200350884030340b10b6007100e003c1c040c2a0f03a11050b00700c2d13100c130a900c280550702400980341c008100410108a5903030140c0102800341800481250031a55010b00014500702880c0d0b0110b0500d08000966030803807615207551484514080071442d0b00c034000760451503640b0031241404900288441c01208181c10b4441c44450050110b42c3e03143c07104c60350304079100a032204900c10800d0000201741e00d031041d00d1507030300160f480a40620944800070107a02c1c4081d95503001082081c01c2c4000a80c40d0313144206912651701c10401b0307104401c418014040c40c1030b00040c2c00743c060350043c401080085c80030001c480c00c0d190003407405601d40849407012210540e041e140198000010340728541100400300082046402c1e20302c0071044c0b0843c000c0151142c01d18403c1328081e9410004480c0440e04054111154901d4245030051901003c00c00240340c0c0031804aa04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 653461016 1250 653459766 653459771
    0x4140a030801060e040b060702010c0c12030c0c060201020c060a020a0e090a05160203030933040c090501080a0210030b010306030606080c01020c041503120c020d06020c1006151d04050901 82
    0x400420307412a0b010f44d0b51010541d01030040022800100d0340a1142c00c030002d040004a02410b07051240c420941c1e000381890799800c0075415200d0a0040100c14025420b84e105852500005113160052086402070560000a4020780e99100ea0325002900702c0c070020801d0080540d031013074040d80d6a4103d1071142d01090000581d504242d40354180f03895020900c1c100b550700401c14080381d0100042c090180d2003043e2814540e044581c0b08040501101910075400c01d010f00007480104821210f04006072280402c2c01c10482c0c0c0c1e54502c0c1030780c41d41021000782d000030349405000a400c0c442e0704031603049003040c1000b01340702d46c1e0790740c0721310450700107034048004c98104c1c80d0030800642c2d050081c500c0009080b9401e005414041c8680e400c55004e901c00100000e506041030601d0341e000b54203032100c0d80d400802e41e80200c40c2a0a00c00065409000d44207114003070200500d8000400d0f100e024184d409648001c4000d020811081e52350051009a12456104041007003106540300d000b150710607164080003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 653462266 1250 653461016 653461019
    0x516030b0901061b23010e0d0212090111190302010b1503011a0c0a140d030c0807140c070f09020903010b01110d0c060e0a031d01090e010e04140a030801 67
    0x500315195000c00c58450620880100041a0f010b002d02c0405446480b007030074404c007140780008960a9000030300d1001700814204094400f019400020b0500c2441d0681d100b01c1111041281c41d1411050700184079001804002525482040051310b5052404101d40c40614901403580e107400701c0900440040c4e4582e8450702e041e05001c5240706170380c480c1c00c54280c2103504003a030140700c0501000000c2d5030004d0118001c4001d0300d01300500e40c100b68010a404009450700041192211a0094020013181c1070484121000b4820342280b44916969030380c0080c41801110604c52a03440201c4419079403040c84404106c0c0d0810400e0800200007030200103940d440200305050959000600c540d051110300c0402106c1460301140e080b0100d40185070030503040983c2e180050081012828a042c41e04c00c3c404803004041d0003024a408040e614900e81110302044001104c03032420318010340d10800d0785e400042105103160700500703030014821440707155102da42c4e80a103032529103584000d60010380c40000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 653463516 1250 653462266 653462311
    0x31924050421030b09010510050702090c040503120301031e02030c180906060301091709150301080607030b1002031e070210051e2110030501020d14061206040f06060905 74
    0x110b0b007050300807a040c00c1c4400c1d00720a000401c0c17514140b04650081c4006640301880a120300100c2d420725034010300e400d1880c24a044205107640060094500a00c102c1c540a1038048550056038103c0f58031015800c22101004100081024444801c0740c040c459002030742001d80c0c403068803103640090030120214030700d04040068035110000e807045000740d14082c9140041406440c0401c008080c450301d030350f660f0b03000c2130128044040504594a00c600007000101c2d001c04003050740c0c1e000f98855503003440010b0b031200402800720410701c2c3e0403025a104003c07118440c402d40703403922005081600b0160500300d1a070041412600600030350b000191000a298a50001400e40510f1003142c0f0b000c070f1802c2c903459044010480600e848a91505800c4900103089411440c4202d005540d00c00002c0d501d40188084c2c400160100c1d8060138810b00c0344900152660034141041d0b02003003100b1000344040d40f01e540703c02998010620040d50420740b5004d010946a6042c00b5480c013480280841281c055407281 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 653464766 1250 653463516 653463563
    0x7020a03021e070510110105010b0702040f0c1e03021b15010f060203032205011b1b0b0103110d1a010501110f0d1407050106030f030e0319240504 64
    0x109562000510b0b100d0b09004418009020070542c0e1050300c501c03403901c14a410031344034122614031014641d17007800300100f0222111000f41050b01d10941d003d00040200c58004802c0c1d8450aa00c040024095030084440768200186c00055201c1400c0041c9440e095803100580d007441103540010b10b501c86440301120168042e061401030040d2413940ca0014201070000b500d0707100140807804802c41c080b0741d1007102c0820340d0720701415680c42002081845481100010255000f2404002040004c000b603000c14608071092070281c1d51209481c1c0c05a030840d41e4140e0040d007004211071700f0126103407007480003d218001583ea140c910181c0d5a038198500000103045c030a4503c0c000c89250444031420585880c0080e40780361039440c03404c1c110741408a29010003c24003554030060301c02d40c00c1c110008188401c0e2030070080f8031703030081e61400702c0c4c0380c3c3c1031040c141d8909180b1310516010310240e008002241202402c2c0240703820b1002c4004403c5252207200307040e20b03c00c0c0c0d0190b8a281b40003d1a010904002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 653466016 1250 653464766 653464783
    0x2090a0608090a06021305190608060a080304090c050708070b040c090e0613030e0a06121a0310090c1d0609090d0f050f043507050607020111011407020a0302 69
    0x91904842070b240103462203850b80007a01d0b004100765004134a00074803034048001d64014110140441134411031710100300096003018410304002c074450b1008a40d103420681a03034070940c1c1d202c0c4015403805140031610402480080ca295003049818071072100081c4001d0000c0100c01e008802844140c28941084c2d6000c11459101040c0039141c090400394510012074441d6021492400041c1c0c401401c0c1010f0f03544102c10300c125030b40b0414044022410581240350961545032000381000130140c100030b5180c2880c00b81d040140d043d482030240c281d448015812040b4803070302c1418035088050796026a0074020914111070344010a0705010400c0300c5c104445215482440d003002000000700342030018202c0242900110100400012015403085004003224018803612501071001e200c0440d0550581e020790f03031501c0140ea05158000b10300d01c0006141411f560008041d94540840c990040d05e001d03400c0e515080700d80d52261404200c004411401600c256010f401410032b0707100034507000742800b800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 653467266 1250 653466016 653466029
    0x150224040b01050904020102010e120d06050a08061801060906030605010810050f150f091807080102030403020c0f120d0801060315080c04092303041a1602040c0c02030a0602090a 78
    0x40808000224100c1441d036411610b007030b9806505900c503800100d01400c0c29610303035085840b800003240e584220700b00c0100160340b03c99504109040c0c4880420040c51903505c00c0b040c450380031801088002d06a200000e08040201000040e61a61000813100f503a407a68019104c075640c420041100d90000d00900b213542c01c41070400c200742c0c58080f40e500504200944807401000080b00441d000d038652004145000500600442c4075107040c0300b031419078075661110b2441e540515000014100b005000790782c01150f040c0c014000c04003190f400d00000a005881f1035620103a60300320480036040c03d01000c1c030781030325691340c0c80c10542c10101d01a041d81c5111790007000b0b1000c0400100b01012001c5545008004201c0e00483d014040c1d0925220850811000c003840340c4030541e51049451001005104903401d481001e208816008101d03441030081ca0416070480b0f0380ba402140052405502c0158035030018102050380700299000310f0303e00000b043c411207c465000039000c019203024022940207051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 653468516 1250 653467266 653467333
    0x3090e0a0506180a0f1404030f11100b0117070e0306090703080316030605060a050a0e0907020a020f120714040f060602211b060609070219080d061502 66
    0x1c2c02804906000b04040424845802c14404100402484d40003100700000e002014814041030403020450008140d0b01280030034080c1d02c4a030030382805000c040c1890756109020384a8079109a40c008058020130b01018100907011101c20344912207004000d000728000d540c2d1401c0d098603003003498070302000035140c0510382d4408001080080c903c581201d5202003507552103c516081940150060049034014942c040d42c0030400070301c0954018054600e640d21a522940b0b54146034041c011801000c0d21000c00503045411420054100500c00521101b400341c44402890100f64905003041b000e40c2086001090341d100311140c81c50140038892000b031501c40c00700401031602001070741c2c8480e40f1011004903020319400100094122055a184c07a00007030302c1a44c03101d031400b00961102c134200c2d80300e449100940b0118074058400110900b500c1c441807540031400115840e40000b1741c0141d41d1154600b034869101088038210011f4046283c0c0b40c1d9001007403880700305081e4104608110a24240c03e01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 653469766 1250 653468516 653468521
    0x5270616020406291c060305060f061507140f0102270405070e010810090f02032406031311150a02060108210918041112030304050a0b0618010303090e0a05 68
    0x80842450980c1143d0301c4e0790250392020424541c00b0030b41c04a1344006401c5141010006c00d004010403101e04c100781c44507034000507a407003a0070003421074000b502d1032a00e51000d0050500059407a0280c244854840d8100d42d0814201c48445007079a002420709411900141381300c01c9000300300170000f18076107003c42d014459860a458010205c100607001c42c0c0c10010700e180410007a10702c012020001d845014006d1000c408400c500d9400b0354001d44007042c081e81c03913100c0d001d8100c440006041041400621051650b00c071007094100b007681a00c01a600050000390b034002e5540d0709a503c103420580100c0b85e80d01d508072940040d043c408168003c0e002904420100c0100b10502c000308402d10a0310300920747c844840c1c9000c503502408003840c800c942c040385070034007090203600101404980d9048038501c5480024a5440d074680c00141c400500303d61121030603100180c0140348183c1e01140292a03ca20751004041496408400382d00641c045042d080e4148605041d0700003403988003458041c03e00150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 653471016 1250 653469766 653469809
    0x308190e0c131107110d0803010801020405010e011805280e010311010503011212090801050f0603120c06010e150a0e090c090103020d0b07050d0e0f0c1005270616020406 74
    0xf80710304c1100404c8107000d03000142076903483c0c0d0110400310350014142d98603036840d11101c6000b907102e8083c1a002c80c95030300d407400656124000303c0c00707410103101d00c9504031403900c01030058a1000003403009034104104032404084890300d40f11401050005e8400c041c81d451402c018106180021105042050800041c014594012030100503294401c030902d2000d20003400c100c8083d40c054201c1c010ba5420700050015280380001540c0c00f41e88205c0c15200011608585810030340714000c218a929088000100800c41c244100150721100d08190407240e81540000240c0460f55608240c01480e00c0b4800c3c030018103000c2020011500301660654003950451f00015065050010004c040413502000501c856118034243c46400c03181c0788051114130600d504c842c0d22681c890401c00d00030301c107240352104c3c0d602d04040390f07031001c001c03d03254035107050084e0a0140c4002c1d10b01c01100c1080c0c618600049090b2210001040701e170401e410042d44400c903d01c100720540d034003580440500c500100c60103142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 653472266 1250 653471016 653471051
    0x11041d310c0b130e0613092916050903030f0a090314030909010b1b011a090f06011b05190c050f010f05220e010801020403120810030308190e0c13 64
    0x640c4c4080440c24210381d01c800020703201804429250180c139003050f28020811104110a0014401c03d028210b00c0c4624850508043c5200719000c00c1c4404180241400b418020f2004208900f00902a0791800d0354240d4140b03881d078441c0c8407000001e110070b40b081003400351040306480042c81140140d45002000c000144644006000751002c29000140f02c05145014082ca00751629140000388401010080c10b00010484030607042e02030102d0200141c0c101e5000c1c0d0559214120503164100310807841000a100001030403002c854034440c002c50100b514943c400c0441c0c82e03d21469141200c41c0c1844148400400080f0300d170b905004d410f101c114441c9030004141c8a1030002c0781e52849008042600444414005600c51000e1492400c004100e80c01c0640050050381c1c00390400851003455500b08a44400d03080300d900701c00b044000c80c14000a07100d251480e402c003000750080340c0c80c0304070b14503154111962480381c4802c0c0c0c0d004501a0b100c0f400e08040d409249080c440c0e08210703210552501315030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 653473516 1250 653472266 653472269
    0x50907050102190c0b25030e0f0306011d0403050d141501050304050618031c050a0501120c181d0a060b01170c03060a0312030c0311041d310c0b13 64
    0x1401940815110400d111186d94000f810f00c400410140e074520030f04019282195a241450007440b00204000071030800207441e5040f100c845004020704d04221120030322000014104808011040042c1e400f10302603405000c0220368000e901c06110304041b10021030464151000c42d0511505104010103d4004210319921100d060030300f0307050b21310700c0c0035003420b61003010301410304103404a5080c0c18045071540b1071403148452100402c8140d8030b4a006003001c081c031501c010680c2e180000140714940c00020843c2c4691020a00030941c1e030500c807031640070303c00c1045900c0034690007034091500f880f0f841d0098484041081c2059014156203001254540d030009200c07041400b400000305030951205003c4000454110003101d0090001d8403000340542500000130000900f0280c11410302403da0088a0498040fa040243e04148540758040f4800e401040c1001c00ca50012500118021605100b100b201c00e000b58050114a50301d482d80d40d03039100c3e400600c0b82c40e17014800d80e0a9440600c44000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 653474766 1250 653473516 653473529
    0x7020c010305150d05120706140a0605130e010213080609060a060b040603020f0f03070513050906091302010908072d051011011e02071104151e09050907050102190c 72
    0x4c483d030392402d1041c034022160000b89019000020f9042c00c0c0000741d440741c107400e400000a200c2c180c44078201c00080e507155001b8603901521280149000da101d0380c7c008201d02c10000009402e04015010380ca03200a8980e1042d0400d4100c90300700700d241030050140c1e0f0b9018074400f00402c81c840c1013045c004114040c80c040d1805040d40007038200b009640440c10f40309503591108900e070740c17460281001400703504800329011144103410f41c085003070303c6e0100c8102c0c4124005080e074085650b4100e902214440c122030b0076418000c0032003001c0703161001403104d00e000c0c00780ca130307004c8000051940000100e9070420a01407420000710740700b071000c0c1e915810009a01705007450a1040d030071402ea0303020300620549201c0782021818220881008042e60080d00100e401024401c201341010028441554031502e8000d00c2c0c1c06403e0824404401015070300e91801e10b10f900c9600c20790307465207200320071103405441d401e0441d440b8200c00c001c40d47c0d0400901c003502207120700d80019050566541c2c0750f010103500846 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 653476016 1250 653474766 653474779
    0x10c091202010c0803090a15050c092724010816140f0301060e04051e0c031509150a0f03080a080a0902041a01020d0c050c0907021f0507020c01030515 66
    0x8007960312aa590008072a040b180c410f9072414110b4041c0d0b070711030102800303c07900032030580c0202030307080948120781c42158001a41c502d0600f40204011340d25125007407082c84084c0c450f0b01c81202c61711310b920243c82081e03070002c440c1000800c50702051514260300e4003241003040081c00c2004a960200c140042c00d649810a030220320215035030451907020391150501d4400000c400019034650100a00c0e681c0c15040d1800c0085465205415418041240d10606c8010708000854030300403024004642c050207005042002c4030000380001d04100c0c059609000e20862000342010611f09a00058010a044800300481c2840c5980d54007540c0034503d403a409001a0200041616000e40c200c020143d40c024020402e03503c5464004a40d01c480c4101c042c01845170040105c6c00500640d900c40502c1d0300100244411220314080003113061b002012402103015070031845285c4012500e4000c0340c1e41c861540450036241c041002480d202c41d000c80c07141010304110510906290310007008008020944a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 653477266 1250 653476016 653476049
    0x21305060a030e0607091a030609070f020319050d0501080a050a03050d1d0a03030b030309150706060302210114130605042402040819021c06060513020714010c09 71
    0x6800500c0103000c111503600800c4c08024225501038000400e82c2d01490040e50055070b984a280310301c0c002200d201d0342045281c4046203030b0a00600b4400c2d804141c0d881124a840c44002034480c5004c1104204004240c020070301e07c400d1800c80c05400e014040c800d000b00462403068550b07a030f8594030040c010f418030ac00003a2081141071245c2025929a882d1003805492541040c034080e40c50110840640001c1d1038201620304510340441101d06864000b40300c14040300700d03843e01d842242c0c0070900440b201030756440004016103520032941051740181003111080d881c074250b06801e4407501c40c0d527204a414403504000c0450032086190300c655400080000e19580c880c40c2c0b40079a6060b06011110b90000c4440c00040d80d1b960fa0020301c02c3e5828101510202c81c0500e03804402c100c06004002c0d40400341140700300c8240805230482c03031803c0c002c0f007001c034500e0360710070204005a840e05003403200e4a800040140500c44001c0d282c1a0902043d0001c10128460a000815031a128043c208a801030100c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 653478516 1250 653477266 653477287
    0x30705091c06061203020c0414011701020d0e011b0e09042301050903030106020d11030a0e01090b07080301030b01050d0b01051c05060930030f06040924050105030102130506 76
    0x2200709a80200100100c94a8140402c00d0710940d00c0110010712034401c51307010600313283c000c1840324040380d00b0051499090200e1025006001201f0004c0c0359400e10030360705a03c400303002c1e00c40600004030000500320700039011505151031030b00743d1350b06118034404086860340b1040a00341d4860b4100784101c001c2e0008d41001a10f01d084c060b01b4130010741c00c04051200f4000040000c41c12902c4c10b808a445802811b1313400c0e543c1045d0f081e51000706401c10b0080760441805403040008041d0f052408211554540019640c01d400c01c041c10b440542010005000300030b6107044041c05032004440717120324410a80c3e41c030414885c05005240c002c01d03189070300527050b221840036035810507400000d6070b01919240150700e035030b8a2b0b000744c604090a40d0306a80c0d4507221207414201c10201d03040350355500d103a40703407402c1d000c5070140540301c150000d139601c0b042ca0100349060601c1d00121110746a00b4448020109a00161401a04030905c01d9204020135041d0302e29645c00081281d009440d41070321100b0245 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 653479766 1250 653478516 653478559
    0x120906091b12011e06090e060412020a02060316090b03040f1202030f040e090105060d0c031b0504050a0f0510061d180c0703080a0501030308070c0204090c06110f0303070509 76
    0x411010b1982042004040d10506208854001e21465001c000f0039599030a0107003a00c040c02c8014016410050100d40890300c14619580b10507600d00444110031480c2d80880c6655104580c4020b941c0a00b000c00c00145034041e2034000248801d41515046042c20f44a807036100c00d1510f4018590300400f01c442c03580c58024010b407410344201050182e00c95648016101081000f00c03100d01e081e510340000070321b451038154616404150001e00180b000c506668910b046c1c040c8580059280440b003000000d165070321801910301c90f1f0811080491039524800800043c0d41c0060440080401d500e80144107440d4804043d4150019074480072514003811000f164051041d5481c80943c91401010421003420440091081510907682c0c00300b645c1c1e441c40754400300c603028080103000503500d80100b00303a1481b4604031030f00580000c20005554605949040180d0a564054008200645441508258140080012244020080c600d14500285c000b0304502c50100300d54130400009098035200312204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 653481016 1250 653479766 653479789
    0x2a031205031918030201050903040e1b04080307080a1706030d051303020604030b01030203160510030506040f06140a230409030903120305041403090d02011b17120906091b 75
    0xb40420003050307040030a03540002d082c80105401660030302c00440d0318104004102d0701200c03202c0d17510798034036114a09028440080741c00704070303103400042c000400d0020080c40100f074143d200e1242d065952182d0003010b0040d1420b0110101c1c40f1001004100d43c0d0b46000c640315409280701d143c540c0d954070351090000200c807026040a5084000442d01108001581c2a1241600d008034200d07a0f4904c401911480f85503603502034107800c020b01c051450140e40c0280c2003582c0000d401000410f1800c0442c440da0100c131100d0380041d2400d03001544004070b030b040c01c041403400703440b0030702c011400340d80c0717140a201000c280304400d80d020300d60b500c0d611000d0500c90351030f12000e164403500718204103020310300040250400b0b032020b45100311034440c041310441b00001100c82c0000003400d400260a9260015103100d080071008441e034140100d010000901400411519108004c08068641052007102c480300080240030032440e5010905106a020001914003100d070842c044058109119030042040200c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 653482266 1250 653481016 653481061
    0x5090a0510020a1407050a06050c070f11040b121b27070818060f1f06050c0f0a05071404110a05030a0c0e0a050103090f0f2a03120503 59
    0x600000c221180080c0d001400301010310781c4c410111300201c00340f04080e84299240100b065001e800c0b131000041c1260442035108112041d454103100540c0c85d0f030320f5044098441121038030000c40c0e0070480ea1400344280d0b429030105071240540f0701940340c0100d40e2851040182c94440e81e180090344604e40c0e800700000b941c495024000302b01c80103242503042c0c80080c1501d0000204251000003407403682a125152103961089000b8901d40d01d82c10800034404030040c004a2040091030182c4d010f07012562002401447c00741d07647ca666440608007503040103090610340815801100300140852000207100040e6403007090400421080b11000500601d94660396058101c2e0210f480e01000e034004010b5072149024210031701c196102d141d804ca640701451100942d1040d4500c17000e00640d440381e84a074850074401d80041014840e20703100c60090074000002191545007103010415000c080d111900f0604000d50f8400030401e007542d03644140c10104000b00410440c0200005900c81c48808240402c00d05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 653483516 1250 653482266 653482273
    0x40206090315010f0816030816020316030302061b040312020f0607110d030905060a02090402070204050a05071403160c0305090901030305041a090d03030209180109051503190605090a05 81
    0x1e40200d00b80b8406402d1040001140101900069541c000b00300c1c03105640c120030703544081a085548002c00d40e080074890484002c0301c90100c00042e10100140403000744d5000e8a485564954580240350140091060309410b21403d000103c200b00c800079101620f038032001030343e02e230200941d0803450f080b600201c026451281206000035a03030000100340b891880a000e84000b195880c07801d909032080000c0c0201668460400a04806015030191500c098001e00241c5441c0703607500001c05039081540e00c40c560580e0340c2c0503c8840390b00a468030a015002d0402e4605618054240d20607041510074050103104d501078000301007510030002c981024400034414019540c40f424024010b41050044842e8171841520070340c0415020000da401010001300b00d6140304940e6507084002c0e4200c4603009401042e2101c010a00e041200352450180c940d0620000d16440c103850403000b40441e1030941c40c001d401894910b049805524544401c45410220200c0c450f02c51000483c908100408040c0035400b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 653484766 1250 653483516 653483533
    0x30c05030d14010608010803090d200603041103060108070b0405040506040b1309053a050c0d05070309050f100c11131506020601081015050a06200303010b120402060903 74
    0x41c07400c030650580d51659035003070460307891f0016261f0780d20922038420703400400700d96030a000405503480054030f1810001c00b0706100c003140011401c241c005a404550308509145400d240381000c1210f40d004000b258000e15005140c0709480091f44640c0c040e590103551607200161540d11160070031b100c0028040c009001b4100311040318001004640001c44186c0100000801d02e0740d541402424418540014a41d8444201143c80a49294000041c0c2800024410009031050500c40c0b0040a5030030307140d60f03039030700c1c0940303001050048280c020600c00c00380a19204c40f2503c0c1c21010144002c29400c1402c82c130042420b0074501c451060031015807058550609050450142c0c011402d41003546d55020700103a00e031a0240c2c0c41e0a824050102c042e40b00741030301080203c1c01e4006840480c2108004861143c50368081000382c1d030160448808181c03080c4035685200d100f8070307003030300074044000c055030465041c80950803c40c441c5d110302c042182a0380300804c0540d6100302c01c40d000c0c3d0000808540903030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 653486016 1250 653484766 653484791
    0x9011d01020a0e04020405062d1209071203050919090c0507020414070206040f080d06031101120b010806040f06081005090607080c3f270307030c05030d 67
    0xb507011000080000300c088240707481034100360080c1c0b0300f80c4000408041c10310280d440c1a1441c0b441d0304031007082410b000c0c006c030004454440024001000c0c42c00b62042c203803520031035042ca0a0801d5010700c046000710f500b0040401c0d8030034180e44100c00b044030310f14441020030114500600141d08031401072450845404407503038118005083e181c0c82500c00f44028000d410014880100450f80000941c01400001c4c00068103580c003c0035092255812a0924034528415802c03182c0c2c035001200c03200003108500380c6035038025044103903000da124418032007480a01300003071030400c000c0d129502071a01c0d40d90950807084950440d001800c00c100455104d00042c00d20000681f606881c010018016600401d607800e106180c0540304658808850307203461380c0304140440d025804000b01c11541b85109050f004000c50312411860205803da1800a81c2890b400720040298444059404046070108900f901c160103c2079904054060810300e204a045080150540c480c034000e20b0703441c9140c58001d02da031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 653487266 1250 653486016 653486021
    0x1e190f080a23090d1209050303060d1401020a03020a031404020f10051209100e061b34020405060f15030702031303030306090b010912060b0a051c1a01030f0b09011d01 73
    0x20700565030b9445c4851805003540030201c4041c4030000d48a50400c1000400c982050324031440d07018420b54005181c40c8200001d41e08a810481d400340c0000d40004003044a16418001d240046010500500c141d052a9001504084200080074003445041c80d1010605c2c3c040c4007600d654040f0b0004d044564035059a000b911602200002000302c0d18100d1a200780810008100384195149140015651903200440403103421804c283c2e4205a55030400318004000c822070b003031084c0c0402c10305261028143c4100415200300070400c42c010981590b0032001680e51484410842c0c054952895403500d606400724210300c20211900082842c9031800030406500d80d1081044840c0d0460030000c50a40c8001101c05130250f2184031540c0b0010780d1101c010482c10346c4110315101d001454210629a101c2c0898103500e0300504074403d101c0105130b04401d00c4014401c141c0c11036040b0001303080540c1143d940c0b80c84248004405092509150000354208030254801100341041200c0f04412898890a2a01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 653488516 1250 653487266 653487283
    0x3120108120301060807140d0e031e0a092d08061803040e01231c1e02030d180816061701030302100c02031e190f080a2309 54
    0x4852142030707480c45002200c0c000742c0b0f050300c0199a444039213440d0328400316411808880080305021b410400e007659040302d48243c49440c43c0000146441c0c1e60081508180d5520407583e000342190200200300c0f005601c150785d9000c0c3d40000400b44209804031403001607428000c00314204003002824042408280000c02c14410450800f482c24041c2080c1078054890090384a01841078440500507c815007105503104807821800070000c41040c032410000b40ca68122180c0d0a8032900c8030304154040c8120323010520f0100e219019410010308075035020a0380c0d030034003c123100e0410841c5052210351141400c20f0600400b901001c40345c040469000a80c0c070006144a5240400c181381580458800c2c409110b904807a00b6802901154102c1900a001b40040608180441c001000321440756064001032840c8401008019030b01d407840da17001c100343c0350002e003154000c6c002c3e007610801c401540210215130080200c040891203940000d4000c40c6e100341c5005c00381840c04500c0c100101020700140041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 653489766 1250 653488516 653488529
    0x30605040c23090f010c0501020d1406030c15040314030706060602010b040b030a030c12170a0c02150c030a0b0a0302090f04020102190201050409020f1c020405030c040e150402010e03031201 83
    0x2030030703007010918042c0c0600c514440580c000800e880c9103805503002c0c0f024059051700035800035143c012024190008c03500340030a40c0941c06940000d1050b1418100b10a50004000340e40c0113002000080000c540d602580c4801000131104c01c0c01804100c01c00c2c01a12440c0e50710441c1070140903160600640602101c089890040380740a001840520340003421001d06501070f03c03040050700b03458986a13205042e180c050380a0140c0d102a510f040510380583c1e500c6801c0400b400250b0711b400d0b0701c00a040006000d09030b0a08a03501040c0520030314000d045075004420400d001a504003a00d01044c82208154000307544840c12400f0481e40c0c04040b4a1640b00c0c80c401d90035110002807002048014001c3d065019000400500051044644a600030142c494808000070f0801c008020306100c0c412800c801c2c5030301c6980100d41046241010084406400700403141031107401d0303040c044241c0c0d40b02c4980d079280380b40429001007801e5900070005c00d00d0040d0058241d0765074484e01103518641c56028442c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 653491016 1250 653489766 653489807
    0x120c0f12090f150703030b010e1c0b010b0a08220b04060509060615091e0d05070e160f1d0604080d0e0d020d030c0519030807110c0619030605040c 64
    0x120b2510301a8181603400381d40400079403c250130364404030000c126807001d050500c82c00309442c0000744d8035142035240005941b144190400103c0c6099542424103902881c0005000c0c806034000d1074104810590013036001c6521000e00110120070541050f076042e01520540740b0718188003d01055030800780c0b250b507202d42241c0340d90b2120814890104031161b9124840c007400d00c9402c040d803810001c50f45001710054948102d2040100000794007a01d084000c840a0b4400702040000031001039107143c1c401070f81600c0d2484130400d801e0241000c11102056001c1005480e21000f03070420004c900800c40300040c0950b034403691145040c43ea180d01c082c1e41c074004200c1001d43d41405190942004000c1513019202e402c051105540a82d0840303032130101110309009480070780246c1000040030104080c0680c0d0b4040440c1400400544440341c1a00c4102c410340042003003040f035848501c21a4a0414042d03960074102c64202c0007100142460741015511500b000c481701907403984a01e96014245107507001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 653492266 1250 653491016 653491039
    0x31308190f11070b130504060b031905100b07080d060f0501090b07021e1302030a090b0f070839040303030b06040e0a1d0a0308010f17120c0f1209 64
    0x58600c480c0b19510014280c2c000041800a81800c0c8058410044511469201c16403100300003029204a070b00107403c03203000801080b0058020f1034585082a02c6010104a582050f0002440ca0303c0503000762803403030100080600800150104039802441101c0007004001c2d22175039001d00ca00241c1c403c035070000762200c0020580d1040704044540481c3d0084c9150001c415110381c18000d410761081081d031100140c0b00313140108241d0f0004500c156407240000900031051300d081561305001034181d0b401c0109480070007083d40d812040303458008002030603060424501c1140000e20105442d074541c06401c0c03c1c02481000e031030150107441030300d1007900d0900244e010f1100b4001a0700a52013041d610700c4e012800308081e286640d0040100c035205a55000c94512070b900308078503201e403a080440024403100300400c41d2000002c00600504002c40703450412022112074142d44444540c0058016000050022101ca50400c091500500b200c426500c80000e01d0100e801503400040045004213602c480c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 653493516 1250 653492266 653492297
    0x30c21020f010204061d014b021005060f0303040303030e010e030f222102120d05090427050f012a0e0a0e1005040f06150503130819 58
    0x36201618003581e00c044a10346d42c2c0c459403480c00c000b020703030703c0c148101541c0b283c06103815400461104003820400c0d010322140e12074132808841c032140608041181d040050302040c0d5002c01d40354041d80d601c00f03010a107900c410001a03640750126020380c0c2e1500c03002600208164054004181048004000300701d006031070341c5a503480788109040703054900001c0061104490309450b00040e40100c840c0c44461442c1c44203441440708410034810003042e0f0a0411540440ca4000120300c01c0042110251090801c0900050030360b0140b80203440c800c1d601c1e00d0515804425440c070b602c07168501c1c00034681001140d4102591140c0080c4401c514550901e9003043c0c10740701181c1090f221400b110300009010401d040e00300c400502c90740455510614805001949000f00c01d05607003d0a004120300048902e09800c000c2201d000c41106503400d410038200f00092021340c2c00c6400800b83c61b0421030350701e994072500b1141440200000500080001c07440c851aaa40824007941b600025154a003800c8441031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 653494766 1250 653493516 653493521
    0x20c0913050604120e0604030606051009180b01121506020f030306100e01020309030d09091a0d0807080d02030406060f051918060810090606050d0f0f030c21020f01 72
    0x1030020340282c0c044004100010f500c42070159040d0110302d080c0c181114070a0000b4003981c0181e000f0303580c00341c50341d10070311991410604400f4214014141240040e140c03503600c10107140c04090b0100d2440da244ca864102c2d1340581500e2400c07106482e01000030300103c0041d480056180d000741d50041c07045038440d48610500104490161100901214031a0755154045900b41041540c0030b045000510540c034054900300140c5035150f4494031a0b8088070706021b00c075402c8604181a56440c4120f03400ca111140e01d03800302804019420001c00c2d955440d450170201c01e1440b0752131103000150310000401c000d200c000d52010b030689038405201902c1650303590401a84070401c0c1034840f1014041c0c0070411924014601911001e0883c0c000850590340d1070036514100210a0168070250f6119503408081103e113110b40030151208072000c1072001d0007a15058a11041340340001c0161101030355076414140112500070050354086885100250380724010301213071000005e1000135103d0030b40b408000031410f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 653496016 1250 653494766 653494801
    0x50108070303082a03181b0a0b0702151b0105240f01021f0b1201060806040b0703090f051f0b0315060d060c090609080106051008041a07020c09 63
    0x10f80d14206503880d00c0030751048000b00c120081d40341c281000a600d04c00c000c40c4002d14800c8103410500d2000000c200c94242c00c1100c141040c001d095402c5404400c507a0b2415211002c1c0c50340a10361640301c102500c0843c0026105150000303505001081288011007010b8103807a00031740d030000074462500c2791412000503111307072113400c200084441d80301c8d002802d000b0905141c0c400705204490319a81da600305c0b250040ba1030400000260b803200c041244600700300c00240340720003425000f005038501c0c000f0b40644900c0e02400017401081460080380070744c0e11a03007103104990341040180b01c0c142c4881c80c0c44ae98031401c2d580c2c0c81d810b109510140860b00d46582c803a9100030320740a030140c2982c0d80060301c1d00603640d1000341394070b5010a210380b40c0c40118860b840340d660041425103555089174102400a8000c42255001c12001da05181e0184800c1e2600d450b1917008454070f081060083c0c5492502690000200903070746203100b5100100b00900760700081c8403d02140c20b5031443c21949a480f0300d5022030580 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 653497266 1250 653496016 653496023
    0x8134e020105061f020c06030a0605030606030706021e0f01110c01051005031b030f0f21070804061416060c03180804050603041401140403140903060619030c03150501080703 76
    0x91403203601c9038548400022004c0c40080c0b0648000749460400107909030000d0351602c14059440d0018001070070f04100c4150080801c400030051140340c414000e603074224a10700d4500a034030300c03441c50001604c2040201084407c903402408041c410729840c4a29401c1540c49a880e907080c28041070400c15030020701c009450015000d8943c00d00070801102d03110a0a080407030305480348000c038107500d007001d014028014002c0c4000e40040a44410202c0b141d144145902c48402420409a0006005801210101e445500340061070121380d458500c124091800c0aa44031001c821140301001501d07400000b141d900f50b2010820504421107200703900e03002610080203074104100900441c80c1c4040950b502070b1003483c80c2245901d000c030480c0d00755480e1110300c04035000c3c4c40c070a00041641162404025020300c2d40a1400c00715003d0020350388a030040c0c80640981c5400da107103160182c403081c4040107160000c40066840d550303443d040c19000d403480052040306c0c0c03405001082070080400c107601100c3c0c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 653498516 1250 653497266 653497279
    0xf25060219030c121a1903020906090c121003051c03051f05040209040b1003051e0601020a02010c020102071a0c1005090619021611010f08134e02010506 67
    0x8550074130ba0003440800d07088080d846074104080300e00d58030802040715441d5144203290407607145205200030594050b1544d441a1008000c00402d40e581720140d41e440c01010428096a072121500541084190741001d80b01c0e000e40d00d29030b492990400c0910303008030540c0c0d40402c0903660380c480001018200b416004496440000e040000f450300742c0140a60b03140040000500696040c00908030350a15900d09012035103410402544030711241915100f1000395401040030700c0c2c100c0000307403503020000000b4148400d1800c20003c1d64030821408004d403081001c2c070300400c0c1c14084000c0c0340b07803c40c1d0100c4c2803510864030074421f2941140030f118000c00e1741400400031b648440c2051005200e400d00d0400c240b5509008102c1d408a108880b0f000c20381c00b4205000300303000414001481490404014002e112081080c13000c0305410807060040c55400c451801ca502d24000d5075442c1c450001794030014038201e100d05a519085404c0c00c0f44481044131b0980d2040404003041c1603003a160111651a40100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 653499766 1250 653498516 653498537
    0x70f061112152b06020d0f0615030b0616140a06150f05030106060f0804030c080a05040509062b0501090c0b030106090e090a110301150303050c010b01050304080f25060219030c 77
    0xc4c041d4019111012000c070001c20500fa42445d1401210b0440d4002d558481d1180209441d0682511900150903016641d152600082d00750010320302c040c844d4010100324005404051211041c011450303240d600c290b0900101c03a0742e07401c92009241c1401448065250b580f0000781e80c2c6070510400c000ca40c00c40d00c994954017050481500d1441c1c00500940502903010040c00001e0b6020340100009030041c0c641c552954145000d011010350004c04540c040d2002c81e40c85115a6540d1200ca03040020181184564001030b00d0541d0241c03001100085c81e61100d0b0001080d407500c5600950b0583c2c00c1d85d81d840300103507600c034882ca40c4d510003500c0070031441e0403905103280032607064603400b10b442c2000317000403413402c40c01e080f1400450442d40c419000980301041c0000315000078061001610000d2030b0403400c40c00c042d01c5070702d11440340038840709103494005011161103040d0440d055614040034080003d03950f40c0c0c00c00386c000e94061040d20a000c58410807004049002c3d115812007001c003551940081c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 653501016 1250 653499766 653499773
    0x114280e0328020d05030304032003072001050d0f020306040e030a09030305031b120a06060504030512071a04050105090c18070c03030204050a09090209010605070f061112152b 77
    0x1401c00102c240c0c1c0121120803581d020850400056000b0b5100c0c0e580c9da07100003a210360708110802d4022004900307801c20008007010800350035104040e9245400d2040c44c0c0351a070801658507101d0920f070528150f01740551003505401a07400795114450564040c80000e0700d0507005a16449030942d200045481040d0500100f4400c40c040c581c81140303581641c0c0805248075031709260b6041040c03c208104c921500300401828207018060041c02c850a06a04041c00c640d54140c03541481303110940c2c03641c0701042250500004002483d101c401ca07052039009420079090190290104813515950780c41a8020f51259040540a61341e12141c400da10700c0c00c549524034202c55a5040361415020140c0900010850360f0b9150107620061192040001c1c50445910601c5150ba405034014014880c05108480201d5410056070307840c940d01640000d503903121021403c1480c0184c000540f00300402e101004104147c196452002e0841200c12404690300c0c80c09076204501c0d001143e000d00c07458065241e000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 653502266 1250 653501016 653501083
    0x15030e060f060303071e150507022e05150a0f14030d0c0201030b01020f013308060c16050105070809011b1e140f040609170a020114280e03 61
    0x41d500b180346d039580c0c050304503203c4d038400c44c1604010034001d03940c0d40103000c81d05070108184000d2506840d903203112907040c0d18088000d80d0f80202d22414050710b5a000682045880072000b000ca0340003443c07a00c1254581c1840b0355180110700510b4401c031101070b0b812405107030002d0400310980c1070b9a120450030346076600440c09401100c1740a419441842d2103045251405e00501c021092031480188200d03c425079404180750600745454901082682c051189850200782030b5880416481e01a81d602c1c480c1309488204880090050565440c14051102069101794041e0080066500070f002115100070356516550304506500086025009080818040c90305094141c3c1c0b9103041125000c46000042005680013680b407001403100041e05202098101c54070401522000c5800480312101d0b945c4030b5540c0c040404040d0610980f80022510030307642c54220b4803125040500d0010f00790180e400701a41c0d0030680d2241003c65120391262a6038100025000560024040c4034000c00c0c06440c80341c0710 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 653503516 1250 653502266 653502293
    0xc050a09062103120507030203070f08090c01140f031f080c030d081e01090504030216031505040c05120a02030d0f0503061c0803091006060c2003010615030e060f06030307 75
    0xe01003140800c0e02c00d950a4821700388508195207002d41d0304d15119900038040b0801c4541c1c42c0500030043c061210307443c0d00240e00c006550007070800c0002003210518030b80d840e0141e41d5800840e10740c0001040381d081d01400c0c0000c0e0f100301860400c041a51100c030340b0341d25444d07610503da8040e84a5240d941401d4480c0785c009400407004a480c1e688000200c0c009200300c4002d82015038016221000c0c0300400d43d040105501c0201c050000c6074025065990f0741101091040a00030710030348810218061003494844000180002807203202d145e1304640f4240c0e265204101d060f0310900034646240e040c90b01442425810488a6445501e550366007030400c1058940d01c00444081403a0f1419400043c060000070f50190320803000400746000b9402d034400076941503400860400503001322480020b10140071002450700007040c10705001c1d050300007007401000303160722520050413902d120081282d0103034022101c07440020142c0302d603aa10400e0f0844403d800f60b0312282c05030b10801c400300c041401283c501c007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 653504766 1250 653503516 653503523
    0x3030310030b0f0411100e030a060b1e01020a110a050d0b0f070503060127030206070c0e2a220b0c0705030a02100c060209190608060904020a091808070c050a090621 72
    0x400707e20172008203250000c00c3e01c0441e50603039181c3c40c00c50146040e2a220300704015401103503400c4400200000d40392251004000c0608451100f04c0d0096a2501101c0f80945009022011014803a05040030316240958a4102c035081d400c0200324482e1042c4103d900c240410b85640d0740030003c08500e00c520813170400c01121065030f01c280100050355840024000f40f40101c98110005041c08400c168412014080112400d0316007455142d615210810a058140c102c08850300c42c0c006203140706c003ca8681c1c180040c241801040030a075150600c0182c0826520f44045459180d1188181a0780c0c0c0c3c0003400195004074121703541d0b484140704030a61b400641c8074150250400c00d05c0070209013031400c070741045820f8505035041132081c103070320280707503a4801c03000c4900140d14102a008540003207100d000b8003600c80c5e1a10100e402c020030034100fa41d200c0750f1140d0141d941d48258104440b04114074002d8030310035602440c00103001c4003903000d000c065840c280c400741c03908406808100320300501c908084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 653506016 1250 653504766 653504777
    0x20a11070f1502120309010b130501082a04330503060126031c0b0d21020c1305061002030a02100c12021603030f11070b1503030310030b0f041110 64
    0x113982004a0f2005940100e00e020000708403038480b0301c104188000040180140c00c0e00e4200100b108141c0095800d42c2e690a00b0b4008405859900420b40100307107240640390403a080c444442002e10100203120407240c030a9899506c0c01d800c0410900301d90301c9038407903203906910100042c40b4a40c1c8202a100c06c22030784510540041c01c03c01521429500000551303055011048206243c02c5124014003415a104075400700140a56594074031100c20300c5001031418030584489461a00d000300010102070000078900d07000440c807900c040f800750104507041400b80844010740025540000107a40e007020b490303000703002c0040c200040c0c03a001b095503210200421820004e00c50030b031903d51000704031303440d001500560040441c0c10040c0560b000c80810044184c5400c0c0c91207030980310303c01901c4c003240c1c1c0101a0724a075240c500300c440c5c0c060450320003c0d6040c0400001c2c0100505d20b9103446044901c04c1038600003599480a01407100b54046034081c000d00d81c19125010325107460108000c1840a80c10300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 653507266 1250 653506016 653506033
    0x1e030a232b0318030206010612020c06070309260714070608180a02060403050f0706091203050904091a04051005040f03200d03060e240108040c09050703020a11070f1502 74
    0x10f081a80c2c0d042506901680021005011080d40225044260422140154a00f2100b120420780e00c11004200c0d01c101a070758074440040246450080c4003070001c20300c02240d04482ca640c89401c0b1740c0035103000c45610b42c25551580803800003140c0482210010707250b0040c16980d030075410500090702e0b038848042e80191000d0400694070100034201850090340185041121134401a1800c3c407160003400610200d80c1c410820305480c400d00556003035140ca44a1349421072480460060004d81c40000c10352009010003104162446d5802c501c6a806442120700859401ca0804121403050b180500b036140100c544002090089851002d012201d4034403041e03002c0b48220b020b04000c8000c14101c00261541010418001c018200a4010325a00c024810b1b2040048a038600c1c421000c5440e030500c00071000040601c20007080c140000c0801e064103001615007000c0c0100290310007500100410340302c0300c01c040441c800044c06800c2c2c0360050030000f2050700f81b0a07407108200f0310441a10441c86a2420b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 653508516 1250 653507266 653507291
    0xf0e1608120702012006130b0f091f06080a0807050d050a050322051c090e10141212130b0316050903010209061306090e0f01051e030a232b03 62
    0x1c41b03441850f400b046000411881e2409500d200ca010700420080d01c0a4001d0084949001ca800c1b101c8a240c180780380e201d9a0305624010142c0388075404941e03940110122039081c0031441c1700812650b1711030806e4407601c0c840000306541d54020910781000241c0c050002410010843e01c02aa0000e007030150a20404510351f03500b4a4201100b140d0000007200010322100140c00480560142021000403100303441c0c950603001081c940e900c5090480d1601003058409611014417495036280c2401c00c3d40e0444a004101011310742c8012100340b50124034040000745880b10000740c1c1d0052100c482040180d800036a021285500140c07003c41c0d25541c02c010110aa0ba1880001c00f10404007e05103800b075440c00f48041e01c0325515030702c502046082e034810017072104100c01525040d40e400f2600410b61001201c1200451210b8190040c0c15204005028050008141c01803203652a82d13a034020071301c000301c080582ca41e8a81c1c800320071041203890284c0c7c9042000c81e0300c003003007102030324002514015016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 653509766 1250 653508516 653508523
    0x151e03110310080105010b070f02090a06120f0516032a17010605030c042a0c2009060f03150c07020315041a040c03080a030f0e16081207020120 63
    0x11101c0c0c00380210b001e0200101d500038091075006240703142515051040c41e8460000004102d23030300900c101108000583c0200d402e81c07248001d004141c041e006040b84ae41b501c080c08054854060310a0300c50307003020103090754403a03c0c55029260301180403603000c1742260040700340608003052880e24000c3c145001c56000c3ca0385c0c0c13031162802c500c00c001142d910f151609040c18114171242d500e000710700b040b0112511190310600340d60310090480712800b040c44440811540c2090f0f12800030010a10940003004280c0c40011b03a100e0a03004840048450b280c0000f007050481c0e15960f5107405030065003071b120140120481c0c6582c131144001c0740500e4212282c1c0020700341200e440f129444a0710180601c030904c104040c0a42c10820320000a800a04080c0c550007140e000501c0700800018000030380240740351107a0043c0d230070814990024403141c860204800d454200050040130700b02d00681c0000307000d54001031080c4840c00c420010358507129054004640c01107080e0b070320423840b403691005203103c55401c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 653511016 1250 653509766 653509771
    0x1902030411030d05070b06091b0a050906070605010510020726030c1002030f0703060b040504022104031d01021b0603060105070506360721020d0809030106151e031103 73
    0x1340d072490b5940c111443c24520f4030801404a038040c00309141004aaa005a003549072040020750050380c5800d4a950708560360300c01c48058507040000420a1410060f02d41c00683c140e070000c031004090051025401c0342e1701c21540c49a080d0f1001c402c084071580002d958030800d0040080380540349022030751ba401510b02407003080d400110560020407c1868800c0c000d44a401949a1400b406111700c0c00c140e4805601450103200e102d113500040640c050700305002c000b610019142d59400c1e01d80f03003900740501140c00041c40311404c8007000310038082c1f40d880030640c031581b0060030345c80c4045802150240f0003540c0004104a0504c0310402071203000c52810002d491240c0f040c4040e1074100c2e84c0c4905184244460040c40380304415080307198a0314201d0205060003900c00d0348940c8441c0500c2c07008a00e03074482d080b8202039007008407110808288580f60b4003c29a16000760000d120440e680d104850a60908208010015403504814920402000540f4203081401e24001c41e0b075403101140140180c0c4103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 653512266 1250 653511016 653511043
    0x2010f1d0a15180b2b090b0f090109080d0e1e030c0c060a0507060f180f0512071e030203270f10090504020c031908041406190203041103 60
    0xc01c5040c24603070780180c804a40881890307800740341c1844e00d0b80300f0b00300d8001d81e0f01001c0080b280b09903024180b0340e5800c01c04464060359806021503c0241080c0c0ca4003c01501d000262034404c1d00021404241406241d402660001e200751403c44000039200003805000882c10300c0740140038120381c8240d004540c54108a180c180903580d20404003005501e0b01400b05021806480e0510011205036042001d0b2600302da080040840c981c515804664014a2000c000034060b400300e443d01020706c02607030480032030244a01c3c02c03202c452024943c0861540540e68005000e000003146050952100103001e030030303181c031a004a0f410082140f120a41c00701040ca68855028030300020300ca441c1c608900b501c1c02d07902c0d0a40300100d8610748444000d140216a01400340030700d800060601c5481410002c071503000d0741300280148214409200104038a00550b0700762413440782d81062001641c000308a05004a40c3c0c0012446240514410740019420040c015110108a590700000d151001d0158030242c101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 653513516 1250 653512266 653512289
    0x50601230c1e011503080301180615050a122a0e031b031e030d09030c0b04050706090b030606040504092306010527070c020a030501060f170a02010f1d0a 67
    0xb09400c44608582802540701c00c07000900c0c40c03c1011135411011281036030003903e1440c9031500c0c48031158019002c158007481c0b910b1404280c2c0130415612001509640403d590b69001404080181074155442d5001046402d1102c0e6200c801210078040310050414030f904080038485002c10009050407105c0d4046a1040d60305035010035a80303001d000c07000e025100d40c6812804007007890811583c0380160b009007a412030790340c0400000d150103250050701c02944081f6a08452929142c45500c8102300e12652010070501c3c50041032a034500c4040c0c1c0e104003405080c0c4c2d810a46410100301c040e0100f0350040d03403807007005e807082d0344481d006035020882c5d1140b40004043d55450841446115071101191a40b862070b42422000055142030519400400340d1821200c00040c500025000e02c0465000612035881d051000800c500d200d10060100c1e0500184c0030b680c0b11002c442d15485490600b4000e0018115850588455000d4001210309044000320b0f02031011841010401507081d03900100d61011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 653514766 1250 653513516 653513563
    0x10311010908030a08060907210f0b10051c0b0301020706060315060609030b06032415060403150905010609091b0503070b07081c020d09030f03050601230c 68
    0x140c000206000030402c4200542c038082c43c0f00b400402c81100079090500c10040130300801c02c03082c4074002d000342e0460181c254500c0709529010460003841e01001142d44030f41410080e81051030071204200303103003155032125031600040c542d030b4072204c0114002c220111540ca03101050551801d101920340f551041b4000075995045007410880c400d59608414100c600f0036006000296001a51030100c0c1c3e440640007400c0c0d292080040d042c000350300d10300d41003910690042000580c0d070304109800b419008120203036404920b03050007007500c1075002c0074140c084a00c20b079200b000d44551201e0402e5002e00000141c8945607a908410768a81c1502901d01c26400300b400a03d49011042660080204500416285183c045481e80c40e008603600a8884400401d2103c401078021040c0d2038619211801199141026800f4000034054903805500103864902d5000000303009100b514010403050312003511080c4d210101140d41c20701824148480c110610084804000070070083c108a103910751881c8491 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 653516016 1250 653514766 653514769
    0x60f0212060a140d0206070b07020604031e050a0e030f030c10140108070e25090e09010c081306020c0601031109070201050402060909091c05030907140f040203100e010311 75
    0x405040e261086400302c00c00c02c0040500540f44001d28004c0d248005110b6103400000c00a00900201030002141a8100b002880c1c2c0460316601c902c1c440e81b2044440001400100e0b0703c0d00d1521442004200100104452140900294090b003000102111100301c03070720310007a085d500003041c000010351006143c200803400d140102c41c1c000384d90403034407074484d8981442e043d6941c00c0c0e4800c0564240701d0002280c1d201c0305007500e400402000054a4602c00c0d010320004090410030311a9200c80d0301000701042e00c184041c055101c50a00d030750354400e540d803907512001183c41c0349d0319821142c0300d50800503000c9000003803041d54020350103421221040000c0c0d5040c000c1c101001000c040c00c42e49030008000043e991074041e9041e4070000c2e103507110140c0d5921002464030010120b0804032058181281041617808002980716044480c00d51700083d9039440c1c800840a5207507241680403141c54900f9455040a03405160300951050000404d950b03120540017901c002078105641d4050402c1ca1040310b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 653517266 1250 653516016 653516047
    0x19060e0109080c0d030315030501150918230a0c0f06110a0b0103030509040b0d050d1209020a0302240706020c0d0507031e110312150111060a020c0a060f02 68
    0x2054201e000e810081420340006400401210300181410743d14880c7d9405c503000c0080007400f40d580a0000c002c8601c10030103402e082012031243e14509424804500c0084986409103641c0d994010030390007600c0d0040c0f01c42c060020905607070000030300c0b50400c030601050003c3d07000e0300200315040d06a44c030f4605140e401002d415401040304415840b030f60950303000034040071500d4110383d0903251141c1c54902c078800040181031424100740e40486020580402e2080108a0000080e09529210203c0420b550380c00143c90b1030030350203540a01801c80400c0541000180d145003060728044401e480c2240c0c1c0c10486031500f1445058940541c00300d074130a0f483e9803c20401480d01484d0804078200303046030b40c005103c90782c5180c0c2184822080410208440d0040c05803608404400c0b040c1d9464503015203900c0d0b0094130495186107800440b40d14044030f5402510310001546910005d4a0155148030161001e035010f804419041c0c8500c4441c5400714a4074456041800206000507a84040402d00f0465 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 653518516 1250 653517266 653517269
    0xb0307050111120c01230a2a11030c07060c051b090105041a04060b090a0b0c060c0703020f190b0601030b0a0501140f1204021e010207031119060e0109 66
    0x140200008a200c2142c00015010f0900d2003c00101c0e568480b09580b0714050300842c3c083e0320050340942420381c54211280f00e0301e845040e0021081003c07102417204068044103c5420541c1e001840c401050210300c47c0c0c0883d401047e0b8502140d191070003040f4418075150710b81e071049000502d0800308008000c014040d8201e900700b4040420080307072041000030301260b81031041c10300c101c1c8e65269543c5c0d510b0041c41c4200603490010400c00440d96070307100d605e80d02d40c800d4aa44d8411200c103000801c590030310f1426114801c0300070008004683e182070f40540c107170f0310001d03095082d4454048202c2c0407035020003950100310250100c01680728694075080700740e06000b0b8072042c1403508104003400180c494aa6480c1168024a03101a481042c801c0c022400d21a071040c2c601c2d88400041d03440c00f40d14204030114086d500c203944034584905680780a2010000e840300081c016042a0004c1010500c02c011103664010300a0407100b2440c0c4408140c030603004564004000300301c02c1034042e0429030f00008ac000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 653519766 1250 653518516 653518519
    0x8061608160503040204090c141309050c0f0d060516110114040b0a06051f0207050a12060b120f0f071a030c0a0c0f20121c1803060b030705 61
    0x20340c40c14500000120207100300241010030001000050a540d03960300030842c5a9000894012905d071910710491f403d400b0101c000f40240b040d07500030310921440c0d106507000c003a040009402035909070b900304401960641c0d48281c2c80004411004003180c2c0382c3c40b94030b01a0f60000c400340c50145104030003070311110040500401d00c2e4507020102241403801c80134558810b500546c20f01665599604110091440c0d4028030340000d210103030207400407016a903007032040400b90226500a60340b00c08000214440d801601c0301420060f190900080490300540007508000b00b08a01070014242c0991414151140001981d40400d000402801c41889450080c00d49281c0100f44103116030042416880040c180c513100c00740c0090303c50f00759440740c80c00004c0d441d880450100c4900c001d0030408802d480d01c544c041035110181845500030301e88030b24031001001c18500030f041c1d0400d803090700107603000001070071000340003410740b0b0702480304841c165241c040c5126030b500040051200c81031501e8009240c1149 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 653521016 1250 653519766 653519777
    0x130e010f0b04060f08060a3b01050604060c05010b041103060901140d0b04110612010608010905070c030e010c14010c03060b120f0c04050d031d01030c050d020f1201080616 75
    0x9110b03e65001e001559000b0050a06080a031102804075411205542c4080480b68404a0354440c5110003030110012032000401c0590001c075490102042500a00c210b940c490000c200420005000707401d01200c0c64012800010078030f4070240450296103501451500c0384200000700100c81c078101300b0942c0940030701c0c00000840022000030540030480f504014285025400026003045007841c2c10781c0075071102820307068032041420103c401c05c1c032b401e01482010403500000400c500d1030611619219290725980d28004045130f881c16102041c00721010fa040020110780e07031001c0340140150b01c00307240b40a400020514244400101298072a801003190f4034001c02c2040074046250340441e400501103010401d0342c0d221030803141e2a5110300d40c049500994848081402d26800c51090712a482903c6818000c0544000046046402c1c813070001c800b040090282144520003680a08011145000090300d0203001c00e01d14218040268403040f174031f5120380c08002c0b040250b11900507601d401e60905 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 653522266 1250 653521016 653521019
    0x3020114040b0c0c010207080a030c02060114010c021509090115030b0f0a03230105070201020d060b070f081e0711030106120b060f010e180106020c0607050c090606130e010f0b04 78
    0xd0b54a215400340c4103030103a80000c00c070b02800c0b190070750444c0d486591003003295039a001c0200016000c1c0201100e540b025005a1000140b45030301a1070240e100c0c0c0701613403911124125039003044040c01d180000c0001107001408007019680740d5034420360190a2180e07c80c401c148040e1002400c0c0d5600e070715101e0042c00c2d40343d4822040e884502004003900e520542d80d40760b4155400207214003c5001860100941c00c1400340500c0715010360003420300e29004402402030b180c46006c103126921540c4002004c41c0190440d2001056500300078041107015003503d205d019240b52030009a80d004640151020300c810350084d0050300c1d091046400a00d00c00000c00194038007600c1d22001c80ca8003e110a00030312081800c40d02d281e1281c010403801d0303a40148070246150580c0312408500000740103501c050f22034002c5400381d514010007600c5000742d0202c01005e336441c10109002000801805203900203138140011000071000643c0b61000c0c2618407410411989400c9425907881c000354400390380310604020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 653523516 1250 653522266 653522273
    0x30606060306080304170316030c02043c0e2d0a05030d0b0402070602160b060f060a0c0c1205030a0f09030803010b090f0301051009110918071701120302011404 70
    0x117036801c841d18040c01d0760a214540110314114030035001101000d00b8004810402c05803c0030031560b80a00a079010032416202c1251400703018001103101040582e05d0441c05581d00340201540480780c2400740c08540c5480c030501d0a40b4120120307051050b40600c03c03084007500d92103051110b123240c00c108001d004280c0c040c2c070392907201d200f00c44140514944459181090740c076990104c071310283c1d104904640d60796281031100007043c40b4041c2111005055804180e062401d95080000f60380006c196a15140000744140d584541041040361010204140081c82107005032004800c00d0241000d5651940a500b000b0520b8440c84031482c140256a1400e00c0400c40c01030583c0e06540c0c5c226441c560300c0c00010300180c103a03210310300000d5056003400c042165038480c0c01130f841c007141c0d440c440510080c285102032a020340103041d50f07a900304440d41e9503400c007085c8071a20180c01007201d04200d42003c102100180b8910000d820118640b8406891501010b80c2441452595030503200c1940e400d007020b41c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 653524766 1250 653523516 653523523
    0x70528031214180c060406121808190309080703020c010801120807030516061a0a1205060f060d0f111518060903150f1b040305060c1602030a0c03060606030608 70
    0x404000c503c6001404200d07950000f00854404001c0040100e515036560300d90040440114100d0141c0c0141060720500c198003140140601496014220301c0c00e10b1a15034450b802c00043d01400d10030103894034180804640e0b014010b0840078000e5001e8480301e031042001500114041e807007140180e03542080308000c28070103000d6801050b071501c0c001c0e96a09040c3c05001c250307840480040e11851030020f04d4110038004066490f40d060054442c11407250303840b100071104c40ca0034500075216400c001e00050541c20001805980088004c6c841c03504645140c94101c888141c101c42110015a4403e6540362850910b1001c82110342200080c0e140442c420700c8075013200011b1500900640c000b2a00c0d840c550f9050040c2100c107411400e1100c00d615003100c2031003603164140c0e084054501205518003525030842e0880702680e40000040040c0e8558003985035090f0b00440c50803041d102c5840035000140c1d41405030700da0450040510060107415402d0280454441d540007400340740c90100204162a80403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 653526016 1250 653524766 653524771
    0xc0304090906390c0215130303030c0201110702061e0f041d060d0605101502070e1006081b0d2c010203010f030b0406060f1e05030303100b070528031214 67
    0xe04c1d04520043c0e0510106082d001c88202c0c1040d142c0c2c0115000d1030134118010040200d0b4081d0350306102d5846103c800381d081b1082c50035011110f900c06c1100c9005800c0041c01849181c103520340d00c4542d421292035020842d0030450511f1611140085c2c00c200303075100c420b1200020308031040380710311604008000840000412800402c041c1d01c2d140001c8030681400d0300c41005010f408003122280d0f0891500944955a60044070301882c5418003080c0404030385010403007602c00584130070f89152101c94400946c2071340804004a030f50310420282601d10114000d0b0b45c806045c0801e80ca140e40840c07036620104505c154503a9031107a10610042204200054195040301d4008804d010643c036070707080010280280350480d0b1070031400218005441104e500225140c43d00c401070600c0600c1e240c008158030f91109403041d8904201c1da202c10711140c200c2c98000d001c51840f42d802c1f288030b59a618000421402c60101c0140760882c031840c0e0358181030b004008102004c410340420013454a40100d40344d501c0801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 653527266 1250 653526016 653526131
    0x121c050d060e1306150512070f08030301030c0e1005040612021806060d09050321010302010801060309030527131a041107030e0307120b0103022d060c0304090906 71
    0x5c445401d600c3d43c0803444400c0c060880506032411580001072480d950b2400352144840b50960380c038001911718404020360703044c2c80c1d2201090314072601d840240795086801922168a00040c40700c005003a903074030b02c1040002e001c0c141c135082818aa070b004010000f0313043c490f50280407000c2d03410040c044d9100b108441000302035000015240a40c0d040007442e6014040c9440c840100e0000c0c00b408076a01c2e201c0b42c41c1200d00c01d0340c0b108107503030703d511007101503480009000740031030824817200840d08411880140440341c481e02102e43c0c402c00c08000741420b01c9030b540203109665901c10705030b543d4110680e5401142000d60b0b00740300c5190485e03681603280c810030704054100002d00d4100307202d42c1c1e003c2c402e0740010f14521004101200341420410740c146020303c01280310b05404404000b4126900f9007040c0e0050040300d40c0d401c2c80400000b8032217254003100c20b4120b90b000822001c90f140200d84250300c210780c01410300044142c41820f5003003c085015800e04c140c601c5000c2d012841643c042415903580380d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 653528516 1250 653527266 653527271
    0x50601030921180e0103050d14160f02060d0b03010c020102040509060405060d0b04030206160e010c02130e010c02010911040e0d11010b06041d0f060d02121c050d060e1306 75
    0x1d4882c4211111180380c000b044101c00c01c050000703000c0d40c1c03800069040c0c030300503001e0350007602e00f00380c013500c020044030f2680d01122020b00410402541d80071aa80c00a80540007002c400a655030005001c0d07800031a81114443d5034030040c0e49181001d00c11001412042d00003149010309040003d1007491005090500c1251640d001901c01d40324481401c032480e0384a41143c0546c2894540a07440c0c01e001c8519201c0010301d003034541101c0344a8100c00c00340103010785a41040b2a40b540a00c8010100703c10055400794580c002c1d681150340c241b02e1000388944550001032002d50500d0000351050042410b680f0482c10102070300403120010030703544025445410f03d01550300d44810480e025091201c0d60321b40c00a4080b40c0058100c0c0c0c2d103044001d0312049000d0908880c0c1d0303420420401000f00391140b40d000b0f9070801c2140e0040c18400c1034840138030101001c032214020312005510b410840c100d040ba00007840420310203040041d60090304090b0052802c10282c51030f18948640b050110030001420054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 653529766 1250 653528516 653528573
    0x3060307170f0d0c05010b060909010b07020d08130509060301051b0d06090906020301090f06080c060f04093801021c0c0b01140f09040b040609022209060506010309 72
    0x40081140300603000002d0140c0351100642c1101800d9010311202c152029400c01500490a1034600221080400000c100302e520743d0038100e03109240d1f0000102242c0211410600300045500300e405070a608a82d0700040100c1400c140600022a90150100307021f60306140500410b15411071401255107481207205e030b101c1a00c101c50a0241074654450b40460f4a040c428500344002034005606031904a10107025035400f420010049500b0f52150050302d8201c050481584e01d4070f14001c103101e80d94003c101d42170603110b018020807984880203204500c1c01061505248542090f0607410341d4070741e042900d00d04180c0a0010f5100c1e03440d81d03614401015003403c4110b1440c0900b0340c041007039800c04203e240f95030b12403c000004108000a1900c14500c201c8010150318065030680e101d43c0c0d018a074450a600d942c1d4510b00981050706e4103e9001c00d900d4000a20702000b5024151103400c10803010441030018100304045503000f408081c10141042005070101d041d41446c61001400b6280c400541c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 653531016 1250 653529766 653529809
    0x1204021302031609060c0b040b0a09240b0d11090705040312021b0301020c1f020405061c0507111f1d030c0d18030f032003030a060b03060307 62
    0x21240004a1003800e4408001c0c8060141e0010b07031562460425140c03051010303100d00c8151080c24129a0003413000900d0f03000580014041450a60441003034030f00400d00944136546c40030120b051140300c4401000e04003c041e068030040c01a07618800040e81c0c0c3e481049090703143c0e0703814200b61001090085c074000f4003142c071051190b81100e004542118500d0400c210f181402500c3d625110f00450a10302500004202c0340b03418401c07079602002140c014405445501c154030480c0c0c10194103280c1c520360070f220008040c2c031510000c0c10b200240340300c11303a00d58200740c0d4140304451000d0001c10401581c01c0711308002000000e8102c80184505230705040c1e43d242d40d10184041c001c0c40c0f901d9075008540c2801da6030502c40000140564041c44000e036030310341c5510b0400710754100341c42c4001d083c1455206410004a9070b2110750041142c060310340202824002101d01c0c008624a074030822440d40700100f006040c1209124080c0078100d10050700385503041c12000a80d44c0c03100350003403004030825500000c0d5003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 653532266 1250 653531016 653531029
    0x91305090c06072303040b090108131a04150603020f010302030a0b120717010209060405120304030b0103030c050d020f0d0f0e03060717010b040501090315230702150903120402 77
    0x1204014440d5607240e1861424000c81c112800309a0745801c40c41000754804c1c04c01205840a442000b00c006007800301450046401c00d40190041e9000c913108024a00450780140c0b101d01c0302210925240014107147c0381c6105100145001842810710300f172414001a0303106007502c0c01440c000d10f409030702d0f0740300d8018010081c1640882c0d1075010b041141803103c41d180200d400c800300d82d01140c6036000c0340c800c24402d9082c3d22800d00d5481d44010100b0080c00075192540398092102071500881e4141520b90740c3c2c00d40b43d400c0c20780099012440b00b5400e401000020071040e040d034552880502004001c1522403940daa500a83c010b040c862186031410f110707841140360015840c8018220351036810001c0c0701501030f008000d4444140d01c0c5110001c510b0080c0c08007102c04907035043e920380c0702d43c82c615140d404c003000b00503490301a0700e500d40410b198a08648502c04000c2c2c2a1a0950851810000d00c041c0c90000c203030341c401200008070340030040761040100558000c5600800303174920580d82e03440082c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 653533516 1250 653532266 653532283
    0x203030a0b0112092603010f05370f0918060b03010e0615181006051b0607030b040b101b0201031805010f0c08161d0310090506010b09130509 62
    0x22075890504480c00b40035882e28420f544a038411140405d820f03084a80a0185c4400d0040d03c1e443c00c0d044d00100046d042030103c0c8c42900032001051214035503181c089a0300183c0580641404c102d551a09001603c85510881d00600e4001c80400c40d1500e00e0b0007181c0a010050344c06405a80d41d0746202034a610300b900240c143c0003980d4203403001c51400002420a500c05050224061001840f0b07030403041584580b01c81c010001880691000d0303140c54400c81e416480508510803c60210b0b05420b00442c1c1001158001d107400d0302d0210b05034106000740400c8458040b603083c420350304501d561600301c0e00000a0480c0410004031008401d00e5400107801400c180e0700030030824203c642a203000d20606501418480010081c103002010501c801145c0e401d030300b0b8170078414a41000c0401e40c8614011000080c00e0f400d8440d00310728201c3d0410008e030600c0300100440e00000e031190740342010400103001581c050130241100b241020544d501240e020802c821045410954030408203000700c008000041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 653534766 1250 653533516 653533547
    0x60f1103040b041d0c0f0318070504050c030604200706020d06081f0e07051c050106030b1006020c0603010602030708030a02090913140c09160903060e01060807150203030a0b01 77
    0x20364895031001800802a80c1d130650040440402000c600b800401c5400c035911a40c41600300c90440c0c9803502c1d554030b461f0501ca0000c1440c0f2460700001441c0d04c480c010306101d00a07440345140c40c2d241420500003601c1128000105d801207048040c88050640c0090b6840349070003840058850026020707910007030110740c0048a9034407540c2107103a200c1c9080d4101400b003803080d407400c0c400c1000142c211a0755154601501341c1c01210310145400c00d0604082d04c00440c4c0c0101c0011904036502c0e22440445030040d0391852402c0303040308040c4500307501000001c2c0d6040068980300c0c6591314100e0003c0d00d0f4020301038020314401001010a00b103800030b40503030302800b00c01441c0c0b809a09102181294005180d1400c44441c20108541d800c00000410311100940010348800c0c410383d5480900f140840800e0186002d0140c079040220109101c3d100304130303d51080e83d00020300103003460401403070401140d2107004802c030110b021701c5071690b020003035942260a410740404d60b5001c00300145c502400516005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 653536016 1250 653534766 653534789
    0x160812070318151d010504090e0a02040f02130f0b030a02031f0914060f0d06050604020d090c0e060d03020a03030c050c030a0c020a050d0c0b0717040f0e10060f110304 73
    0x8100b001c43e07946180c4001140380c496035002c004600307043c0c0b22421403003201e41c041442400100208074268102900484611050b200c18180301c0d0b0024089902c3c902158048075804640081555003500500340500005030180f0451407900303e42004500c4001e090000181d00440402c440c2458a50000c142040c06407001d5100380d1185480d800a10f40c04070401c40d0710b00040080303021802c2140446c2b681207c0640303807040c0340c491600d550016210180550b50000d17420418044040a80e200d0880c20521401161100300d10b007080c4107030060b0001d041300d840744e0142c15074100000d800040c0c2c03c0650364103090215810f480c42d2811750301402083d11920b1240030024192460b0f940c4880031100d024400c940c00076009860768180301e44044240001006040b1158007802100e4000001d8200584203000c940450380f8031009208903500a5408482c5003031100c4400d12060402621481d40089282104081c1c9860a04002c20413140c010051040c01124800c5e02c6c00c0c0d100030b20440e00906881141d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 653537266 1250 653536016 653536019
    0x209280f170105010f080d030b0319230304180504320f0106061b1e0b0108060702010902060421051b0a09090c0515040807090e160812070318 62
    0x41c08402024114100c005510300750001c190411901d00e810309441c2008000c090b202c2e4481c4041c2c0043c414004481c0c0e061040001c510120308000c00c400140038816600c004400c8030841d024040c440c44041b441c03c03035820500c818000307404103c2c140811000e112002091b40d40396418000f459800c0c0591007200c0c10b200c40c0201c0c0c0c4282d10144803000c02505d0400b11521030250100441c2290300c03074003501e40080d1203601204040171200002100ca140185865040155101c01c0c101c01d0b41c1820804a4a68035078400410205030140103003940650349000071302032545154000f036090b1060b80103144110048458051121780500080c0c4112a406004c90780c412b059039480300d11605107100414400c03220040c0100b1510f91130f001c0c1c41e8480c0e0b40219144401c0f4103010410403822070f05a158140c40600380b0000951903810003450004041d0401c0000c3e0a0b01c44d00f071003500304901003401070100301c0c04071010088988006500c0040c1c0480030122621100f46160440d0091400303100494001d100480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 653538516 1250 653537266 653537279
    0xf092403072a030309110a030206221e0e0907060c0b09011e1a010207030213020912101a0103230a140f0601020601060c05030f0706020c01090b0601120209280f 70
    0x1517034140603046940900109030100b040c80515030000a42104041c41215840e100000c03050407540c91080c044000141c071250740703000b010031017200d051104000c050100140e0305d0240f0280d81090b2181e0203442e0a1342400700180114044c410024070158140e400100301c9142035000c014100c0ca601c028001443c41e244041d030182c5100d000c14202d91111414804203503000107000300c101d0398013400b01321150204401e40802508800f0b622504403580c8200b0320302c0d50006002180260b8000003001a07070088030583d44c0003500d40d800c081c81c113052400c0d41d514520040e10b90855503d44c2884c43d942402c0c0d0b0348040c4100a00f040320042c11014000e4400c6c001184150000544106404e03400c1760309681e0b85100490f502c01c3c150034090901c2d01308005003000c002102000b0000789000e10405494190300f103c0150031641959029242d0707401001c00c2c044190ba22200c0e0350788019554030103605182464001070203441c1074140d2040b11940e403416020155001c1001c005c010118480d600400035501e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 653539766 1250 653538516 653538521
    0x90301091a0c1e07020f06030a020721172d16140712090509010305010c02010e010e07090f0605060313030e0d0f030e150f092403072a0303 61
    0x1c2420307100c0c015000a900300400d00c00382d0714840c0c100320354194820074010122105074040d160580c0c124101c044082e46a8907184000d6005240601c1c0040e0380c0d10380c81c1040101e4034039266515038085000003100e0159030f4002a01020345882012803080c0da200c0c4080d0800d0082c200383c035480740c2c40c0440c64594140c2441000d003403160003d45170924100c007901c181140d0101e4802983e8401a41c10312080780451103411318804055914103000f076059840340002a0103000c2640101e88070307911500324000c0942e0a00511900c54030f600001d1090108210000b600d6003084c1c000c541c541940d400000085120300c0d0007040007024050401940c9007007200d610600092115000e4000c45c101010342c10190601802c00d2265075004000c07a82d0500940d5400c80d407a070040d440484e8416002070600da103006043c0000c1410700081550183c6d105201c02c18806500d44030b00300019801d8005000701c618980620031668409820700d45072046000758000403181c04c078500042c4010002e0884010100754066 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 653541016 1250 653539766 653539793
    0x50d0b09160f0501030b030a0c120f02210f060103080a030e030d02302a070204050108010b18190e07031b03020a150207050103050a0e060c0706140c09060f09030109 72
    0x1c0e613003404106e0030b82c410300d565001c0c001c5004012041c07440c4200041690704c1058914a8410140d0001720016500001da51501c05105000f04840d01c0300003800882e01040030b4840501c005000d0b1100c0c7d891501d91080d10b010b50000c00c0103050f261960804c05020030f2049032071040c600401191101840c00c0311560800c420307402200030080890b14441d42160818032a4802c081c0d4192700a250309903103841007140052a00300d140c01840a00c503140050b5542d0085c00c0c041c00b422400045e1000052040146405d80301242d212004800b4040c02110800c502c540c0c2510b91000c0b4010030401040030540b1300e172201a42c4058894100d5400c0300c161040112100c00449000f101c1007480940c941d2150340c1c000380b001e00c2c02005a804800c00300000d502980000340e200c15841d0001501c8000807400d00c0c102102190a5000400b00050345801c0002500c207601c0d04041c0e04940308060b180080002d0744521078034a42903c124008115408140750300c02c100c4642102c003030000e028036562451300480c2d15154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 653542266 1250 653541016 653541019
    0xd2a050f01090b070212090607080d090b04060501050105120f040302070f030605070f110a120909020a0203211b09151c0b040c05041e0f0608070306050307050d0b09160f05 75
    0x3d00c080340040e07100148030700000000d11301c810720303042030f0714100b05483d8459902141c001e4828001c03130640d0310703080c03117036402039801281601d00600e4685411411940140c00150511609105485c1c00088a0748a5980700c000c0d8030703e8012988032810103910b4100d890380400c0007440324850100800000d50030007401018151100400c0990085040e00e050b0b1205009041503844140d094001c1004400c990f00c05240d54101204081d440d520700d001a80d120420b0400541d02c0024814203407051010b110b803003d003040f40e440d44281841e07001c42001e801c148483c001c6201000c5006110f07a40c1e0010042c0e01c1081a032a12550341100e840c0d0300c502c60882081e0b0450b450710307000710500305080034020381c50055449d80d62186420f06099010700512102a00c816418500110110b042a16204140082c003015101d0312100d10305090000c050b20140d03008903000340c000c190100015196081c4008025034081e0b07158120790746640e100b41c50004000309100080080150008045200441c0b01059030700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 653543516 1250 653542266 653542283
    0x607081e0301050d1112010c05040609050f0a121109040c080f070b0307050708220509090d020d05090f040501060807030c0203040e1807150905040c020d2a050f0109 72
    0x8402180d11050100348140c640000340340500200145a20030804040c83d8010700031000000e0707240302139007103602941716003001c5500010280b140c1034011620a000344130407622102840d001c20301164080e020b0344940d0260401c420900380c01c215161041d40116500542298040d107020b00340042e024096204101c458007031040c20480d1400c0224540b010345207810b032154a10b4032003a00c102c0342a401441c2c107441c40340091003081d5030b0340e407007035002c900d00c1e18140000e05100b4140000c02001079800f4200c10040e501000c911500c590300400c1021000500341041030f1074410b803c0110b03405981040d055a44646400000304400c3c0d000380380350307000d00d205035010004c49100840c242c0e07072171145004810403030070302000040741c181c143e4500e41d4107000114151030646943c3c4055016000505030303901c02088450a060040e42810b11801d014404644024260341041c0440944040c40d1040102a0f1009596502e55009500c40154014030791001c01c031130400c10a107140900038480040704469410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 653544766 1250 653543516 653543557
    0x409111b0316020f030c0405010306020909060618011b02180414070f21170309010f0b061b0c030f10060e070504090504030905090a09110915091005060708 68
    0x10039100720300340b44414075a0b09810b540030410420440013100e54588507400d800c114030f03160f078043e0134020f5200d8180541c40e6084441003145186000305200d000741014400c040b45403404417007000044100303080598074810604149056400c8800b0f003c0d4000b04548001c03082404241c900340e01c91401603003803d184820034400c043d02c502861145401300d80c0109404d100f2620542c01012000d840501c2c058002d5881e0760f15001504221101e501403520007004000e4020000e0040517801010000d0030050384500200003803041c091200c140f04c0e000d114400d20060110100681c034050345000307045664080804c40c9081c0d60f42c0040100020072420203400066460307800d04413501540c480d031501070500b800d20140c1c100a100007801a000c1103829400045c0b90f84498000783c0c003c681d4101e000c110902582099111400118032140c095841c02c000c0001e44150325042d20072541d021140d921f0ba50b200e4003e50912191180c02c641e0340031000060b80c20030429140c00902554480e0303110000b00e203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 653546016 1250 653544766 653544817
    0x5100b150403032708240106141308120d1b02060402011101090c031a0f150f010c060f1e0204060c06090615060503190e12030c040911 59
    0x6400030a880c04900301030109000283c0101d005104160107050706485124140b0800c1d80d446126a1240206410110118041402d03000c48041075001103c40380f00c40d940340ca1401013a0309000300c00500803c501150080c2001c110f4171003000101248812211450150161031815a00200641400514281200003100b40901c80d0030948d44103038001e004103580702e0b0010f4070b140c8002d00d0855805e550f988030900c0001c1052080c3c0f4051402140c2a80c00c240d4200208001440d01402e14589161480f00700041020700d05422000341005549151201b030b103090050340d980c0c1c0c0f8124014406801c10640b070000c0b21840d0721195030944c4404410300b100d8440c2c8482c2c070880c82240211000628511030100120f010782c0c10840543c1d2003401e0002e01c0205055849014554982190000580010500c8168485e007000c400c0c40d20180307071042080300441c100095990100a80c138046801c000700000d0400301504058074014200c01c01c0a010460074081d008032700b41d00176288024940d0582d210076000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 653547266 1250 653546016 653546029
    0x60d0b0d320a0215130f03030302070b0f06030714130e0303100e011508060d0212012f032703070c051804110f030322150c02060403060506040605040905100b 69
    0x15241c0250003118130710682e00c003e130103e900c2424859004c25880c080014058400c149690046009540050301d0f80410711b440f40c240ea40c0640768585101c4158240318051360046000000c0b01c5420fa4004040880500880c0d0030600721491205650728000800300411008001103214003029480805203d44840a90034048801c2c044d04005c104141d00310003082d4041c5a8542e044900100702d503d010125174000389112805019240c9103945503031030006000300100543c0558114015550301c501c1c401171010655000052045d03412405c0c001c500003050301415200390040384214181e035614a5142021400592a481103602030500c0c600110000c01c0c81200c0c941c02030340d1050508819444031420401d0104020f158158940000c01c061030411448420040c00001401e00c1d0b004014078080e4a4110355114000307120500c4607040c05000143d42e80f4080300e043d0399200c40f00007100e45235080400cac000c2a00341c05c101d0f0441c2c6462100300a00c00009083e0b0200b24215009014030810202400781 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 653548516 1250 653547266 653547283
    0x708060403052b050c130807120b04020a0801060803030711120d0c0e0a17010f020306011e030e0a0308040b07020715050f09090103061d0606060d0b0d32 67
    0x20401c1c4039012500d81246a0482a58015480362101c900c0800100040304c20641d0168450040000c0102d10800080b000c40010841700c0c0107414058980b4030800e05442241600030501c0d000440000d04540c1c5d80d070034180180107860000c100281d260001c0590340d500642c0d01d00b01103000140301820f40d500c0011082e41a03441c2280c41d0707003024112410440508051b0149009000c10601801902e88496841800400328041503c004140904c4610308650b0302e00303152600a401082000f5150740c0009134002a00d1a80456802c400204c80d0114010b192000200c541c1c0c1c01000c080c4402e06500403401c40c0070b94015100440c09840d503003010303a51120b481c031400d01808112800c2d803211754003031806015080c0e86456050f1a100c0e8000004003d08026007040340c041d0303581c109040c3e2810540300d4848000004d00010f0026050000c009200c0e0301079001461011904e855401800d901c8031321011140c00c4d17005c615801180380d000784044250003800e44034041e003c3d15500036451010000303407004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 653549766 1250 653548516 653548523
    0x613021207092405030a02220f0f0f06050d08031b030103031722020907090506281b120c060507081815013302030304170301051c111305060307080604 66
    0x3c1c1903010303900380411142c819041c521b64034002101e452308102c640c0180c400c400880240080c007800d2401d1442d045890003002d0384100e529004080c0035540f1000146448507811142c0581c80750f50302c110700c901210281d1003040e0000f2001c800002050740282000d65003200b4481307000ba15585a0015010340403424400c0340c1c00c4810040400f0150602c13008490b00020140342645680d6190000710301107a00050000c40781a80b240c542c0e460601900003040e0a081c0d903480d180301c0a0748a81146515031b920700c8000303815540c50070340100300390f4003c46188081650002e0244007614000328040c08010701112064160304c0a9286100040c03004541d98071358144580c511005a401c100c403410f400c1c0c102c0c81b207400061042c0e80c1c2c01040c3e81c140f81c2d00050520000d034020340d581d160503d030009183c00764070241104c8800030300c010f0143da5030382c0d0021a6100291303600003100d8141e900b089180c0030401c0100c19040540321411880d104000c0e040a8441c410a80413141059501e06465a44090464026 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 653551016 1250 653549766 653549773
    0x90e090d030b06130815090606011d0406050a0315050f0c1804140c180109030c0501030e0c1c022404060f020a020a0b0c0618061302120709240503 64
    0xc800900a80c004010444041c20407810003030a08260801c1d0b94094201e0311980c0e02075103500c600003942441241d400b150450240c420b42c1009000680322040c1c183c0c601d41c1e51103040010304919245ca038000b00081c50002c04029a09644c5d0910003002907003102030020260800c8000790b101030229041c24000c0301c0502007030386080700309090444200c82c41d000007544140c80c0c00141c0c000c2825102c1d4180240041850a0b075581c00c1414254060410004542c0c14090b00351810004500003401c04402c81d102070034007040521203c5000c1d801c10b04c0494160790b10080a45010402440c02800c1d4540700d4429070b4000104040b00b100c2c688400d5044245900342181000b003402810311540b41200d24224038011030708480d16035400100320344c0464016039040c1001150b6810021010840b1035003118503820b2213040d09140303000030340d12441c00806071214603981440780d0086482c1c0702804148071704040195035140f51610a040082c004101c0802c0804001410341c0c0034003140d20b20514200c48000703004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 653552266 1250 653551016 653551033
    0x21009030b010b13030b0103060203100f0303020303061302120411010908030f07110a03150507140306091f090e150705040b09100309020306091c0504181a0604080d090e09 75
    0x40760300da40c4c0304030008890341d042e4500002c00600044031060103140314090168a80c5044143c0610341d044079804400381c00c48808080001c243c011048036001481074410080407845101038401a1240c0c0040840000b40e510801091001019a46401042c01d07030301c99103002d58a45055540b40140c4a00322181202048a03034005a03202c14106103220014001001030340e40e03501c41203010240c1c0440c291a07203443e1000c002e241907111810007400c0207880c540c03500f9070070000d000c01d50a0303030020401154807280c41d0802e80c070580c01249105c010301c10080700b8400e549081aa00741c5540401840e1224501714070040f603446402507040c1c0b8143c60030407802a080004c0701c800c201100c0c1400c81c800c0e0506a5800a040168900b400000d219082c9403004195000d140108490303040c001052410420900340010b011001000c1c040d40d400351025180070800310008820f03804541486584550b03c07400015001440340c2001c00c0413003089940b9150802c00350360310420843d40603803c843c0e5082a0b08045e00c13 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 653553516 1250 653552266 653552279
    0x80402010216140f03071d04060b0901060203161b0801141003050a03030f06030803010b07050f0c061b1509060a05010902070f0201051b01051005040e0f0604020105030a0e0118021009030b01 83
    0x601e22080c020003812110101c0d607d0b0f03140f0380361a040305801c1301200160810001846100e00419280c0401034802c810650324048000f5100d00481d5000941030241051042c248003030300c280b04000e00c09024442c204541e440b61001d00a000c1400d201c520445440c0025001103521070590b41140d41180140400d10090f07941100201960791421259a07640c82000c8041540070740514040e202e050030240d0b8500c80e6050451030a614900c5481d1141e10800c03003001c454852009030f88981c03022410a080b0003800002050400582c804014040d200080400c0f02050b0002a103901413034171410100201e0b40c80340d80d81d0050703110f00c640181107400390001c104019441000140f182050301039030010800c004606003030a6403c19141244000e031584d006004900d0b044c403d40c0603000da40c40081030816030020100c2d4482d41d004001a06110b00400058072090044d04a00c02903030030076008000d010340d007442166806402c184264044c00038a40b00b1001d0070302444500b0160b940140802d102a0719250 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 653554766 1250 653553516 653553529
    0x120b030120070602130611010506032e0902030f010518030702031b010c0510200910051b010606170f040b0c0a050f030906011d07050306010e040e0d08040201021614 72
    0x2004a40042c0d080100d81d840000c5c0c8000c0c9005000107645200740c1c07401c03c2488a080d1a0046e04040c031a070030910600349849541e5a50b5045a80394021034002400d611201500074824180041e4040c001d0340c10030404a4410b42c0702c2031003803801185106d10405410b040a989004140b002505175101c0968400551151b03001f003003c4020502d80381c01030b000d19a640a00700705291500c682820b40b9500c400d00ea803039000100c0e844000c100300b041c41c100242c00000400c1080c58400c1d50041c09000034234400c82c03180f43c80860100e0010700000384112039580324014414a04844047d0041c00719202103a0482581c28034240515000603500d04191a40b0101c44000e9100410703c00502c030081045070707600c2403d80003543c4918510300141c911036140c0307650501611030741072072500801402400c00c0360b140d0300101a207030042001c0c81c1c030310031100c02000414010b03c44105500a10b109850180200540c07000c40c1501c61032003a0f003030324900312707040401c480c00c1582c81c001d26215480740a80445c5071309080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 653556016 1250 653554766 653554777
    0x1150206131e0323071e0201030b091003020a090207030f08101703041806082a06070803071808070614070b0f09190804060c02040615120b030120 64
    0x141142240090000d20424011075040c108602040c014000300c91001900b00d641342c150681c5024040c9010032559501c011011010b41d084240c48290001c1c2055902c6a4007030414100c029054840d6420942c10800c0c244925100c100c4c0710b03104481d07010510f0710b014000d0355084c5070703d41ca440b40c156007407040a40301400b0050203100341c1e050301d00d800128040ca16800884103404030024641e2603091101542802c41c1c0406c4042d106402c000c010081c010001070341d054008070407a11490f045501a01c1c11003001ca458060a6010a000c1880001e0019040003140a0340e069180c8081c1d46591044000c0340d803070301d44100c40117034102407c1000795034050010000551002c450503403402510703640d601c840b0203080d200010300c140e0403020010202d40420203a0b004010b0718400e903100d480c4503649d032806481980503004c100700580c0001c3c02192502d4203d60b001e4035032140003d10b42c0348107000c014a001010420800d100341443d8a952003400c0611a000c001d4040b041ca203164010300713844295059100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 653557266 1250 653556016 653556023
    0xf120601020c060a05040603060b030702150c09040606030f0c03060302060a03021804050708220c0627080c0f0d0b0a020702010c0c060512010902090f040e03070602031008060115020613 81
    0x20b81c40d032811180e03214401002c1c044042d45810f62501d05000c0002e00320b500340e0b08410041c0804005110400c0d4000801c02041c00042e14141340355642e0f00b411501c1ca000b0610f045420504200012560303d4040d0005144002030503010000c01c251040200c040c0d8403a88400303508200c04020a0855502c25001008076031090060720f00458200400702c0d00302c0f00b0485075480015801c00900445030861340d00c803440560100402c28100c80d903074440082021191040a046c0f04d0804810f441c100001d540310240395920001998480d0380e50042d050711241c0102106200d842400c00d200b81900e04030007040c06042d0051f0b80401a82d030303655080c034001c1d84402d006034103100c501c09011000601d62801d10002d40702aa42e801d8451807007820755002c80788103070894003096006100001d45900c50a64880d2003480468010034503c158480f0541103102d00b20000d80b0b5240000104036030401411066411500c846003204c500d41e9035080f800641c1c0460100d04da006801c80d00c0841c0c9019290f8a100046901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 653558516 1250 653557266 653557273
    0xe01020109080c03040e010b070804061b050319020d020115030605060a030b0106171e040308040201180b040314010b1e0a050405090109122a051002070f0c0b0f12060102 74
    0x781511071402542020b1a00180ca82c00010180051942c0c6906a80108500d01c8600e0400c421682c3c1d241880c0914003442c8104885216808088050200b00d0518282c101341540e98400c0d008251408520300040c401000d88182c0c47c0441c0300c01c0c41403044010700320341005503480ca03a0540d41d83c00f0207803002602e5194041040d150103c003041d0003121440c0200b500751501114164002c6455040303801c000c200784d2102041d06010400800001106a072107503162031f0a1099584500c0162101c01010351246040070300740c000803c0d00c29034140104207590161044200c0c10103409804c2d400c1e10400702000d5005041e0f12442e030302104010601441c003000042803480029103400104080314400c0312000b086070b46403520441400f224190003000c45009103800440360401040381d4004640326a007500302e5a104140020520105101d07464028030900029555240c1ca03040c1480310503030b0881c003030351035404580000070400a000100c46d000f00c030107000907080440d82030304400719140052030385040d0700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 653559766 1250 653558516 653558531
    0xc0307050a030b03030717041a0936090c0102070807080718230a140f011707050a0e1807081b0d061104140f090c0a170f071b030f0e010201 61
    0x20441f400041006440148154440303251060700102c0700042d1001c1c1c49040020040340d13010b42c48000704501490000100034044e0b0324100400450000c686e442412180400014400000c40c0440e1420092200740d013243d00d280d07115054561521107500c684035103584491b404000004a0714040184030030034010001d030303130400707581d0417013480394640d0424402c860b644080004200880c80b41d90340044007603c0c407680c40d1a08400c01141010107002e00a4501c2c1500d20700051f017001004110003518003d00b208035501d9a6801916000d2010b55a9818100d028850107500b110001840001c03980710310010075003491322154210121401010454014032400c50440200300d841c05940101c11344002e0381a5203134075181c140001d203041c0880c990b1080c0344012111031640d81c0c4030885a0024901d051803035807105054003d40700d081c01c6e1b0054034085c40c1c000c01045507620121088501c00c0146464035460540200350201508034100d40040100c0c030b801c0e405515107407042c4206981c04106000004182 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 653561016 1250 653559766 653559773
    0xc2e021b0d1502040e0105040f200f0f070c06021c08070509121506011211031b040f03030206070f030b0916090918020307050411300a090b0c0307050a030b030307 71
    0x207034041e401c00e8220305048001008642410b12a8032014104508104a880117902b80e9420380400c3d921400d04141022800e0055040700100b11911105001d590555810381c070318201a40ca039183c440c10000d80a400310202c81182c5103420325401300c01030340d1244010b58580e401603030306412481402e80c01c0f4084145407440400308000d84a01c0c0f140b40c02c03065004d46054000140700800c404100c0c2e425032300300100011070719021402d99800141c0e01d01400152103500d5002480c0c0d000da540007410071040340c000082450b03000703e011070103031480750b86521109a00047c1170b0182c0314122541a0001034103000128070060914081e03142560302d103001c0d900f2942d0b0354181b0041d551001d040804006240f042d080c1140390421000f00282016502807203509269201c03440b850060001001f040031141d00e1014030420307880c0c0c010b1503e008022110007241410080e0078000c2800c83d0b82180c404030040d011848002036103095030310442ea1a520b052070310402c9002103000d1700c00d101c280f5402d0321040c02120f000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 653562266 1250 653561016 653561021
    0x40b0105030108120a170702210a050901110f010c18080a0b0c0304030306030b0c0408150115110c18011d090607030b0d0f0803090709051009050601020c2e021b0d15 72
    0x800080e801003c0300d08000840c1d10303007806500c224109c1c0d110100100e0a8258201c03040d1030300204242002002007040c940d80500f0b001c0c01201e4580c00d5440c00d009020340c15000141980c444042841a522203078640c00019a01c0a0081005d4170011000340003030581042203009543c410300c685000302d28580d40f995290010174041d80c0031840d9502c089001d02440f6010801c0340134007828181d0540329949807418030081c18240c49041000c001d0101158041070310100300c8100d820702c01802030048104000f6080c26444c0c0b0a000d0400003440f07840d2541c0000c1c0c181c0903c00d008080060103812a91502c030b206078018070140d840326800c01c2c0e683c46000c022400017515840001c0c05209c48a9903840c0106605041003520f0f04141d001520385414040c0c201920001e0100780c0e5806d20300040c068450b600144e181008449a640d40542072400c0c191510348420303c0702c3c0b000780c030b014040500c2d0380e00710b0016615401000341100c90005a6202d1740c5140c94082011103001e030051240b03082904003c2660800d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 653563516 1250 653562266 653562271
    0x4060f0917041d010f030f03050f0c0c01091502121605071d130b0f1b03101e0b0f03040f081b06060607030c170c1b040b0105030108120a17 61
    0x180d5100102e810811000d02c1c00201580c0e00700007155003c1581040021902031180b8000036103504d04001040d410503000340c08941d03440c192003001355240d6200c040829910440c200c5a10b00040740c45000048110f16030094007100041034018203482094074004041c160814841d01c0d0602c2e803040d24500100f0b400703101510141c00310703000740d080c20301220b2141c2486c14000b42c43c5c1141c240414010401103485100015048846031300e10034030703644603128242c601743d04041422100320000801d20002c20317021010101203d6080c0c86004030001040c04900c0d4884491113103d05d8151704200c4017408100f03020007954010300c260071206600c0c0d500e8540c5401070300003420310305403142408082d14042000b00203150307006170b085400a1800c0c409590040614924020003444c410700010426505807000c0142c0f41e20303100031411160013014010b00480e55100092145015500d01001074806521034011281a100b06100400721414251179002040d44410f01900070040d0105000d9aa608100e08050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 653564766 1250 653563516 653563553
    0x5040f08060a0b03060603100b0117070e040f05100909020a1e031b0b1206010c02120a15060819050307021302030a0c0201090b1b04030803070305070f031404060f09 72
    0x414a0300030718040c00c80f1081d200c8548a035202c40200015954001040300c00720701d0244001c100415120010b83d000c40ba1000d03840a40d660070002c105944e54023582940071200c0c00c803806d00100041c081d002b01121070640b283c810303080c4040c10510024030ba07500300060051024100350346007a03640804482d00300c076058102c0100d40c00141c040052042c0303240181c0e01074103181840209249402c0624440344121002d843c90b500d035078030028a050380503441b00c000c0e454015040980f0064400708507600c0d0142303804121514100031444c42900c0e80b06104140c00d41d2511002040f1000d00c01403000c0505c0d10b006821201c0c0c0c03004100303500058403100503905c400309080c0d6000d41c90707087c03000110040d582204105401c42e85020b00103401719040288550700206414035039441224407003d0014240f04541001e030542c80c0000074480302d00d50641c4038510a031801c0d0740d518450145000d089080c0c41081c2000107805541501040109040b42e00101122561120005504403140d680150595400c0e0f12403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 653566016 1250 653564766 653564773
    0x12271401020d0615080c03010302010e03010209100206090d1b021909090602070204050f10170a140304060f0f051c0e0a03020d0306120b0109020306010509030615011403040510090305040f08 83
    0x1001314650a8000d11100c811138100845d151030019090022408140f1000c0c0c104400401d001100741c80a50440e00c0c01500031b0301c0d00120903000c540207540c6a8090782d9180f81440b88078070199040e84242c00d01080b4280c2d04000b1001502e0070340070480081c480d04620064a9410300000441035158819402c0c0680300c0d40015880f01000d004003c22a400106181083c85482c01040148078103840b204d400e0356a5014442e288500206105180042500c001440d105c114403499240e100004050030440b5000d6603820442928174004444995104840724040743c014807030f004080c110380c40450010f00562070300080c80000b4000e501c0c90001c04803800d40150300001c0100511a070b050040101500003011402160034560750341100c4010705101d040030040c0d010010605681c840c6c3c00320b54008070000c0488480d424003041c080ba41e545035405c1980810305e101c5d603030706085200c80d00b5a44140d4105010b007041d41007940d0b064010b800c1c1e2110403010070000304400b0031b041c01c10302e0a4501070b00804004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 653567266 1250 653566016 653566019
    0x30406230114090a0b1c030504050a1206051b030f1b0406080a1505100c05010b091f060f050301030f030905040203190b1f21140712271401020d06 64
    0x510004840140100d034184d81401103510b0a500c8140d01c0030054203451184601c01c1e40e560a0440d50303801550440c550003d51582c00080004030825100f003100d0103404100300940f1140140d501e04820038406035840d240a00003d180c44841001969100104081e07401c0d12001c0161b10768041d41c010342014010450070403e200055520b8450240c41d000e10b038009100071401c02001454000c0d40403001d008101400000d0745c03c214080d04500142c1c0342c00b403c00403c07400c00c008109004010b1840605420040002c0026036502c9420f0800340d8140700d4031918a50790071511910b80014182c8010b4041c070071084000038003178650740f0040d03208901c030891142650402d1580d45060382c0032960311610541030541da0440c0402d09103442520280705040460040d082d0132141e4054014050800580d50700e4070481c50103060004078100e03c6900240d488119911407407910100700d078a100c014010764010010300080b00c9800b0b030034820f0340d94000e03180c403807e02c0504009142a603020340c0d05420544c0e01c8040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 653568516 1250 653567266 653567269
    0x90301050a270302072303010624020a0b0103060504020d0506040804051215070302031909050a0204240902090607021e03060702060906060415150306031707020105030406230114 78
    0x8110b40e150101402c100d0800003514000e60380e01090140100050072805141c20040c11050204101040580240300c0b41b0b5a9a2407105031b00e007051070300542e18011401c01084644003081441480d42e0044001006900b5a20303003000400c40100100d030000748803525040410380070800d8a20a03842003041c1640d460914050003100d00c110308941a49502400510120101d010f064640c401000d140c010b84950344d00c4425810001c11441544d42c0500d01904001031003004a1050b0200b8001c6d541808104022041e02c150b04101d1560300d030001c1414202482280581e40003009681d0300101007a00f031a0b081d070002030341d42410034201004110b01c1c40404000c0e08083c04205c2e0311164a001402182c0b0f8036003941a210074000300b210744600e83e103400c1c814409c0a002d407100301501c8400e5003a10001072664000e00181111b020503540c01c1c0d244807030192980390a1084800746ca80c180d443c1400e40d1220380c0d41a01401c51001c0c1c445040b1540c001449400b45c4a030080390082a0151461070f0b00c809980 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 653569766 1250 653568516 653568551
    0x10216050c030309060d090c0b0d09201c0c09020408150a02070203032209020c060912040f0b0702040902190e0c090907080402150a121d061803090301050a 68
    0x14a8680030b0f40051000c5400340d56404142c0715550800807001c61121154604a0018502c80c0c2081a00e000040f440c03042c824415489941690300c07a505400303507518003000d2211007521045030945e0100c001c8a482d0040540412000c10700792248115030f6203551216410016a013068114404941c480080340054001002d02d658200801100c114940581a00030239120320402c1286081c808440c403480300c1d08604001003030001c00042400310745441000809607102da00c29501c00d40c0c0c038403c0000e510210325043c4103c908440c448100000414a00304086100f900100c000340e1740941d03641d802030003680340c4000c0c4020f11b13010310348400c0965080142030000000c010345100030301c0c2803d1003030194640321010810303001005410840c00c0d80e0b03142d1000881401800a0a2912080104004840a030820580907650104900502c0301000e0040c0d180a60230100d240c038103040c0d000402045d8003120300224008460703495802e40349007010000200e0b09682098a00e03a022135900c410b00000c044611 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 653571016 1250 653569766 653569783
    0x2060103020f2707171b2a030f0306011d01022e09082104050309010c050109050f010e120708040e1801090b0613020304150506010c0606032907020304230301021605 72
    0x84080e51040c0e8025210051180141f030f01280806008980d02a200c90010070038031104001c503002c40c0e5442001486011f515002075a8283c04600f004040c2d00340300d003a00c19400c01e0200180d0052400b0022042c0c804044101e654140411131003003c5ea4400419180c09400b00b4680501c0d45613641c1c1c03084000c0c2c0100360500400e804c00b1201a0380902c40041c00200451788400802d20b000d403c01d620600f0100e00410402800415030310510065254041c0190808400b40e0850002e41c2c0d1980c040c50303844a1140f0030181c00802c0e00c00200002c1c021a01349588458000352540002c15450300341c12012800c40360241c0096640481e000200859440c041455a1032046688419400e5040540e40d43c201e60790306e2502c0c08411b0340c489d0001019039119207021000075411401c01e001d01940d038142013140c40c3e00540c1310b6140701d03d89942c03120501403000b440390003146241e00640c5043d2602d08424a540302107140140c03034070803086001140350703000d0010b419100c420004011203180149802071400d550f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 653572266 1250 653571016 653571031
    0x108060f070e0405071205100905010603020f090d0809090406020c06100302221808090f030109020d0b100f081e0607020703060b0d061b0e0102060103020f270717 71
    0x1854200103015a020204003202030b4251030100c1c5903142d070f030406d035180e1819074400300381d1514200801c485030098101500450307070107800400080e40c80300b6049003a4800c4001280c100c0ca01000100c449041c00034008807000e00a10041d030a142d10100019401c41e0b056a0a444041c1c000c00ca80d000400c2c18003040e07030030186c03024440d01c6041c17440d400700741110403403c404c100f07185030038900d0190030695800c25000a0654490004001c403036190014440c1c0006e401d4a0184000c2c0c08460154101403085107a1507800230320340e802903030039039565400fa1500103180841d40034100c070002400e841c550420401400e82031029003400d03004550121ba0160a0810741c03403203580150240100c40307401240100641e83c0011000c0b0b003006030303d40820f0b49611005001400e0618060038003090b41e03404c80503000321002c0c95841c48244200c4400480ea02d840030f001c085e500c461030280d91001d62a000085202c940003822020684c01c2030403004210500d02202c1d40c1002c82c03454100c0d24013031044113101d00e070f0182c0d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 653573516 1250 653572266 653572291
    0x430020705101e0c120f03110405060304080a020c06210604052206060509010609061202090a14180903090a210f05070816090b040c020d0302090109031a010806 70
    0x2040d070401440c0b0f005a40f00400d0310790700d0340d4030046618031a12001c100c0da5001148030084041d800743c0105050045d02c8660002440d004180b07601c036103400704071030848a005102506545503511121140d81c001b1480d41e0951245101e00031040c2c41e604080c11103d2183e6021008409140d2403940e6540c00c014500e0380300311300d090200907000c1000080e5400c2c90743c401039620050032071468080d001340300c03030b401040d070180c069400002e903150b128500e9400d40b0110b07510392410300030b156580c0003a40507181c0c80680c0582c800c2000d10800620003030703001103800c00a00100c0b4401c0700e589191071010094a07005d0980c0c00015000200d0f0802084031001000601449540300150002c040d9103a104240002c249802e8511540103000e410000c81025050b048152002e2000c90340e40c10541c0c4c0e41c0c1d48500c034000303424038664070f10303a2800c2d1040c0d0140d0010b0b50060800c003444408114020f500c940003c50601880c980040301103144011070b1004c2c2c00c2c80d401040255410484040d01e01000180f01003071700038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 653574766 1250 653573516 653573539
    0x1140409290904051b0a09110307030e03040f0b0f0d09110306060f0315060402190309110a050303070201181701050906090a1a0702010b1e040c03020301060c02090430020705 76
    0x10344c00602e160407120044040c00000200000040300140a6070200c101d00e418000c00c4200401c9001c01103008840d1900e08000e541c00c5200140d03128081c503c00c80d807060f01d40c058108150038280005000725a034040d240791800c0484100c102c103d5800000c140d0307010040342d402e814141010061246c0010f42203800d20318403030201300040d5071000407170f80120141d80404041999a180d6405480d02d16201a004100c0030040d41001030003000c40601c01e441292008810700040d0070328444ca0707029542c000e00a145003000c03d40054842c64010804500b684c102c01c1000180041e581e400c0c1c81656841100109440c14040c3d07640b0700c1d201f4003070301002054102504a00020350b04481082c483c0c40d07034501d201300c640c0c3d440c002640102282c40741706400c01200110000300c1d0440001c004030800c800c89042102c046d900c202281240002d005900200301c604120b00702618100c00550760161244d0540300c840729125540c44031030405021b0540c01c0c0346801448041c1650180700600c0589001d880303c10058 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 653576016 1250 653574766 653574773
    0x3060207150e10090204090c06111203040308070c030918090212010b010903021908071202190501090512011e0506090109020711011215030b3301140409290904 70
    0x401500301e10a0440d9071313407043c5800f1034441740c0000104a40180c440748030f495071041c000d0107a980181c402d90090148450240ca2841c1880c141e030700a54040d95119401da80706101561400a42d90044e000e01031001c02c005510140d04545a070821401b0001048441c0760340306010b00c050807480c0342c80c0b41d64105401b4085a0741e03c1291fa4044075012a48550b2016001c07a560180f4805a00455018081d80c00b01007060b41a0007102204507200b42c41580e5400f10f800c0b54030b00d411500d0700505000074100703a000c0000d8904071000400038862140006042c03c040d400808125071040b002e68001521a030030400c0718a08036141c54014a079004003507180642655403492600240216135042c041859007a94664515030b12422402911580c1400c0107a100d050622001d007040380c1e0700d003024080c3c0c54899105c80e245130200702110166a0102c000e0701c003250041d1840b062120100d400b01209210014040005000b42c0040d103803c0803c0042c88801080314010780c401038554a030213500a10140300c0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 653577266 1250 653576016 653576023
    0x1707061403060d081b030406120903090b0c030d02270909120315040e0c130603020d02060708090619090e15041a04020a030b09090f0a0b06040603080403060207150e 72
    0x30007401c4850340f4608031140b400d45a1801151101d0170680c0c00804078000d020700001c0100241e8060380c58600a088584001c0c0068824140c40180002c0006c141041408800805464070942c0d01d001d407030400e031240001004903000309c400c009440c094071804550101c007401c0d6180b4440d4041d03d0702c403a50700e003402e0b900b83d50344c0f40314502c0b4030b14150000c0020320b400c100b814800d5840b10001c1091069410324105c00750380307003911b40b10307107105082e02809004100c060707201e10800c41f940a403d411040d1150780810840da0400705098070507203010030080e02c0a0307840000034141c0048c0380c400c400242e0030440c0b0003000c140454020031200d00043c014401000c4140703518541c211411030300802d22841501c00107500c1e5607681400c1d0b40190001c10100e5109070035410103451900140d13280e080513680d000300703980c2d1a807024420f400590040403101d00410000c000c1c00360b00c804084d102246075585c9548210070b90340070368803d54009a01140f48800c028014021402242818009002030200310040710344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 653578516 1250 653577266 653577271
    0x20c0a0503030a0504140604380c250e090607020f010b1e03100632060f03070932190b07030219260f0304030e0d050105011707061403 59
    0x10002101603850b46c90b0b502d00046070003910004d144c0703645040342a00354040960341da003003001100300c0650465500c50b56013000d881a0301e00080003404103030010000182201072108a207003505020043c08542c203850f030401e0320b01490b000c3c00140701c40d107000708000342049100d100d801141d9051207040a429a11580c03007001101d070048040310084d01500000b864840d00841d800c1956081102c0003c00704c0c0300c1c01030790700030300011a65550007101c482244403d01440c014500d5018000f0b00141c05119111400346500010034288030118580303507155110f1a2140040c03042820b44008070080801400300e0044074807070400e90340100300c1031a108404c40d4102243c02060841e072000314192060501c20010354101003050074a045258080b030070030101c0c0d00303100008000035070f4a0342e030400d04015210089484460742108418190741b80c1e40d400321030050746408540c0d0321115211112000c58003c1c81000d0091411040b072010407001172800c141058a40d40c03040e070900080d8a41000b0160b150811240e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 653579766 1250 653578516 653578529
    0x3010302150f070501150510230c0708030c010b01030b030c090403230708120609130204090c05061603110c03061603091208060a050d020f010e040219020c0a0503030a0504 75
    0x341c80703503030292060b40c542c040c002002e000c9600b0030102c0e582411200c034880b0262a0b042d1049802c0316540031040d00d00300100e41c00e80f0181d0b04030918120795840b1078005001c80d801c21000b41c070400c50b40c4904241c51600000020300c4140d42d01d081c02e00066805100348200c108007a030280500000001c00a2250040180080c1c00e01aa1f2101400098110000e01450514008886032030b08924100f038100754000c9140c2240750451000480c1041c03500119803441740628401500c42034040742d091001a092403102140e091810000129030b40c0e80d0800034100100803043d4034241c452607401c0044c80300103115000c480540002d42914902d0710302146203540104c00c18090b03c986101100210010460100e024011840108904014a5000c40d1107400744008640070154140c403082008075400090724001e52150018540000325401200450b01c1130600600050400c210044840012110f030400300c80141c0104803d003c5900d0050080d001402d03054000f5410306880032000b800e02c1c4078501464 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 653581016 1250 653579766 653579809
    0x120314090616020f0d0c1208010b030a091703010e060a0e01051c140303070f03060b09010f0c1a0108150901090b010621060f06080612061f05090411030d0503010302 72
    0xb8141140200403644041042004580d0001681c2000528072030b407010089444480c480d403088040c91103005218180d44000a00f20301e59200e4801c8034004201d20704048a240d045480000d2000c2e100c03001541c02090200701035040c5140c16010032000c070f00340c0d800041028410328014090751315000500c02000c0010004114440070a0034a11800061500b10201d81d100020400102e01c0d0320280540a82d10745803001e0202c980ca43c002070050340660010540000c0040100c0411140700d021404440e5000d554020107807242c1a0300001d9159098000c1c8203154060302c01001704000152450383d00056071002040810802c1d0748440303280506129803020482d0b42580030845902481e1b00700010f10030030b20204491551450424030030003003440b500c1d000ca1651000034805041400301d800c2003800c580094a01555030700d0508403c04600030300c1800b03200c20743c04d0204882d1100224640110b00a56131196081c042030b003058600f950a5134a002002420300040005032504800d11043d003c0b400c00b00d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 653582266 1250 653581016 653581051
    0x6021219111b010b0303041212020f0607030c0e1504080d021b06070519050624030601060503280533130f1515050408060a05060103090206071203140906 67
    0x100d83c0500a0283c1c05641400002030000b4102103c10403c0c03d1903100342c100070242c841a0308282e1701c6183c02c290f1032155810240005a03194403171743c480301255040c0d0904100c0c94040c080441c11079005068168030381440000c007880307098020040d18029440b944000c00d10101d00f264074600081e4082200c078044c80c4003007111000c10005104c080e2611082003001b400040c10b0b402c00c03030b58800082d5603e14415201100202a6403140d0350202c6107490046c00416059113002d00413111648000c201c203001007410f104248042c1000180c001c506642d1070070214041c108a401141c03640c0d584d17000e03904c40d544888001070705252510001c000640045540d40c0b8440c04d40368542c0b018211070428030200c01d14188400b01000c0c03490252201f075410010100c5210120410140d170240300c0d50081c00050303407210740056014146508419840380d410303d00814101c690758041413181e00000c008403114031014414138103096140c030622a100c2804030786698079090080410380c40380700140c0310203204224200c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 653583516 1250 653582266 653582317
    0x807090b090d14010e06070903060f020405060306010e0319030c201302180607050607031406030a1106070203071503051b090910210b060904031403090a0602121911 72
    0x48030b0700c0302d10b0345c200b511304910708203500920700c0d00039000c00c440542c504006507040d0b0045100b500c2c1540c001400151560f22281c00641c0c0500060b14a00d60610402010600d482d00c030006603248144030703440d680400040ea02c0c000148450b03e120f0b20140402048041086a444014405001c1811300005035141c0340707000c0300c900b1064241e099941001c0300040307820401100061282c89012aa9030400054800d1300c4c100d607010ba82680d200350b0544c44035820398003140300721100e008540780080ca81031814a055020030308000c040c0d070150301c400c007007070b113800b52420703014020306510110b41c000842040401c1016105240a4803610314052420003000800350107160803108050000c800445031100b41c071075604202c145280d0021240709100381c02040f02400c0c40c2d00d00703901031640b5450314624006042403400060708014005041c0d0302ca04a454008106248000c00e40d4100c0b00d602c40745c082c0340500c20410584d00b42c00b01403400d946090709032850341c0103c0041c0d8902242084641039807226800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 653584766 1250 653583516 653583521
    0x120c030b070e0603150102011404031413090f02070b0108030a08010b030711340f06050f131409090a030212090604030506011d090a0f0303090317070807090b090d1401 73
    0x8044903000b43d40002880441480030455085491003603001740080c400302001004203240c2a034004001c6465508131481c22070b0a14068648a95011121000c21f0b607116182410385074844001506a079001039000d00f031040c003141840c05011004020742c130700245528010515141403003803409038072001c00404c2c140c500c244c26001e40c070481c5400b100e45142410544c000180c0060400707107601c2800300c6203d40c00b029611542c000702c17030466003170341c00341b81c0340a009036400e80c0310503e5418100f100700181d420014101c1500d10151074107c9941d0505a0060140044188003038a9120b082e0300420881001030741c0003415141010b0940c4510b42c03601c2107400440c01078061500001e0450107428000700b41540100240c0e0040e8004000c60b02c03154540c1002d258542812000c007074408003225007a28003207402a0060101d242c46480c0009009940249803900c8440130748416000881d580103001501c2e40c022000e001600003561000d1a01d40d019002882d6102020380c02005c4100aa821807500c21083d07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 653586016 1250 653584766 653584787
    0x100e07080a18060507082a0304020103180506010302010e09131b05040c2c0915150703081501032c030c0708030c0d020120090a0302060a03090606120c030b07 69
    0x207000310304032100189020005010200d9000380020851790000c3c454201044502a0911141c061403584844154003072682d584014803d2f4113041d11502801c0311041104a4030158a010f0000707032506504501c00141860608108103101742100380a214407a00c4d00c0030406500c1b0b5110301594a80030503200a4501028254051507201e0324008221005641248a00ba4802c030070908041d803900300303c1c4540d001108083c0800350429002c1c00042c40d0080308060389044520001c1000c02c00206010590700e06500c241b808030b0000700841d060021aa4200a014942030000d0900f800440d0055603031070f02c2c0e0a0790580078411145059003c103611079040c0115004240c6050a03181a00d4860790815907a038410080d001d103510a40740d5070301041e8410b00c0b503070b02096400e140708500c180351042070361031642102450742e40c0180d44500010050792140000c00c0d203688162404180344001d800c0803001c54445070300400682440101000009142428000a5035440100040c603a10b44220465481c05503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 653587266 1250 653586016 653586041
    0x70f060309150f1b0201090b1b041806210b0f010e1302060c010c0f180b030a0c05092808010905030301030305030403090305012c030a020a030e0111060f0906100e07080a 74
    0x3900a49001c0d507a047d005141d40d1405150800015101c86446100203c0c444035a5800103405000a0283e20140c04c885407408440030000300f51683c40351030080003000103518603d12941d03500380000400500c201440e0b4400341c031090308411907142c24124007420324004c00300d91002660046c510115a05e5006482910107404020030031071041c080040d102030702012940780440e00b040c0031102050381e031000880c00e6854983c07840782113481c1d002e003190103044c198034054203005003809900155218420114040c102c4810064801e401c03100000408042c141c00405242c1d04220303a44010640000440307044990510740a642c942d80ca04088806206a400c010665420140b2035002000c403c4046c2ca01d410308120900c004500401c20b1a42e6413241c0104c0c0d00141e000800400046030040c82e40c0051482e060500c401d020000c940703003500340403044400100e5444d0f18414040c4640c0104401640000041061000c036800c102e80980d90310f2005040c0307010021200c1c0041d40702c1803980c0000d03114045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 653588516 1250 653587266 653587301
    0x617091f022506060b0304051b010e062d0c060402190503030c010b1009050915060d06180608010204050a0e0c040911070209070f0c06050a1d070f060309150f 69
    0x1e03400421400402030348802c0c2d4140b070500d600410300400e05d00031240103d51100080c81480e10300700d0300da111140d1180c641380c1407080c844056030303060711000000c01a5030284450418614050590010030040d41c051a180007907050017030810200c00040d0903504540c0403220300d02e80800100d84000a40a1a04981d4150001080703982c603661054000995200d81200c1d821411218180210380314400c3e4468240c0c41041940480d1240703000d1000040b5959001d40202d15040c44d038a0000255030f655408040c10060040a4004c00715407841200003400540c4020751078585803000190401070140500300c8551120740c0426400792809007110000c01c03009178103200e0145104035408031a000f0000990190104400203031516100e485900c3d000d000c42d403200650085540c44240c01490000c1c040200c1c5503070b452000d8100304000010594400b0840018016036042c001c14200f003c0055010105260808003510b000500381e8560041c5102d0306180040c06410150002010b000320007046000c0341c0703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 653589766 1250 653588516 653588557
    0x3020c160e01031703060d060f09060c02070608010f351c030e0604050717030d06030c06020f070513090206130b0c1e0d050c150a060617091f02 63
    0x11030700c01d00303604807409a034040071030716410280300030745100031902140c1c4035000038a2600000d03070300d510152006110380e0300040c3c00d85650391610b04440c0758510f80e10242c2d012800c1042100d074001c42c444d000d040f07125942c079210792820460420383c50044101e0341b071035070b0651800ca0407010345100800466460908548060104103032064601d0800654600041e0804c0e920445001c000115035004582c860014003101c3d1a00021444c0e02c1c0e002c2441841d6401700b00440c1c00b00c071200740a00c00255018514010324a86000006442e10079500c2070f0a4664010b0002005583d5654541807100640d000d004151641c00e40f001800324403e00c0d03100c40590031a110003280403828007010f80703502505801220600540300840940c0d0303c4840e8404070b000d5010300d540c4119684200f002c1c002411680341100d401d450b0042d2844501601241c0d03581e07810b41d450f2401c0200940c08818000c148460010960041c205010743c162582030f260401c1010511310000e5007e00311084cde0469a200f002d182a640006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 653591016 1250 653589766 653589779
    0x302161d010b09030703020f010302120a050f162321061002030c071806080f15071e03050718060306090c02061314030d050a05070f1404030303020c16 66
    0x280c000e804000080805040042141c0380400b040740c490700c030020020016540745500700f1000d0484a05070504041d006d00c601c5103846a030f405003034000c0400300c0022800c3d01d0042c180c840551001070071100d151003481c2180c000e6940040c103412850b00415020300307403070300c00c1103080d0140e109002015070004ca01072452460042da443d481c901511044941925141c004001243d50303008801c04200141c0003610104080078001c0f185014007210481d0201d155651038a11a0500200280300c00441e04040c981100d03900382c00c4035990f40b080c0d1604022030203030b10801d00744095120300641141811751b280e01198a0038005e100112030481074200d03d020641d10350000401401a5100703441c1c0050802d40c480b0303807550010071164841c013035120203022403200c03035110381014003c80190301550740000c2008005070215130007800d114449140d4042014200044003d01050b1030351078803003c210101d8420198456104102c400726905490090788600110618504001d001c06110900d56101c910000d544c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 653592266 1250 653591016 653591039
    0x1b1e1c0905151b031905010803030a05060a0308030703090501090203010c050901021b010f051803030304140c0102010504050c0613050603040606080706052a030d060e0a0b0301020c03030a0504030216 87
    0x6031446101070350120160714004941140003a1084002c54a0218151400d0030b000d001640d8020031088815482c0c400a080120480d84280c000e07a4458000108220400c000da0040680201e01529800740440c61500c0c3d00c1c906000180050b8105030700c4440c04c00c01e1007800d410004501c0d400400070000510b000c0000350079a4000e041035070243c040c040040780a56010080c2000d00306042e16864a2030b4081081102c5c25401a0254400403403640c54503103c0b03407000c0000d5071203503111b991050480403455282904d4030140030002811603040c14200400204081140078482400f50703119612500c505040c4001440103400454118074040100403d001c0290801c0080301e0500c81502c09554907010200c4151044809c00020801d413000c0e040d603aa0250390310130b49448040403d1780d080c0000d52602100741c42d215444480410b64000601400030064402c0b404c0c1c014040340214544070b20300240c1504c0f400024421110b0541e51000181494020b000040c50003020b031034a070840545500c80000ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 653593516 1250 653592266 653592281
    0x40501030b0616030f020f0105340e09060321031e1005060703030e011d0c030114040b0606120903041a1218011803020c04051b1e1c 58
    0x641000703401406400d04004035800e4082c1112001c52801658400740c40c00e070028080b600c214410b101c10700c00b100c6000c1c8503d500901012030803241050750341809600803082100e28041c0a005229010b00c40c3d80c0044e00001c0d200c00a03034a0a0956999a00003400d08220342c0030784078000e201c0e451049101c1101402144145d03840e0b20344c040c000c060902584001001104d20306502d101079501880320345000009050000e12030319000c250382000701011401c0d2403800f0840c080e8082c1c07030f6a6a030301c0d00905005440100c142600200811940ca04158004100c007800c040c0200302071101190440c1c850004458545158100c015141d00b450b0a1203a5207034410720a808040c12401c0d107a42c411002c140c2150b01600c1004000c0c203d40d11390a0034040700d00b0400102c50082d658440c00034030741003501c0500000e100e001e5006001700101000510055580003000528583c0e001c1c0314200d02244001c080d1200e502814207561041082d0070040c82107807088050100419005c09112542c160864001c0070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 653594766 1250 653593516 653593519
    0x90315010905130206030a0b060421030311030c0f090a050a060c0506010f3002031e06060303030412050d0609050a02190e0a060c02190305060603210421060c03020405 73
    0x3002e5500d446607402060403150b402540f0907001c00100760300101c41d03042240328402c0100f1462800c0d070b440c05001d05500b506c460400114264620f4041416014030070741c08000c0d90003c0d07803480c614100721481054030988040c0e084900020a02c0320f000d45400700c90102804000e01000c04140e02c440c2d002d40500030540d030844892180000206030a07180c802c00300c0480300310492541c0c852010410548207014140f00640303810084030b16507005a601040000090b460b40c03070800b0880c034140b80e00349040c01001400310b40254001c005100014580c0c13a503240c0d2005803803030002d894140340d00f90304015100b15445021041e04260500080c00b40960003006860301001c80401010ba0350407007550b440030344170f10301ca80c00f61055004108241c051584060481e01c01482c48407900b942e04035403e6103464170b8100792501d41c00710f01045001d00b0108680601e500580260802a800c600c0312070005225034064032200507958131002003034840c19102c4120a641c8010248616400410010003e40180c860315 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 653596016 1250 653594766 653594771
    0x210b0c04170a0302060a0b0d0b070f1803020f04020c1006060215060d020a0504051b0d0c020d050f03071d0303180406050406030c0504051f030302060115030501080d030903050903150109 81
    0x225008807000415203aa268140c000d411181ea454034600000c02e140101203030080348808081000030b00105520b0302c0383da2140c446440701d6040002c008c10014502c9503010f19200500000e00140c0e40c0c80d80c181346c080c00c048802603942c08101140c03d081c01140f911a0840b00d003010004502190003050381038101028224140b510307a40c001c1004444a00c00e00069001800c10f02c080c0424140781e007049a000a107200c84040e082240501082d8a510010700341c2d11050b0359180b40380b115030b810320900910b2020f0389086424807800718205400b034400078004000780030406140000312201c1048a501080c2c00601380c98a0f00c00d44420414444080806284140d1403d880800c55240074441d20f0b0550fa0800302035139003e4109018030006010141a070705910311a8943c41190524022104000d58481d60250105501d490300044580e8402c104940c289401c00b401131203400c1c800030f00c000e100f5100c1e1034085290b1216050030395562082c80c46a903018094429103201807442c01a09a0490b007031500e04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 653597122 1106 653596016 653596049
    0x150f040b030f03040902090f123417010b01050310140607020a0f0305060c2701120213050a08120a051308070e0403021c0207210b0c04 59
    0x110340c451300000c03003800e1070401c4407188c401201c044d10742c2104548a030300c0c460340310000962050103408c50300351401c1c8a20b00301c1c0001000c910804144070040c03034403280a100407540c0c03440710072031b0766080c002e0541c000d51043d408c4a20a841c1001d44451150402c0d07144806080001600c6600c08001c1c00400b0160780c40980440040807046c1d00c0740c20482c91442e01c1070503c20300404581c0c1200d406d00194510000a10004076201002513080800c42c08100c010b0303a01400f450b03c001e20013880070a5100080e40f200d12030906071001103e4400071140c1c0c40d041c0380d98171019807081084e910f2051010142d203a0041010301440740e16070324003030641a150440c1d9443c1140e141d00c9062513007038210134401895018030011407207080c002d003a034000404810700039503030f1801c603c42e0702c8544128490007500900c80d42810320326036a02502c8100f131802c15040310360b210782083c001d16000c1c0c00e00d83d08 = true := by decide +kernel

theorem cover : BRFrame.Cov 653417266 653597122 := by
  have h0 := BRFrame.cov_init 653417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 653417266 ≤ n) (h2 : n < 653597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
