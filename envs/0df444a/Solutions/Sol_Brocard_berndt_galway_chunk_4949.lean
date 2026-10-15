-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4949
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:15:10.148322+00:00
-- url     : https://prove2.me/submissions/4dc617ef-f676-44c9-95bf-cb49cafafb39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 889928057 ≤ n < 890107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 889929307 1250 889928057 889928063
    0x609020a0804110a030501051603141b0a171609050d031710031202060f07090608152409040f0605092e120312020c0304050f030102090301090f03110118 67
    0x3d0480440403560342c5441400c02160701000074095440c1c04510704048001c1002003030040b0f030500003506104580c1d82c0c841441849070781d00c19000d401ca401c020350380a803c41140c5100340540f2580a01208040f0440302e40710b039820028041030340c020130300c00400c00742540d40600e0003200c4041d107032030002ea084200c09030344ac5900c840481e0580d032a011044120f01c2c080d4070140924400c06015002a0b901245103840351f140c14000940940721000c04031003152286c4a494001200d18003c41c540e06000b0320f01c1c0c000b4034130080000d00581c080c002801d8170030240d44503403166103000081c1c3d628a810140100074034801504003c210603440d04002c10b5080b24010310000c0c80d4400000b1a840c9903d81c4007680a51106404160744200c0e21520301e4082880b200000340c0225500f040107030451803c038001c0304c0c0c11b4420074000c1c0d810079160106006420340e10040c0c0790380c5075400b800444181d07107007403260446043c01418a4080461a803c02520101c80c1c0c41100b91543d0401000c501140e1185101d112441c1d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 889930557 1250 889929307 889929323
    0x20705150c1c150320060a09031b060c14070512011409030f25080d0218220b06040308030709060f0e0a0506030402060c0d0203180904050604030f110706080a0609020a0804 75
    0x101441d43d0741a200c1404c17008076840180454a42c04260313020b15424244c82c400c101d005400c2d82c2d054140003411a5a200e000001805110a00d0020302070701010007001c141070045801064036803000410300411118105e403da0740d100360f46e03402621a8150b454106600c080518030340840b640300507409204100764410b4040c141842481c40360020801b4419503500414400e0300c0c0c0040c000b00c40040d6009401e0824080442c0801410618102400342940c40c024004407501101081070700c0e019045003103241d503100000b400300101040c1c20600541c407510460742c41d0601c80b420a03101070011400041d140f01000004020220180c50703c0e40e040e402d685089591580300e5a5030320000d041c52040c020881101e0281d02c44c0c84401c2c5800001a0020144040070420030b00010300610011f5007084034080c290381c0c080d401060200340204103d003645920340c83c01000381c44000640f6464003411f44e0284001402000402c007401c5c50074440c0502a0031641001d500d8406003c000514901001e40040e105c0070b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 889931807 1250 889930557 889930583
    0x105090d03060b1b03040902070f03080601021b040c020f10090308010e010e0103060213122409050601090203040204090b041b23040f020d23060604030c0603020705150c1c1503 77
    0x3440170070541700141000b8a056681d82524038042d12074501212044020660301404036109600205062645182d1715a407000c8205445080002508000341d4503003d40c02190010b0300400c030140300500c3c031541c1d810404500340310245001809104164860359000a00e0001440196404946941100e400840c05070312020104510724104060398000c02030042443e4524080010340380d12203401344910b0300303c001e401c000c0e5087d61040e40c143d894000c2954104000502a54071030350b0145410a0010300005040d001c590381e40c08410505503420340d03550b55160040c0204003040c50007036026019201c1c000f103035178dc3d0b1a400000b4615038289014802c584030f0b00714414030720059054540d41c26150b078040c001c62500301c03c61041c00280710f10740c83d103804003840012003a05040c0100ca045a41c05000700c03202c0392900c8421002900502000c880c2e48c01a0040418169109003141c3d000d11841c03035580e6502c02c8607140542c02c514203680781a8046040290690100d1244a001e01c2141e07004020803403c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 889933057 1250 889931807 889931857
    0x2010804032616030608030903030f07060b0a0e1501031e090327050a050f1c03050c0102070309172a0a0b0c1c0806061c0207050601080105090d03060b 66
    0x5065103000c004003004100c0c00f04038080b4075080041103c40d1850720208001611110b41603280d22400d021540c0690041010107580034200c0024080d150007103a0025400003c880000c0d2003042c640e100c04012007107041408103140c0c3c001038011554109003401c0080324030315840e40880803550b4460b04680f07070b80d0303010410901d40240c200c0216450041804a1584d1060b4200c0c01510081c0c0184d9004000c82c18012809003000c7c0c40d4111003110007004d0038040713554184d56001185140b41c0c22410000d0501c002d90b41d500c001d001601c0d11510a869600f42c8908014001482801c0b2411256440d840001c4001d81c0d107900c00300c2004104c019818410280315580302144500700076500c01c3c840c43c0c0300060401e1003007201060011403150000c03030441c401e1256100440e034402d001e0341e0040d4801c1040207a080c3e51750640340400c20084100c40301504141c107d844e1b1a09201c000d0340710201c0c60751110b0800204000600004052083d0703800c042040c1c07410700356800e807203009110101081001c294107003940c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 889934307 1250 889933057 889933097
    0x3021c11040f02031509010e010308091f08160810030605090a0f05010e0c0102030c0d12140723040806061005160804081612030c060e0d0302030618040201080403 71
    0x1440e0010380148071103078048646400035881203800c201110600c0305000302c03919024840e181240c0c0d0200003208141d0075a1161081507000c00c256a1b480030342c00d50406201e9040c002a401500043e0300c84101503d02a00c0d080b420f106400d00d9501004110b80400030341c9104450940d0a0304e0700300c0400125642c400c003406103845c00030035019003240030140040782085415000810750121400507120400800c00041e6902d0040c6481d044154110040e02c400c01403145d41700a0801c42101c40114610b000b1b210b041d2a55002502c41c03038002895400c03c040c0021985200102c1080281e2003e032520f490320725411781b5440c026103441c0c0b24580e0030442803c003034420800d64a012481d6801840c400d4207030302c1d011a00398094465180280183c2444e445000d005114090403201c01000c0e05606403144d640c22115640861002c448a9a40c7d01203425200800c0004101d01419030300d00603900d0501c40c1c2000fa088000c10001c2c00d0000c414420040180d83c8a603000d90000d42c5424013944100300c15200801d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 889935557 1250 889934307 889934333
    0x31101030e0d0c03201006060c03080f1b03070201020910110a020418080c0d080c040509070c0f0c090b0117040c0e0a0207151b080103020f10110d020c1903021c 70
    0x9414400e54a07500d0140b40081a400300c2a070301b003041044000d660307140c2034034403c501100140104075494005548142c0403045154002d0a0010501c0d0a03e01e403040315007140c00944d81d1200503940810071400318100700301c0d049047c420f241032040040003074990b5103503a032401c0c0e80001d0149481d0003450200b80d030382801003e802903101d15201e403100c0c01001c0c10356440c1e4a1509000020300c1c0f00000c60070303042c2d00c0811103060701d001801c00300059450042c00d03500d02c2c1d10320008546001083c0d0840e40418065185a000341903103006c0458038120321800180810004002e01c04240d00c04000c0c130000681400c0e80c4070840c0c0840308003064030b030303619406080203015405004d4070095100c2034013001da030202e0340041e03100b50f0010220801180e86000403149040f09000007508a0705034031035411130345000c2d8607040c0707040810b2406000a071515002c6170301f4904141601c40c09a031061400395058a0b18954108034920701d100c641da01e0b10b1441d00080c0e1481a0341500c00038841850092800307205010302c07040c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 889936807 1250 889935557 889935587
    0x80609150a0b0a140c2415010e030a0b0709050111010e03180d06090302010b0406090b0f0f1306030c081e0705190e1e0106020d020c041a0a030b01031101030e0d0c03 72
    0x117074130b8100110300d01e42c498004084100946032618600400c2ea030701c000c042070140c100d51a105208071060001560414a8290300c1030345803041804010000d6480303c4000d03c00e410b00d5940e040c9039031424001500041d01201c40c9800c0b84d0408400c0f100070074000040e505003400c003c01680016400c500803841c0d61070503040c054021401d0a48007424540c054000b190f211030700f510700b04046e030b58a525410454449002e1301d58011804071024a5502d041032000100840c014034501c03041001c00c000c0b000311801a4800c07a0705851444040101d01d50500a9040d445403c200c001a01003c54291584802c0c9074044d0718401e110340c102e00310340b00000849150144c1207201c1c014245080c500042c0140c840a481e440300e0301d03100700d4008243c5900c04920781d04101d0094004002210720001040007500b01520b4294221807002c0c003020056466080c500000c50003404508625410741c206040c4000c1944442818142840140d8104190001d54204035201d14a440c080d481054582110010741080d100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 889938057 1250 889936807 889936847
    0x301361e080408120a0e040c031805011a0607020109060507030207030c080a061119050f0d140a1a0108011e0b0a02030c060a0c170c0c030703080609150a0b0a 69
    0x600800501e4801442640c00c035408644007101c10b01c3e010441880b8902d02d410000b62500a00d8070b9a0405800a082030f02080c14040790740600c2e0428140181384a840c181c03684d03916854116103030342c0049420040c800041d104149028000c1d00041c241164501c90481000000030307240c01032510034045d0802950380000a45220b035900e075802a40e4040301103042e100d4171314000078028000e040c80100c0d940b003203048400010680388103a003a0b400ba000714480e519410020404080c42c24101c2c41707004041c8142502d0640c0e20300b00704410804455200d40d90046000013084402035507030b00020b031181100d0580300c40310a186c0d11351032480201c1c52107138401515410b001c80c0c50865960040098070350085500c0071200030381c0c0c0b1070140302c1c2550014001840032945001801207104464240d00b5402040020404c2c42e04001c10480c0345950320985064000840e5a800c1c040d942c80c14102240d00090f00031400b03645c2c0d03000d910000d02d20303800600c074028881c10300040d1000898000c0855a407010502401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 889939307 1250 889938057 889938113
    0x30b0403050708130e041103010c0e0613050303040f171504060f0b09090c0411090907110708030a03060302120c100f14030a0509070e070f1404050915030136 69
    0x5c0d00300c1c84003055908803046091000a450903080500c60350801480d1561000001e0202c1c6013808462b5000040342400fa02500b00e010445d510108024002403000005000c002e500c1c1c41c4007070312507102e03600280d02160000410400e030703000c8034080960015009000094000701c080d05400040041280b819048442d0f2800c0142c99140800c82c0d4605640a42e0240034440c203003c40505684140b44c03800b540801c4030b40110702e65511800d070300e040d003001d000100c07924241c861202e2850f5030050145880013079101c440500031030405069110302100a00000c0c0300031021303d8000f8078101003c83c0490100310300143d8140190b841441800c0040c80501e040d02c2c0d0301d01708044954081d0104441d01403c40c4641c0300000b90494007440d01c503104075829a1101d21b0344280c6442154807480c200300c40610386009010105296840d2104680a10700d140a8108684950028982510940201e0881c04c0d0401c404943c0c04d500c002d031002800d102880c2c5c3c1c0702e0803140f062410903014812580e54400407180802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 889940557 1250 889939307 889939319
    0x30a02120403082401020a2604080a0512040303120e0c10030e011404020604121104020a020a1502040b07241d190210050c100c020d08060604030b040305070813 70
    0x11000d8042c0d400e203d12180c150384e50102160105100710b00450059201c046a400803c10003050342e81d0846581055030805143c16402442981003600a2903064010348284001c0060400a103404c0b0003100c144541001d10710344000c4d0008015400301395901c3d4980c112400340b84801d0200d80f58641c40241403031404114000d0050042c031000c1c2c0001c03015071170002011400310a038020944190743c020140384c51710f401d242655a03240030100c4212500058544998400e80c0c81d8006001c1004a0713a00134030740ca1a00e8241003000280380592181c07001e03c100028829a0109022960515005011405400d10481240740318121112038580c94514210346410820580c00041da00781048004507a0080c4141800500c094940e9000941c4400340020441e903040c01103000e4000c19107003409076120318550184245c141e9054440c55001a040300c0c964110064201c0c0c1d4483d041241070341c0b4581040c0c2140c0d150385910a01420180c14030034045140400c1002e0307803088070034404000c1b80100310181c1c2c0720 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 889941807 1250 889940557 889940567
    0x30c1f09031e031103010f211e06060906030b0703140f1b07020904030e150406050702090921190c0c05090c0d111903020a0c170702040204031226040305030a02120403 73
    0x8000d500503691058504140c8d024100403050030160080040710040c50101915046080c80120840b00292140e000041903216071046100560040d40342001c145400f40009080341da46050f80380103201320005109051003061061507100e602e282402c0554a01039034a20024007510380300a601040d038000304400c1603030054480d81d41190903100c030032403050101c41c60000d0780142c0c054840041c0050100f200549000c00c0c440303400c5541d1200341c4000d6120790840c2d0400c04d94881c040d107040718001850801c0302001c882c0c958120761881c9003541002000e03554001c4601e05c14032039a445444e034400452071821810702110321010315000e0030402c4c00140c072206090354110504003c1014200302d03801c500c4600034000c0328020b0440d0f9540004085643c0d4500005c0c0b08a040c400e1803401080c0300d0000143c45510040c40554015960801e916850300b000400b6240441c10f440041c2c00b126000104400c07401800b940c0050741424130603207039543c0d0f810300c8000740600c06071122194040307000e1200381a001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 889943057 1250 889941807 889941809
    0xb0108030c0d0f02031623011d0a0302060a020705250f050406051305180d020f010605030a05100b040f020418060b19120e030c1f09031e031103010f 65
    0x900d05481d0840e03203000065030428503940b18034015800820403200401103001c2c1b013031603040c400c1140d0420750202d4007405110412019480541760340d07031b9500ca95400c0e48204001c00c4040850018102d1030201e41d0025115000500f41c503051907004143c00c41041014450710481440c908403082ca002030916818460840501c1041e2a800a00c0c070003103040d04050150909907000a420354501c1500f840b011070080200070400d09644840180b4091000d8041c0180c40c000f140e15801024502ea4605186084410300d42c02903200354032002d03048001036000302e0042c140c002152400201403010745c2c0131801820040d0404000c2a10004001c00c0240a0a022030b00f1590108030400c003075902c17045a8840c41c030545400c44800b24040841c083c1c1c030351180c1c0d10280111f41803100800c1c00c0c0301c292065881c50f0080e00d40003401c0c0d0484003003182032040b08941b070380c80d0007480c1e0703c14821003e1799100035003001c12281aa40d08c0b1010102e0107542c00f4001e0b08111000082003201d070740d40303680d07400c5011038075151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 889944307 1250 889943057 889943077
    0x30c04110301030b010918240609090203072916080d0e100c090909030306090e0724200c0312030610140301050f01090b0406020304031103160e0a090b010803 69
    0x10740089102e06051058035070314013180407c45a10b40b0607407900489000003075622612903c0c800d5050840d0a1340380581402030102c0d400100b034002c083e1040609041c0703103410042c1a0784c107503540e0315025a55505650300c8080c2030204550b46074040c03106001020052080030b01903070300000c0c098400366601ea000c50145201503043c0d903c001b81071031140d41500c0c03036203d4150008285d0407003449071103d5540700e01c95041c82404d00045c4140d65130304071800c1e2081c080d103881540d00444030400c407002121422140484a40d20404103225450383c002d00035101201408591007443c0344020507112040140100805000b4100e94042d01800c000c52201e41c07084403072501481c17084c003000c5405070040b000340b2041d120604115046a0920040c0322240344500c0c400782c100301100000007110405040100041c01a66014554550440c1030031003580d0301001c65680203601c620b00090b00c0745c018443c0030041e04c80c40c00c1c0c00d1401e5140c0b10300300005000028400f400138014040002030400b400002008202d003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 889945557 1250 889944307 889944323
    0xf0304080a0c060e0310020a051606020703030c05040b070809011101090f05010b0d0213050a15030b010503070e0c07150f0c0306151115060d0c03060f0e0303010b0703080402030c0411030103 83
    0x18444108482d03281440e10485d030942d00c20382c00200304036902c0c1c018044100b02440c1560512100d401030650403050300d407090341d540d94005406401c0c0b40c3e160082c1c8803040c4d49800c0940c5045d15009030b02c041d0384550080a0030f000400f040b54480d503840307121041c500c0e20008000744003003c0242814181c902807100e00725443c0d840c000d4800641d05094100b2019160018014074034048030f002044044c0800604071441d142c1d8404d1900d01c40c600d08000c500c05140030b031f88800c140f0341c140f2043c1450106150490402d012214040040c501c5403003007250801a400250012800411100c490240426490b019200c40c10560b500c40c2e01c5926520520840b0003410010341d030318429101c15641d0700207041254000360400c41c1c500c0301d80301d0391341085070700030101606c0b841c4070b802280c4956a882a082d04100d4800380c894000c1c4c7c03903e6015006501e02c04410740041e6240d5403404402c100944112500207040c01085c00024055681c28048409007840c05030051160220304401d82405034400d00007114510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 889946807 1250 889945557 889945559
    0x10b0913170f0318010c050a12200d0e06060616050a080c0d080a050606030624030a050702010c09080c190801090321150611010f0e0f0f010203060303040303110f0304080a0c 76
    0x4d02c05000312601249642c5505290071a141c004a030341c3c03a040714050303443c6a100d00c0c01408407503801594005025010b40c00c81d4548070304000800640b003446105000680c008c0701404881e698034000c41d81c0c0c4a50344030751815030a8291408a0401c041d001d0083c007410000b10301141581c1c00800c2e600590701c040c1c0e036084880e030b0f02d01c0700c40d4084a00a80307440e50040d1050001403118149003902c01071201c000301c042124180300c051000d0b0b103940200c03042a07001d07450740103000d0815024020842490424100700c419242400041e0780e030341990003819442030301012044010760541c903114001511444009005041450502a0014140c080224141801150403070100d80d0780f80714800304e000043c400c20048a141140c2141c0c1901078502c030031115541c030b407160b0000c0700c000d20506841d03200010146c0000c040d8583e419040a0603030001d1220740c0d0040040003500c0e0b80100031036080c1c1e5454180211003402ea1241c143c60448000300d005414400042c002c40d107140d00081240d103040c4541d80c02c3c5005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 889948057 1250 889946807 889946851
    0x180d030201062c0a09020d0f0c030c0b07030c11210a030219150b0f03011409060601030204030b061c0203300703050313020f1005130602010b0913170f03 67
    0x4403121200210740c07010000104186441303940010000d5030000f004240045200e0300e034a60600c50404049500d030840301401c00c20008021200300050040d4031070309040001030f0302c0c0602503944905000341801e000071881500c5650f0401c0396070365100f4612a1881644020503115940d00700c8940c00c0e4050300c2000b0500c00146e0b21002e01140c07669000da05c14080010918038080075103101100700e0b91050008200c019652001d01c2881909107254a80b403c007400c15040507070504101406c40e90400d401040207201040040307030143e8000a09407060002603900e08015440305071308510007941401000680c507807019415003415840e44020f81000741100c42151107080340c1c800c030301004000c20000c1c0009002000403840041c07203e030001d07040440301c2d1404000289890326a101040c0480d401003055110074501041140c01742c10140020001184404002101d000e130082c1402000619210303c60100300e404092541c0300648640d5407500d60842100d01801d50f002141d219a101c02c25444003610 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 889949307 1250 889948057 889948109
    0x70506030118020a020a140105190c020a0b04080f0703050307030e1f0902122a091b0c011523030111180a0807120302070e0f0606180d03020106 63
    0x4a406040c1080750116102e540b91020390420340c045420b42c0100c1c2c3c00100464041c20320a020034040e4000001c0b071b45050300099501a40c64062030381090724255480e0341c0780d40c0000c0c012a0045d00070744d40e01180e0781d0f9031820520343d00c265000c101c40400041014410183c010380918040d0115032018003102c0354482201c3d940d440040070303c1d50a52400a00801d02648562000c80010300140111000c500d07101021803606039214001900d4500c085420300800b580c008550125030801c40303000c052405c1140200c800e1090030840740e80c0e561400610011441004d500282500208420003410035603a40d03107107401248a2090742d8410008004210302a01d010300c00c1c1210303411071070b9806042140e002c02e006003000120075000e4000541c0b01c408118100d0400c00c0500400d1031052041c4500741c03518000b810008158040038200c40c000092043e0031407075843d2160b00c0b81054032010703202c41580400c0d500480d07503c000241c12039084111702052580c19009407040e0f400c5103100300030075141414841c80d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 889950557 1250 889949307 889949309
    0x9080d09020114030609340206060a050a081507170f0711010504050d1d06070503070606051e190510020d031a010503012c0703020705070b090d020d050f0706020304080705060301 78
    0x1602140800001c1c0070a01d244121f03c040d030810407949003850181048542c4240382c000315503030142c2d000c0800c005d003d292004060000d00000d0f80c0144d5503a1070490500c0c3d031000c92035011308000258400007880280714441680c001c9540c0d006101d02420030341301500e4a50707829144440051400d1a00400c10041400307524081d43d400303002131401002540e8211038001e8240100442d40c0040548186282e0390007015006e0240518051a0340d0b20305480e0050854001b039202c14003031045401d21005a982d402400065140d041c0e40c100d241001d048079410900344a03800207030b884039680c1504030b142640040e401015000301d4500300907460301c02c54080700102e41e030489107000840400041c06440140002804400188800c40c010703840110880241400115400d800103540407904100f8440308010300c1c0000c00d00c904a0a241c1456800030900070514003501074000d01102c16000e0801104110050506204c0b03802c1da2085c54452400a45036441845400494461190042402c0c606001124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 889951807 1250 889950557 889950559
    0x2413171e0f070209060f0a2d030203060a180f03020606040c09052211030721050714090a050307090209030705040b01090312030f020a030b011209110d0609080d090201140306 76
    0xb400e0460903401c100b070b2a03800426154020782d0f1200c900741c5a486464411000e8249408650440c0e015040003098420710690080a5201541d40810151700d0101d60b060304140a00004684288501102460924005401002c00e00218080424542d0129046010700d104440c00d0200241d01d0f4000c55420030750340500359010305404031003031154480c400c00d58011030720802c01040180400801c603825410441b40c072400b1030b080d0310303030b52031540c884400b280c11f00c10426100b0005824480c40c003c1c940c5141e400b0450700000f00082001143c0d4811000c3c03002044020b003184c1a0940b50106103020b0b4102c0c0031850f002c0d2003400310201d06842c140c02500054041a07650344082441c60303c8640850390130011003024155660803c0d010300e881070005211080081d24003154280b51880018494544c032100c10048516020801002034403a80344440e8409044420114908580c01c1803802001e500307000400950000511811044035a003002074900e000341ca0741100d1072810b81f401100c0d407004071a00307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 889953057 1250 889951807 889951837
    0x60f05010c0f0c03440c19030e01140322021f181e0312090504061e0f0810020a03141014032413171e 45
    0x60046501c600340e8190994000c0c0d0b002c0c81d480380983c40d000c204001c40c3e007098903042000081003014030013040c8105400c41426842d00d0b0601d0109059040c09102c1d504800d00010700005c200d48006800c02062210f5110354403020306c2001589005014002d1900b03545010803080e10081c08968081b405480c850000700d10f0344160408000540b20060818942c00c076400040340d0095802c0c800d0f0703011601c0c1d4120036a140c461030b0482d00c59240e0424200780d80031043c0c00e01e55000302c06090003402c8908085903881022229041216442070710078555540060b60480e14004002440c0843c640c040401d190031031100c8016203498003201422440940603492990307200089000754081654000c0450100614001078880703001d4510b2000320a0a650780080c40c0d168900510a02002002092b00d103003013180244002c0805030b01c3e429408480500550316000032000140000107194038000b8000e03030040000520750b007044202c81442d00840008156004000c0310080062854811154644502010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 889954307 1250 889953057 889953059
    0x110f030708070201030917030928171b03091003020306210102070204090f0b160f08150a030c0905010b18100207050310090516060503180a1a0613060f 66
    0x70341d0303226034000c0d84200e041540d1400581c0108038019400c1410314204000c280e5a414080e22080c5000c071101c0d070350b03080b180410500003100e0030140d07a1266596404036801401c1c441080498109002d00d8607400441904002445e00c903c80120007000741c108121000b150550701444200c081780012101107070490300031950551700714911206641818032120002d8984582540031400b601d44140045500c2540805481c0411455006c61a407046c48512002c5401d0440840244401f20140d030290601042001040a90101d5001081c0250000c0e00d0142c00c0ca690303240104d000401442411041032500c0000f0404503100c1c0300300c03a043c01c1084440702c0e24012a40811621070102d41000781584504000000c0a0b181804020401403580c20001403802007814040d04260000786084e00d987c0c91001c040c40611782080640307401100d22041e50b000e014044201c1440c040e48000e02924140e1116505081100c0b49e440907407080c6d0007510070000350040040c501090301c801e4040c204602c010030314 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 889955557 1250 889954307 889954313
    0x903091802040317090103050615030106141e04150207080714030a0f0c050406050d080304030e0d0b0901020a0f02062703041d0604050601081009110c0d020d110f0307 73
    0x40345010340406640052400342d0365a01c1d89122040d803004c03c8081040030400e44c245680512406921010685004101440d803e006002c03503c0140501424450124032503400903135960f050705c140700c43c004800794008941071540040303500a13100701e10349100c4c40e0202c2c0603441d20108066044500d542d004091190030120b500301c4d04501e80f10a580c0520441009501081c10a98018140e9000c1d00d00d8001e90b0741041c06020541c2c6203a00401d004980303010044000480420840380e00c50780520f01800f03520000d40004030035485000d400340098040b081400b01041042d802001c41c1440342c0c50312510744008402c00d03600e40000b02c07001e4240b905121005034000320044c4180703040c4400002560700e480c0c0c44415103829100e004d6200f8284407454002c210040c2000d201d07058010f1024200b40d5030600c3c06c0000304844140780d02032110744580703504010b580216204141c40c980602c0c60300341c1d000d002515030001e6072620b43c00b40d40320005003a502c915015010103d25030404c0c9981201552604915031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 889956807 1250 889955557 889955579
    0xc030804020d06020f0d0606090503070f0e060402090d1202211623071418040f060f050c0703081b0406051b120409050705090a090b0d060f0b030f01090309 68
    0x300d060b03c03000e4080200421182c2d048005120980d050314001074000d00b4000010170140c4a504000c2c001e0740b0921090000d102809088000c813505450307840019a2a0380101e40039008422401d41c010700088010410040c0090400b802da100d298226003003503041e103c0c2c10100c0700d0500d944c00040d2408000c2080f01031402d00340c0c61072480c0076500305514610070f0b5181289400d054550703d0f0740c94105030402d100c5c0000c2408682a01d0108071255680780c002502c04640006005d08020000f008600f00340c010841540c11480c5c80300c0030000c003003143e803034613800740c10703040d80542c8007100014203190011300b01d514402d030400d00b42c140c02100182071a00b07210042e191070384064250081c000d0030f4166500104410170502400314910040f541d1240d140c1210030081c0c0323401506540c2484000d002061071525202c51410807150321400c00f26881c002100812201814a50045c1c0742c1801c0c80780701002d107400fa030031003003250304164200c6008060480f00340d1b00305c894410005000520100081004d44004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 889958057 1250 889956807 889956829
    0x403080609060f09070207051905102d0e1003140c090a15023009090a09020a081b0303120f04051207110f06071104020d020d050c190c03080402 63
    0x390201015450100005101004c00c842c1c1e03c005a2010000f07009500380f10f1103d962014100640c01c4400d4242800500c0e0f070075079680c03604204281c51821041c5040d0b999003861000c41c0104480d12034000c2c0b03120007003850032500d807080d0180c1c0c41c0700544444c2e548a80300d07003507800c04813840310542d43c3ca03003074000c804a522488409501a44500c00030501d00c1d040040d03840a801250010195001c410a6200700c80d406e10505242da27a10520346405600c03100c07002c485013030740c080b5901c02c0143e07200500301009100071030010390001c00b45807000c2013400300003600104603040319203040501ca070102c04050381e9100c2d280c005d01c0d040001c1e0001c0b034148401c440c100740d0400e00c00c000751030001c50b1600c44c5480c00d4000250989185140c4a4090414207082100310200c14007039600b5843d024482e200c00c241c002d42003a495000d194000340750302005480b5030686190b450032510912403418001c1c0c1421280e0440e446154940d140c161454040740d01814501101503815200c090045da51a02000070348241 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 889959307 1250 889958057 889958059
    0x60b03010207080d02130f1202040f1d010b0102010e0109031d120a030c1a0606121f06020a06050624030a0f06091a030706120905071e09050f040308060906 68
    0xa02c040c50004100d0005000f829910540c016111400c40c8802c1d1001c800c1c1d50301c02201d00d0300e906024050f48114500c0425625015030f00450303c4c00c0303c0512240209003404103c032041d031030058071050181c0190010400400241d0007409000c00c0035031814200c9140d050010045000e1012090b12219809040c1c0300c0303404010082c11041e96250200d508010420f14128001174078070228070f040200c0e04e01038a001400200c422442071070640040381d440d01c039441c0781d07205402c21100042c240840c0e41d0310f036076010540341c200464001e0380d030040030b560742d50003039801c540032801d002c002001400e010120450703901c007861600081c17200c46c1c031046000303920245c004064903440300030b295505501400740100a00104100045034440050010b1240710001074107807194100f08020030145501c00c81c0c0c0d48103508003030400588900340e0700e4840c0ca42400d540c0300810036941268010803402c0d16801c1103049541100e400d0005503901c03030024240b1801110000c001c10f641c14003041003070a02101c51580004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 889960557 1250 889959307 889959311
    0x421020609210d0201092a080f07030605090f0a1712130b071701091512050115080a030210180510050603100b1f09090606020618030313060b0301 64
    0xc425000300c0e5040d0b481081c030100350039440c0c2989030914400c0180c0d983e11441c030300c020081c044c01541c61030500040d10300e10010804500c00c0000c1303e071100c054210010f08404040f01c50545003c0c03070854a41c182032205507015803510002800520012404154420510025003000091035a03810301202a0381c803004900007041c01060042d44101a0190050420110201150140b4030706840c2e8488014004030400446d04840000802c0c04081d081c10b45000d8140800c224070324030031001e01070410307501062070400502552002d1180640c03020090212010300b4520058441e8200c40d030750021842c008006910685908040341a00d50006141032002e4002180030740154a5251401c901025a00348042c0e56505210a624041005040700d05620b1400d000c40c4410400294506551550002c00e0a00201881e01136511402e103140151011150801c16036803a40750003550f400702100c0c02500070b02c01008000d044000001a02c0c400e0100ca04d05508208860761440083d10900c80740c540c1540d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 889961807 1250 889960557 889960567
    0x4050c040e030d1503060c0e240c03070c0f08060106050f030612030c1015180203061203030906041203060326040b1617030403020604060e0a0f120305090304210206 72
    0xf4124018120303011900d4000d0700c044c5045003042d0045442540c01134040c041034110304d80f290b403684440e000301e054100c0c1d001c0170811120700350b141c00c3c1e20400c5a840c1040c04005a00e10411404186200907564001640403013180c43d0640156102007c0c0144400701d501070004010701c000d40c3c0d0040da40311602500d052000710982000c940b443d00180c4c154070a5030440010120030360002c1c441c02d15031240e11a0000c02d07007498005103d00c0d030000c0d2000c005d8400e40000c00601d00c0e0b125200c44071000f6410100b1641d0300c0c0b610081568882c0010b4034211010005408206000c510038055001a82d40010117002d005460790115136404000c40d00014460b10f090100068441e58900034103103101840071400c0b10010f031440c0c804402110a21003031480e9405200780008a580040c845038841c0c0e00000009a0041c20701c19240b0380004104020000c4081d040820200f007000004000000440e88043c4143c0d210520310340d440740114026404240302d10702150582e110031100e4008580d0010302824500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 889963057 1250 889961807 889961827
    0x2408150405070b161106090d0f05011404260307080f040c0f06020c01030608160302090705090a0b07060c0e0f010e04060e0a0209100207060c020f040236030604050c040e03 75
    0x29004140800d218134030144101c4240801414184600c00b8100ea550346842105800a0082d080c817100142c40703d03141e41070060820a09606c4096020756200d508031640c43c091070049000c490603030807161003401c8101000790150422050300d0280c2c5032620340c0c010943ea071401c030401016004100b911981d0540074001580000000c0002c050420741d070191113640400740c0050140c811a61040060381e1001c4900355078001c0340c4644100707403a0b048500b1803851721000400c8801f8011210140e0740701e002c03a44001449032074030000b04402480f81c00280440320040b03006403000408a41e104d03403c4820724407e00320710741c40340341060700c2c40390300400009246403241c4172090203030003c482200c515980002c1d4040c0c28903000b010a00001114401484c50505080c0014040901040c2c020300501a18441d0105940c880d01a21282944041907180784c240132154000e240446c040850001080740c00f0b0285281000301d06a0b20958105000b8801c131070080062100402c5180c410483c14003081c0011182 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 889964307 1250 889963057 889963079
    0x417070f06291210020f0c030a122403121205040501090c080a0507090f090203060a0902010e030c03031c062c39040f09240815040507 59
    0x58219400d84402c0390440c00d0700514600e59800c0070b10784511000ca60101030407000003420400c040c104007015031104401e11904445000b2901e0711070760b9000201740f040792203030b0104440d2502c8a11680521598118040304401c44030002801d407045c030300c2400144049409022408004c01f07513460500c0420303041100c0441143c00540d0101d64594640b4010707002d10070034003104400380c1400c4026108160841d0b59003036071880c081c40303124100c54492180e10f03828551a0700c04296035070040d00381c51035403524021200040c41c40d01c0b005c9000c5056a5000b644d10f04000905100c0b40c0b2019008506e0001c201c0101409910441000111691a0340000c41c2c0c1500303030030401e00e4a20742800d03c05004500c2d07801100034450000c1800000e640294014470701c92951407010746217090218560703901502c507040301c1c00161080d60001540100300c0c40002803010a0381c0d10107202e1a807000112080c00e01d440e070025416100904c10740c004c80d030104c0f808a10381d42c6c400744203540084c460812501d030b03284d4403c03d40301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 889965557 1250 889964307 889964321
    0x3250f080303040c140307031209030b0108010b0312040b0403110a090e0609011128140f0c0c030c0f150405030a12020f010c080a02130b03040f02030706080417070f06 73
    0x215800120520007040043c13000d410142480b040210141324580c00480c1c0c0d2112a8840076180c0204605082601405460048051908507040400d07075070716901414041d2044504640c0240300d81d60b402d20247c92180107681c140c641d08051540b9081c510745032181b038842c00c1812980d1000c0c031194002208d180034403038400b98036461000340c8242e18000c422582144c5540c1c80f01d030400181000686094100b02c04809140504000b1800000c0d0350301c0d60443d0303546582814440e504100046088900c11304030050620b8140840c01c03120300c005000141616403d051051076000f080e134841280052a007031203007120454900e04124105603130342e000a440c10904640c1a140c501f11422140600c960500c00540b0700701c8040020300041c400e20400412400f1300404100c3c82950220b00d0000702d404003040d41d4000d000403c4220b489082905016402c2280c4000891183c030400b68009811800b80751a103103d980c0181600c000b0045000300110320368403140381207803104a0001c95074000f501d5031107030368 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 889966807 1250 889965557 889965569
    0x60307031d150105090a0605061611030a2d0c0b1b0706030204030c0503010b100503060607060e030415090605041e031e051002041202040b0a0509012d0503250f 70
    0x102e025490601440400003010305100074044c02e0240500c04e58403040202c8400010000003424500c400381013034001c0040c0e10a0700395050141046c00f0781031002e80c4080314000400601241142120096441584100450014000300301300100b0003240c00c104010305580c220010081c030000301c2c0e4401144c20182c0c01c1d08100003099000c05c051082c403251140880103810103030000c001e03414000f4005508030031114500c1040143c0080000e41d81d03101c000c25141441c1c2d00200500402c404980300c65141c2e000340c090040340c07500b286070b8055850703c03490100c007c0b10120b4484500c0c240c140b41001c02d40c4000d0300f42202000185900000004034624a42000c58002d0342c4031013409a00c51500f9802d1030040c1c82c031520344034018082072080d0340d440080e50b140e0b0342c0c4c116000604401e582000c290740303903c203900180d8041e420300000100b00c8400a4007002070b821703101455201d04001c401803020a601401296055030102203070100c02c0005441c0c6d50800c460112340c50541540d60340902d07a045840d50442 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 889968057 1250 889966807 889966843
    0x170705060108100b010c0210050421061b080c0a031103090115091b110106051c050f0127030324030b0a141306020405060307031b0c02060307031d 64
    0x4105440080c0481c030207035410300300240000302d11140000c006d6608034402030700c07519418051001c2d050141c400c5400400f00611080072890340840300140707030300c04514203030358544c1001d065104980407035900500b045919210301c00707d506c944003500c4031508248148070a05945040001044e0782c82070181d0310643c19000003082d4101032014000740e01d4055070110000c04c2c14100c0078141028109000c5601805901d01007584032000400356014008a510607600910700d403495080b00e030a03210038a4207450203001180c904e4141080d41500302e90030031400044e0070800d03040c40c02c45400039000c0e5070150790007440d011807020340745060744558180d40e40401d01c2030030f040442041009280180e9580c8602c1c40c0c003042100000303401c110225000000c01184031420f005107401d04025490741582c000d400060a2141c0307900e01f0344800350003804900503507a270540100c400312640340e1088242440c916030203018179046450b0b0000c2a8060102034016031040c5c0e031700541c41d103449042080840641d6082d1900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 889969307 1250 889968057 889968059
    0xf02060301152601090b0a0b030405010605011704030504030201050708120108062a031305030d02070309170606101d03120d0b0a06090e04020109120b090c040e10091707050601 77
    0x8040d03c00460705a00b00c066907440419401100504556641114806900498003002000000e25462056000b1000400e408400d200c14000158003610542d502a00c4510711854a1000040301d07807001c42c1e0003000035008100a000552040f070103041d41034440d40d07225042411129500464a20036001406154007220070132101c10004845558490b5003042a001014500011010644030081c110078a095224070300600304070f800c008980c0b4801e0304000441d114201454020f20400d07080c46200310400a215034600f41c0c2c400401c1d858007640c402880314a420b440c035a81503682c3e880003017203c0441d210140519105440070b05c1800d41a001c40c21250760380302c0014a01200f11032030002034a000b0350340c050040c031805d0381140d40d04054a004515071a41c40d40d4a10040721400080d421a484900c5113481c0e0004101140084c940100b65400503600030b021210280012900c00c80e5001c0003a81c000e549511038114154070004950340640601070031920106440e201c40c2d4030550003140c042c0e102c080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 889970557 1250 889969307 889969349
    0x50d0908031603231807030b0109050115030501120f171c0608070f03080c03090d030c020310110d020c010f090f0303050709151b050709020a08130b04030c0f02060301 73
    0xc50718202c4c4c44036843d0400b481110800c04064640000c080382c56030441c0c1d59552903500d2080105100441e8003480860701907840303108402c0540420311803400e542c140c1444000845019000d024140d400c512103421014a041c0c42c0c440321240c03c070384151441e02c1109429898402900b0080850003e510300040e00f108c0702c810303110100c8034030760700182d03003500840418416440700d01d4800c8200c80d00310300311540b120046000715041d4442d07403011942c0640180b0441c420181c008000c0c4c00d04a000710107840b08000b900b100542138546c03480d40c5800c480320410000200d030f222a40a80442142600006401e0315604401011500340e240203646c0a015807111a0400d5898040c46502c02d0301e03490140582850200001410070441d0002000e002a6050424891060a0020204a401404442d506070b95401c0140096200c2c54265000480307a000182135034208114032411694031910004160360b494030100c81120450a0485034274440e8110711015940701c8018501908405049440c440b034014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 889971807 1250 889970557 889970561
    0x40603020a1b080a050304140115060f111c030e1504150605010806040c0c0b01090629160203030f0f04050414060f1513090606030b03120a050d0908031603 68
    0x10340060030512041c45030000143c1031006442c042c9925040640d125125071500240460440002d00000c4d8070f8809000c840b184600700403000c4a4a68941e20381c0c010100c40c00302d41125140044222035030104d8006030351600f0008060601d0144c1d4a400149440080a5a818100022000e00c0000419004d10050105840d03040c55418049081005010b11307120020f0a4480300400c240d20482e42e8001c442c40c0316000c1c20460b400940c0c8079403242665a154101e080c000c0c003060080e941d100000690705040451102076125003551210310442c14828000e500c0743da9600e00701c6040740c1500003409461004c1c0001b1024008240c141041261220700709070500040b240c1c0003150403100310210051010307503100c054402051100c00d81d4030401914244c000c0748524030030205818040e1045100000d02c99a0a500000550390103079000c1c0020b00c01c2c4410190755194124416001038010808084100d0040b4014038000e4030b0903a01080d40c84503074584800d50b40040310348607054a07442d00106180b95041c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 889973057 1250 889971807 889971827
    0x601060f090e13033915020c15090a030207181811010806041e0e01021c0203150901050a0e13020604030305130b0c03040b07050c03010501030f0b0105030604030503190b0402040603020a 81
    0x98400e15800b40c00c5c91508140354810700044c2d22402e0140c030600c001e024003007803448400304040105650311468044650380c0c1c1c104008402c4552641003000c545000000f08140b400703150554004d012080c1010004900c010445104540b200d50b5126031202c8510a2000740780305a00071351354000740d500403c0c0050000000100404d00c284d1402802e502c02010640d110340880803004c00010741c0000c01d115540c020b215016401e00b20b54000701040700300150341e4000f14441e51409034031145192280044c41f148610a008480c4e02c508094428050000d1070714003c0d6014026203e42c0040c8403003130700440c2143e4030682080c0d00007100020a0149841c0b0280a503000b4010564000d280007a0101d16035181d0055005060503507400294130b50a00c5010014101e581c3c000400030006944d40f80750129490140c2201101e0321038000c40001040c1c82d02140b0340d0f00ca541c054403200d2840d580c02d807503014450f0b200300358441066038640d502411138a0346d20103000648016100140e41e0344584030044d0544580d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 889974307 1250 889973057 889973087
    0x30b180105090d02160501540506030c0a0503130206120121031d0301110c010504021008070f080403110601080f0c06040302060904020f04081501090b030d020601060f090e1303 77
    0x6820400440e688000e0240081e0007031160024230069a00485c20f20305410081c0c07420100e406510b131480c07030030b840c849200110038066944040603a68810300080d400100c0d01071741802030910000002a00130f10007164001c0101130300b58070038211540003404c181c000886484420310400014495440380e54080300d001000038541c0e495a26003175500904e80c9241002c1d4010306824a50352003070344d807800d404c0400b0340c114501f10329031907503802e08407a03008000441c0c0c16445225000082c0d61002c1c003500d00f032030081030150344015007029501d00507110b006000c5c10031020803540804400d00e004060010a01910210380900140d0444510342403a01224014242c82032200704010401a03441c6c07401c40705115415280941c039003a1600c807803060b90080d5801030b003050041d0305074042d544092010f42816200c1d15070080081512020605958031254400307000075911540c0103003c142d02035054aa0040054500180440c3e00d1303040182200303006076032148100e07444c846000e04150f001600680c071800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 889975557 1250 889974307 889974343
    0x9090105030a151d011e1104140415030515091b060d0f090c1503060905060f0f03011b1805030a08120a020910020d03060803030907030b180105090d02 66
    0xc40c0c43c2c0c0d1042400002a040c0d10f203689181c0900351161406048101100c03000007080f903400d01c0b103544c00c100c80d000c4080e40d0305207103452122209000c95000340d405503241481c4101140360503006000080c400e0b5182842d2884c00310030004002441000a031280e41c0d218400e00082d03003420b01c2c1c00c0303280c0b0b6074035851040610349640c2440042d8841409403048801400408108040d02c0c40050004103030341c041c00303064103044c1140071035400e00e40c05102151941c107076010015580d40f992000c00320b50080c1c40c01688410b5640f4160468600000d99180806005000113040d1000c848031040c012488070400006c00c041d404200c1030340b00e55034411801458154090008410b095031109190301c90200e1007141c5481c01000b242280d0426411313221440300c0a09103000548190381c011350b0f6003141541e59000641030220105400b000032042d240107452040050882c1401d5546500061100406000c2c0361001101c101841c02000d000e184d0241d40030304080d05900b030840c075000b030500174034040c042c41d07481c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 889976807 1250 889975557 889975573
    0x705010219020603270624010c02060702180a0902040e01020c0715090911120a0c020c010c1106030403030605100509030c0105070303141503071e0621110909010503 72
    0x11a4003520341c0d0a5040780c0305960f0340d482e4810000e846079a000c080e09000c0e40003030340d2603030113200244803805189284101d0800640000d12941c0da1000d101d265400203500140d1800107041c144c001d01811840206121851041003681402c2c0e940d040b20b100100781e440703502400035810f0500c2083d03800440c01000758545980d41a540d55141d005100d028030302444e080300c0000191045075660b000c1c28000c0401d01200e0b80a1101070000d400004080e42120034920204644841070301c102e8008951540140a28074444001540d5403034000f0000e0f1b8107c002016200541c0d5100c800551040d403182d10001102814882030048080040901d5414000100182c40e41507400085103601c030102403800070f83d00d014078642280948000800e10440d0a400ca00380080408440d030454080d0a0a504031030005a03558803410501d0383c0da200300c1e520954191020700034036100d10902c0201ca1494080700c0d00daa4002c904a104840b0950134445124002052400c1d0b1480c00002d84c1d80105000c038001c003988 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 889978057 1250 889976807 889976833
    0x60504030c260a1a0705092d1201050702010c140421120305011403030406050f0f04050603090d17160309141204081c1b030903061d07050102 62
    0x100310300034048010201225485414031400780660450005815650f0381c000501c0c155a96100103020404508280ca001942c641c1c440e00c290385088000402d004410703080c100380c2c0300300d81000640300f0650400040f44201144c80e90340701070f9440d00542c400001d2510f421300000b8212000c641c240c2040200f04a1003c142025180540342640c680c50342201d0042e031310700d0000044603030780b03072000308072b01d87c2d50781d0801c030068040c0d2180707049a50b10451501403811007410140c0f00d00c514001e5030007041b814040c0e0282c50f607000e03000d491541108101140f91a86800016060303810031500800d081d03204a8080046540c0316005c00101d02455503450024102044c06603a0f020109032040e040640d0f840c10b20b07040c0407641c180c260103400284d0981c0c854168402d4241c1032580700340241d5141d442410005a01a113210701e5990b04032050703036601c50000e004000e01d503180940c0010140c040040e01000400454001e02c207401c490310007040c1a500007024240c1075070801c4100d82c40381c1e065410803600e4001e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 889979307 1250 889978057 889978073
    0xd1b05071101210504030f0302210c041a0d060504140f04110910030b0c031b0c0a0515240a060c06060b03010b070b0112030219061d01020a030606050403 67
    0xc840e5108254070404a00748004940031042d07031210300710b07488140081851100840d8040d50240c0d00075a5650750303200350810241c0507840b8403d1071030300800c800145021210030b0352102941210b040310b90b07646403980e2040a40da0307010120500030140740c000108115004101d00c41c050040c18140c80174011181900d100c20540c2300c0c002d01e60402905c800000800300182c5c09100852050000e00001ca641003215226070340d8402800111001b4841001103601c10b500c0c001509c2c8070b1180441009802c0d0040003c40e0081c7c0c00034030308030480784204c0c0c0c18140001e005110070800c140c0c81e0040420649404d030741011803000104000f855100079584a2902c54030f405446005840303a17810031140141e0f8915101004008a912026040c1c10110001c44c0e610403240082c907035103006454205d01d590b00e07158040703c03000d02c90ba0000c0c0507078400642d440d40140840e044620060080b1000a00c080350651a9000c0241c42c0d80042e20503540090304130340c120b416214500140030107140c194109410340d034503028 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 889980557 1250 889979307 889979317
    0x709060809030c01060612060b07050d20010c02150a050403080105121f02040509221209030501050f010608011401080c0903030c03070609060c0c110108060a0f08030d1b05 75
    0x40208403400100400030410440700e19040c0c0304020170500760307103101c010886000c0d085a520090304040000542482d842c2c05d45a400d82c01c480500344403d8028800d0311100800d01006c00100d0381352442c3c1c60140e0082c4511882840740341c0103401e640c0800308820b101404001c0100241529200621001c29031060103507064910540b0040c02100300c5129052078904110030681e04102d0502d803c0d0003184c480d80103841141c1e0b00755220107294540d0302051503c0c40c3e440c590040f0050010068030701084c29030b9016000e00c9094105000382d55100e0700d502d82900c20807961041d0100314080100043d5911207896401800398213030448400081c0c00008209503809003184406201c00301310303106903540910448000c0c88015040326950300051511901138114040251012032411a5500009001d8905114429440132101001c40720000041d0354894004d402560003000c8800082440c01c80c6600c101f014114001c01580c40d8204140d910003901c49042406846034120f008000a1980010940e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 889981807 1250 889980557 889980569
    0x151d0c0304211209050c090c0415080c09060406110d02030301081b0a0b1308072306030a0e0d0e030c041503021516080c0d0c0209180a020d03180e0709 66
    0x1501070395401e408803600103d200c1c003d9034991400c540c090820600091500e0300311401e40c1d00e03440603540c0c43c1c1442c00e1070040d4407500f040c4401c4184900c52281c0b02c1e4814543c00356140c0c00e454140340b460004070702d198000340c11040c0800c0212655229009040005020540440c4011451907040440c44c0d5200d546290b01340710030305401003850b09076990740ca50b03800c054404905050740703e895111410366001b0017482003510b1030258007008208002683c0c030003d50803600c002561002c17407021083c4030300395100500341c00c103a5588408544180f841801f10090500840d030319007a200341003804060404203031003005803189281c10a203004000c0f030715820400301c0340c0480f00d50707003101c65120520b0603d100300200712075102ca00bd02d141c010400b01002400c03d9803045021142c1d00401480c05841e0b0031403022001e58804640c030001003c0040c044001c140302441385040d07400c9070f001a030200700d40348050b6400301c0c0400c071080848a14550b00a0210f401056402d140108a06042d500500001024001d04c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 889983057 1250 889981807 889981853
    0xf04110607060f090507060906031112040203160e07091d0105150c0f070315142701150e100605070803060f0904050109031b08091201151d0c0304 64
    0xd410b20401d40d000c0d82c04240e00030b00504c030629143c68034580b100c60341d001e441c000c2115501c0210320b25103e44110701b0714000352001c140c54454206014014003400174000c90341485180c807840e4854200c95140c8d0020500043d124407141041c44001d0100c2c0c10705c1d008141c5440c450802ea090f28541031010504558040e01c0c2c94280a02102c0390b10518400d04550a8a0f40f00e0801c0c8075401240000e021011030b406480c1180814600c00c40081c1601d2034121074440c0042e00c04e0104c0c115500c0c0003030038140d25101c0180000480802d050050a6803100c0c0740d44940501d159034204420544640425444140b299201c14403d0420b1005881c9000c0c071000988018000f100080880c2c4403102030b2450b0040c01000300c03006107401c0c6421400b820894004400182c0d107001184084039400c0500458aa40054014144010081480a140005c00110905640b2141c02020001d0160882e50182100c0841550403000741030344490000809048503013902000c1080001040c98006102c070021108100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 889984307 1250 889983057 889983067
    0x1309030507021207080c1c020112020c070902090a0819030309022103070210080702070603090503092701050f01080a02090102010f110a1805090106050c01060b0409090b0f041106 78
    0x8031900e0240d1540290480c00c0b090320320b0307484440000c03114126841181100c00e11450a8140030007468400c0c0f88040500e0b9441c803c0d001503010300003c00007101254401030a001004013024076000d19640070b0f5442131303030000d0781074100e00b000e07010000039120040081030840c1204400b191070300310a80e40501055600c4171307081c0440d41c54004482e05090605800d80c030903140d41380e4603174a0742d10140089108030b40342d008906080f030048050b02d1080c0701d41c0d0040c200e154500700c1d09801074210400104d07402e02041201031030555419002d00304258140c0b4584070400341c00300602609980c10381049104440050782502d05a80c40004070341e00c640c0f44070016844102010040c0c0c05018000010720b050781c1840c202c40540841c410190240ca0210f03901c0d42c20710804100324401c0e4034000d000e0b140d08114208014801f00e40640300078644419482c00004050307648095082168204d03800800b4059161240d400c1480704000c40036402618048d0200c04030304051ba6040d61000243c80018020240825 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 889985557 1250 889984307 889984313
    0x121a13090809011803020303040906061d0618040b1507021e030706030b04090204050a020d0606090510080423100b0613090b0406031506080d050c0a060902060903030a090812091309 79
    0x90040c004586c003800301c0c2c1c1ca464030b80901074064681c0b030085800040d82c2c2d482038501d00811a03448044914082c062514102c140d610f15905800032048aa411a4a401c0c4614041e02c07940c102d02c0b8990401c04d0b12644400c083e00c10040313811514498070790396007a1644c00b40c01a81d0041441404c60f00207040001380d1864845c042000303004202d001a60051500301000f0500080340c00816811315050010400e503a00d441c001e0f00d0f03001c0c89000e000e411500040003110018061048a07400a0040b020603042c54015280c00145a0003100d268803a50492010000a01d01c50300800d8a844003c07100f5038100780d060b49003260100ca13544a84c00d022611041119450345455100c00080c41e0072203c0030702555030389406007009e04558840c1a55601c245100100a81c0c070800c240c0c1c032410100000f51003080840e442c0d40c00038289074401070b40c0c003800c01c00c00300025a0b0108010031003802c654540a5015290241c09d80c100f4070310f220088054902044114266504c40f94845180c05c411100000c0c50032080c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 889986807 1250 889985557 889985597
    0x1140f031503240609040609060e340b0705010605030304090f060f0b03040b18030c0307140d083705090d0203131a0c121201091802010f121a1309080901 67
    0x40d00240400d4542216181d607200c0c0030031414204110217039041400513202088be50040072003054100110f1a110080c4031028010009184290241d070011803520f0702c400000c3c0c11a40140c4c0850a0070b560ba01c0c084090a4060158800501e88814581041403400c20300680c50f100061009040c000c101c00058008280c810304841405141000c99484000500440340d50b64490031003551402294019101c2e800c04c0080c020603159010350702c6052944030034002c049a04c41400b001c2800aa081d054404403046a00140c2c0205140a20114480c103140000074101210030051000b190400c02003220b0b9401c0030780350030341214040c4a44003010500c41d80510464000c0c14100c00d40c90203448544440c0c210700d18042d003d50a100380c05408180d0381c50000d0b034201ca00320380c440c2620001845010f00503600481c1c5041ca00e80c0c19041c40303e200400f03c0007440c1156051a04081c4010703c0305020700741d90810820084914500034000c00101c9520784a025180c01000c0c0c3c40d074104201c0300040140b118800c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 889988057 1250 889986807 889986821
    0x120309090e100e0c010c020d1401020d0605120606061b0c030a081201080109120503090a0213020d14130b060303070c0303031b0e0d0201140f0315032406090406 70
    0x2002005050314900d00d4035210307a68282c000078102e0406496040007400440d203c010950142c407041107a8155600f0701c003400c00c01140650381d51010540121070800c1c20f00003000701c1c12100200290440c00c105c10414182c0c03084004001c5075002408000c200d8a40004a6105e030125080f920807092003040d4583c0361811601000e40c15000c2c0303a000e58204500e11010b00f141c0c203c0c90402251580c2c071420f00608803a02000060a611808030b20622590300900080d0b801101072000d40300495515008145000c210b158071202d070640c0018011000b00481c425079002078441600500a820544901c81e4800b81c2e03000d0240c200d001110115005a404104903240300340c0c0045c00c0c28405540e414090004c010030000c0212402060032075101142c42181451a03103c001800c400c00c0040300c0e001100e400c2d41710700721070041c2d103000c00040c0c00d62603900f0040c5206032b000c049662001445d24061504008880d00b2001c1d61190050740c0b0308640c800d001c1125481041a10f440180d6951420410050104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 889989307 1250 889988057 889988069
    0x17040f03031e0905010203040311060903040501030906060521060606071a06030703050a030e1005040506070b0c0417030921060a0c17010608040c0b0a050a0e130c170a06030c120309 79
    0x3d0016200304116064010754403450003520f4109050300d82d481c6d41d9444480803100000550003c000c180314a601030340c045101c16004a60000c2c24030380741c00128648090613440c0c021b07140300046a0b084084400c10816502c41c01c20365505040682035070300c041d0050490324085852150003000540a0713201000040025608401200e81c07080c003905001d00f00d1004d02e0358840c001c04242029507070140c041c000b00c0b07084500181c04640b0348003164646071107002014081e051145802c1100080307490046141d10000c034102400f540c0c0e15400360007003008103000a103032a100b0f0a0003c2c0380342c42e09031010480306d82c440740c07891004c500003401400c111b600154503407480c10382020400001c83d0041e88545001d2150b031054090003209030f00e07901c101565000389156403000850400c802401144a001c1080f500d00007c0c0c5410f503448132080b40d0340c041c4c4481c0c0c5003500026810720501e01c11100000c0103140c1203440381d80c08006183c1580c030f4804aa100b1802009060108100b020080603c520000d00050031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 889990557 1250 889989307 889989311
    0x40c06032c03120f1e04020f040209041b03060816080d0503070306030f08090103051806061002070f0602160b040f14011115090c0402280224010617040f03031e 70
    0x50400621072141c03005840511100c624443d0001629003005d0001d030055170010420607003c0004410800a5481030b2543c54201c0d4a071071900e100c42c411a115040040c00c00c0d100803d00781c3c02e02c20b0052410044881c40d10608503008004c000a0101054090646400e89460b076138954400038180c003c0c01d2242d100030200a07000c04134600341704200d00504a040400d0b0307814455515203504900c0754500008a090540d0404000303e1441e1501d040a1103103c011030055a070f00c02e44c0e03025480384c0f1030070700d42c40740b4050f8014508400100c118881601c0140481004003820141004441c05900c0b43c280a01340d03080c110540d00c01e0300c80e80901e1440c0380c42240c100884669010614507040150310542c1d90701118032903c0402002c07803510b4000e4406002c40810320301034146212541e801140ca44c007000c08158040c070808886510729a407041c054001d070080007a503495240c180010710303025400c201c8166000c00c0c902400300080810441002058040c500440e81c1c903940204c1c501c01d49403601c20f010001e8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 889991807 1250 889990557 889990561
    0x219061e0c030c03111e0c1b09160e0f0a05130501060306050d0321021b0a030e15070f02060f0d090201020c0103060b0a1107091802040f0b090714090a0608040c06032c0312 75
    0x207110580c03a00d203407501618400d270341e41c8030305d0016a00b03c45016406004135400001c110390b035052000030703440e61003001042d044105590380003054034855840007621a542d181c400500446405000715002000b0944641085800c2c3d900d0040802c844110b006000300910740e0070326041c45150701910421201e20b1b02d00c1c080d100707401c030807140d540140f903000310040360391200c01c00107916202300400c05011507440418a03106299544044181e0904c00c101d920250a0003d50702104201000e0309054580c00300004050b80c080c000a032a094a40038950b0425060400900a03840b01105580c41440c03e81050741d020721800103228181036068101c03600c080d241c0704030321880c1c0400a940700c048600a680800c00070f4401030300711060310020040b050708100010081290148101140520300000507201801c1c0780d0303144000781303801e81c15901160008442c40b003400b050000c003c4983c0c0081000f401c00704241d29400700200554540c080750f8040d00c4090200c4000e02400601c11100e04082c4c40010003070354 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 889993057 1250 889991807 889991833
    0x302010902061908060f0f040905070e090304170a230a023007030c03020108040c0801090303141003170705070807060315090b010219061e0c030c03111e0c 68
    0x2c001e14450070001131048021809904010304142410300c0e003c0e001050221840d0140005031460500494441c400d9001c0040c404c52a195030b02d0280764a900a1507440385000200c0c000188624521015908406c524000280c4102c4c3d6a002000c41e040822101d400d003404070700e042440022001e0f4108000100f0031181440c43c0448a9005615100810f0314911280d03040c0d03941d00f013901000b0f0002007004400c0c0017541c00f0750310302940140329504600c100b40d11851407509651416000301c010035281d008081c0ca4103003000300c1c9640315240920306500e603072840c5c5030301c400f0030070300c45058007507030000100802406028800040a005c000007121040740d51440010300a000c8a400f01401c181e0000d070114506000c0d02400c0440d02c2d05a0090124400303c00301d0701c2000f442004115800c81da280c06000d001101140e48000c0e605070300c40001404a61103101a00b590200b000c4041018030300042c500d40c0003181c50076104400f4848001400c901c09d119851002485a400541c5452145258103904 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 889994307 1250 889993057 889993087
    0x2040c050a0216081002030c0d11040e180705010815031603051903120f141e0a06050114071e0f0614070507020d0813030605040210020607021504030201090206 70
    0xa040b03500b00e41001d0010007604000c0101c81c001d441c035903048038079095a0201a50080d6400c0020086520303e070030081d124117411100307184e07042d10055a004c02c080044400c82150a64421004440442091309a9546a4a0701024000c0e281440384810104032103181340c217031310f20342c941010b000c4441d403d10b0b240016025190611003114140302c0c240c280b82c001080c90b40b4dc0e503446541500c030300313044404110410000e03090b007400c81e5400c182d881030200700c0c0c108980241c600451346a94200c02510001d0004142e92a009240d808000d041a03001c00450f42c5c08141440c07030518081d491030700c0b0744032454190610a04442d41c200c46072242c81c407100a10501c0310448509900c1210104203403040881d00d541040001c03101400400e42c117002c8a009420702e8011a0907441c4101d016034540303908210007858040c800d400030b44215039032740f0822045041000a20134443d02c14001001285080c0800943e02c0003c1f074990744c0d00c058060040350030175000b504118400c0c2d030b00a141c1601d81c0945a04028 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 889995557 1250 889994307 889994317
    0xf1704080a0b070f0801120203100501030803060102060105040c140f13061d011b11030f060702070f120b041e060c030902040b04150b0a110f0a2a050f030a02040c05 72
    0x955850b80c000800d450500544015408900ca43c90742c9100782e00e405800d05040700c80764000d90f0180108a071a1581c552244035040c00395100d003c00c41c2d16424886c000a1405205801c039a001d41d00e400b005c000360580010400c603d9104241e2100d40e2040c6004805100f40201d81e0400e00c400211500403170341e2500402d17181a02d100c0c00c500c0c094001050401140c40d44d11003c071009046640a41c6100072407420707808240680c801904592403940910442850040c0840b09031006030040c24091000c404d0f80d20200000b000c0c038860350108545a5140c0844250340544010900c41c4c0e06026200c407088c481503840c2155030001010410200603602c041c0c00f502c0d031a1300c1240320350715111b04d481c0f080c9098410940304070700d00744c000442c0c00d050014543e8241d1250000341e040c488840b001500c1c003201005104042040300740900041c41e07a500e03182c20342c800c02c40f84000440f0031a40c04110040100842403045803030884290b549a141b90000c24201507800303401035003150030441149900c1c2e81090042c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 889996807 1250 889995557 889995563
    0x705180114120910150909050c1008010521060c03040309090609050f1602060103111809070f1710110c0102030403090806070516060c03061716210f1704080a 69
    0x1030070300001881130104460041010340c4141002e107100b84160741c050391140714040d204004449505c102c00d00001c805869800304240061046401400136043c000a2401c8034160700c00100a018200d04802d501c0b80c40013441800707680780100c005802c1c91b03c907022030f1000f4010f8440801c0150b4580d900100134050880384640c0010480c2c01117515541a15501e507615070311640035110310b900315503410941c00103030000c480d80a840da045071000e1300208a4220300078405103000380201ca00e003002c0024059066402084110210107001c1611040410340700a02c5601e01710014800703441c1a0f11245030b02a8010014082d031020003003004140c1c00641c0a0152240350088442135615480200d403603208503449001500124091350300005c0036600414040e2070a4100452455285d452505401c3d4000c400f031071941e48103046024900c0c08803001d0300041c0c07070044c0d001c403187c28002807110202d507404400140b0194071240c09805200120750082c100e0f0303000903090351303640ba41d60141c40d540701e440b03000c15 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 889998057 1250 889996807 889996813
    0x20a030519180806270624041404050d020304080d110a08040909140c0604140315041b060c02062205060c010f060905060109180b040c2607051801141209 67
    0x2600303a889003058082200b02c40607008100603601e8160501052081241c7d150502d84e0740c0c5c0d0003204c556154015640c207003106c0c0c0014400341c070f01800c03c02e180c1010300fa445429504108010301044402081007001c010303542c181044028198803980e8507081e409a4003030440c02000c140840c1c10b040d550003014100303020344004030810035100203694030303840a0034260783c7c8050100020001900e9204240308042c0006099403203104840045100030002107400700c4042c008c034030449185d80d0300d150450010b480149400540840300740d020404503c500001e6194030100c5032242e0380021400d290200161401800b8192202040c501c10b0340688030451401d203815040c05800f056101880c401d4511844050b03440e0391090b40b6211040d002c0c00940285180c0c101e0311000306000703c0d160360140950a0002e0b586540007800d2404140d46a13070020451041d0f00e03130500c000c4c800c486d80e001040d2100e40201ca861110207107000c01c01a0360000310650040700d007400108403d0751403018400e601b4403415840c000d07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 889999307 1250 889998057 889998091
    0x120a090b060103270f020901030b180102032a090d140d02011b0c02190b0904111e0d200a140313061505130b0a06020a030519180806 58
    0x15800c1d0b59115414400e400c1005400c1821026451103e01d00280200014000782105c1d0300401c2c0c113404240c1060ba9954440814881021050f0400c0d5a022160900031400d42c281340b0208005010003001e04840216406002c451007510402141c40c0310704000d1500582a0013880d144455407600d400380c100720b00588544a005600601611480407031042c108002c01801c0c0d001503d1000c00b2207010398200d031124412100362812141c101028090380d4241c2034440c10308408200079100c000e04003c19045040c010307003801190161541c144800d520700c0c0240c40b440c40d00c00090003030800c003044100442440501030b52200d01040100241c2929907540249000b07402104c9400784000d55400442d41c0801d01240041035099000c400340c009008030070342140d9514800200b04407402c903c1403000599a0141406070300d407020b4144020100c0d400902201e400716100a0818026500030161000101e04428450b6210304165003440001301280c0002c3c64840490955031038046913801003480140c1c00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 890000557 1250 889999307 889999309
    0x61209010c020102131a0708041701151809050f0129040606020a06090c090504060c090e131b05120708060c04030c23121b0409021014120a090b06 64
    0x2183c60000c284500001070900d0412440c0400401020700c0c80c500c04240b00b4440060b810723400500c000c080c1d960b030552005000713019113821191007050944141d40a25801c12040340c0e418251010740c0080840001c29101d1801d0550801c04000c0005805500e00300201401c900c0140c0f0849010320070449010300016100184400c465040c010030000da400034107110001007054208002003446620280c0e1b4040d40d4400c0681900e0703081d181202c2003600c1e0b084072403a00350300025200040202c0795840d41c00d4249044909441e00c00440080d2802e40340c590140384640366020004001e0201824440c0001082455035440d403115008588542c01140b020481494810003503d0989400c44030790007501d0310740240e815964014022200101c0018054489581d981d8803042d40c0803d1010042c04800c544266500c2c1c524005c55005842945401e103000d000d0784030890418000d05c618100803080a255030725a180700c0c000c42c803000c1440502c06040006134451a041841114400c400f0080952940c40c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 890001807 1250 890000557 890000561
    0x308070c030c080a0302071b1d1503071701050a0510060507050124080601080f0d05030702011814071e060309021c0804050915030a0201180305060c0309061609050609010e061209010c0201 82
    0x481400d142c442203807400d101c04261410022b80140c4034240303000402c02e203480441c0c20907010380d01c0303803542c2500b4600703800143c0000c4c05620303841700f2407203002c0006e0314280c06a42c5030540c290213014104100417604104000096002001a03508108045110782c805001c42c4910001c90241000701d0040000004003101e001800346103060702000a40706c211740100d030444158200030304802c11036484007601444c201001ea0030f040850300554180d01d806994040c01482d0444035840180c0c05190031a03076246410948042000340c030814a000300b440344150002540700304914080700c03066011604213038104040e640040080b0703030081d80c01d02c0035650389aa0703885800c0c101858039505500503902810056109040034100f40032a040c0070356403940c1b01d44030a4036026044544030510070780041403001e03007001000425800710843d19100020104450004c107001500c3c40303202c0c06100b02003510807060f801a002c0d1482078002a1200781c4402c0039448a180700c043c15294605903510f4100b10702d50a502c18 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 890003057 1250 890001807 890001809
    0x120c040317030f01060e0d021309030207061b0620042c060d060906270b01050901050604060806061902061501081303140d0207030810050406030308070c030c080a0302071b 75
    0x104806440f0b40c0c6031a0b8183c510b108440401c0e0351014004030000e006a0f651050b003400d16141c00340000c0c4242440c81d0183c90b184141c0c220700244081c0b05020000d05001040c041c44040d885600458000310141541c2c5c01d031008010b41c3d00c240e000104020546000040380122007101c4000c0c107119220703042c60340d2210180b0076140c507a080f221140300d84000c108960040044a841040b001901481c404884003603540100c41e0020b81484040004003400500031025003d04021503111495524050008046200324841c0000b84a2102e001a640e5600c0b20159105461a09400e100d0200c1c0d040d0700035102c0c401110168504001102c1406142d44078140701d0303214030312283c172030140c45c20f840c0c41c1540c41801c0141060141081001016070120380c40c0054035200b40b090302e90810340e042101848000003055081140102e02c0c080e01040460b92040c8119000411400c10080c1176070a800c00300e510b5406684041c02881000070f06910496043d4000c0c14401d0003240314a0603941c0c4046101504041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 890004307 1250 890003057 890003071
    0x120c0302040506160201170c0915251109070503040519020109270603080702010f031a010c022404050a0503030403170f0c07060c0b060f0a1802120c04031703 69
    0x81130046001c1c0108001d980c0550500505242a1b905c0c40d900303402a410f0b8086941c40e0020502151622103405c0541c807102c440c40d0040303010b13810101d2541030628036001a09440100c8040c244482080c40026180c03c0034601001d4140042031070202d0340a480e0303910a640845940c400d0f0004065100741c848045480282e050303680d241c2c490310b00000c041c81900b000006500e0100c5400c00c120030b884603403003402c004503c5030240303030f4847d4100d000240c41401101110b409260074490391900035240902c1030413041700242800c1580d0502d50010409100c00030500a0b403802481042c00480c1c000c140140084403000c4446030700742c030b483d42c062540303c2c06984030043c00401400b07010204540361401424100740c0c0700c0e00300e034141002c03040f40c0b40c44d19809a108102207240f0307104910520540004580e403240c01500e5402049650300701040401c1c040d4828400030000b0419407204001c5550101d8864085c01c11414030281850074080c40070380d015200407240c410340c180040c8003035a04642035a1140007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 890005557 1250 890004307 890004319
    0x2d1a06280b0307090b0c0d0f2d0e0d05010b033315060a051804020f03150301020c0a11090907031e11280902090a030206070203100903120c03020405 65
    0x1c07030190201025000900040b051006005002c2081d100301c2d40076140c07400c10b0100800031507107403034009401c038214044c80c802040307101c00c0a0552203180710080050400c00300c40a1081405000c001c617000802140744075032004400c1800c2081c05815009200504001c400f0790399800b04120450030a0302d419500c0c02c400001a108501140e12001500795114040c060310030561065600014000e511041505010400c0441e11780312042d9140c000d00c80e683e805039800c500d00515605200614040100b0002003400720a41000d900e403000c1d0181c0302c0e0317894414200c40484840385028242c00c840b81c0b4209004e1040d030740026040000008003082107e8000c40b241c501010300002004c5608401d04040d00c0030489507480d651951910440c034030010700c005200360003042800c512445408955401003900c0750040c04031506a907148001c03c01100d80c11104203a07503d500d403000c06c0c207105d443c904411405140c4032800c018540c100b4011b105822508100b00300042410300700f9822070059000c0e10f038100d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 890006807 1250 890005557 890005559
    0x5010e0102161509080c06150f0f0607030c0206160b0901050c190908151501020a082502040204030602030612030a17180714030d08042d1a0628 63
    0x98040c200c4040482c51a04000c13a4501850311013442a500481c84101c2d07a0f4000002c000c00d000000191605495003111741041851210380024008807a5592840c40344c0000206007040502405510100680c05022030703403198060030074041454808602035034040b84a0000410411040c45110300ca055680c1425082c4040d4213202400300c400c1903820018003c03164004218050100542c68a1ba020a050300c21907241c2088501c048110580055041d9484030b5407802c0041c0446043e11403098144c3c40a0070242c000261010060b0310841010b50428800500070040c80300e1500214400d035015601d4440000c245c400482d0303a88540a071040010341034a41c1c03c100280011444e942080000100c890828041c45900d400c0002c9a4403080d441e2180f4a00440f140c1002c0c0301604070740c001e90400c8403a030716103030f250480a007080400700f21800da07440070015020113400c000f08942642040c14140b1016125612004010003541c01920a1800201c1c2202111010440428050321002c0400b462 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 890008057 1250 890006807 890006813
    0x140913110a08060a05060109080d27030f0602120106080c041404110c0705030c0109030b0112030c05070305030a0e041802120c19031704060527041805010e010216 71
    0x10040201680d0707010001010000d04004108901401408680800034035420800c0000d01190045d40c03020342190000c50b5a0341080d60808107002040c600c100c06601000040c942ea20304860389500700501c040080c005d240e0610075103501130401c1e40709407150707510140d8851070259003070281114a454505c2d4100020300c40c010070041004070b20b250140c0003051011460210b29600c2e0000400007816030300c0381500300b040c1c1c501009410b243c2403003030074841c89242c01d5031690410502d05020f550004070f6040803030030030140310704448040260007200b0f88804940341e191168480c1d011000c400005040603003021103500d0140719041201440e00014210f412142c0e00b03000190540c0c40d10410140038000e054440343c3c6400e441c48002e900c1130300e90a0740442c1540307820300003010600c1511603405418482444403d4201d0101e5691143d507661480f000010351014111050792030110642040c1070000c010b413010400c14601072454480e000074051518003000031400c0780900070712454220781c004088008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 890009307 1250 890008057 890008073
    0x40b060603190c030f09050d0207051e221407030f020a0806010e0109080601060c0515100519261902010f2003030f16170f071b030207140913 62
    0x1141010b410042100d841104081007240d207481407e6a0540000450000640d8180481409424121402c083d51154000110b612041c0f05424900444c103c01860b902070450303200ca00d088440c045414050014190200c06007420f040e1a12000701e818815031044a07452402650505079260356180503584d1484011100c41e203031410350394144900c400f004100300d0410f0101d1030182102d500e038009404010b1501510b000300304045003160381d54520620141410b0300c1040421035204681c2e00141c030403200d4140c08415460b81c0180c2c3c0d040d0070104090004410a03454220b485101c800f030702c4130113504801c0d092482402c014002c2c000345d01540341c2c140b000d00544840c6801747d83c9414500004150103951450341c2c1c4207843c0d6541414808042010079000e0582d044100e540500e070a02100329600401c4188030350140c80e4050006000d8001481541304000f021490038059241d11865540c504020351624118007402c000d9000c86034014042e42400801c0364000d45013a02d81c201c4c03500c004e0b152250 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 890010557 1250 890009307 890009321
    0x80a03031802030723191a0d0216230606040e030403060204090605040e070819030512040b06040f0e0a120302040806010e1f03050309091b070308040b06060319 70
    0x60407482141d4400541c40800081e000b6011114480b0184040308a904140e943c0003281944508000050840c100454010f054111909265000c4c50720000700031585140c003c80704203001e01407001c1180c8400e11000d44000002a018407080b00641050302d0341d902e641c10b80e0a0841c400c6031b111801082150a241c1d200c0320030140000c05607400c0548079616403003645e009501c4040101d403a000d040c841407406109061809a9680082400903d00704113261a10030151400003010b6864641900b03140c06442110b5030160001d4407001c0364a450b14107403482c00c070141c450301c1c002c500d031900c40304000025106001c4144c031060300038840402d80740d940b40700041002c085102016001e201c005440441013110318042c05070303800304000500d0480035500341c0004001005001c43d0046400300b0100c0d0001c0115441440207840c8003c855840e0a040090f01d40119500010704000180200c207061340403074000d014920810380e000c0303140c8446040101c180000c2e0345c04546200001421b034800303041580168 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 890011807 1250 890010557 890010581
    0x108040c1502060619080601090506010302070b040605091e07051c120f0f05070804091503021203070201021b060a120615050a030b010f1e02030f0c0d1107080a0303 72
    0x184120303407140d12454003044a1158140581e22520501415107410691884034280d80484200410b240200c00c9540c0ca40c107118007041959590081032450b44a07404032908135412000c0d60b03445041601d000c0c40200800c8890410034003030340700b2000b16112610b0811040c800706c400184049400d0100700b200b0243c0040c1c80e600f404000e4001c1000140a203140c0300c0c48050103445400c2125840240504015040c12003002000300c1009000005580201541c060301c0e1040800605080032480c15441007030180c00195000340404c542e034560803c000010270703020f4801c0e82650702d41401742c0c07504002590341a0000c1da000009201c81c0300751611030350404201040086004c183c640d90b40c454a10010b01580d1032100007880000c0800f0604c0d00f501444203d02c10a00e09a101c54000080003007080c030064040380003015044041800b035920070401e942c20811740c8400d85545080d25100596600b50074540d00780170070020011f2070380302c403030200b1528119080f46010b00803414895500303d006010ad901d01d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 890013057 1250 890011807 890011823
    0x1150f030b0301090308040b070507051207020102030706062903040f0602090310090c150f0804021207051c120813030c020a1e030c080309011d0a0e0a05160c020f010804 74
    0x41c0280d99024010f00001c00e020780c86008050a240c00c18a031110b46c020070140c180801000150006040085c3d94036603040709140c03950b151152440102c0c2540f00b00003002d000d080c2030140109503000c102401c124181e6921a9a011b1016048680d90300c07800200d5024040c2601a510380c0d010624540082c070700d000c0010180c0d40301d0515581d848040f1000004142c0d00320520740c805000c0b0040f0b034060500303100e4080c01d0175084c3e1a05600000d05001c0000c10081c020190089880c0d10401d041000c44060100141541c1032070054140d8400300c0c214569007030381d03032051146000786110301540c01c1c64040c0c820700c0c03444c0c405140780b51000e541501074214100c2c0c100f4082000020b0301a40b240408116400c0c0c41ca5482c00d0a1450401117460510b0b0340240c0d40c40e800400000300a681c000407000d41d103904240000610300752000c00a584002c040c0c0c803038062020702d10100098541594002c0707103c3c4191401c4006011084a000c64140c401c002000b03401401440c1484881e60142160607442480741e442 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 890014307 1250 890013057 890013071
    0x6012106090611030901020918010509070c320d08040f0b0907090e0f072c0c09040507090306050a29030a0203030c070e010806040503070b090a05120304061401150f03 73
    0xf407990543c0c011604800965030114040000703181001c3c80c601e0885500c1c03d801001d50401e0300140d01c500d8090582000c0c041d0030400e9204002800c569816030480841d00300014a1920170210312030000041c00c41c2c244c1c083c2e904400708417400b44030800d0042e83c010820405070350081d03407020a02207024107068000c0c0305082d000102800c00707020b030132103904004024001182c4040300843c50301c00e40d900309a0102500c03400040c290300c15504071040740041101c1c410030380c1d144d08540c000d00744500100350b03400508100801102607040341c1d1308012248504000c0090341c0d1007018081c21078081e010b588449106a4007141607840d02521080c07080d001c02401d40340b0544280c2d000915550044802c011250000b51041094618000d4040e0040013a4800380c4880c1c5066540e9985034401c00d44001c181d10004004180016010016512050381c06030485075038804a00b0640d14541084400300d90640c14042038292440040c2c2d9014101e91882000242d85642c941045c0c903d031391001046400c256903aa4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 890015557 1250 890014307 890014331
    0x1e0c01090804063906021207020a170a1209050c030a03080108121e03040f2405010902090a03150f0207060f060503030f090103150302090708060102060121060906 71
    0x1050921040c81800402d640710310700381c000b8000d84045001120710394811040d00c1900b13104c3d00c1100c00320004588483e05003403028035005000380035000000401c1100e40341040700e51600050004000c90240014689a42c008000c40030300d845941d0b50440090040c1292840c1a241d40d040303c206980709800341e078881c2c0c98000103c0c1c64444850002e400055a080041000c604144207000400021881c0315142000d138003110502483c10380080f00c10b4000c0080090f0602040c154185c0032503030b210714004024003002a0780c07142542c00c000002601c600d00300002814510743c1c421940041005402c030401d6901c0d5840301d4030101901a805c408041e01d90407a14008095403000300303041c61003138000003585021030085804032400d542045000b6482008960351071800c440940302025024a0085100d828103280b0717848508050344001c1d01300300b40006100d4050380010301948101d000b0b0742150116a602c40102d40f4130b405940c245203409142002d280046605500f080101c1402420b01042641d5021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 890016807 1250 890015557 890015561
    0x80a05040b0a0807090503010e1506060405100806010e0a060206040210110109030507350c07090926030118022a0615012309040b1009060801080a0302031e0c01 70
    0x7204442c001012034080103180ea8002090340050801034008100182d140300443e980c525203884210407001c409000500c190741c8202c02c98028010242000c0306c4200317440405400504240c1c0d1103404100d82201d402d0060134003d0350791044800c0d50340200725503103454091000411420003003104000c00044030190b022000d0050084040c403d6071202d6950055091000204456088c80013440b10701c00041c04481d81c8050540c2070860000001c13a948030340c00d00055207018044d601100d2402d040c40e4010060010708844648080500b030b40c81071740b14a1440802d40075200c01d000c0c1c00201d9920309982409040154090310301c00025542221100601007605410280c1d210440400c82c0d100108002040720b00400a17500c0e0007080c00c00c42c01407c0c813541603085040107a80180510380c40829120419505c0c0c0d00000c20210b0080c02c0c540c5191491038000b00548294000d0100cc5110080002070401c4001400642981c1680c05181803d00c4190202e601c0a128018059100014010080700d540b080c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 890018057 1250 890016807 890016817
    0x6090209010602071d09030307050a030b220c0221090f031516030612030f200105160e09060904050708030f04050a050102030a080a020a090305030c0c2b080a05040b 72
    0xb0307800921040c1d2400390300d0750030303400401e182d00f100c1001c080c01d20031807020000640e60000820b08015860303600710441180140450025107034401d000030130381d11030b8000d010244409104110310910031a040d04101307aa88040b1101c181981254900b0040d074240100005071085a5004140c01240741a050004c2e00d4400d6080380c00c0c0e050051402400760044040d00240c003c134299041c00d100961034204a150903020740c12010702030007881d86104990701c0c4504a0040d02200944c2c40002d40b0903d45106402004125040d80b14000000c58120010f80220500c200c5108014000700281d6030f0641807164608020303000b00d801d4441c5540100d103080c818409000030140c6003150341d850b036191030104188070170642d010f6419900700700310810441c0d42c0104442d5101c040d4540150381d80ca01107004441c58841940090600c0c00086410040680040b6403003003a46000c8907480010014404072a0029943c2c20b0b100e20703100311000c4d0540c0021008406490103003079a00b4601e00340f96681c1e5400806902c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 890019307 1250 890018057 890018069
    0x18060322120305070c0b0a02031801050703141e0109090807080d0905011109091b0f040b04050a0915030b07020109020d03111011041404060906060f09050306040312090609020901 78
    0x1040159020142c0c58441d00fa0300c104140341122040026488007128243e01801ca80d02c4182c0010005024540c2e46400c5000459410000c101510305540002d000340060800c0c0c0c0c46408101c0003040c80340c0d088094201403000301c0c81040340e40d0707441c0007044801806403100443d10800c050000e0b4000c540d101c4046c020384d191141010801600510f802801c56000360600c08010005116160079501c4458417150701c80c0c07600700c01d46001d00386030002808500503d02505d803107070000600440c414100030040e008454054030204520f988035819402a240e54280f0f2240044c0f24040420118140085c80c1d50010058000064510b91300d4000c030b80c480414150640106503420341c1c1c4402e40790b04018409002015000c00c010020200d0b401c960140700c0c078440c0034031100c0e80c2c68100101d6a210381c84400202409101001407550f0780501034030f144000d0800700046684220700142a00f4041031040c0324a0781542c0340f04c02c0031040c103000001094001307420b660f690b0352a0241070058440c480e0309406428 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 890020557 1250 890019307 890019323
    0x60825030f1a0703021908040c03080a05040603060807060512151306170c100e01050f0c0601061416080304060f0606120e01140103030c1b0e15010518060322 69
    0x2d2031840d141ca6580107440e80c070030584100b04504881c2644c0801d0200b00e0f10a2400c0c004a485500300208441e805030406800740c2d10000b101c100c0c4c2608900100200c1e249520148501a540c03031a007500d81249104200c00300b07d04020702134011400220305544103680b9040752609000d00d034081188494070034030036019190b0b01d000900c40010312850325400440448004c161540b4000d000c90840b08081c1c0ea01424040c2140c01e03204242e014400769112a804000c10ba6240d0041c2d94400340d4a201c284980c801081100c0c0f60103680005c40800c81d40d803404910b815085d50819aa104003481d80028019506542d550b06107001c0d117412800f41c0c90041c980c56403140314100b5042c03107842c102d0f9a0592100310a030314140c40c540c10700c412003044504482d01807c0420b401005414040503058a40c004000450500600807950360184910f0a014440801c0803020514400b0015201441a9003401d400000d0110400310796250040c0210380c0094038180740c1021815a40c40745036050b0145408a410310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 890021807 1250 890020557 890020583
    0x1009080d09090605030105190e010f1a04180b0708060d060f1a010c0f02060c01022809060807020613020a08120706050604050c16020315040f0b0109060825030f 70
    0x201d6000c3d900241078224020840e03410a00700d0840e5581c0e00c0f8400100c1d060b01d4031345070701c001380b4203601009901c20300741d1043c0641071009001200380501c0c1d1030418401d80c0f82c803032041040c44501d860711142c80d5100724644065160f0401c260340c3c904008001c540c1c8451025518000290140114405400101c0f0007240d007040035944110501c064040c558104445100d1003801726241030b1044007d10380540741d2655031554041201e003e8450a44841c40c4519040800031403446840d010030400181039903103036042c0f41c0b0360031300725446030701550618016807107100481e1300003c20390040fa20880c070041c919691141e451b14858206504941c0320990040041345030000d10515000350317070384004e040703504001302d19045031064064090601881054041694400215202080700e240e01d0400384a04501525017840e120f4a0340b0003d400c103c6125080500000710912103024541c1502d280c2c90140105444400d007401c1740082e9089a013506080303030070002011940c40c228005105001d200740301c00c61 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 890023057 1250 890021807 890021819
    0x3020c1c050d1509020f0a0201110a1706030a0c09020a08090a0503070b040c1805190b090606070201020a1a1f0320030a02040c020c010e01031a1009080d09 68
    0x4240035039210380002024110300c0d551940902241d6103446040c2001a03189085070f48021803054582245915500c001012540c4ca4071440c003610242085074000d1001d00610078030807000e8000c3d12813a0021422140302550402410125140d01c5200030341160001c220301c0c1c5a880f00010b02c0ea11218646a0006000d001c10344e110941a6124104800401c041c0c08c0030395030680d0728410707424080d1072046610003240c00c10600c2d030894001440d03401d41c1c244043c3c035001d22030b0f80100300c2510010308000d403190104461040c10f00407460031020042010707580390b51b080280700d8650321145003241107015111054000070200b0340d054080c60321801d8202d2052a000d140d404520081c1c40302d032140c1c0d400c004410000640c01003d09c0314200c0c1400041c0c0000c003124404a450400f25000081d809401c0036518011558002511001140300740e80d0111480d10f020015003c480d408940741050054844882940f42082c2c403004509482915002071034566482100341021001c1050f84000f800310b41c010455 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 890024307 1250 890023057 890023063
    0x50c01060e010e04080f0724180209060402090609040912020708030304170a030b0405090a232a15030a0501090b24190e1008070f2d03020c 61
    0xd030920301e0003a0303095410034030525000240100010b1500c280005c6880a041c4514180ca40d1150300c149410510124440c0c1000c03a8820500704880710340c5401e10701d8515141000500d904a0307000f4083d50920f84508050001960102104a41081c010801603a003501e8030311800c820075000350340100181d0904803000b401e000c0190300c000410781c030620503c8003140d02e40003299010441014001c1d030781c000e614026400340205100080d0301c27615000c204070342c0d580086481590349102c1d10703102c0c0c4000480c000500c0c60881d98025960b899100c0e03142c00c0d1a0403404040c0c45a1a000c03a001d00d00088000300024111002c0740c2d100051945003c0b040c4045e022440c0145400742164510501402c11391002140c3c240311819200410440200102801c40a980c004c80d00e001d01c40030554a04480081740c041d05410014940e9401014104016052148207d003414000c203032559036124000000b03a021161030f024104443c0100808140070101c0d00d00545041c40c00700d080762409030f199441c010005007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 890025557 1250 890024307 890024309
    0x1f050f0a0207020a270501030b07020d09060905190f0807090e1c081801052a040803030c1b060106170f0906160e0301090501021e040e0103060b1807050c0106 69
    0x10480e4018081040180d8801210005440309004500c54034442240b00361514002c581c04ca0f00000d10700030000c010f10944840d064850030913a000c40c1d1104440e00c200310380d0601e140c4120400280d05030000d02081c42c1c042440c1404000b4404d0403d8421381750010340c920400158402181503228480c1000713903551368007400b8400c1800d4009800c1d0007803010400c1c4010070002c000d140400c4401000540951780080c048120088040e001b0401480c005132000c40c1d2407500501804160440940c08541004560458064441690155085440314800220700b43c1003400c540c100005c150340000381c1c0c3c0c501040814000d244907620407c0c0e61009000c00d40038884081c00b05c00d02c41c441c10080200c90740700000d1654028640111504058002d61000c0307822a02207040c040d4503500b082e206c1010b201054019041000400461000500508a04030003904c00c1e40310701905020420700400110300340790310000c048400501b550355a072000e04034645449900b01c5555011400c04110034050312024031071b00d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 890026807 1250 890025557 890025571
    0x5031f050a08150106090f03230f061506040305030f03130b070e041d0604021c1b0303260a1505042a03090803060603150604091e0507050a111f050f 65
    0x11105034140b07c1c0a14803c18a03000107072611699a10030a003007a41080b42c1c901800c441c41c00d072044480000c0030103468140958480c400d496540110205601c2c0c010f040b281141e500c60011840c04003484c0410400c1c0d003009214003844103020000300301041006801c103101b10700c0755444040000001003007004070b40c426075841c0440c0d101102d12003150301000510940154040f141c0c0c600b080c807070f0982101000403515000b0040040003c0c00c03580c03a80d804081d2001d891088d02e80b401c0070f003c180020a404018500380a02131400080400c01900107507007c1303424400201d0000d00215142c1c8003107019100500e12140a00580003044952111040f04d10b8420044500e014081c03442c803626880d02c980005090f152140c400080400c1900c0014841a0350310540686000d8490b80c0d241280c0380140000c00c0b020003510165901305447d40c41c1807166503c5030059803103840c00c02e0641d07003084804070700304208000039100d5185580004c0b00d0005000241d25040310020a01d85442c00ca0400001800b80c401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 890028057 1250 890026807 890026817
    0x1401090e0307170c16090e0c1806181602010e010b010e1309020a030b040519020109090207151e06080d09050603040f0b0708060319020105031f050a08150106 69
    0x112880c08804030844221a0300400c040d461640300008088040c415101c11035824441c0715800c0c020003141542a808651030a401001850310380f03007409807aa8998044a40d00812103c004503614500b0710006d03070480b6002d4803d090192400d00f0500c2d10312810796041c43c1c80c01c0700c001c0060500764240100b034010703009040248844103010300060706210300d0000c020300c10700e415079202d06501c0d40c513400251714036001044004896604c3c00d01c0e000000080d40c2c2076500c5d0140044614400800d20302c2e1402107603060f03440440302c0749131002003802901b000e04107c0389842e8082c0036204a10a50045003039484080b0364260000c2e50010022046030102e5000112035040a200b11041035000030545d002c0f00c005881456076a03844c1d1170804400c1c0c49005000303006113001418030181a5006c0b40383d5116a000740c040b40c00c281119014140c00030300242c0f00030b0004004000040001a90405d03202d0044410038020840c0350301c410005100204540101105600501480e0240c4c29520100d60042841d401c203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 890029307 1250 890028057 890028071
    0x403200d0e06070510020304030f180f090513021203031608010803041e09020a0503040605010909020904021c0f0501020a171003020d020109051c0b0610120504050c030d03140109 78
    0x1d48480900c160040c82a007000c0390000c140803043c0820010641c010004540e00d01d05480e028020281c18544000010041c00000c5010000e40d8003840a4542089139032005924240a01019000042200c0903030f0b00000c01d06801a11002c2803412410450400746841e4900b0f4828203017021400031070141046162001080705020100880d000c0d83c1411008041e0844011039100201d5229407006495070b1002940c109000d0b0702401450107544100c00c14441030340c0c0c80851800f038440c01c2201960004004020030018038001c9170440d444d80c01300e0300c0301101d804940c842c68070704141c05000b52080d0b500000d21001710341e070105130000c40003422a10341c04582000d5842d542c61000c1400024003440305098407005680c054070140009050042c01d410100944050040c4140752115045443c2002030b008030350145040b85801b20b040402d55940c0440e5035080c101000501409042662280200c5081c6055900c060000040c044100c0d2008180c2c505900c2c80c5039000c0005034080c2c02c05600d0841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 890030557 1250 890029307 890029333
    0x3090204050a0b011e110706030f141e090c03010c031b080f0f0405070504022205010203041202061309020304030c110102070636060e1e06160305090306040320 70
    0x49122103909404485c080d060340103205403402c01601c60303d0031851290b8880002d8495040d080031103004154442800240884c2642c580514026210011414090036102095030f140061895001e03451a003110800100c07000800d0031035502103442c90020b900c4203450303902c600c06481c0c0c1103124906440c000d1003e18000601801042e4007803c0c4010918544010a09026040104502030080200700715510324103040680c0e60182d2100e0b404842103103107040013a8039800170050b14115440050341709a40e51260707080015681c000500c5c0000112010004201751016101451142d4070a46800c807030305c2890305203202c0d155402180b42e411940201014007613213600040109440300c40303c02442c3d203c03000120320801100040d58100c2644035401c8001010347e40100d90f40c407141400e0350044220120181c40740007032a144c0068035004007040040e580080ea10b0903940310f949019240550420340e0850019040c480c3c151001d0300000e030b80840701403440c54084000d82c10740107a4001080103140480c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 890031807 1250 890030557 890030567
    0x6070b07140903160e0f0906060402070c0807031a0114100f1b0b15060304332307031b030506360c0c100b01030e0d03090204050a0b01 59
    0x20191820008822a001140749404003610403480c001000d40d16038a03e089510285003206100d001c0303942c00702c1004111404c030030140741402000d4540c0640110b9a4000a00c00a0361204e1000c85507003180140010b00040184540d0020390f105104082c14210080303020f044407081a0043c0400000f04280207001e41d590904800040c092802d03d040401c409820580f200c407200700c182903012a080b0074100810200740e038030a214023480742ca010220000c1005000c12030100f103500402d800c1c0c550600960b4905550101000240b41001800100441c4031a403425208a04019603003c1c0b120318001210800e801c280030340c4404980303070401040c003617411083d164400c800b840707605042d1b5034400304450f80c42e00c1007801d4850030f4154241306100c3c440c0c1e840e84501c90364800c64903017900452010411006500007250721030214400144104001c84110000621410798441d0506a49920400341c0301300500100c604044651070015188803c0d0040c0401d030703513000b010040d54034035004508810fa80c000d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 890033057 1250 890031807 890031811
    0xe06180c07060506040e1509071e0302060c011d0d030501090513060903050426010c0e0109090507030b0d03080f1b0d02070807020a0e100801020403030905010c0c090e010603060b06070b 81
    0x10400701c0d2640702c4e140460010f00d6003480682280c019406c030034110000c03107421240280b140310101d5403600d84d205204180741d6804800700c04202c07403600741000035242c0304016080d4410042c0000600d144d8805688400c00440c3d80281c100340c1080e0400d40b1043e07014840c090040000180a00051800c00c204252010341d014006103503598506d151030505102e0381c10b85005c0d0140303000c40071031101075a0703800e52441108001a41c0b503600f8160a480315170301c9050019041407060b1120000f1a003801110700103848000d103a00105907a5540111095030303403190707094920f8000c0e03c2c4d501050511098028802d07400402c0300c1422240030764442c3c403d4122004455003070485940040e100d0810f1702d411300c00e51085c1c04000c0d42c8a1456900801c0e1004000c240c1e5001e03842c07072030415110547c3c40800c1c6090b401940710260204500e081d040100f94002c01280103034a03c41d40c0100107054a5590940403a05800400000740e0b540d000b0a02c204104da1042c4103060381c080710a40d061240c035544054450b200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 890034307 1250 890033057 890033063
    0xc041410020114100e01080a080a081302060403030306031101030e0c01050f07141507030b101d0d321b0607051c0e010c020f0906030312010e06180c07 66
    0x484486003408038401e6004080040d261180710845060244940150138424050b0040100380d0350000030744410006004000030b6441241142017029500040e150f449000b410400c00e032001502d01c1e40142e03541001803028510a4800040403401e41c02d0040000703441c014036a044c07600d40915110364250018a101003100c007440c0207503030b8582400603070076980100c1e00700501180321803a101440d4207011403030912a420800c0b80558507038905000700c05450601e55040d03000554140a52820340c1300d1050306000521130901035083d154000082901e014002c04c09030f90090300d050310900a0010760084040030381400c100315052001d00c20140781c0f2048644100034102084000e101107649804080e86e529540000507500030304100f01e50700181c00d02138044e040c0040c04270b05e2009403c1d8001d0000741061500500600d48095104083c020b2511001d031007654944001d005480c1c00c2c00c00240c1c143d000c0c03c00076540c13078010f05110b018404000000791109040140e100208144600e0340e0b020f5610382a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 890035557 1250 890034307 890034319
    0x10e0402030c1003060b130e06030a0819090e0703090506091f0c021207030201020c06010e43110d0201020f03152403100b03010503031b01061d0f0c0414 67
    0x1201441a4028812a4000d91b0719000120b103c800708600407041100310b440c414401d071003d540742e40070562a0000554001c054603400e0091102c01c0711241503070540c05416003001000740303481d800700307001d029011200d481c0060340f1100500d04000e800c0c8200340c0c1003a50300d0014030720102c20030440302d841800e51415910440d500c46804281e1031007040059110410408183d60722115810000d000c0c0d4000d1034a88428800c5000008078002e12100540c403030b0329901a9045403d0944904824020200d8901400450140c0010381d00d641040e04c910244c148079290080c049100d940801c0c2842c82c5c5070303403030f4095905c140003d100c01102c403000c5aa01c0f50302042d4820b807000700c43c400034204040030712031204581e02250002503032040d00c00065020340741407280c2505403036071001ca102d0300d071000740101034060304180640340f4011804400651198440c40010603681e440d11207a00d107070710300311128003407504549060000d80e440d40d0642e960070480c0b40c4141842c01d401c1c0b0080000d808003c4604a0084d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 890036807 1250 890035557 890035579
    0x1814210703080a200304061401060c060c0c1401020c01050f060d0f0f060c08150a06091211030604050604021201020a080712020d060e01260c01180314060f010e0402030c 74
    0x70943d80e100f00010859500b04581c14801c0030400e45590700200d0b4121281890710013200f0561042c6034600d4101c5240307a40d0064001003942da1607006d4080440010188000d01c283d0800140892a0304c0303444400e20800182c88103034024170302e400c4d540040c040c0310321030b4204800e01030b2949480c50440c0070150094948241e5807861f141001040141c2e81002c1e083c9440c01360001318869010745414003400c48640d0342d240c00c10f03040c800c00c1030320030f080d00c54880403d00c818810041040f0310041030600341e00070260b4142c0d840304000402c2c06c02d0b00448085900750444c00c100400c514041d0282c001e00c000b034600031410645c915401400b2910007500c0d201c00c1c006c01800e6203803045400c0e01150074010107500140913483e41d55400f840d840034217001c1c0c600402c02c14001640d40011801c141011400250001c1500c0c1c07030180c00540b204140900e18040c82c6804c00c1011003c10f009548819001280000501c901d01c1c050070340c42402c07003042c1c02c49000400c1d01b0f803d1101603a0001a8040c948104441600240c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 890038057 1250 890036807 890036821
    0x15170d09120209280b010905010f0c0b0606090604030b0604060f0b09010302031302030a0b0103231015080a0807110a08031206130e06101a0715181421070308 69
    0x20340110744000c0071132054401e0045150803608050001d11302a00c482014a841c1c100658221072007200e00b0303000031800307104000400d01821010b604040007030b1026140002101c042a4168402c1c0c00c20b0b100c0c1c080d6141030018904045c41444010220120b00ae0342c828201402c8800074072a8642e414105134010000c02c690b10352010b00e041d6240da000b02103c40000552810480d622424403080c0d40d1008006076600c0c10110320258589101e8688019080441580c12000002c104401710a031325481d0400000c2008a000c1268061a501800ea0180c50b01c030681b401074203988007000440d010740b440701030030807000d240082580c40d60340902c542c0955666400c800f060300340c0c00918138000407500b815410016001c3c0465598059050180f038244690380b9600180e05948900b407080c200541c003000014080b81c12035403841508540070b44046a50390110300e00c0e542194034444191507400044800d01c0c1d08560820040300e40d50340c0400b5015401951042d201070301d0042880c040c00784030074a4005003030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 890039307 1250 890038057 890038081
    0x304060209040501030b0703050601050901051b0705041401080601050109030209040201030b040b03011b180e1b0d1e0b04050105010813060b0319020a0806040c0302010c050115170d09120209 83
    0x20700300c00680204855a940c1c02c0c84501000144e40d0000441e283c5408540785500c03c01c216940300300103031201d0307241041410407036401c0c241c0043c0f440b40a006500012401d5915401024030071008041003e01650410f544141440c4069120505004e64031004100507180c541c5459071003502401c0c009220f028010104001c0c1c0031540d2402e5040d442c3c803150204110b0a850341112140081d40e8180004414141010001c910303801086072500c0c80c6000a280452138248100486d200780885605215000003803101b0b5446460742e259a071403006540e0708401c0402d110710302c3c06250448051003954581000a0210640541000300c0681c124184070144041078201c0422958058101c03008000340300180c04e801c1e040204128415080d5040002d0308000c00030f112800741d40c001c003004007102d241d5401910401155101162655240d045503940c08500d601e200008103074240354074104408400d2418206100c0032200c03c240060b0420910280802c00340b101c02d62603041d1070b6510140c48900d06581 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 890040557 1250 890039307 890039317
    0xa02060114040e10020a12061406070503130e040b0a140f0c1b030d05010f2d0806040311211911030a09030204110a050d0c090b0708071205040602100203040602 70
    0x201803180b50031000240061368000d25124000c0c1d81d508104003a6195108107980483c85143c40007540e00c42c1c9c1d00b10903d45035008245080c81a812285440a01c010144c960310159106410f8080c07003108000501090484079076101e4a0140200100003142c6d030401503506010301030700e8000b210100040c498168a07411039200000c005081901d0622a103881a40c070b40c01105000141d80c2003100009805d81d82600791402d0b00c0e1040071483c820b03c13100d0000380c40041b43c1002030300500ca81c80300000780c0284c02d011190095001c2c0c0d680044004200741003510707110140c00e41c164010403559186680c881050251040c00540d075106503940c91200d44110784042c540503a180b903a010026030708105d01d4103c80078000301da200355000c0c003010070dc040c0d08000034010101c0040c0440d0040001000080540e4020002c203802410156041610344038210060340100300c0455001500007209030504c8100d00b002819213025242c42441c050030058000e440b280d030380e09a40c00998001c07012030f040040b00c0d01610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 890041807 1250 890040557 890040581
    0x9160c0c0506041e08010209030a0620070f0302060c0a0c0b04141504031404030b0612011b020c0a05100c080c07050409080910030b01050405060c19080406090b0a0206011404 76
    0x281c4858076401a1130310200303480d070340000544445100140d512018001c0d10907200008015006071007140d20b40030060312551b80d052014a05015456880850381c0014018880c05040884a056014078001c1c0c90494007800302c0140c4a4284801200640d108030f80d0540075901800c1940e6075211858850002e104210740c4113072900a2802c640410703011403a42602c07a501a580d111591402c001c1052104c6c0320b2400080c024001d91030004002d824030b030068442404403440009680340d83d903050b0704043c3e003003552103d006030040052030f80545018000f25018102c200e9921403000c241ca00090940d494016005200d02e4003c549602800014458a0300900c0701800900c240f828528141c005940b2041c21240704160009240300750500c20322460340c1141041e12051322709402e000c20040c1c1c50300846203d452502c212a0062180c040b007100a420540c421940652258201000948841d03040d80080c0101031051065040896001440c41c3c1101d01881c81303a00304100c0d4001103006804408900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 890043057 1250 890041807 890041819
    0xa031103090a031202030411060c0a0209010f14040b030d2007060203030711010e0a062f0c010605120c06181908161a0c07051309020f09160c0c05 64
    0x1c507000c200800c403410726611a0307440400c192100081e036012404182c9000c3c00084860748054440d040840c02008aa40323404112003d01d1981d41c005541503d00b6004840e41d00a040c1007084000c2c02e40e845480c1000080700c06000036180c1101280d5280042c5000000700103142113420110268040f500c00d11030952000d40d0701680d12514040d40da079109851000004540c0540890789420600c610320810544d03401501a0001b0780c0c03a810050315012919114010111384c1d400c2060f2102c001680020310b5126205840d015180982070031140564000c42c01508070841d0f5803840c1c2400700301d8030b0101c1e0080720f0007500e07180c00c001200f085014000b08650060580035190902c843c2c03041c03c1c60111851a42103076100750701e0305081e44071205248112070b48580c02840c2c1c110010100c0014000b4107104600b01c4400c0e40e91400010f0246060400c0400019035a01e896415403c10710225480d4a40a0b070b40c00c3c440f42089030b4503503040a10099103c080003850001a01040402400003004040081c02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 890044307 1250 890043057 890043061
    0x100f030606051309210210020a0207080c0f0a1229151f0309061503150c0903030915021002030a150f08120a091a07050c091b0a031103 59
    0x1190300182054000c0078412028840e185a140306180140d2030a6680403980455541c1d88212003140420310700b201805601401980300038407241c501c05020300c0810396008001040c82c00399000d0030702041d880c0c8107003d07910040c010700b440c1c1c4900004004540402e401700b403041c2d0290400800d610280c1c81c1d400d00c0c5480078070307404050707920300d0404600500708043c00022a101d07180410810302c4a40c0643c1104455400a10314032500a502480390320380110b10219980b00d14032049807001c0d003e504129540300700d500010341141680d126245412a150034204000390a54030b02401141003441010a084000105800c00704d109100c10481d00508040c25501c0c0c2c00c007020300c84040c244130043c00030301a00d8540300103108017a028030102103d91810107403851a03400402109251b002c085030b90244604c2c030074002444c5410308030441003003030000b80d25512a0380c036103051410504002c055078400e002060a021950354004c1203607603407110150029541d20001001134001d84552071040c8040840401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 890045557 1250 890044307 890044313
    0x51b190308010501120e060703090302030403120c0b0c0f0702040902060d05010f1a04300807240203060f06030720070503060702060403021005072f0d03020403020d020405100f03 78
    0x28480303050f5402629420001101030510004999184070026050f50141d000304100302e009510203465107000b4030542e80707066100d80304d050306074040d03001c1c1d440011a044854001d102c2c64004154020041c3e4205510300f010f0038145840c00d01813181c019102d1581c0d0b044000442d51040101c034184643c0b0314041c00a5a590b640658200c1a64864074082030f51001140342d000240108482c00c0ea4694483c0f4880061100c12000f440c0e11021788810407026041201d078003040c01480900742d07042c03040c0f002d0100e500803101180b0020f101e244120110a00600a01205590b1400d045034032010568a0300d48950381c5c01801c0301c600720f402003580c02c08180066100d0700448085504020360710103030110b8050380c036030b504101d07560207049501034016003003940b040d60f03500404c2d00b1140c0c00014510340001481c0501c00e001080a10404080001003240945c20800c04000e2020712000e19a50a045007002c1ca1900031804524401c04024807070707903a07580024841c01f000c441600103440030074126410365440e03203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 890046807 1250 890045557 890045567
    0xc03090b1c1a1201020405090a180b010e041a070f080a0204170703060c21090807080f07061a030d03050603071a030702070e0c044a060907051b1903 65
    0x150065005400071044034050b00014006c49003140c102400c40e000325550382d200d00e401404c0303030a9215008020401e28401090355140001c1c0684405040203829003403030319022003071500500301066489200b004101d04542c0211001d82142c0081c01d100c042c2da0303222800b4078004e201e550048100c90854420002c10200000382c1300e003d0320310885040009040c035007004c1d61100799070481d040090040e41a482c0c0d40c40d105800241e0914411414141401d444e90b40320215a042820184035403040487d80e401441100e01400700002c441d403004a80381001000440d03150194041d0b20014981c40ea07000c1400c030f45003040540001e003007d94800c0c030f0030758800506511640c001d031640001031090040110300c1164040d001c074010a4404001031130945081e588ed0748040304060801002045155071003800d250f000b04402000c80040180030f0f519414003c3c040343c601e0080c20752801800c6460420050342e41100844400030040c1c07500b4600f9030b4a0200740c0b840c1000240d41184a88007000024017015044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 890048057 1250 890046807 890046851
    0xe0a140c03010e031305120c0612040b06041a0616080309030403051c0207060f02210c011808030106030b0a0909080901090803090a06210203010b0909070c03090b1c 72
    0x7100280001d01e82050641c1d540d00840442001508100008001600c0d00346415601e40c40741c0c0003a07440c0c5000394800070b00b05402240d101000440e07418101300401c034003d03a840382e11140881d41005604d80328450358401d014a02d00321401050002500715641840c00c0074050000d40c004401c13503491502c40d05d0140c4940091000b202c19120300511030206e25081c118003c00442903500500240d0300c5e01c0341c00c540038040300742c2001c20b500500841e6000391404100c046a130118102c09580d0b1070a48007856402c44801d12036100c2c584000c0281500000c5051040b80d0440d1094900410b007000690002400e030610390384448802854088050308001e650405002c032494241ca54070b041d5565201e00071f85a20404102d1544498014424081c10340514422201c45070701c0581344142100f03081040c01240c0c820b03004001170541c0458020801d203845940340d9030203c85813400341d5425a0f1560040c10310f00a500804020420108500901100c2044c04425121020320240701e8072072105000d03900300b00c3c0c0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 890049307 1250 890048057 890048059
    0x160b0c10020d020d0b03060c0d0504080c0a0c080c03120906210708040b011a1c0f0c0203070b1f03200406060f020c10210f02071218180e0a140c 63
    0x600c610b0700d04915000c00c80c1f0784207001c4500600d1a180d2400189802010000c00171554030300c0c1840030620303007a0104892009203200d4000112304504122010b0b01d850041d40c1c082d40f20f54000051301c010400b0a4094a9280c001035403005c7c1c031a0440340c0701184c03241d1036084d040360310301c0400c081210383c59000c2c0c070700e40c006c6010f08143c03d06a600c40105801400181894044601003005200800080070040c040800088000007403030003130400f074480503101e41e001c140b801a40b012400b681070244000d05150080b28920704003404500c01c19035012042c0b11444050601c8402d40a880301d07030003034407008000b8448002c0040049540306c403400f409400d1203242810040c840d0142200040c24034226101022125440c3d603a411840d00b0f45820302c007030410269244254a900c8501c600d034060380043c0041c180702d07540810140e0802c8100605c02c2c602d840074840e220510400803c4103040c8080d11401c103514109021865075010040d0a19005410074002d020034403d0045079450300000c5509214044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 890050557 1250 890049307 890049311
    0x405041a01080c0d08130305060c0403140601032414010e01060806041103150a17010c0f020a030c02060a1806031a010804020a0e1806091c02160b0c10020d020d 70
    0x1880c0e215107a0381e040c218103d950800651007001011549410180055240c1130414442181c2c407a5201e0303080c500d041e26901c1003c28081000c2c0200085440500c20f000e0000001780030329071564540214180c5000300100e461312110143d01c1d640803050300130712042c40c1e0400c0c48030368550355840c01d61400704007403003504005203d00d00401d000c1e103400d0180b00071403141c5100f028110345902c21410750454081d614550b112201c540e0001d1440500f403005404040d40c800001060041da0501038841010401000b0440d0490380c0c000d80000c1d01303c01010015a01a500c00383c84518104054920410941503d001c1c3c84c00d44800242c181c0e41900102400118107612144c0c00820100550344c01209803402076002900c1d800c00c0c82501181a0250360010171100c2d140d08400030314852908000701a5041009604000c036a41303580134101456103503500043c4010040ca014644400100e0a00350003642540c0c0b4000800c07050040c000c002c4140c41003802102190b1701c0780400d003010003d500690030021028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 890051807 1250 890050557 890050559
    0x150c070b04060f0f0e1905120303090f0303090a0314040b1603090b070b0f070512090a0b010f0312030b0a0b04060507020a0b190e0a090912081005030705010e0f0405041a01 75
    0x520a00c4c255081180a4581140701048031041007460220642816988904100c0010303407540e0f01c00000402c40e00410140d5034034244010002e0400c02e40c3e070440b0200740c3c4100b0900104a10009d08001c1c62500740c0f5040242d070350054642840c174411640441800d150114824200300848034041001d58480d0f10b03a000b00b5551490910b0290080e108050a060301910010300119006051550720000a151041c944403940010086200081e100d8036030319840f000910b0108460310400038050300c030305c50341c0e00d044030315550301c07001784000806200c4101174075500040b1040d140d0a10520141c14228451500c480d1503104c018102d8101c800c069100305a90640003c211204404a9885100882e900b8100854505060300e444a8200300160050030000000404e5980c6200382c00b20244619006504aa52844001c01880c0c0c044e1040c000540c540c1420449030380c000662004a680038240344100008607030000303200095a0325465082070404082000b0490b07040004000d1010f1003010340d1240e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 890053057 1250 890051807 890051837
    0x1a1005030106081f09060504050709060530121803060c0c1c0c02060f0306010809010c1d0303040b1206120c010813080c010e0f07091406150c070b0406 66
    0x80c0300e10380304441c400e0b04544104a4500e14000c020400300d10a0880485d9006440d40c6007002c0f2542181d00390f0b010342064a00b401502d8181c003903030004000803a0080680c071602442600b010050b000130080309586040301c42070045052080300000880a60aa5100d41d0a02204851084100c804a10a00404000440c4040300109640341404c0d040700a0103100f00b078000c00d03441d00c0c020f0b194010601080100d40c0d00180d403164002c05094030b51138030f00c81d200c0c207280c0005800d81001a1100a0750f904181ba80040c460784220303030001c000140d071581c64410341da0781c01003821481513810400582c81c00180c040f00308450f41c0000c03401104252514000c03940084403860300c4e11011846d542c00076071144046181f042e540f505265280e400b807456146018242c510b080d08450180480001c1da401003c12800011028083d480c000d01d420402400000c040030401d400284000304624890891004c0e40300c040000002900c4014910300d00316001c0a80b43c20904115810600c40c03840054070b414020140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 890054307 1250 890053057 890053061
    0xb010f02030301030c031e0c09090317150f010315120302070f03050705060318030a210b0d0615080a0b06100504050306130215041814060607030e0d1a10050301 70
    0x102c940101c0794400c41c5d400d658a40c484400b580382c2c0f101c0c404104a80f0384020414420144d002081164030014904206240c09400c4030411001c20f0408007501d01007003464014041c400b003020004480c0340003217034900380040e0300501c054441e8001580014a02266902410072035001942c0a03400700e0340340700c0c0e4a14a141c2a0300071400001c0040d08030800030811820200003a5401c884d00700c0c1c0c0034218500c0050507a10310f030808007180c4001038594448540c201d03070a072110000188400c000344400701d89440411a051615503000304913035039612100300aa05103800c210068135440c0165480802c20703003002c1080e0b00302910a90302c00c0e400074100325801c0d8002c03000c48040300e0029016100545d07501c0207070300700c000f9450300c01d0307130815140e410603000d000a0300018030243c080c1100c4007410240b0745210030210f840310350341c40440344070301028050035943e9882510411b035814030b0280a443d507000e005c15142302140700002d04040d441d00402c4001d0700c040d288248203404090340001450b0780c62041500b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 890055557 1250 890054307 890054309
    0x303040501061505182e0f030221040f050d0f030b0a050a05060c071a0c0c0a08060415200a0e1008070309141219140f0a031805010b010f02030301 64
    0x40b8408001c0070400003000e20b048074074500000c044015928600c0c0462545d440da006c40d00400301c00300400ca090440e040200842e51010b01d00c1c0441c24a0682100400c18090100003440200c1525001800b00210341d528840c040740c3c4481901c1c00c40082282c00b404455075100c1c001c01090030003200403800d0034405d10102c100c2d407008111160040c42d14050000c1984000080da0345800340b0400442c1c50314001c030f215440111384825041e03807405503d00381420000071501d640c0c4640c8144100b0001e26500051058105810201821001102c004c00c80300a001441807404480c09a454104070099180054004102161100381701030000908000d1000304044000d070120747c11034081081d01d84681c2c00b07614034511901954a09084003407807181381c201600c0050715a80b000046020b10080c041250845000d8a8143301c1c1d5481c82c044d4075142035008040030350f003088101041c05461644250407440d03215154000d503078660b40b003c2c10700e00d010b1b140c503240e540c0c04200c049001401c09840002224 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 890056807 1250 890055557 890055599
    0xe0c030318030c065203030e010518160b040e0c0403060e010c090915030b0c0c070e07022509110904021303050106051c0809010e1c030f1b02040527030304050106 71
    0x41c110701c0489a203000103150101046d03040584d1480c641c210078000f4483c441c01003d4446e2070010188a01c6600b503c1c000b0900d9030b518800c166084200640744006058070309540c81c6020600440d41c42c641c408100380100d034005040035050404d04040b150040d0300088502041d43c2c1c82c011a20b4440d8440000d0300d610180301c030394009004c0c1e802c01c00300f0010741d505500072880c013807040d140640358860a0715003002508442c44402d60202800311507901003040340e108049940307e01d401d074000d4160780b0003a070980b840b80d003c00a40b511046c080f445806401c9500303103c0014000c41d12200902c1160031004142e000480d02c41d841d011340410b507031801c850124518803014038000c109040a0340d0f020324642140c1d2074a13040c0131f0050b1141180e65a10104603032070b0410441500c5010050303080041a800885107801c05010a0502c14003002161140b403070500794040d9008640c546495003880d01c903010101080340c030150898450172040034040021402507000c1d600034030504c0d441d8503c42c0c181a901034440c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 890058057 1250 890056807 890056927
    0x2701090b01030605030c0108040c0906090b0907030509070b070203120f090a05061c02090406030816050d0c1101050711060c030406080c1216050d0f0507030e0c030318030c06 76
    0x100920f0740c030036024a40c0c030074452b20203030101c161381d49a40029141030750080740d2402d4070b41524010b541001e00007694803651529052182d82040a031464a6402900070310200b5500011400103644040000ba00b4031400201026901c040030441102d0640226020341d220308000d0b80c0002e003900e0848241d0303007204455001041c0c42c2a01c004500c00a5100e28911a001520741c0b400001080c9007a0252000c180c0000342c042e40e848c0945802401c0408261040c4140404078140502044001d80500c400c2482828034030f5036181582001d441565031291016440580001c0500d40d011010001d00102c0b040c03030300c8055250f219207524445c03d0003117141280a81007200006040e4004101c005a440c080509203a4507003a00c00314040300b40c402a01c1c003a0300702c1d91140d0500240c181d0601c1404004101c0102030a612049040002e40742e114211100301c015925868290070b680e021300c03001d4200301000f84019601c3c03079414100908600b60605107001c82c043c14448600d50613030000f207441d0207109034420b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 890059307 1250 890058057 890058073
    0xc03120903051e0a120f0915120f020c160815010e062205040f11010503091b1507050604120906050405040f1806141e13022701090b0103060503 63
    0x79400c1042c0340143e440c2c5903889400307080804121003000400491700543d07281d6000c07051a20014100c85550341c401101c0e4202d81c46c61211181d4011031441c103054191002055001645984002a000d0107098030071600401081c2803903181c04086440490b00d081094440498545951019003842441501c1c580707084803000400c24070f04a54400b0002d80740d62281e50540007849156021503604480c2180c0c0700310b90403003500a0002448802c03225500034a003443c918074101c0852612480080d003091050304580c08d1662032646d90071032807840349881041c01612526541410f903600ca6050724240e45116110290032022032203601744009640c9241c80b040d241900e802c041c00003e1858841d05588a0340d1030f00800e2543c407002114140e4140941001f0480c2059010402800138026040003403160000f01800701a400c80c044072548003e226000c0b054101142c000308075200e41c00403007003031020412500056492011ba01c4541a50807803101001800318640040d8200c0720a8003406031b055025402d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 890060557 1250 890059307 890059333
    0xc07150f1d060c15071202040303020a06150b1c050105030c0a06080c0409050a0b01021006050a030602130b0304051506010216091a0616021912020108090309030a0c0312090305 77
    0x100c501007804018054525001c500c003a090b04102c8012068151003840c4000e2040342584440803000e9600c164030114075091942e41c000c1d42d41c0811042c0200500d40b1680c3c04201803611303c0c141e400410101e401c0f15039503081122030001130ba90380c2200d01002450074001160b81d00300054030350398104000c0c0a9200c2c141c14454140e544280003801c0c00b091a1080201052603485805107600411042e00041075080210001a00b80840301071301d80d081501c1d1480802c090f55680d10f8404c101c94100d1b82c016942d901d00d03c5c10300c0460310a070300029500702c0000305000c1000400201c4081070940381c042110304e900d4120049881d400200c034403c1400d22010b0091000349010b40c8021924000207101d4032080d8031074000715130b240d005180c0004440440d603034164194240050741e14000e4030048405501d0a04000030445101c0092070064100420680090714a12041044070442603004040b10070175030b0b00d4a0701c1800e100b81408115881c05c03c1c001200400c900800021094907030100280001a80c050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 890061807 1250 890060557 890060597
    0x60201062d030b0a0b03120306132903030906130e0c0405010f1b020a080d0e030708250e04080a0306050f0108070815040212010504060f03080327030c07150f 69
    0x5070604c80340a44e103070074600c10343d07400700000300540803000300711034032864020f0810506001e2149139030159070900c80f580f110407054003d54001621000b9804c1c0426411501091071405001559a00301c000060400c07152882449448111752814103406c0d400e6641c0c1c2d188100b0340c09203109050100e40e06840095545024200b2500c0400010301d19000d0b6010700e800180700c5006d56807240c0000e4011042006210341e000e420084000025002802544d04c0c2071481c9980d80d440c0203c1080c0c0020300c50300d41c0c124000508102c0010403d070b00700f805960a03d8140358180d1b074880c0b183d080100b07240810000325802c100c00035401000c1c05031075810039a591140c003602c940d00003d2080d8070342c0d88401d442402c0d0b40e4413480a0407082c0381d0041414140d60509050104480b502c1d0010254104864010000503403408212640000241400242d190220b41075101415804030304850500000c903401c2044100007400504071a0700c4440d2052a072201c40301a030712900081100d030005007004510024100d458 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 890063057 1250 890061807 890061811
    0x100c0f03030f0e01050a0b0a080c0d020d0809031b1e090a2c01140705070b0705281e1d010c0503070606060c03020f010c051b100204060201062d030b 65
    0x400b000700314120541c0c0036030708480085030700860075503841349100c1103801e1240c200c001400c0244010102c2000210003d0384017601448002c1c40b0b007411099180410a000080d104030745005000c0b01e044c0310011aa0041c00e841c00c0d0501070240d500d086104a001d06122090700c203584010703000100a88405982c030300580b9012401058105400070500103402a0b0521400c081c1e1122000040350a12107110101200d4050842020407005004a1012903041111243c000d8114240385d03954218002c2220351340c0000441f01045a4040200d14284a0b005141005800400c4200c5688680b181c4010345039522142190400c4031802210b00c0f100354050300000308a18000c0080301d0400c215650341005545040d0030800004e00c515010b40201901004070b68111202c400c000d110702420414010138a0091407490f40207810100aa46840c01c401d0040c0441c2c03980d100003d541d640c1e190b0320061b0280845100d51010201900c03080ca42c01000b03215882e0070416004800b90b030b00c0385940c665450007140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 890064307 1250 890063057 890063081
    0x7051819210204060902040e0c0c0c10050c0606030f030409110f0c07080601080a0515040f02030a050f0d0e090403030203040314124302030c061302100c0f0303 70
    0x140a001103040c000715003040c400c0000d00d00095042140c0361062009884503a40b04072529401400280030308042c4200e616400310902c40d03500d40b56258a0b0885103021700c8070403882d41020000311800c400c2603003c8000d05111151344101c030b0b02d0b516201e0905a42e61200c03211800d46400030700c821b1110240541142100a0140c011581801200c4650710005d45c08502d0300f056540c0040340130011004188200e5005200c0032000d05806406500ea064032148440c00d00d41c2c1c1c01504100040070000d80b000c000c53b203960060215110020b0f10301e030150f6980546540c10100e0300c46c98040101e114442d00c1c802d020700c1405031601c149603c8590b400d0707000c0d400181c022400e00407000410f141004500b8007903d000b621b200e00c00300e100d040a0380384002d507802520b03c50403001407050303405c0b00703410601c0c07074940e5120707114803504215515180007281107025402982c0b10500032101030010745200d90301e203040010f000b03c07424045071034009001d98800143c98401032050b41c000201c80f000c070b4080e5209000c8509 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 890065557 1250 890064307 890064349
    0x207051009081902012312060a121a011a0708030907030807030906120204050f010f141611060c120904060f030b10140604170c0307030b0a05070518 65
    0x18842c0c10301800c1010442c1620010b00c1c0080a2005540c0e02c44170b02d500c105442042d00310840c4985602c407021303114a1510507010090040482c145880329911280281443c080d205c00c602c1261a241c10b03008000030034400040444000030841c12405000207015641c1825150b02e85031703035541d5498042c3c00040c0050060b00030000000f01081d04038000700304040c401d5407840100c17418081c000d03100038051080303024036510500c02444552509803a440c3c481c1801d09103050a0701440b038040710f000c3c0f43c051101e00341c02c20118003500e03060094203201048502c260804402c81d000b0384103002541c0529000c0b8101039100c2e401c1d040100200000804541034060404550b25031691a00140180e40b036104540c0f0400f4402040b1a10880000142c040d01014502041110b4128002802c0c1e001d20300880410041c5554443c58071001002040942e9030080d06444046981e41444200844101d030030001143c1400c0000b85034a103d001151043d01b00c4000d80001120f5103814840c0803640b010341d40034604 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 890066807 1250 890065557 890065559
    0x901050a2619050702010203190b150c0d0e0906010e1513060809010b0307030c0510030930030531201002061605160605010305030304060b010e010207051009 69
    0x184002440d00c51080d10700c251003020b0700601c804046942c000e0a1004592051042c03148006400100310510403015a010401c0800350000403141054891081d80c1c400000441d80e01000001c11080180045030300e0340c11420b0341d450300340034590100b00c510a00217010900814070b5840d000300510b070000310030707164030b07040c85c2c00641041d804100369040000454510404c0000303c82c024060ba28003200b0a0340500440351031641e0361040801c1d11f0203910710800c0d01c400d00300f000318482c0d48005512500940640680300030b131322007501c4c0417140321101801001c0900510410701d0280c0641805417145011800240c40a03d01c003c0000c500d4020144042d00ca9450680225041740200308940cac50322441d803c05004c40d4820000307004000c40c00358040d50403940400c60705030303030440d40d208504003142007155882e80c0760003020440c50340c800c0f801081c50f03260800100030b10000001440c4180d03ca401d042048290040055610340045585680180d025030014000c0d410000180c209821160401110403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 890068057 1250 890066807 890066867
    0xb0f090a03150f0501240915171e0a0b1c0c03060c08090601050409020619170907030c180e060c12010b07150e07050406080c030114060a03110a0b040e06150901050a 72
    0x1a03518160031000051f1079120449440180c0c95109e60881240710711920f00d20700c60f4140f03d41c2088010701404c8182d03514032030b41c0d59680301da48542c10301e041e12205108641c070b00d03403605440c1c1c000c0300e01065441502d007280c0036054901074401d09006e0704160700204100e0f841c1101700005099080802c90700002c051200c400481051410b01000180329110424aa120101e54000c5000e00502c1440c040d8807003e02000401d020312007040540344160742c01c001c1c10803d4540e030009800107403081c060600c0b50f802048800e8020802600070b002c01048080d800741d0b81c4400070903e174000c3c818080c1c141c4169011a001d00034580e401070b00d4100c101c60a58401c01d59500010781110400c3d402460b141d0440d400c01c246c90728080c8103540c0640000c124592890a2030340101c0e010f0400344c04010240c82c8040d0466405a40d00e4002100034034902d0074460390360f901c80c036010102503400c0d00e0300c0380136400318024024241390400c107840c44600181e44035030a08104000c01c40b0504d118a040f030030f421000c1950b0310700e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 890069307 1250 890068057 890068079
    0x10f05010e040506090c010c140313030c061d0a06082e140405040309030308090a060510150c030212071103030a02030a0908010e06010b0f090a03150f05012409 70
    0x280841c1910080c24074050902d00d041030340003000045160480c8001135020381e0800311040500c0c0e040f0060811350901c1141c410301c1c520640554504042c400207000003045482e00c25175058a1a5540742003e803403018060b80761888400c2052135101e07501d00e200780543c91083d0171180d807048032486000c6581a4041084003070744004005000b11464194050020f070001f00040d03c55540191010429868640c50040201220740001020801d2080100d010541d041083c1c40809030045070170030590400c00c194000600c15032040e1115501c801d00c0102c5018014801090300c6901900500310012101400400c2c0390700c00202250400c441d03d90401d101e44040010303003482465a00115540c4c034070b001001d084001c203940300005d0340c0c2c14902c10902350303040458800c1c11070b00c0901002d62039a10900450255005040c1d0300c58110144002c00810304c40c3c403000041034000440d00401c0308091407042a4141c50003401440b03031203602061450300035510360500c0b070301d0520607203454101180c4403c4220b503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 890070557 1250 890069307 890069309
    0xc0305100c0e030705040e12030f041104090512220b130509160521070f26011a04050a030b06182403161d0604050408040b0c010f0501 59
    0x5460390184208068086052284000411060a2450140300240c00080d038074241406010301031600e61380070303141490080082400c0900d9181d601c1e5117903c0c2042e004003200804a50540d06c0004180840059040611038040140e4101024021541e2011821110f0740e20503401036075400d40d2508035681500070101c007503000c0c10280300041d81d1031003088840c0503040765a03080140300718980000d2090b640790403090b0f101e90703003420b00b005500c544001580304081084220112560340c0500104a1100e41c0440741c0740d58945281c07103030b80083c10100515030f403c0e0008803081070b0714040d2a0052191036405032040510000218a80c1c2c5040d482c0c50100d0a00001603104981e90403240050044038070300543c403a5403d074000382c0065018640081e58440c6020301141221201e002e0601c404c655882c180f00f00490603404110706c2170703610f03a11170b10442c1c4200030318841c01c0d26000001c08182e4a1401d4000c080c021a00890300c5070502c0e00f000c01c080d115500406219100307660b91801a60707003410701d0003024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 890071807 1250 890070557 890070563
    0xb0a09020d0f1b050a1b060e15071b030e240301060e042702240a080a0b0a03030807051c0209100306033810031a0907060f05070c03 58
    0x302d02c109441801d0b0007035582c060304260702d83d907180121444056000f001d03551028010b141002d0495404282c1c02c2d080b0b40d640030050007450030705514004082002600c055004440c0300506003a07660100300b107403504074504100510a0000810708003180c8203500001001c84028400b01104054144607060303445c2070f503056017851002000400600c3e13046503504502d4881964103100340901d8841980c0000072040708141c07041040b00120095450300741c030003402c000c030802d2043c001c6903241a100c0c240d0b4000d6804400011400000105141c10900841c00080e0006c4c100010351030460350180e40149004010b403003089030030700400603034585407a149800c1c1c0d42c0020005036070b507403140c050002d8045120b8444040c1402c1c81d00400c00981000354550100e040600ea071140701c4248030030703840c01c005480d48041914003000d051000c8210456440300869206a03282010260303849000750316504120307a002066002490100100b50140c20903400a6106103403003494601c59a0f00c40502950343e400a03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 890073057 1250 890071807 890071811
    0xf03010c0e0112020307120203040501140a1e060b0f0f0d0903050304140105060a150207050301061e170d260a1410121b0506040801050609010b09130b0a09020d 70
    0x140c911943c0100003408050060a015495440c0504003c0c000e030005034004203200d540080024103110082d40004c003013111501007010f540c204032544601501c0c8003100c8a5206405580102040c2058481c1c64201e42c03a5510b801d092500404460386160010a00d00001c007408008400000f584c0e4800e402a80303203e0f8552a4403400d05040080c1c5c481901c0c4190700aa81c07502c02807150a5540300d450310101d5102140e03905604290000403810000d1b140c2c03020340c0640c00e0440c00308000000501250881c405d058000c03101558803c159160040e40c100410b000da0031002034041002e2007a8078101c18819000000d40c00d0f0f0a4405481c40f03403210440715203440503a100c481480e119110161142c00410283c0e00f682401d040103000500d24100721801030a000c0c6c861102c1604040c0c0d00e440c02c0041030010501740d181c0c0c0c3e50f01c0c1101e010384011a28144908003040000c01c000c00441c00b46e030513040e0082c0c0341d031010b1000744042500400c010510b65501290340040003d2146c400c2c0010080003002e0240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 890074307 1250 890073057 890073077
    0xf0f050d030b060301240908030a02011a150a0c02060f040303050d0b0a0f0512100606020304030501060f12020f010e09190e060721090507031208060d1205090f03010c 73
    0x200508481e0340d840c02d107104501c02c00040204c0020160709032110304a40d40f400495030a0104240d408018035408440240008a401c5964503010361110704204800c50152481c2f680040803c0341d00c1e00f0109402c0203243d0140700e0442c00901c40c1e0090012a80701500711031a141c6021880b1a81b40c20517801180001e0002609140c101542c0c05010000403003602e081c9241d81c1000b61001400b00c1c03c3c020280030b00300d44045040f001000700001030348000c00c04420400e2b01d459100c025105d91040c042600c1d076600f490350000e4200060f141c59000c550460342d044202a440c1da0801c02072180d002240c604100c10651601d070241d4600410074003e044103025100c0001504210304261200c0c0c00c414905500000304028803207030061000b88213038400600312600d80c01000d00002c001c180242d0701030814890302d0400f0007009111101d001c1d8042481e01c400c0310940d04c8400b0804000400b5200406610380c01d9807041405015030060010107000400d4501001a50340c0031a00f100c0354049507100207200000d0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 890075557 1250 890074307 890074333
    0x10204030b071e05180a03060908091e01080c0d02091e040b01031a09040512030a060320012102091203070308010b120402010c02060f0c0106061206050a030f0f0f05 72
    0x104030102e642c8a8889030300c3c6800324030070140c00d50080d1540148200c444501700300481e40c507030242001450340280d0400c81c0c0052410144895000070010034091001c5e20800d00d051102d44a40d80c40e44081691200096640d101e203c0840360031032169811100c1c0c0920401290340c0d110000a41e00c0c04140380f42c0c0340c580804408000c00c4c1c410140c05541450300c1c00346031034405036910096030f102c0901941c211f0165211407520700d1130444102c112800c3c07010301100b44811501c040d04900200e03406000e00c0f01c241040c5007000d0700e12056200c46d01d40425500c6000a4032408180003807800c0a070511001814003a20002280d01d030002d040052556407c001603550805030070018903400b6050515003a4100b1003881a40d925403003000c0c0029050102e60001d2004641d80e4034202e44032040100400b540341c0c40b0300c1844901805140c007803c408030700a10007801010b5140d200303071011620300a03d0102107600e0342c1c5544464001e540e00603506010244544000300b01d0500311580e440e44160010100703810184 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 890076807 1250 890075557 890075567
    0xa030506010e042f040314030711011409040e010b0a0306150b04051e06190c1a06012a0f03020609060f15040e15070e0a150f0f030e010204030b07 64
    0x1401051040c0d2a15060308102500c031207100304d15004030040c40b8002882c00c0d00d01d442c10b01490f40000c0035032040352912070041901001070007040d44100d40d00b070300b010100d80041d250441c0411050036140e0060107040040d10301900003050090840e000002e04003030080104810f0441e58105403280d58071110f51069501e40304198800600000c4038540c1002c4c02c000008181d10098580346403160405441c2c40e000d6566441110b010005500910003400e00018000d8070900c00c0d41d8003034800002c1281c0d046a14078401c1000e80c800e2a05035500ca848951500101d0300c211603c001205040460f03840580000c0c40c04010502d45138040d800401d0185000c01203186010700003820410544600e005108a00c1d407200c8110400310340071200842c500b21040f2009142000249406102e40145018003804580000d40105028810b403591801d0540b0703460807005c88107044041394002a0020a81203405100d0001e682140d002840c0101e01080d820f001542642c1160700144d8800c5c40100c00d000d2443c4d044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 890078057 1250 890076807 890076827
    0x4021c1e20060306060d06090911131416090f031b090c0207030201030221010f05030f060c07060c020304080304090203010e090c031002090d0f0609051213030f03030905030a03050601 80
    0xa0806580c0706201407002c140c45003c058032103802070001194101c0324420a4006102804a03420204220146400c08101c3c1215548580d8001d0708064454511046240240c0b0685500c110140c0f060303440e0920342e4541e0004510a880402c142403002048241e5903030000c8004601418002c0302d030707000b134140d828528801980300c240c110b0b180544000c0303c1d42d0040b03000d1085980900300140c036100b80844405018010110341300403102c560001150403142c070301510094420030340031150102d458182440c1d41c1c80003902c032aa0080001d0022100184868000342121391052042d05c0c241a69002401d01c2d43d041904141e1000f5000f00044c410403104401241c0d12152280043c03008003281c20203c3c0c3c590006c038184842c03d9800141e11101070300c4034001000b0059216040c07202401e0203013021001000500400c48190244103140c1608020400c16140c4880b20100b180b00c2e0245180d480b40c8038007038818001c030203045e21898180c0200d4020f10140404075031546002c12249010b4000500071240c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 890079307 1250 890078057 890078093
    0x1401080f06010b0a0e030d120b0301021213020f090702010606021b1305181e0c0402070b160e13050f180c1201020702091612021204021c1e 61
    0x101400e08050100000c015044860300b150040c0c1c0c40c48a0f0b0700443e900d040001d20642c0520407152182c0c26107902007030310601110204c0081040f0007000741094284e11504129516011000020070f181e4030007050000c04442c4000c0c516014000350b14041249080300f1203c40002d81d545000801c006034051100071f6000f0740c49050b84800704211000503040c42900a0702d1100c0b01c0c0d6483c0000c0740c440740c0000e00300303a0f15003034812070324081c9208002c2c003e0b0748500001c00d01607010710b1001607540c1c1441d0080d5941240c1c800c004841582e50510000b6204450107462410070220400070380c02034a80341402012100002c002003240c1c81c010381119072030352028080e0101403004248414401c0008070b103c02c01407000b01e61140903803074441c13241400fa0040792400303136100307680c0f1080c8581307180c085082c0d00980025032140d003104540b414600f012070044030340010140c0702c0c03100082c005140402c0701c141e10f009184034840301b402080e12800f104418481c49124804401c0c10480b05112175021401103810b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 890080557 1250 890079307 890079313
    0x10803030f0a020a02070b0c07240e0d050a0605010e0a0b090c04170307140606090a090b07050d140c09010e120c21011109040c030b01020a140718140108 67
    0x18030741040040c00d480144201a1070380e01140981c00b5901c00c0c0700d940d00401240322443d450703010004503513465840d14862400d05816101e5217844443c0011516190106151110080303a803480040c0086040c401c0c42c00c882c076024181c0d05000103102449403038068100400f001c2c00c84e162452090044600c40340080e88100045000c100040300300d0070460b000e071001e00070348000321181020021300d9800344040050010013400301b24010001e000134405d105440c101c50140158a5130312040040b50343c46500501140368038000100024010300080205850551001a5161000c4c410440b901c00685254080e42000503101e880c40d84d02950081d142d10307013101c0e040500d14010340401d81d55480d568205004034042400002e66694031054580520a000c00070702009410004408150b4800304c0740760701c0366182c078500740280c41c4244111403400d00c068000b081c1360650303503c800c510314003e4031641010784140e19003c0744405011604140c000660100456681750360400d600410300c0507000b4104940c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 890081807 1250 890080557 890080561
    0x91523070810031104020f03040609061d120f040801020705010c120b03061302030c0a0303080103030206011d060f0321030103200a0605090f041404031d010c11060c01111201080303 79
    0x21200d03020b4044950041c0c24885004d55040490081e0003000d1803c000c020000c0100014058a600700a1070710b449014200280754040810070350001520400390000c2c1c1c0052100841412180001c00355680d15840d00c80c1001d95910180742aa0300440c070845250b512410441009134000c8040110185800c0c0244000c50000012960b90301c40100381e01e5052808510744000e6407818005160380303000280c806910390b0b8503810080d20202007840b0881c010b05c02c8100000e161908040700b1aa000d007a441c01310f45a494000400114000038201950f01d4000d01c1c440a41052009d0f503510325091548013559280d40c03550414240300340ca091059100c4d501001141035a0741c0d203a035080b00550307080341449511442c40601094005400c4403580b41c0103413802e0030021321040d4070060580325601c43e035030360302c0110020b440b0165065800701a150100e07190001c00310000f540c5c4020000c07803190140205041c240035a00385070956088014101d44058002402920141d80c203078039501401c2c40200641c030318 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 890083057 1250 890081807 890081821
    0xc0509091f050c160f02150307020d0c030e0f1f0e0f100207121104020d020322020f0d030203070b07080115050f0a110a0506090d030e06010e0a0915230708 68
    0xf0744a000d44180309902d10480d0582000104030705452100d4000d40020360340088035500d142136030b0060390300d10058071807103d010603c84d01c541c00e4000650b81c190343c0c0c440904050000d100042ca2540d00240c3d00c86002c42250484889513010f03079008a21035640c00e601c840b00c94082c004500c61412226000f1441551911a41030b0001100c100300e0fa44503191110740350a42c140320040b00d0007403110541c00303400018200e9a0000c41d401031402022500620100c400c1c090110322020088103800035040050300c54200d0403442d20281c1018168006e006032480d1a54981d10040440030483c0d903180420035000042c45101e1495446001001e41401c1551400c0d00c85080700c0c110f4000c40c0320340410000d810b01203084800e03081c4800030856074000100c41c481e04146d20801c2c0c96035546030341e000000c1d290a031000d041d6440012002d0480d42a111821032603201c05030a030000d0300441c0c906640502d00011100743d118005d110b041380380240e003884d45070346840e8000c0d9007410003c007600540c10881b0040074000c00f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 890084307 1250 890083057 890083081
    0x90b0111060403110f030d02040f0504180822080604030e030d120c0504080a0b0604050a0b13051e0c09041a211906020304150c0512040c0509091f05 65
    0x540c0600b1300038a40c8508140007484e01401520001d618080403402080c64980780e00680140e0f14003c41643c16191514103100403599480f6110540c0c0651462a40100b0100750040c00e0407500c42c1289070001ca14040c03900b089400d503500c404034580c0164100414107911000e10300c030412003103001d00031540c1880c0d80142090441070001349080e07510140103100c81d000e04110340c000c01c1b0740816600c481c0e4583c1030002e100c00c021074a4600490810780052030324015440703482858000200040034808406840e44010031000317040d4501d1301100c05502c11914142c4480e00d102c1d507410041c10340d880700174105200c00e94055500c00e0710620f4659481c51800e03513801c6139041000e44c00e0301c1e01380c040200350283e8070326040307088032210750103985506604184047c540045100b1800b4454545200d40e0f00c01c2c40104460180c401c6070700041062000c000103032204080160407034094017140301025201e40c000b4102c450255128034a40e8421140c20325100d000860040d408181a001081640741040007140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 890085557 1250 890084307 890084311
    0x509010e0d1d120d02100e0a060f1404080301061d180a0615030204050a08070b04181103070c12030510170709180203060c040b040b0f0d090606090b011106 68
    0x140403410b0100d1182000018030300d540010020a04200502c2500000c1c0d111a07103107601e03a006020f0030400c0425864680078404400c1ca0400c02000c545603240c540380c006142c0821181b0005454803020f144542038070741140c2c0914040c05180d5070b01d5141a0b0090403504070000c5c04440c1c444080b0358402c16944101a0031820940025142690b03a11a0f4010b401803801d0b0300012003184000724009030440d850b81c081d0054078411340d4203d03025a213502080b40d48258034400c1222110080005120080c8a0408600303101c10710074010074446200e1542000a070011074800c00000e901c0303001c03001885a18501d03120800814103081006081c070b4002c01c0c1c00e15850b80948400907007040b81012f001a003c000c0e4800030030389400200a00f500d040d10310352001c180ca1b42c0c164864800e9401083c59039800c4c4003106c044894203008213160500c1c1c00c00756505034008403d4030741c141364140000e1a80380c159000e200b000c14070035400020320b40d0030081c0403000c640c10300010a04000c0841e450202c0791400046241d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 890086807 1250 890085557 890085583
    0xe0705040e01020d05040501150603020304050601171f050601090b070f080a0207050d1101230711010e1309020a060306080c06031b220b071a04150207080d0509010e 72
    0x41030007100c04200c00e02a205442591100134030f400100000d11006600029151207803500050310140d41d42e00881c16404280d401030040c0d00090300402c0800031955004541101300020b03a9109440c540c4030003a00b228942903901040c3d114010401c003982d12503808409007820608030707424002c85032606600380c18100743c010a119000120b030007003d03000b0068400101401048650072040e00e20305081e0382522985007a000c10f403081d84205041103050070704022010349028082c100203040c0c555000010006100d01e042c002254003411054481e6900000403a000240100d000c0050b881070003c050b030b10340d000c2030400d85055801d00c07959101203541500030900f103c41580329150002260322100d1a050800e2403100000b03021500700c030149c8840300c441d03c003000102d1201580d410060300184210300c002440141c8407090342c0e68101c11450650340007400b80d01c0403401c95603154160000c03a8010402910403400c0481c60501b55034807405030b6540004004002c0c04038034142100d9035603510340c1460f41 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 890088057 1250 890086807 890086811
    0x70b07200109081b01140a05091e01020616050d0e16090b010512151c05060106091404051e010b07050c0301060b03060d06180f0201020d0c170d0609020c07050907030e070504 76
    0x40145a201b595407802d1100c1541a1907074524030a10040d00359409942204d000e41c081c002c420307169102c0210041f01e40f04041c0c014001a54421030031010000b207804880041c800140f00d4041d01081c14400c1118024010b00107022040501c030702111446180d0b440604050705013003a240712664046c1c00e03241310072011511100355840f80071500c1c501b0b50481d603026030000c460f0300420310415200003944c007003103009a09840311642c84940884420a0034061080c03504650080d907050707410035502c0598048400500c1d4140c0c0c1d400038100000b018800c0e8401c0d440d0500c04940d50040c40410301c140303c40c140045008001d00c0303181c03a807450024000204900c0c45141c080c0310500c00c0c00600d4121442e02d25906400590340030362072405102190000f031050780140325415001c40c165006810f05500306d50400d041c0316104003802c116081950014030040c03103031070301c803100014803a949001900812501401500c0024105000e10841000007000c0390201820f0503500c0305890400300c0c0d8041599415200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 890089307 1250 890088057 890088103
    0x12030f030103030c0212060c0d0f0e100c080c090a060c0213050c0a030c2c010207080d18211401090b190b0603071b020109032913020306060f03070b0720010908 70
    0x401342c000d00d645002f1144ca4090940000100b0419620a021809003500c0d15440d03611400841d5440f40030b80580e5070342200e943c071030500c41c003401651a502158030003031040d18845070624400c000d907101a142e01c01c1c40200401d200340000c1d090b01403207100c884a840d0001c81e40080c41c0000c1c9040042d5883c8041d0041803403d4184c20780d1080c44084090301011084810300543d0300b00042c002c1c400b0525000100c0305565022646e030380341e048074411520100803001e00154640e11185030300070140441045d02c0d90303140d0b5004006001c0c084c119201d00307d8101500078000420711903d0070358540c1c1108a220300c0080041244240c0c1103000b45001036440021003000c18400d1005a0f10b140040d007000c7d2204041d5102601c00c24030200304529868401140b610003501c43d508809400c00c030034800294181c02c000c0c0000d00070704000c540c0c08411580101250301c0709640302040c0105501441098031080f1030890300110300741464085651607042841d1080c5458508200582c490040840800d010550201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 890090557 1250 890089307 890089331
    0xb100215090109200f0a0503061803040503070306020c0706080405100c020c120c101b020f0d020d0302160f0b040b090d05010216060f1a12030f030103030c0212060c0d 73
    0x100480300c4940c081540d90348440060001c03011030f80013820340b502c40d5040e509448454104003003400c045450140c010559902e4888403641035400038081c40d62a4402031000103000d41e010848540158000d0000595030001c807100103003829981e03040f07981800703010010700c4001342c0d002900301d080745108080024400752a02049051041c040d0910390b2203007510315580480480030807040c800440455204a500c02d10305010380e034844240043c08010450030100e400581442c0d0282c101c1107500410368114450f0742d40c001003111803081c0041d0014ad00c065540c5034400c041c00020005041a01d50a922207890710a41c0c517154444c9000d031801c0600c01041019161310b0380c00130015800c0d8400002d649a00302030a0036201c0c0e01c401d0900f82c46840c28000014840883e61107204898103020910817464103c04050210b224074a034034941c1b152008100c1d12200d10301460242d800380d8825078a2405a000c2070040141110760b030505075450ba0803a40c10b00c4075a1714005d080341c20110180101042c00c94440f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 890091807 1250 890090557 890090561
    0x1b10020c040606050910140405062803051e01050f100c0f24062d03060629030f040b0c2106150a090603021e070c090b1002150901 57
    0xc040550800d007008030100345281c0002c06070111800c2507640300c10000e4a010100e60300c89054003603a4036071030100806e015506082d8020109044030314000222031034281d00c60120615015884000a03941b0005e012000c1180b103561109a04550301c502c2c01d9505001c0000c04405411564900c5056410000018140918105a04503411480402ea81006030825210b0300b5100440c120400707410703030501a014481c41c41068260313000301c4022072b0308c040c0380703841640a90315442203400003c0540e00c0c00000280703a070164102410481c4180f142c02221404546801e02019000b44111a03060041000700001111500e5201d60000c820107101e841d000c407001118814070079400c203001245203a0b80c410484042d1268000d210580340944174039800f0082c0403040c003861003000001219100c080040503c0f07900902403494104284070039450740090003144580c0250300c01c850741c0b440d40e80d041112151521445041c04c40689120348031503100d0500a4580c0081c40c030980c1c140b2034440115220007025 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 890093057 1250 890091807 890091823
    0x10f1a0f13030605160f02070b1b01110c161505031303121103011409040302030d0b01031805010e0606010806220b03160305060c0a0f03050601020f0d0c060e1b1002 72
    0x1403c1040b49080c0500c0c003a0350a0f45080300ca00220f502481e64801c60352000400404075075280b030a590034440741c1680003070405c146400c840320944d03c0b2036008100d20080c0000b0b200345100c6034002c0c507190f016001d02d80504010f03944201005900d0080f01c004071908030080301e030311031841c04408491b0302582c40d064400000590f900c604403482d1200c0030f19910385000055058402d034111500249461104110b40380108071002801a042800282c86082e5190042e00c440d030014140451031600007100c1180015104d40142c40c0380c1e45900c00340e8202c100a01c1455000402882c10405034134080011400600415080601c0300c00d95040c1c441c44084654021810000c00a058601241e540700ba000c04901c1580415039841c0241c03800b107000b038203800d0111107a1500c10344a52840c3c083d806c809070000e00c8020641419030244005001e22a40103002102030294a81c450550410087c20840101c4801207030943d00383c1d0110f801502000c5c7c0f10150b0140c09207040755060074184005000328140781b54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 890094307 1250 890093057 890093063
    0x51003030c1a0c090307050a080d3207120c0302030f0702010c2306130f170c0105091609020405064e0708040309031712090303010f1a0f1303 62
    0x20b41060000b03036900f032401400e500c0b4088040700e90840d2141d0401c0041f208912400340b40b640004014101d09001c1c06060644404c08807500800300f02c0c00c69558016101264801c682ca0320028400c000c1160015806a07220740034600300740c0450325039171701a51303138820030f15050031900010400e8801c680c410307032035041e41e15030001d04281505231203003041c9070840d18001c41c080140907a07000950a40c102c1011240d81c1a0446941002902180c0351174400344140000110218000c00101003002c10902030140035030085c100415110a0b9050a01c0c100201e58011601c0d40e801000200010b40e100c01c1612004102c0c0422004400840814040d0114400303002d69255400300c6041c0000c00c01d02c00200303440290f50098484c00b9500d2440c01c81c0c03c0d180031074004002c20411041840401c6c02c4030182003444d45001c1840b440c0811003035040d0054030007103810f20000d600c00001807041001c2803c100c00240701c95040c0da001c00d902d1820701e0381d290103400713120807483d48040b0b08140c11711011000d007401503070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 890095557 1250 890094307 890094353
    0x6140114090c22080c030708190209102403110702130b010905030d0f020c0a030210030e0c030304030b101e0e0a0f020c0a03030e030319110904062601051003030c 71
    0xd82c0303940540c2c841c0c60715005c0d0352007802029000908060081054812a1035041c0d07014050400c550800c070714000c004d0103440000b59a000c0201d491208541c3c1014a9580003803400903e0b0002c1c003000302501c0c0e9442854000c0c01c0240813100042e116014104d00c80450383c50040780c0c6003c0c400040f2030101c130540c0700c0356041c45544800501701d9000341a03441e440f4007550030f45007a68810070030700c0400816880000d402804030900c0c901c00c1d62081c0c0c4409036000d0a001a01c40001300f1070002451030700079030000e6903d0300310b14080c0240c0c1050340019000520b200c0034840380010302e020140301d80720682d1081112012030080056003404107030340328101d16903200d0360445d15030f440144c0450369000f0b00708086011900e494011400b444000064a10071040070300c41c0300030070282c1152000a4070008a40c8204410244889202c640c2c4078064070000c0c103003140303059401e410100340c652215100d11411041c0c2d6403405c010300106100380004d4006403030f01802c01c0c01c042600342c80d144112060350f2650b100c03059 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 890096807 1250 890095557 890095559
    0x50706090f210905040c090605130e010f09050105030f0616051e030a050601031a1014030a02120a0e07060806030a05010c11120903060105010e0a0f0306140114090c22 73
    0x2070034040120200410940da0f0740c24482d00c400510041360a0801294046030522404015044c4100c0040040c150100f54801c0d0081e5a000c0c10f01200134281c02540c01982074130014490484a88203480c01443c0c114000d020309108003404a440b20ba014082010a030b441c1ca040484160103102203c260074410382c0500d120030800d814220054009031385a55816003468045644d940c440d0054542c07400a035100310392001d64000401100d84d8003600b860060064000385401c10701d0181d0061482402c01050140c4d03100310313400068500038801000f004440c1c3c0361951a80d0a030000140e90016501a401d020004c0d8031407600092801210400c01011503003031048407080d0f290300000104504010360219040e100941da0010310728010b8a0b416901940301200400c11903200d11803604e00b10a010300401045a01c3d1402c2402103070058209545068489502c01541c48403881d000b0b006080056680550b043c0290000f1491400940b1121101c000420300e215100b440740256a540101002c14000c1a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 890098057 1250 890096807 890096843
    0x7051209011d06041a09010b0a080c0f120303280c0c0b01051012020904021303111504031a0601030608160e010807060807050d0906050f0402041506050706090f 70
    0x10303005a0161800325229042c2640c2e01c6000018002d00456004602c15110300000c0300e083c06494004242404564a52080e04908c0d106c05c407982e00513111800251030071203001c01c01d00002502841c5424010070b802c07a0310542080c404803d07207030840034003007031003144050a4241c040c0c0009451401c202080c508580540e88507040711080e074040b441a007001d10b45a0742ca004205c1c80030f81041c0e41c100410000d468903e4550a01e9006090107007000b0001070910781c030ba035012010080c480d00100c404c40810b005420040c500441a070020a40c40c1c50940d1404e415541c6803400c4000741030b43c6c102c8244030f02c004100c1c168080c1d00008042d259500841300c04459150303100c54501c100c1e203d84840b07400450300104c2c1203200030601e001911030a48841c916611145400c4803664440f00120b0076840d502c2d0b41c8400054520b01407180203d03049215000d20741401d00400080310700a010014288602c1542005990780090a039007159130040c00c0005c50784610700b440d2128181c044030003810381c20301550000d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890099307 1250 890098057 890098061
    0xd0b040213020d09120f050d0509030c152406040501050306010908061e060301020a09030201080c2b0c020601060806450f04020d0b0405030c16090e0303011a030705120901 75
    0x34a4064501d0740d82c401740c1d240b010f80f0340000181035080000d01c20003604045202503080160400c10000489151610300040c0e1414084400c024500d208001c1080c06020a404494508107600300303150400740203020300000e402c0c1e205501c01e0314140a000300020360540c3c0161035400060115900b554003916060f812088618220400184003400240225045050510070750345030703005c0e946510255500315001592260002041e000c40c00740c0c100010081c004c20030b0700400080c131140403464400c0390164a01c03416150f410f030a9a045600050042100c240c2c88058a43c111400340e5250300744031120089030740c6014150503001040c01044500200000d000c1501114652041c80d5009a54a4664030582044426038001e940103501d082d5800204100c000704540240c07165040b02e20748101581414140804d5000c0c200040d6480070041004481b40e000310300100c10120055480c1d507040c21240c0e010f103082d0322500c403101702000c00094102400380049818100c1107a1200c11140741481000340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 890100557 1250 890099307 890099321
    0x711011d0d021e072d0e01151e050d0e0102031e1e07030c09120c06090f0602100b060903030423040b03030304020915120f0d0203090d0b040213020d 65
    0x600ca81c90341d5050a0708280340c4003026030041009000c02a1420740d4100b68000d0300038003520f1003401c4944555200840b0b0400c41d0051806d907140c0c200d190300d006840f0400801c130048442c248107456010300f800c0b2845a0300814400c0300340c101030785c031000020310a6004022041c010285584000140907500b0071000d01e02294030742030142c6e0b203015034400c210b0b00142000000c580c03101c19500004600024040d4010f40544c4180b80b51a801d50b91b0340307148900c0c0700d0b82c00500aa46000e89540c00b8880307164801d40c1d00c4090000382460050307141c5000d0000323540360740e540f203200c1e007455840d8103201442e40d034003049550003807009040325291502c45c10041a00d1100e078400c07500c0350a0100b6401c049041c02c3c02158007003000140035508642e2141c00303200c643c100061504c100107200015031902e40e60b40b803505841801c4908020100101e00b031580900d01119914030704250760090003861200c1c0e5420b20750703c10302c607800303405014186c07100e101180c3c07030303c5003080c0c421a050300205192f0480403541d40110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 890101807 1250 890100557 890100583
    0xa05030a05010602030a140f0d0908030411010302031003020105130f06020601210c030809030f03040915080c031e01020c0a2103060b090607291e01060203030711011d 73
    0x146903030300e90f41641c0d07074850641c0301404501c0208070340310240f840750068900a001400820f00d0180900c18a104503160368000300c490708804018801401844100c50103a00003e003011490350038903101e031300300e16165880000e04120300010050f200c90074904103a002030690b02d03001485581c880a019440e0007090217040400da82c44900d484074202030540e0340302c80540041d0390341107040c1075855400c002d0f8000480d823601841001800d031005803003000180000d003410000000d000000d01d00c5610b003040c00c0d900c83c420701d50051440170565600820803603920fa1490050445030a8604001f5000e8000e4004802e858058140558180950306030340d02c810f000f80c0003007010590f19240c0c09608485181c0a8040e4041c41800300740300394100343c401000d02c40e014008100d17081c0601c0c1f621040c3e03c000400e00152002d14070b001d2040b80c1002540800c2ca00042d00d0600c103640d81003501c000e5690100405460410502880c5204991000e5102d030049000c036010b540754841107a01607a0352449840c04176 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 890103057 1250 890101807 890101811
    0x6040b0f0f0d0b0a0b190b0a121803090f1403190c0e010f15031b110102160c090b010504060f050a480c050402070302011d0c0a051c20060a05030a 64
    0x41c0e04c0c0400800c151400c0350100341c213042e6038032317402c40c6d03100d081005400382c140d030705c03440003e0205c2e034404650219031007551580e07a45401d100c40e00b02e00d441d00e41d014100000040d8489402d40e0b502140b1040c0402c510007076007072000d00d0b0381040d601c41ca0965002c1d40820301508004121180d071703500071070261404209619024800140c0c05c0341210040d4640301c18685460035094490741c400d150b0075400c142804000360400e00c23520186000391984c41c000322180c5280440400c01c04c4c2050141d850042000d08016003060714000300901180c0c00c5079020002c01600040940180d40110180305000c071481183c2e000410038214151400480300c200800207600c03c6508042204049030415101984281d10750348079464842131102a420039402101075548844650f14010091300195250207a850300030115401201d0501507085080c2e0040b601802c80c180c00e07a1417186141513010b9207158807003081003550038155503000329907a171f001d2580c0c1d202c0b0000441c244040d07030100c055405481c82d0303101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 890104307 1250 890103057 890103079
    0x90b0702240705011b08010e060112060801020406030527151b0403030201022d04050d05010204080616080a050f040f06140c0d0e0312070f05071a0702010506040b0f0f0d0b0a0b 77
    0x51b00d0809003481a030360868170354000904070b0b522440409845000b420000700f6100d4880c00a50b007680c03c540c01c00800030781d071031341080000c56550030b800381c0064030341c0c41e8007141c4105003030b9081c2c45a059010702c1481c54600404112040c10200130524180090070541c1e444980705d15001b4083d600041c40340c81e030681c108044482461040c0305d108151083c00c00341d20320382454101070007009240440700361100c1d50700740300c00110300070140b11803031181d040c00c007040014900003513000c0d11000340035101000c6a031600c81001140660000b4150300650804c816a00700282072500801802c010741441c07650f5420703002400080e4000c00090600c18000003414011074400003042c43e42c9000385c683e50003486003903102081e1154010f51000d90061031a140c20742ca4540d03682c03941d600e020300364246442c000541c1000c000108e903080c030415810031001c4800b0300205c14000000313000c1c001c103400e409101e1041145080800e80d03c018802500c031307600030444c542d10b140511182c0000c0c080c45200c24050004241 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 890105557 1250 890104307 890104361
    0xf0714040902030a202208190209070f120908070f150c02030309062a070b0103060b0102031305092809031e080a0c111e0d090b070224070501 62
    0x201c198800208440035070078505500c00340a541c40c4005a804091b41000401103504182401142003c55000ca08111060100c3c41404a00980200203c0030025409494006142c0c03069808540c507445440104140f1004d0412414030321407001c0044c84102805d140c0700c10840303582045500058003803010010b108031690b05a0300c0744401ca41c00690f5400c080b0004840906c580b8806038500443c610070000e50180d0a0142000d03030003003105982284034200104200720301c40c054944491000e1022f141030410302809400c0381c4c0d50310302606109484003c00690114241d00d00140080441750a070101c2c4d161000101c001440e5416054000030500380c60070503001076500411600304003e030345180069407400c003060006c2803107207410001c02c0507855840b1000b0b02c007080044000800803074000d611040d076200350341c03a0200c0d901005c020700c01c6070350082040c517141d141071320402901514400000c20124901b602c001c101306a079211118004a005e0045c0041588005458100321010042440c0c448c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 890106807 1250 890105557 890105591
    0x10501260303180a0f11030105060f0d030f1b0609020411041d0903070807050d0206250e030115150206070905100509150406020a02010e06030f0f0714040902030a 71
    0x4019550a41c42040420120b28040540041c00325010b415599980e40ca581c03003c3c94503d0ba03060580e07043c0300744030000d00c03140b4082c07094a410020484610740d050768680c0c00b0030690345802402405005150040d142294000c0b0b414841547c205910039101026a16018000b8030070814107a004503e0a810804141040c108990589100b041d003221130b140d01d0b1b011200c5403680209951150302092041600050090029242c0700388900f01910400e88400c40003803030034000410840003682440102c90720075a85404200302c201052600301501c002d00000720340900031160049086a91524000407134001c0c00360314000075580c0798241c0d100c40c1c4819904844154040c09210303800794a680140c0c6417680030b04001c01a0303400145c00d116038140000403e800c6504030340d01034005600807201c59411582d01071020000e0550403941c050460501e01842c20841d60010f05c0056444a10008100039038090080613100c44c0303401d06400d980b544c9800e0b25802942040d100b11906604054010000768410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 890107913 1106 890106807 890106869
    0xf0203060403081801050705181503010603290105090603060f0405040510112107021002030c040504231506091215071715130c02010501 60
    0x10303520703008222120f03c800e131382c503915220030800308642260079100784400d4104642035040c21000850110540c03001e84060114001c00005051640740d00602d440b5400c9468900b00c50200e00300c80205a0f010496581c003281041c440260b041c14440b01442d40708100401d5560446000c10220702146c4c0c003501c1c25a15500f200b000032014010501980801130440080d01e8940f240030b9441c10060103440707030314402c8281c2c21070115100510800803a007110300c002034219602d00341504040340c1a40b19104142c0207504200ca20f1455011495251070001402d100156550340c1c2c0001411400c800c05420703580c0b203c0300b404187c1640e11401554886514280002c00b10195040540c040a0500070500d50811400b1702e1201502c0c021380012503000703844081045480340300c00d40003a0340c044d0742f40d4500103000e28110400c1203543d815000f050407241101020b10a180d0040c0f8610b403058a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 889928057 890107913 := by
  have h0 := BRFrame.cov_init 889928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 889928057 ≤ n) (h2 : n < 890107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
