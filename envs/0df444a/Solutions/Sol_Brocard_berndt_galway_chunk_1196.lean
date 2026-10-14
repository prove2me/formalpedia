-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1196
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:42:33.399287+00:00
-- url     : https://prove2.me/submissions/ddc8fe61-a41f-4288-95f1-f4ac33b98273

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 214928057 ≤ n < 215107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 214929307 1250 214928057 214928113
    0x9060309070614090a0e060d02120c0a05060f03060d1a07020a0308060105070c06120609060f0801150e0c0d021b0d110f0a060203100b030117010510030f0609080d0e 72
    0x20511101070b0304d54445c00d10388120703642c0000c05040c44d25030400007511000c2c441002503003c07200303015032403007000045410440303a00308980b29000d4640e5001171094a00c035140c0841d10340e2904100242c0c047c505941112050307801800300c102e02880c81080043c01c02d00c1035411750096441001c40004046e07012004581c4014203281040c180716580c0d4400c1d9190000340038840a010101c4c031500c000c0041d0754072503002040c040c4028403400d5650f5002c019410800c1c081c0c4045035003400c0321020142d0740c02c0003400c110344001401c90b50390b40e6506480c882e141c020b5420003a0740d50302046145040e50204001e00ca01a14071006024540c00545c0c000d090800682040c40319074202c81c2120002c0d440205021100303540115015076aa41c600d100c2006500c1c00b40c00256145401000200d18040c500c800c1104041600008111a0f1185076a49544c80fa16201c01040a24106100c000182d119000340c2d00c068890047e60f81456950900320081e2400040c000c10291f1209248100d03e4000d94a40c0d403040364 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 214930557 1250 214929307 214929347
    0x1e0906050c0403050a020904080c0d0309020907080408030109050a0902060309030a110705010210020705010213120303050702060c0405010e0d0b01121a0408090918030409061d06130b030102090603090706 89
    0x116544e560350300d8201003440640310341ea104000809100c580000c89a403e5081f0003507502d0b202c004580500104034050341607005407006400210014081d000183c01640c1151415045078139255540016140007840c0d070740c0390f0761220011001615030300701a500400e03142c4081e54607413410030401450310b841c8a41c02200d40d80704030810403075640c0100f410000c0310b0b43e0f80005642c44455003010ba000e446140d07a172000f0403241c51000603050740c0c54031305080ba4a00c41e80d01400940c80e4007000b02d0b900c070340c00d81d01032085406c104000c00c000d60040c0d0441c19000700142a030500340504e034035100c51046c403d80c0f001280c040905010003c00802c41129000d5030000d215400050505889101850089203035070303402031004034041004c41441c1101c082040039110100da40da1511400a4009001c0c1072052810450340c02c203015062040010807113200b02030103402550325a0300c0c207200ca03024000781e0030026050b5608100001c20341c0c0b070340e00003540b00d54000c0780141085031901c140200141c04800c45032450341 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 214931807 1250 214930557 214930559
    0x301090209041a06030a0c090503060c0307020d050901091214070b0306100504031106030c0c121b01090b0601140904180b0112080d050a06050402070c0306180c090c02011e0906050c04 80
    0x141e5240c0c240d80e040507071b0100008149240304403d44414001d5008a82e26104a0781003284003c2401c000310b2185076190300303641c00d21480a00548040c06450150350106148100a220303102446c49030802e410700a003095038549109200d02401c050b000d800c160b8015800108114080c1070442040c1612401c0d03180040c5030134038588548105000b0440140d00c509030000200f0305140030700090b90b02d40a5040240d403a201180ca40e050f00d150702281d4003900b040000300c0c00c1ea03021201849048800ca4000095000c41c0d95003400445202688545441d040141031250700c5603901c03544a507a200c410030510f68184180c0c8d5080a15801c1e20580c8a20102001603182d1400558400159801c2408840d808240c80d01c801c2c002c070014043d10340100c0c0c0c0041c40421100c0030300465000300700449000301d50400c0700d1450800c1340c21010802d46c00150484803801b400304110140d0380d000b0321140c5268400011202c14120050706082c0d01c201521004035140c010f5081401114403a00d5002010300c0026840c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 214933057 1250 214931807 214931809
    0xc030201260c0d0b12030304020405150105180102070906060503100e07020a06110910032306030c0607020a0b1306020610360510140f06071202120301090209041a 71
    0x166100420940c9400404600c0c203007810f40641052010400090421450310400c01d242c0e50f5942003118241e215038100004545c42282e01c0e0303002140303a138060352030b18580031421503500082d15002c010141103100342d00e00055a10101d2107160003406540d036481d0303524107241810024418060308590070710b100c050309022000307800240c030a0455500c040085500c000b0342440b43d446000e13240b402500510360000380101c8075410b5124281c4082400007c0030000c2c0011036003200000c084a0080d01035020504000941c44c002c4090240c5500c02402c0540440d1a07410012107034202e000c4426030383c0224442401090b4061204590114542511201c120303c0e02c0480c80b074401d10181c08120041d001000180541295400c80d498442520380c2444182440d00800c440c9440b0380c0b181d07000880700c4050664041c60100b0030f40c0c840000080000d8140180d9032140c440d841282ca8038041584a09035110103036148441c003940c0240314040700181c41c0c4442c00184030039990364040b0b81a0b0f0300301c2a030481c51a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 214934307 1250 214933057 214933127
    0x30c170a0e030316151e09050f15060d050c060a05030f01060c0819050d09030210060803030c1e040e15010305070527010e18041b08100b060f03040c030201 68
    0x10080d004041170300d0104001640200405200d882c44c0d070345182c018180542032a0a4014500d41e134031510440b20322807850311a803503c428030303201d02801210040011400900d801c0100090090103001510084002a4002030103a4842d18007440400c0006c0704120340190f010710a9070040c816810801c450200c01d40e103103005403041180c021a4021150f01c40c200c418401c8040c1c1d50512095803081019141d90306000e95110413001400d2012800d100b40442d18203000300c2540c0c080c2444070180760428000c00e2100186503400c1c1013240420310b0a1200151400401c06442d00482401e00c2c1d5954503482c4800060544200070700c024140704040050b0001c04040012203105d10318090b66480c5005030900040381c210b0300315054960f10400300903c620490200c201c0d103c1c052441045501c0140360040000403d1080b54820200c09422002d43c0942c0c281c21038025000040c80102014600700f041c11485a6580055a0070f0381c000607a5034003401107513044642140f04250071800e02d8051101c4604041d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 214935557 1250 214934307 214934347
    0xa0507060309031205090610090c0504170a1a06100302070b040201230c0f0c010206073218030f01050c090409080f04030302030310060309020f010c030c170a0e0303 72
    0x1010703900c50021060521800303071000340411301c020034011820048146991540d0503a26048032160780c10780018090f4031442012801e1700f085d260310382050314007000441c4071442075001008a014282e03104000460725140750031226982010600b06050880078400d100c101e00c22101c083c54410846280400d200d5010b942e400765091038441d201458071441e04007000d0b1104d0010400c0c41f03021580044100c0c001c0b506460040403101110504125003004a0703440c2402d68009000c82c11424031000302c50003043c000c4085020340c4410300c0c000b20751180d0450705135010320005104140044030340c01880c6024000440320440340002800a8241450000702503c201501c0c180300750755807101002000300003401d860400c6c007100e0389207481e15504d081c041e4890344100e43c820b044040311400031030110f010384a18000a50017810360310503012403034010765220b0f140220034ac081c4405504c8080019507094082480c00e13000e01807140e1202040390b0080c1c844522045058440c0e041804041e07078003c101b4003800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 214936807 1250 214935557 214935569
    0x10b040b07020a090501060c020906180c030408090a180b0d17070f02040f050601080907030c03110d02040e100f060302031b060d0f06061e02060105090604020f0d0b01110a0507 77
    0x5580ca00c07840c030028000403010303070000003954184000020b0039a040484010014020303104c4a125554480400802140d101044651614002c1c04100086150006141e01600c02c00c415458003184000050300c5686580c44200300c1c1c8440c19902800401c28007078005034090607240304000d4402566034121054228140c85009007020030000284040c02a501207580c0d000341c010880c01b0500500c00e00901002c0300d01501107100350b008a5031040f000030703410b01165045104e0744000c0b0304550301c03044450b041901c000c0c2d10140c08010400581d440d4881c201e12410b541c00200000c10503a20103800b5240420058909245482c40402c0941c80211781300390081080c0d0402942d01d120301c40000d1040c010031012007005132425001455808865016030295010703500d0308424040380031460715402070441d18140041c0c01820042001c1d041090bd40da4003c0c100030809424503100c01c038920016080100c05100807500d501d000440c0396009040c1460040f0010003600c00040f107070321181d54905140c4528 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 214938057 1250 214936807 214936829
    0x30e0a02040b01120203040602040e090a030e1009150c120509030c0f0604030f061a090618101a0d0501060906051c06170a1203020a020c0913120503070314010b04 71
    0x81000e0f07032246001d4040c58150745800c540303900705030900d20000e402600520103da05803c1c049200c41c04d001039070700155941030b91402015450b260074840e074071207940194014009018030204050501c1d010150413944a550340c1c007012041e44c2404100e0514200c0c1d2030003070200800c507000154502045440008a00751118443d50110300d000c40e007036100d01d030301c007802942d0780901c640c08000e5aa0421010601c58407001c02c2820081c004010103540240c40080c0e02903802a64044003144034203005070701101e500d0301e564036256520b03004e000c00312076035101c1610140b0010303841c2028507203031103400d0250031030b4038200d81c445052400151141c4248070400c1c610880c4013409040001168202c03801a24454030b4500340059100d0003c4d66983d80d10408494a58183c0d404802c603a200307109681c2d221031030350300405174120802d0500a03445c030b0191038022000701c2214440089551008a480008826500c01c3e58a2070b040400404840c12003003820f418030f81e8900100003044c43c01054905441c0e107040d00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 214939307 1250 214938057 214938071
    0x3150c0306050310050c0c0d02031305100503040b040501060b0c071d06180c041a0903152203020a06060e10060503040b010e0a150308041a040b1207020307140d0906030e0a0204 77
    0x6d00c4450301170400c07208918407450708200c002d154048040e00031860001030003130065440f08208102c03400c040c030300304000620600010780030481c043c41040d0824015000015031544032691a00d1691200035131a500c1c3d40401e00803c401082c8409851042c103918144140c9814000000351071a03482410300ea01c00d0b0340388004148400ca601e41200c00134000006100c1000000224122550700302c455600d200c1e0040e0103d07080c00d4581000392900c03a0450040101403140d2400d052007100e00b858400b82e085114070746a03e0001482440380502a01089071100c52600c0c00c1c603090109140b064014004024060061000083c444000380b03054802c2640c2c8040165210740c2e901c0020800d10116604620900f41c0010900c88468018815030b00c010818180a209881d4001c503c0c1c07195100f00240307010200701020054040080090700000c4500c1a44c1c034003e0f03192100d034800601380c4800c0c2241d40240c0d400c240343e0f5800405480041c4071904003440341c3c0c47c0d01c07005140c58030200c02019002c1e80d00c46c2c031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 214940557 1250 214939307 214939321
    0xd060506011404180501080c010207050405071202030a06050a0b160b070c0f12030501080d05030103111207080c01122703111203061509030703060e0a0204020403150c030605031005 79
    0x1e03542c4000e00140e001c0355101c9a690070204495030758140c0305000c86141034000700d43c5000c0400c0500c1c0c0319406030000d1228078504410300c0003d03e0020081020408078100311001000c29000843c0200090780c000f09a45041c0342c204001a600c0740c5c820354105030108030000441c0c089c07285250f180ca401c0400da12060350381c44810790f0140700f02e5100800300c1e14140c13160410440c080f14243c1d0b880e80c0541c0c042003140e0b00e4001c0b4955a07180044100c2c040f55050004000007240b280c40c40c00400342c00f5040171001010fa400c107500e030003480c0d000300c00940c00c900200c1080f56480300140c0d0918a9142c0144813410410702080400386a035150b80c1d03500c0841421b10f809041c000c2010b680501214800c0381e614052403c5240c0d01500309607041e502c901d036a85c0b45500340e11040f100b075800103100200648900703880c60f56010002c0c0b542c072040030142e000c2e40707940c000965a61b101a1008500804042480c901410080b508841c0d600d124075040c50303d000f0307040c0929100061448000380001c040080c0e0760312002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 214941807 1250 214940557 214940567
    0xb0310050405041b050f03030d0b06070501150603050c090906040f11190e0306161b0501020307030b240a0e0a09091b090608060a0f090b04140d0203090d06050601 71
    0x341103035030032900300303070520007003220903003c2e45a40140e10000e402080c0c0c68100300405ca0199180044d815032007800303940003000c2143e20640040c0e20003480310785000c0c80e607540d0740c1c2907078410503404600d9200c1d001c04000d0380350503008030340e805a404020b1a20382601e000020350a1000589614050780d40d881c42d100c02801e09030300034104090089401d545030a41d20000209158560140c1d00c00180340e070248a040703040010305d540c003c0340d14000c0c0b0700052200000450320300006d00c2804120b4403050240c000401c0b42880298020416582c0102c0c4842c102000d2041e0303249801d0a880c812443e004074220705440e6101680c001803054038240042c017920000141a403101c43d006500c5492600c0801c0b403c12000c1c1004000c1503140140081c0303190b640c0c60301c207011a40584034002007a00300c0c90004011181e16449100440c0303070003030001101104d649540c11024001c81e41210301d41811030004d54510b10803c0034034405011341c4000c0d8549500c1c000812041d00c00c40400030f0005494001054040c0e000b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 214943057 1250 214941807 214941809
    0x4030f05010b0406080304140103110406111501030614070e10030b0103090b010801020915030103030c080307050f0c0601170f07030f02030c0907021506040b1f0909090f050f07030c0b0310 82
    0x10000c1c4244c54070345401c0760311790340140302d924900303025995100f0880d40a40101c2d180400d5107400f0360b003011324081301a5414101508000000c5c007500720780c2103e00c52101880d030702860081500040b072800014a1010010020b410002801041000002e0310703035801d902d84c0c50b0350250b4070340030850b142d01c44016006060b4200b4000c01d024452030001c64994030550280c94500780c12116070032003805540900c84c0620080c00080c00081010000c00c01203803641d8025504407281d4500b007460712091b1a15000650040703400708038030740c11030b000400c01180c444840680070752504002c1c0c0042c20415006503500c1c4a03038800100610700b0b00e180042595401c1c085141805001341002080e4540540020345a0314070821b18400c82c95480f011801d2400c2600c9624901c0502a264243c1c040c2c0c840c0441c1e204015044a1408211301d4030360100c1d07480d0582c0038098090744280544440d09880f03240544c148440820000d1095101c0802000450304241d200411204042c42c9943d50f078803417844603c5403400d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 214944307 1250 214943057 214943059
    0x1212070c050906220b030f0d110106090b1809330108010501150e030c0a0f031703040308070806120f0309090c0f09010c030201062c0a38031002030717040804030f05010b 74
    0x10300728100d02c130355800c0309e26101070400c0100204219500c0f25064411601d051142c5038010700304815580c1103060140082c0c1c0c200c881c483c21118004e2032501120031503101100c140700c0030580c0241c400c20b840003d918550241200c0e0000744540c2d030522600c40030b2201c0090741c10041260030001340007507440c1071000115144020f850642c182d5290500102c00946074401225583c0071200c1141a041c628015203019590640e40c20400e901d54520490710130201074401e030303808809413000d55404001001590480242c4030065a10307295002d080054680f4010b050b40d041c00005c000c0014154070640c00c85100351000d00b4442001c08041c02c00300d0040541d904003940741143d2400720a00d80d403070850040300101c03001d82034095950320101200159400840c900440481846c3e601c0c08000c04052043c05c1c54011921061280340b641c030009150503499644240d1480d400400d02001c580c0c06070700314201d041001d4500c80d1504140d900e81800e8070803448007402036101c4080c140308000c0203400410002d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 214945557 1250 214944307 214944313
    0x200f01022a0607141b03071503020c0a20010507050d050f07050601080106091d121b010216051507020706030917030415051e04021212070c050906220b030f 68
    0xc941e103880916a0903403c071050301440b5074090049200008981004503610246c00b40207610314190910154507a481001400c0c990240955a4a400100102e40b10170740079040c40794582841000301c85280e041000f20a040107410440d03880405c40000302101c06c441300d45040743e6180c038091111a418003400100906500440300000f892100540050081d5080c5980400c40d81400018020b6001801500c2d8103243e005400702c11941140c44014000720815040c241103074031900d480070742c00ca0384400e50501c1500c0c0b1201c0c008090000c20082048211410050519507042410010307544100d54400c0d4410507891303d041c0801c01c0300001c240c983c00c0380041d007401d440741410700c0c101140721070b2400721146452500700001e0f10701c0b0080024105c6004208082241a2aa034080c082206428840c10041d403080301900000700e80d421004144040c003c00c210081c080c00c203410080f0000300601400e100f0310002c0e4000301c00d0120320464041d500c0c002080020351105440c00703e414400f0345000000030340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 214946807 1250 214945557 214945567
    0x41b060c020306181504080d1118040902010503160203070c03030507050d09050d140f0303010b030405061b0f0c011b050a080a05090a0b070e0409200f01022a06 70
    0x150000400c1034020700c00c9040e610282c0d6510703460021000280500f285a40c00f0015540c40303802c0e00e46680da0014080c2000b10700e0a44811004c2043c3ca001c0e41c1044401040001d00c038900c004a8000700441070780481c0c0500c130381071081d00001c0031400083c01e900441c00602101c441602d000700200c81d0301d6940443c40c011141e40c1ca04015015030844102030303c00c2c0c0540030508845611032100001a0340780203044000d51030b820f40314100a50b00d40802c0d205944207640441c100f05000300702840c003c0c95103281c0b0b541d0305d00d468502141800d01c081c012810005a40849140d8a0b01d60380654540c004e41c840e10f940c8070720141c1c800501502c0b4030300072039010181c2000300344010b541c04001403480c2000f0781c81300c00c01a1201d200e00000c450044428007900e8020445480004401031201c5400081c2407400f4a01c45140e10b00240c100c5d10261000c8503414143ea200c09812510b102e20045039030001c0340e85007490460180040c1d10395031441c0142440c0604848000d0003100911402c041c50ba50203011141c80d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 214948057 1250 214946807 214946819
    0x40804030201030e0f071208040b04080f1002070b0f061c030302090118030203030406050327010207060c17012606041104060503030304120806130c02010b150f03040b041b 75
    0x1692060000381c0c002802c100c1071140c60240010a00b012884200c003d095681c030703040c00c0020400703940304111042c101c204000a0100c50030005440941440350281403050002c0402c9403804080c9607075034909900500c080700105090808a50f44500d17012041a0f0960360400011070550700d90003061411903036401100145581035010b8080a4002e80340e0f40820340c80f0b0320804d444020340d8407000750715910400050108502c80c50146411000000f0000d04030a4080307410500f0f44c0e401c440c090b00507175010800c94240400360080c0030028855081c07031820300005560340e440402050280c0c503900c41ca4070a90310b81100384c40546c2d0001c0d035040c406591080c00c0900d00044154906064984a54180000441e042c030b4048201da01a95000c5c40050000c25225402c0c0c0305500018440d44d03100c4034945c2c600050b412a40280705070081c3d1a80006288900c500400c0f20a941650b07003880c17400c006000e01c06801540d0f5049981003a007054802c0b1403a52145803040c40c0d02160f900802880369007910005030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 214949307 1250 214948057 214948073
    0xc0a09150f08060a0e010519080d120606080c09241c0b010e0612060a0308030903070c0801052211040e03040e130c060305060d0203060c180409050a03051605010504 72
    0x4031110b03510000c19448000c200304900109020b59a1000f4141e0010403c42c42c1250b07000040000706112200c0496480e0f0460341800315101c0c0142c0410320704075032144a44c00701d01c00c16002d000141001039407410004d050401d6801560b003054012408900314120101c1d01207882c2e0030031a0410400b40e600d04503440d21010f20800144082c141504180800d41c0c10b6004221140c1c3c0b80c90023806860921042e0568107455400c041c1485410610000d404400302d81d0303c0004521481804008640e940c0881c60110030312500d030751040070303280d2501e428041001042500ea500c3c250000f140c40c604400a030820000c005400350341e15512610700306c2c02490202020001d4011035080a01587c2d06681c4d1102d0704207e02d800c00001080c50820f0300c02801b58034007a91005411003405081c000d54002c07a5400b09250481c103030b441e5001180041500e0b420669194443e10036010281c0b01403203495910381d17a25a40e543e003a64020103209000c11000c0d400c42c0211611407820303420900034445030030300b42080c1c2d0b9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 214950557 1250 214949307 214949327
    0xc030c080a091a040305030a08280507020c0306090c060f220e15060f0c01020d0c0201021801090b03070e0607080406050405090f040c03060f0b090906061212030c0a0915 74
    0x24059249441000b1040f116420349080300e8201019600d00700300102c0460750408024100348042d2a104c1a100d542c0450b5100c800ca180c1c1c0d144800203050811400c0649440190305142c4c0c401c1d4441d03801c01219200c0480c4a10399964244c1d00c6544a0303420200840b4140a03c44080e209803844070010b42c5103400010103a82101c0300b100304041c01e40c4498071080940c030701d440a51a04000c2c100007140304411500c0040144e00340c1a000181414034443e1240150340545000400607900495006c88440e4104940300c2c6140007424808052880c19600e02e80e6408020318120a0203803003030280089031103100444140c07650143c3c0c1d0a5a0f29260784002d04180c00500400b80608207501c001034010f4424260540076980210298114520359550785000d0f0490445d1070042c2a116210b8202c0350300c031011210700461001d400b800817441c201042c80003012242e042e1444031b40c46284526603950b0060120f03504905002d8103036039211810f490030b45070a01c0ea03a100449c1081c0111130a20210b41c0000810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 214951807 1250 214950557 214950569
    0x1060f0219080f04080d11010614090f092806050c0c03090f0307050a0308070215030412080408040b070501020a0906110c011b08130608090303010e070c030c080a09 72
    0x11a400229002241e032050000c16541032030004840d030307034040703030070800504050481c141d00c2e039181c00e0701d03848558100705000c103088002c207580c8102e03039202071030030b0180f03901800b0040c0761035080101940001d904204050a44104d1706006400f045829500784078807074600c050341c50814950b2500e0030140700b8070031340c0703201c207032040703458100400e008050342400c89200c01c1c1108001c50a1104110030460010030349281c035589445034040000301c80d25160161401940104029a1542800e0040c001c100007041d200b9150311904000f00b00c00111800096200000146004110303a81e4030b1501d41454840e40c0c004103010000840c0d1720080000540040035141c00c27a80e111007445964100603034485d16003810f241e5580c4c009043c0c0700d81a5208010110120701541c803028070450840d218020703d030340a1400782400c07c0c03030340d101401080d8001503220380213035044000b10f24561518001f0003101d40d020741110104050f000c100c0043c94400d4604c01000da4201d03c0c00b49ea20341c2d5160300581640103a100e40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 214953057 1250 214951807 214951817
    0x4080c010c08010f03030f0e10050a0306050f0d1e0f08031f0b0d0f02070f08041d0609040807050a15060609050103060305030f0a0512010612050901021615020d11030106 74
    0x1a49818420b90315203040303682c08070f420380d000d508559007542c81031803040d018810440500b840e00f911366101248018615280e454036640c410300e03224014182c461542000d80a00c10121071800c07107803200b520340b10500303800c100c8512560841000100c00c00c100c80902408800b8120b20324010300560800842c082c4990103001850b20700782030048203035280c0d01d105030b9140c84000c0c0604004903809401c045000c0092207001890100c4598500070301646a103030640d0994404603061003003008031060703940800c0541500c0001440c000001900800d00184000c00000011440400f008010400d60310a43d610030f1403458140e60106521005001d548a030700f0002c1e000440000e81765000e44144010350b508000074625005010b001c00310643d1200c8003010401008115007000802c800c10814081d203041e95403100581d2503003070b01c1c7c419920041c051070354591040202e00c01e50b0700b81030850840c087c1e2049070b840740072040881e440024052000c04101090400c0d03c02130b0310b5403034000154142c45281d112 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 214954307 1250 214953057 214953071
    0x1009170703050d050919020103020d060810060f0e010311060708120a0b0306180303040f02030a0b0907050f04020a0c02010f26160905010206070507020301061d041a06010203090f0402070b04080c01 86
    0x95179a9422041c2c0c041d42e54500c50103010310240d4400e0300144001c22a0080200e200c1d551040302904e0414032840c5c03545442c1c0d0700c00e0305000c0251a14a550010a5001240125075045860700303c0040101d40f0820700c1414001104d41c00c104805065840d07601140440d45c8032440d11303111b039001600f81090f10901c2805860001605a00ba02c1800042c103800e0400450a41d42d540e602c058401e10070201c160390500c618200c440c00980e04110080c40b84011030701a00d0082c1c60300092141042062503140d200702e00510404285035402040d0b214200c0d0240391a01590b015084152450b8502a090400f100c02c4039030858078050a11301800d020f444080c10a0046080c0020112043c0400e4060a801070304540d010a074214450400f40c0010b5000800000385a03a4601d840303c0103140b500c00c8203250038031141c03c010500801500031003901203a8006000c0524101000075201c1c862000c4451003801448480b41103600d41768103030351200e98058032010b0641440e051440050b04110400d0300d10790308140d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 214955557 1250 214954307 214954321
    0x90f08100e07060e0904061103090d020c0102030f1c06080d0c0b0a0b0604030b1e010e060f010206070206060d1109010f030b09121902030910080a060e0105031009170703050d05 77
    0x1d507002c1143c10319543c0c40725003200b407020010302000141050b0341490300c0e8485000304038003a0008600440e11800144601400480040d08020810361010b05541046c002c191949130781c2400c41d0407501d0305c40c5041d8022890714884a009080e15002002940b085c405816036150300320512020a0f8001e020303c0311a95960000340c0c0644d0000d0b541d2540211090000300002144ca205090f04406035120b031501d016a010007420b4210003d070301007034004103c0018040e40d800c04070701e0804090400c3c13002d49074618240324080d5544c50058002c0b030040480c0f2000740300303200a0184115031103070001c014030a07550f582c4400410004043c081130b07500045440200340071000028032a04a40031403020300742440c4c010500f010f103440d644141801540020081e490310340d03452096200350650a61140c2001d810007074107580881d034154004d881103c1ea03000041c0705a07600003d500c11001d00c20300010603004603e180200f0500a5180d0100e0040740c0411301c24109a004006070070b080030744400402565a50312 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 214956807 1250 214955557 214955563
    0x180303061d100302060307020709050903040905010605030402211227010207080c04020306060d0c1112090319050703080f030118091218050604030503120105041506030c090f08100e 79
    0x10700c0782c0c03000d420800800c00040c00c144003c0c6900c540c09006503040c0700c0c0e907004201d0a40d1400c842404072074100260038055001d0398840c15001d030006240141c02c6241a50200e0040451001c210004020310300c139008000808018624650400c0c04101d5140e405580045240740c403030809000a041c100c00301d02105510004540c000ca828540050041000720380601c0020351000e0a05900002c0c100311004010710f0074003c0381542c0d0599612103128218681030396082600740c0170303150391500d801c000740d14141e6400100f01240c00e050700d0403408241c269140c01031400f00c040e070006024880100c1c015101825100256048407682074089021040d010041012181c010f90014501034204030001c210a10070300d5442c003040100300180ba401629000000d509401c1503104aa095100040d410182c82039110198018001590144040c1000041002500e00c5501409003003655507808424100c0c4144955002000c00d20140b5011a860b20101a00d400107061819802d90a014010b12194800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 214958057 1250 214956807 214956811
    0x20a020708280b0a02160b070e04060f14030316230d1d01200c01120902090711031e070308090d09090c0302040f0e0103050714030309010c0204180303061d 68
    0x1041ca6111845241e950b0f804080102910903103019600f030103426002e44a0203036000358640101d4000682c3c1c50704010003841c484142240a02407070a09004000c2c80308004285004e0328040108514013045d841d0100b4a140229000104901e0140c880c2106112001750b000c04105100440401c03004070140b242c0303a64542c3c90f000c07140001c000e940e104140c100c003408111458441490705564050503141144241192032120b5501a00800c142c10b00d40d41e040a011410540c0942c42480320708075540014026860092058080c05400100305810300300910803203a80c803007146203800c402c5158040940040c0c000c2c0c4022800705810702c007c1201c1810009540c0300ca103119076602010300f8180f6078070f440a4030381481c4500526400b40170204140300040c0c00c1c03c000d40903115122410f985141880d524103440b6500020b2003201c20340310002682c0303020003102c5801070203082c80100c104051005c00c4c0200300b0401c0407070313151203400f010004065140d004141103581141c56030120030b103e440200869142 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 214959307 1250 214958057 214958113
    0x1030b010f08030c0d0c0515071d180103120504150507140604020a17210a030b1903260d1406030c0901170f03070c0504110405060904050a0f020a020708 67
    0x200505d54140e45125003800c001c2c445c821030135134500103040e40c40b8600c415010384071000402c038111043c52403041901081104a00212102c40307030b0700e0f81441c0d1000f8180041c08042e201040e1141c005100d02d010b00101c400801d2a07050440034003028140c020490303003011900700c0e02e1410314a6006280480000c0503401541c0080c000e00f04680341046941d982004450480c0c624001e8440e07038141c4d0740c18110307503024030780509001503650140000001c0c01c540340c1c001031901c00c00c03000643c10b4044840b418102c0c140c941c001404a03245001c0000c4d03907181d42c1d040100404c80c4800048071030040b103264003c002c1da80c0c030a003140d04640e02e61904160b126a1181c2d80c039508629804010400d105501c0f000980b8043c1083c2980e03558004441c1d014195031210b0b000343c600a00c1600104258105842091008020f480c102c071705143c01c5c203001443c81c4c850a141680b2903a103a90200340c1d4020a070340324450640c0d5420b801c40d5904c0d01c01c44082c0d00c0d6806440b40e08c0542c02260860100c0d06c03081070100c039440345 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 214960557 1250 214959307 214959313
    0x40506060f03010b040906240f090b0d1203020a031a030a081b0106030311100c050304121101050106110c1005030c0315031615030614010c05010906020301030b010f08030c 75
    0x80e46005115240690301410365043d901c03141250082c2e21244035403030405005002c003042d06159089551060701034100218016000b550342080b54503040c1c810700060b0342a000010942441190002c2d1070651304000c00780800c0141c60103102c2ca581c150340181800110b43d00e0a011048074035008070749048121103910b4040d000003031103000103489040181802504030004141d00c68610329842d00310317082d540003103004ca5a0701e20101a500300c20441c20004034400142800038425607030300249030340006000200b0164104060710b86141c003600c1000135004510000304010741e982e42c0000d0540008800700031450003074010011f032038241322000300381418007034507154916100e19440c0781443d0b1000304510450400108400020747e004d00074280400b0003c804442960b042070011507240100030b090b4020f240c9003d40410040001e5000744010302c2c801d0a10708500901400d200e80580340a94000b070400344000004010024041450b0f412707a01002d1909200d40d0700c422010f6624482c0540c130f03079203641c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 214961807 1250 214960557 214960561
    0x706091503020d020d0b120f150603011407090501110123040524150d0302060c0a1101180501110a05030a020d060909060e0610030b010b1308070f06090509040506 71
    0x408140030395000c0000307458018507284592100104903001007040343c0d14142c13140320a0140c0c1c9010103440903030403121030241c40516500b03050707903554984140310008100c00490001f012507800b94041d01000c0e03d141d0000ca55131918003c0100514924000e44e0f001c00c2c00c3c10510501000f05120349100c42d2030410100c0062070504010b4500200c0042c403c8070725100e4410001d0741680f00840c080e510f50f05420101140d420302003c40101030700c5c2c080c0306501542e910b100d20b40c007103513000030340503001240c401ca050360300d50b100340c001ca40480314440c41c50341d0b40d8200300310250407103411803d0040450161000300007001b0b00d000b85600e18814200d2000c00520b00b07001185d519111030b801401010761400000070311584e42c070074240503240d4601c025900c56a0710205000791400500800b5440003804499860244c110759030b0120f040302c10301601e44c42100104441c17282c1100d410315800a8246c1d40125403c035981e464074090039144501944000440d00b41700041c080c1024110103002c1d50f4032501610040e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214963057 1250 214961807 214961819
    0x14060306070c1509020d0c030f0201080a02160609020609030f070306050c04061d01030906050a0f0608030f0f03090703140f070e06060f0306040b1f09050d050a0201080411040f1409070609 82
    0x180c64100c0313090382e0090010b006000040c0441940800441c1b00307404850a0b44200e00024086c024000c0062900700c0c010040c00345408542222052040d6000c0c0e0000351080c0c9034008288140500d03c0c0040d003500c81d2500014100708009003070411640310395002d20481e66940c1c41840b540c0281c0c4245808541c03100c81841c5c1e0000080d100543c03141b810b240008600351035480c0d030400c1c0c4000f070b644008026519a125141880c440c01041c0243c0003a8000310719225002ca41d03040d032481260301d05205c498021010030b000c0002801a000255001082d25035810301c01d10302d482d141d4aa501c40080c15108581c1e0002d0f039502941e483d603120b1000100201d041190ba1802740c0002d034001090070394425521042c003c01551a545110b8824614044510010b1500c00c03000d40b5031001500141e06c40c2d5100422800081d40000348500c113a42e0a181c83d2120303484514040e8003560101340e00c16801800c0080319101c07400d89920140148400001c140380940b80c600e5507980b210320038012080020b40c2c6c54014054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 214964307 1250 214963057 214963061
    0x8180f030109020f13020c030301090e0f01060609090902030703020406060e1306080a0312020d050a0c0207120809100c0b040f0309060e030601231906140f090d060f14060306070c15 79
    0x4040070800d4003501d4035001c8605981152720036000280703900e955a49081c0c541d2810000a080a00c100300200011030401c000035024810a10600368066115540b480442d1000d10181e0010b613800b0700184407054440744041e1542c1000c040e0039001d000c1031014401c0c049618007a12044811354030207012480710b540c404035148885c461ba20041181c080140c5084070700944105441809450740016420584810090511220b644210b214544800140e00418281e004980c0340c860115968918090540800c1c1d60000344070002521940c08034081100b4000c0030b42926002d184644c0d5005000d51719541c00359400ea1201c001c05815601950051084e090a0690a43c2c823584c0400040b41c0c40d900040000c100d8a00001c9030070b40c505a18004000e09500540b07103a02c00b800705503025090030180324100a840c00b466211901c034103550304558051041a40c4452240f005542d0240900d03001d05004055064041d03540705d010303101340300016940718811000b08900f0307540309010689590002c507003040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 214965557 1250 214964307 214964329
    0x607030c02130605090f0402120309061603090518151f030515060406020f0f1207061503150b0906061c0504230715020a030804020603100308180f030109020f 69
    0xc0001e0f41d0341d001198a07074030ba0340102e210ba4000d21454032035107007520600007540700f00e21409101d80d1051045004641d5141c050b40c01c0300204540d401c42921260600f201c40c1060707580714640095103010343c00e41441e100b2103614031425500308103500d000101c40074000f4140e400080c81410116411880c00264401c1d008581c1110302d400c2d0444040c0c42040018025500560001002d80d0098085192190007489144203400c80c0c44040d110124030703c10540c46610426000038100c1c0c1e41c0b100c4140f9030941c98020f03000038580100d00c1c400e5045500d40b00100400c1c4040041d0f124007814000201c4138500442110302c109039281440103460a100c0211018240151007107072009800076888520401007002e9500240a280003032504510781102109040b42e0f40340500119001900010046034101e82d4a5400c642d0541c2c0c01642d0380c1d80c1005040202a0341e0300b00a241c0c41e0300180c020754641d80c0d5960408a0314040312007916544141080500726203075140002d4101040c100302009a29003859208 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 214966807 1250 214965557 214965589
    0x71a0a060f06110601050f01050a120e0a0606090e06100512031b0a12020f03030412030f141005090f07030c0c0b090d0908031e0313020d0507140607030c02 68
    0x209525899900002190840e40c201000040000190010001c1c0400c00580104016500951f4403004200000c280e131041a40034400d206a048401d04188150b038400e4034850480401c2d105d03810418a008005409244148070b0300c0350400d8052000c071000402c00c41d0259070801044003500740782c00c00303000c04030701d000500b01400e02051001911032245221102000d41c141d0000d0082c0e1807a41c5001300c5a0519502500110b50140c600f0313182c0350380000222508240c0241512626103d03603201200a400070300411000d032803c01103c1a800b00034030108600808440c04004c0d0600d03140d50131320010304412244100c0781140c41000ca484035000754070108001402d0320340b1400e00202c0f0f4072800e00c00802904c50304038950101c030748440308990112104000c1c00c58071015514140c44220440f011a0780300110700c0b031031440007010800c500e5500c104c1400305a4041c4c407852a0034940d041082d1600c4031485640c440c0c49070364015400314034000781100c0c903440d80354480c8019450035409010044110240c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 214968057 1250 214966807 214966811
    0x90b06040b03180f070b0f0904060b0c06160e03211e0403050712032003040f090501050301050a0908040e060a030c0308070314160b0c04170a17071a0a 66
    0x10507041c0ca0030000398842c41201d107549000044409a803403070a210300744540c1194101c0041030100ca59684100c45c99140302ea00e00940343c00002000400500e126402140c0580c000a00d244100d0404641c81e481001c0c1100d01c07101203000d006040e164486019901645a000202200707182e61462038000c60003103094116508114946030404d100340b604e405c0c50600c034100858100100602003006002a02c505060020764010580e0090b061221501441c229400089460410504104103880c01480b07001014415107544060110041c5401e0107035034002c3d420600081c590302458004c0f20a0140d01000030b0f4505840e05100e030340a0580a000c4540c4040b00040003c00b140d040c800c1080614001c100213682c5e45c2c094940500b5500403601d03c0000098103001040c40c818180710040016a044103000a00c4e0791000480d01152003103400c030b40c4004a481105082e095400070304508070500c80c0520386518074a03180c00340558010300200614400e01850502d0b01c94103000c8806400455450780 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 214969307 1250 214968057 214968059
    0x80a0c020d180e0711071406030a020c0a050d030204140306060a0b0a0905030d09082b051b06130c090501030b06060d091502181c03050703090e041a0903090901090b0604 74
    0x410310040003d03104d4a0004a1942020081c0c0c501808280e00501c14484d0b04081e0720204004078015000080c03005000a80c00b05d0b2200103000c0501000d03050355449010760741c036184805005402500035000341c00310301071039100314080742c00d00290203802000024081c40d03040d850218129241c5d40100c4001040068000d4001a20340f800c00021882c0304203a1200b6a545082103810751804021245086242c62400000962054403030140400c1e80c44615240c1d940b42d1504501c10006001001038450500c5507000700448210a0a001c9805034031441d41134090a0fa268203020a46030b00b0300000d04545641c00c041441071400701c0041c0401204040007083c2d5110b19202d2001c0b944a507a15139034400c1d00001d1002c1c1520007444c4004a08404031010000d009c4040c07000050035440080003024000006200c200307150007840200010300c0b205044000c9440c0c286041c02406031039100b0b108800001e40c1c08240c403480084195000107401421400031070b1300e01120b640103004003504c010340141c42044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 214970557 1250 214969307 214969319
    0x1030b0f1b040909031e0e040f02070b090c0f03240709030605090607032009100e0901090c02060618061519090f0501030b0307030b1e07030c080a0c020d18 68
    0x42c0c4018084032000103041c911908000e04524010070040301c0340c20140d2880042c80790442d44040d14501f041e50001407011001089200a10810341c0143c01d40b00207004220310004000b40b940324808040e200440740c0708504d000d2541e540405130682d03002c2000342043c4007900b100b44071003d038840d01e649080c0031115542d441e100f081310300941d04555203401030010860050740601518441c4000d0f00e860306284140400017101c0c40c01040c3c9400d05c50b144120440c0303055482401404603401c0010003001c03955035038000f44001480f1810281c000b600800000400350302d000d1211034005170707400780c400c21242d5891042100c140c2d1203042c2c01c00c01100601041c803525052035003a2001040c151601140541006000e000b540400d900103030400d0300301900320886d03460100d0404202c0c1d034407802c3d01c0c40703d03281d02014524402c1f07103016202200c01900104540760f40d050f0000306170750600b525010425250360200106031080d4200b01005684406083e18465114840050801c048003064007011610340e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 214971807 1250 214970557 214970611
    0x150102070905040308070f0f050d0b0a03120206071218020907020a150905190507270c05120a110a050a020307020409050f070603060f0b07060b2107060801030b0f 71
    0x40c0e002c2d40020b134045d00b0800410307000709146503000042c0c200f10a0304403d0b0f4400511600c0744250100b01d0756210341014000d51182c10450021319801681c0f61002400c0360310003940c8180488400c40040c02e5221201c41100f03c0e0b1142c1030b840006080e1103502c01b2b419030284a002000500f80c1000c40c8104401a800f1a440c040c18600c590000340c4041400146414001c1c03810090b503000618010384100d1000c00a0300000b644002c4070903003d0f0343e0500d031614031000e103100500601ca0700d14650030140c0780446594014014400321501150054240d143c2e1a1081d08940390020741103e101010040000301e140504007400084c2c8141c81142d2815020742e002c24140c9003451000c50f0594800001010600b200380301900141816185c100002840c1014110425400388900490ba40000459000b0b101c0503030802c00e01c4174805401c0d03549400ba80350021158008c0540208400e0003144004140584a0380707445d4100d0b60441c0090301107845140110480c40c0d0b02908240c9107145403501848104048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 214973057 1250 214971807 214971811
    0x3040213061e0b030c0403030e0307150206010e07110a030e04020f27060307020712020120160501090f1406090a140a090501030201050316020309030a060608010f05040803150102070905 81
    0x450040031240c9034031501041c0b00b115040b030b6030400002d00030030069181000948049030b4041c90081d60034820a404241450001d8100300c050074115081000140c1d00002c505040751a1030b450204181d440641c00c0741c03002c800e114801d4240d041a0030080100344107905090f0f010314014401860b149880c2c90f0110650f1000b000d110641d652005084100c1685242d000d1122005070f440c54907600d4000002900c501c0c03540103421032440028500415640300301080e15949a044070781075414100090920750701c101008401d80c496a06500100300b03544114503001c01c0b82d003100c1c00e0120060070074240c40030308614107443c2c0303410003c107001082d2150b030b0307080f06000186076a80050394140503480c180030481400303170040208582003000400050742d000b4104ca030701c0720402e14000611445030b00b0407411032140020075580b500c510400102030210395440700c400c41d000c0302c00802c24801050003504c01d07a2021540a442c0039000d00000c0c0003034400d1420400a210144140c821094440320305408907881 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 214974307 1250 214973057 214973069
    0x30070303050402030105061203030a090f0204020d0506030705042304060f02160605010f0b030f090f0f0309040f06052103070204140f060f09070f02120703031b0503040f080304021306 80
    0x1c5009200c1581001e00c22550080016920800f044041c510300d5560707480f001d04000c80c80341d41d60000205012000e10b06484042d4028000e566a0110034cc041014000548809200c2d0082c00c000050390b240a2003840d440c1c02c03401115804003c00001600b0821100900035100c403500d640b492a880d08251000b000207920704481c0740c680700d0182c02c181c01200d505800c128445c0c0c05910040c040c100040c4280c0c2c0d405440518500c3e015a02c290f5024107080360340881d81d14a100303601c01d464914202102801001e03005542c200008050800c005041e2046072140d03a4200340e25600850a0720945800b2080c5407142000700d03480c00c5490b5021400f00c0b407204000300e600d40883c4007440302808806003656040a82140c2c3c22800c4942c2400140b00d145000d010b0f0010b03c801401c5140401c1d00038855084e2151050b0029915100f85040280141900411560030181d1021080280c03030b01990580c1d000310f4011600e09000303865507444c00e005034405001680d000c440c0c90440300d042e0080d070080e480a031903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 214975557 1250 214974307 214974311
    0xe06070c1d0c04030803010509180106150e040902100c1a0702030a0905010203120c090409060615180612050a0612050a0b06040b0105092407120f1130070303 69
    0x1c2081c803000c040d00038040d031444110400c010400b040c410801e40e419280101c800d40c1d01511541000684611000c0e0851810750034008009444681d04884006242058542419941d05041003004031981840000e60200f080000444154400c01000c0340c0b20303101350b01000d42640414621107090004490800042e0300001d2032a00c81c1d0750000005c4010b20081c00154285058032100010710ac000070018104103001103a1900300384d5881e08002051a08000104003181c0c030303000e1a01000d0400318800f00440c981d01c2c3d08042d00c2810040110480b4202d503504054101c00300d2180700a000080d0036002d260b0745941c400b0800004410450f00c110b4440c40042c103505003075203808143d12900400c03943c0300700d281c0b22401034540d070800c0131103084c01c4044031940d0700070038510f002c40c1c00c01000f820300140e40c540c00700d165010051071703404540844c0c440d81c40c0d0f5903c020390701d50102c9455082e02107100e80c40d0449141074400c01c01502800d415400b141c03c00c0c0c2c0d82140400d12220058201c0041600025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 214976807 1250 214975557 214975589
    0xe100504020f0603150f010522032a0b0c0327041416050c160b0301030501111e030711060c0d06080a0201021207061e020306090a05040b070e06070c 65
    0x3242011402e030300c2040a8884606500d132900008607101550851300b40038150b000340984c0c42c0e0703220f0b204548096400b902c080e440380e01161169109100742e40421100c4054200c04850480c1c101519205c0001441480003c403d082c000e031740e00f06400c501d40000d041c0c0b009100301c10940070300b01101c81c0682030b038101000c00d040d00e02c001c101c141c800c03030b14520901070115400c7c4000840403175403a00340d0800034281550354a1540726081c1c0b07400a150b410f101820341c01e40740402c03956989001981242d010307200034030018020680750b110394840d50b03a80048c000d140c0c0091110100014019581c041c20780d00700034003c5020001194140007085403401406e00300059240c007414024403d1001400d100801044d02000c1640040d6441c50000700e81c22098101040200030008a07400a42080140c080d0f401d01540e8200d034544c02940099030804d1150b5040c0d80016100412486041d100d603804c40e009441e40c1d00c0d0600c00351405000c809038903401403410406040407850042100008142012005001c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 214978057 1250 214976807 214976809
    0x609020a0e19030b06010f0c170a12050c030f04020d020a0e06100e0a050108100f12020f0402070b180102041a03100503060f0c0d0605100c170903030d0f0e10050402 72
    0x20b03600b500c03481c54040c0c240c1e814404640910400caa00403003e00340302c1a150213140e403d80b010507002e00020f000040d80214140102078084c0034058100040d111030181c4003511204d902940d0080f00c00e81601c020620000340040652011a5040323400074004030b071400304030303004200045841c0c2c0182d004c2d0142c1c4e2051040c1c7e401d01801c10342c5101014545442544085000101603031a2403050604201401c0003044800c0c0d49408503c0040c08100e0000b0f00e516510050103180b07030700044082e40301d0700c294111018541414000c43d071036603900c05071484040d42d40d1450902c54a40c0321481c0c081a65003800081031040c0d44040c59024420810401c9483e0f1a040c0083c0c502c010040c3c00150194024209000c2204480f41c003042c0c014030010b03040b0b0b0310b80c6000400c200c01400e0a910aa0303120049001459a03160411f01010446005844405e041100ca0004040c5031190000c841d4050b403007049400c03805000e550111025149421001c80c80c44100e164940c03038940c0650f1041602507840042c4411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 214979307 1250 214978057 214978069
    0x110d08191a0a050a23040213060210060e15040e0708120421080f0d110a051e09031e15040c0f080a1505070e03030c1006052b060609020a0e 61
    0x2c2908a6490f0741c04c41c1800c542104850005400c4445081142c50460b440d5aa40c4c064840c080418064071100580c3d5840c000d6075110300c19840340304207150410204175090506042c6100d50501171841402094907414031008200d102c1240000303008003400464544424403140f45241c3d1ba541e10541c0780c2c0d05001c41c4203c0b40620350384001c0320041041110000444000a60f45840c2c88200610784912407082c802010300716060125a400700c00050b1070b0b02c141d07000320160002910812072140303034498000d496140d43c4517211009a055200481c0301e015a05001851802c0c070070f00c0402e07500790400328210b5081540c000d540c1101e080b000c0700018010810080306c184010612000181201c0480d0f4403904410050b080d00860144d80351000030750700d07038040c1c03040741102c04d405400c4907503590700860050f0f210300d0850404400b10f0304040c000180c626140c1c8a030781c0000085403205030071104080720380030310aa044004035031041e100d6600042c56002c510140c02e07940c041c0d8691b05a444445410820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 214980557 1250 214979307 214979309
    0xa030e030109050c0d0503040504020a1e030e0c19080a0f02090a05100b030c072001090b03040b0c1c020412020414130204020a1202040801060305060106110d08191a0a 73
    0x8041d078908800c220100307034006030702d5407422401d81e800030700486a400c100b41544599081035402c00e000086d4234100c0d40c5d03c402740750600790321100d4900ca1406080011026940800c209001c180c0c002442e811091524211045801c0182c8840d011036541d038070081d43c1003070704441d42a2020301d81501c0a90640c1040d5800030341c8031280f510f0411081c50142c10071074034000070b401515030100c1c9c0800003698040c000d00441d1046600303e5a8004c5050380e9a0b28050f06400b56004d190019070250000110a01c4a6090f039001e180c1c000640c4406546072122860f440d00084c4000008007407013405040040030520061001c0c1c405021403404010301c4c3d00510007524021074440074003001c18420091031043c0c1c02030380003040b0313412600580d44103004c0d10216883c4c6040410f410b000c0d840040d0020311810150700040889100c0c1050341c01c142ea850300d003690708412002680d01c543d00502c44469145100d42c40c0154000c0c08542501d0b2440e54200810040300c985108060464110551300701c010310781044114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 214981807 1250 214980557 214980559
    0x703020a090e130c150206070c06020c101e0207030512060120010527100f0b0a090204170313060804170403050c010e0604050f04020913020f0a030b04090b1f080f0a030e 74
    0x5c503a140c0c003000025551840101102c04110301d0381904020015250125900e4800000458403d0f085501150000304612000007259800341083c4000010041c002d42d080d85816440b12828035440361034150100c04002c044504021034142c00c5210070402d01e0108990fa051880001403500d0703c181ca0700c0c1e0701644900c101040c20b070060448600e034203001848030a59040c40401094400c1201205800b400b10743c59102e134010070200d4041100d40d255806071084510900d450459000c4016400d42c680c0300300003030070081c400004018481e0600413101e4540252280e04500c1c50800c17102000358070f40d04943c10445503a0810761601c40f80b580e10440700c40d46224200e91251078146004006001080d803003203018040e030340100710095207549a92982e1550380c0d6042096564440f0401841c1040e0310640241000c42e1a00c0700742c0c1154242031140301e070b4941c0e02503046007041d200c5022070040d199000340500d04d03080040502043c061024429000302c111790380020650182e4038a000340001100961036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 214983057 1250 214981807 214981829
    0x2060907030f0201050d0f1802090c0a050f03090a0f06020702030d0f0206160219080901120b060f0d02070c0e0601020f010207080a0e0303070b07050a11010c080703020a090e130c 78
    0x1c1c03021811080440c04034940c242840c03540c0701c02c1440840050705440002c81c0c0c4582c641300c0000c2048041001200b8014400c403104042542e484da0780c0000c0e070103007045800001e60184500d41d8095178030307401036410440003801c43da02038983d645c07606001010301c20102ca2042d00400d49100b1800c0810005218214905008411844100b4001e40c1d440005000c1c88450742c0341440f6540b4540244076150825081c11301d074000e01c40719030400c1c495540c01024203070f000446203010040b1000d058403541088000040001c2e10b0041c4401207000c01d900310034102907099031b080102c03c0015442004030401802c0c4020155542c1c80d280340060308040c10940049040c0c0d004005023000521030408035003400d012030078054111064400801c4c51801231150003001c0200820074800d18940000250284c2d4685503140c03400c1d1840904840c0c00d81e0789001400011400b0600800c010380c4c042c0c0c000c0c2c1401c000b2480e08841d000e6448020150301340065400300d16080d01074900100707212070036134080c0180441c007001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 214984307 1250 214983057 214983059
    0xa2306090a110d050709020c07050108042a050904050709110702090a0e03130303030b03010f020a020d122c0105090f0604080c070902030a0b130b1e03010605030a050a0302060907 78
    0x6a034581031101c2004000388203410603005203a64500c81510300079008022a0380349a12111010000c0d031203002c1043c454820303450b00040b10741c030402800d0f210300e6101c11080d03110307080340c50011243c0c00d04840f0180d010303038807000120741313a2103210405124501400c0180314062410209904640b2a403601d000c40c10310070030203c00580c584c1840241c11801e20b540010b1039403c0842044c0c1503001d0684c00c81d1070310303ea020707000042c07503407581010300c1452040303008108101c140128807040348141206c12000d60403c2c0d50158450b805201c0b0f03807042072a06840800c2c0000151400c641c5500340012300381729280d82034a4560030070800d00c41c65a0200c0280010013100072140744090b92040700400040101c1320002c0c0101c00004240080300c001d06000c0004d540781d080901014001d0210340f81130b2b5004001707964500c007420109025902e0700c0300c40070303190a0080702c1c004803032101a43c210415039010741d26442c00181341e40303042104520503070043c005841080780c6460024204040034206040742d80c41004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 214985557 1250 214984307 214984321
    0xf03020f2101080c0f24070308090606060301050a030305030604090204060602032a030712020a05010c031e0624031e020919080309010503071106010e1006020721080c0a2306 76
    0x40005c1000c82c04484400e80040c000e80500b807030f1514106a0b010840003c28000100b41e00000046d0041042c0e000740d401a50b6084140314a42c002403081c1503012920340d00c02c0011a001c0c500440d042600035202061108607a0082019a072050b4007441c0160b100003100c10303042c180082010107408450b10030070010724000d070f40c95a59029110000c0c00400c498042d542106000304400e18116a04c40b000b0300c410780e10004058000c0030484105038140b40740503818005810b0500c035000c150b6181d4403a40b1745401909447e1740b445910a00900180760340d0740c03402c030306a14a4500040c1c0c903240121001d43d40343702030b03800c0c0800441d400500c64001414150140662503003c815113000c3c0000f031a0030341d00c81e602c803581103600440084860a65024080003c1003110801c0c04c202d1194203030440b04100a503544908036924480c82c0300d00352106a0040031004000d0015511808150282403902c0c20106080e1400341401d000355030032202c01601001c0d51070340d00c030381f04c0b101420541034a000e0022460400c2e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 214986807 1250 214985557 214985569
    0x5031006050f040e10141c11010210050c0306010e06040b04050103050c070f0f120c1a0c1210180b03030702010e03010219020303090c0406030c060f03020f2101080c 72
    0x3005900c28040085064003403004401c0907140100b035a40e200e00381034106540707000c105051500582e649014088000c042e5410046001d459401c4026040446600c10b5101c1e4070b29035585404240c1103000b0001413068400603405064040c00340c885410b0352740e090400015080180890301c041c02401c0c1400708200f4403070f04009450440704282400305840d521601265210f22031a040113007a82400035105080c0003420b88003002d003d2044d4000120052584000c1d00c4600450900803d1032920300c5c02102100351000381e56400500d820301150401c441c0b91104900007000f01c41e504441100180704001c2106609100232810020682c100109002500481d8891103100d5010341030145e06c0d401c0c4821510250304039a940c02c40f00d181381c005a141204000d40b0380d030055078900854450800707910050701d01882140202c035801054044014640541690b0340081070b03200205060b801e01620b40e050100c0300080100c034000b00e910f15045100d1002d00d14941ca01a0440849a8041c154010f0a40c0b101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 214988057 1250 214986807 214986809
    0x1305030d0206130305130f080d080109020412020609030c030d02150c07110405100512031b0f06040210030b09040c050301052a0f071e0209010909020907030b18040b100501050310 78
    0x7524180d50782d0b506058450780b080300c00d1f9000750003c02c000e10001a9402002c00c0c05107000174643c3e42c050b0721340d80e1403a072082a4040d5010314ae2101550440460051038101700401d504003014043e41d40144014000a0504207141003000140c0c100001e89601540c5481803240d025415001860a00d0311546800c03c9101103808440d004644c0c900226010007201d04090006142c000c1041c0d40f900d4031411016241d0b040202401c9070b50707801d02c420b0420b0a01c0880e41c03c0280d041c0000900d4555102e80030084010240b0440c2000d156075969a004c8580b50801010303c40d5000b1061000100e140805040c01c6420043c07480201c1c01030382081c00c0364100d40c0009103040c3c000390654161030303920712134420340c8070b1140700070043c41e200c0300190012003807148401046010740229000d0040341e9a0340751200079600440b000962103820b001c0001d030828025841191041c5000e00802e0090003140d00c040100d40080c3d8080e1054414142003099100001103110043c0c0020b1070424110b080a45e60311a500c0d02d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 214989307 1250 214988057 214988063
    0x4090606030b13030f080613050106050a09080f03070201030c050415031a0f010806091026010c05030702070b03040609050a0b0f061806040903050903120406022a10030609021305030d020613 83
    0x401b2011170115900d94150b07401e0585054400c210a5a41d5600604a907100003440f030082541000001400d00c4003041c4108400b20602c051890940703d03500440040c8490101c0070203020050101040007011a0170300807560b8426100007601110648200c2e1000023600422032051280c4000c0c0d409a0340e2090060340c0200042e5600304050700c40840c0c65601200c02e800422459041200806000e01c20b84c0741450715000c1c0e140200030444444000311101d100803101680503912110041105007440002503900601074000028440311540c4c400d4184281e0b000240d426200b080c00f80704454007003404050300260b04603051540341d02803518000e02d4120040c89144100d41e281d01070800d05002d582280c1980c1001420f550200482d51800d55564000d801144014400c06503241402d030192208070001080d0010b01030761002e10036080040840c8440da010081540307540000484821500140180c40c0359050003021050620f014503203810f0049964600b1507000605200e4280314100f100710003190 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 214990557 1250 214989307 214989317
    0x6051203190302160c030c0f062007050d0b060405010503210309030705120c160506031f0b0d060305060f0705090d030c020d15050702010905030f130504090606030b13030f 75
    0x28a050250b00074081c1410035040754401c00c59050401c405134049400366445448a800c640740c035804d03000803011241c0074280c003003440e50015100010b101c100b0a030105900f80101c1c4d80a58540001c641982020030084903080460024402e4601e0240581c2d8090001070340100041e100c10101c400054091101d9a00c0307100000020800201090048649054003c81102c03468140c0c58915003841c2d104200c00003060003448041982800910440b6003182c200808040c1561a04642a00301c228420306002034010380300c1c00090f1505620340902400c60f03058800140e040c0c61418890f06080c1c008285413142002d030340070051402e40107400d540b10b219040d20407801c090154a404d07140c030181c04401943c41f90203a00a9020041e1400041c8408103101c072007805141c440325401d030701740c1c1d44c038043c0100190418000d15188000403400780c1382c480702c4019521402c5640d0004981100da1825054550702c0d102c01040c030a01200c091400d80040b43c1030710558007442540c400802004e1741444000c1044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 214991807 1250 214990557 214990597
    0x3140f211e070507080f011a0f010c05070801061e03021c0f08030a0207110301090309051002150a0c0201050c030f01090c030902120d0f0f02071716090e0106051203 72
    0x1071011110405590000361160ba20340da541400307075803004076104000352445000c0c544007280c08107000326080012101c8800162080500400003641080c007a040e040040d10040080800c6080050380010200031000041550400b4910703449074005883e10980440101020401a118a20191081812080030703003101645845c1c07044604013047d9002c2c14500000c422f000d2456a20342c01403040781d00c18a003901002c0019002d16099514004020340440e10540b000c20980c104408040c158030306a1064840400c031425084015880648002c1d400783c0d501c0e482241c48580912440390050418403046017907240211041100c1d07881401303000d001d15140c1d400c2c16040e41c00f9400108000341d0003001d0301c1880c9101000e040c0d0300c1e401c0d220160009604c86016500e903501416200c582142d4540c090302c5514200311414050040300c0350703120014410960f032140680c5041e00164058030007924046089090308041909461141d0402445041c6189003940461070010031141c0e49181e05440342011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 214993057 1250 214991807 214991827
    0xc0c090912070302070f090c05070b0a0e010905071d1311040615230301050f0415030f0803010f080606010903110d02091807170726030403140f21 64
    0x1c01e88441c1c03984000007003108020950040b071400c050314801628220784660b110030300801d07035405000301400305501f08007240100746041c000680c001030440000c80e0811105200380e003151b9107007109071807640100c2800c0c4000d0512452604000d4011a4030801c28241840000002d00e280f001c000c0403902103100360b1005407680d400c0340c00140812407148203401c202e5100a0315070482c0302d41e210b1001c0c0c118030070306001141e03210949050b500080d00058401c0104002e0100500180910794580740107048000000b40034030000f0381103140b092020079102d52505ca10340d19410007079001604a500700000700070307013640c0c090740360412640c0054410001382800d5011900066450304081e41104845040188a064180400d104420000c0c04c85410a03038400c0c2d0f20311140c030300800c0040c0c96008540100446441400e106c800003191600040c562121249102e14650099004031002d808004209008039024000500f0480070300b00502008100b00d680031003031942d54803a003102142d0102c1c40500e8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 214994307 1250 214993057 214993063
    0x32406040621060e100f0b030a05030901030e2a091b1c0b04090602090f0108040b06121014010f0b0316030e010204050a0e0901111201030201080613050f040b0c0c0c0909 74
    0xc2020b00300141c0f900c00720750685e10b0703001e0413a43d44002001070030005081ca040c00c001130b0000070140c1040240d030070310a500c001100500b000300f848504d1849032041100740c0d900302c0c01700100d8108015000030010000d14080c0701354040020300c56403061512140300d4441c15010400c80f600c922401d036580c070300d00c00c141421100504011020a4215180441314001c01401c5c4d401818003000444182c400b400f504c200444440504480051010815002244007030034503280400606181900ba0760010700b01c0306c101b0b42100c80c103514020000c001e8400420040c00c2032040c040160a23141d080e41d145140c06000066901c0ba0240030204055403a07910300340c106800c1d0705a40c05008003c01010405645407035a6407032000550301407055520702020f4202141411086034004e200b00c0e04101196803850300159400d00c1300078542a0000b0001d40311140540e04d61260368400d400511114203207052a06100e005610028200a4104420030100c0d5002d2400108102110030803500c410040e07a41d9410941 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 214995557 1250 214994307 214994321
    0x2202040906140906040204150b0f2d0d0b0103020f030f04021c0602030a0f020306100f0c020901090c09080105061e03030403080a051b01060b030f070e03240604062106 73
    0x8000c00c028400d000e10f01c040400c3d02d0b0b010790700844e0140200c50340d09100002c0c0c520301e8030420710900410081031b920940e001015080001010600b0041d014074032000b80f1684a04031030960b000d010014420000c2000d611034100000828070301142070041001d4603d9592102500140c0c4441c101c50020301159201d0301d1079851029560100c000c0520740d03240041c06500700780d86003003544c3c1c24100889068810342c42540c2c4100301c01825503240f08100001a81c2403450300c000c080400019440c0c6c0005a11009600b60092029680000d04420309500043c0f440a0b40e400030401030f418a0280301c2941d5a071915910762040200041d0040e400f0100000d01c2c521559000911140d03000c00c00c40021500301703000c3c102c0e00010000e02c500484140310000e0884540d030082c914014804d0004c10802182d8482d0994010940e00b815181c444d547c1001034603003201805102210584c90b0518032141c0791440310540c020300166004d100c40303030400400340340e48500001482803a0700f48100050038044903070807030301e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 214996807 1250 214995557 214995581
    0x301090207020a0819020f0f0306011802040f0611190221030c0a0b01050117010806070813050109061b09030c0b09010c0605010f05180907140301060504110d052202040906 75
    0x1443e0240300c000c00307050390f04c02030344161f1184e542c40703000300502e0078603a90180b4150001006800c0c0307a802c10506d19641d810700020324032426400c0c0408181d00c100340c55071030081d14103510f904c2140c44035040303124580f2801d86c00405010303c0740503000006032a20b07844141d10078402106501c4891940c05800d2a5010784c54003184548103402002040c0005110380038141d90080e40d4180101c00035080d15880760b0030038412442c56500484c005040148a618202e81105d502d4802c0e201e850030a440e03081c2903e411b054140d520a036214100310450000c04c80203010b23280c1b60b0501a011625503264008494600d104540f01300100044a40550784901d1600001690245081010f5616001038901030000e501440c0e000d181a48441e820025000080c244207000c0d90300201802814508041e8941414000b01a095900c85401280303a90b901d0040764a41032610119544031003550300d1500540d04007404800c0040705200384010305618403004a025250140d03400703e551101c6140ca04010852100c0003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 214998057 1250 214996807 214996813
    0x201180206181309050d0f08130201090312120b1203041701060e040c030605060603060d060c05040504061d10080607051c0507050c0c030303070e0d06150f060906050f0301090207020a08 81
    0x15000b0f91455841003502d40d0141c0e00f1515403080110040d580000b9038910400410400c038001410400411a42142c451061400c07040c0d4a039070b943c0f154040a5807840d01004200010002c81c080f070300520034142a00d06c2111011210180e1201090700e2384102e0240d4003805410060400030000250401002011a02c0110340300e0316040c20800c02541080c01b0440301e150808010401e1071500c10181c80c000c0900410804003204141e41d460000c0100001c0c0c041485001d0000258580d60391090400400c0030910725200000302180c00848041c0040c4056260003003884280140c01c0c000a03619403002490a000765111a04002d0782900700400305440c144030304180070400b10981c07041c00703000b10404036012904428600002c161300c2e4081240c0030f500140d03a13a150120b0b14901016800c402c58083c3c0c90014100f550980d10020070100394102504c082410403003040b9940d44200c419000702018503000f0704003048079641c2d29141c407040c0700b00d50a00c2d4000c9151401e550b503203124000100404412 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 214999307 1250 214998057 214998079
    0xa05030703030b010311040b070c080f01020703090803041d0a02040b0703051206011d011b0501020403210203120106030e010b0307090617060c070b0903070b150907020118020618 78
    0x105a403a4820041100001e0412044150070f500030300900c2814403ca40c4002c0c00d0a040442132881038210b0281038074140b44000300065640401c0c4015000e14861800150780d59140707003005082c102b42e90748103ca5035030082108101a4000803000004180c0544401815445141905000c2e004541050ba14890000351080406810100034031503049010490584d5665440064032014038500d04403122a42c1c0302a0354500f5841081c10068a040e07901d1004580a56500c0b4a800c98000d41c00c02c42d130014000c400d00011005800000f540a0414401549803550315402000b40c0c90341031042c0405e25446028110180304290020410b50f84041c0441d5811985e41c100d0038040c007040e2080752400b0280301019080d0150110300b507841203568001180c545038159030342c24103040c0002c00401441c042402a00001000100c80f030b402007600180203011002110300700512110090300680943e8076240041c0001d8680f01015440d080c2c04a03072491300e4012624035142211443c9450a43c4400784103c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 215000557 1250 214999307 214999313
    0xa0c0806070e040504150510090603080301060806090709051c0206190806030a08071722061e1b0c080709060906090207050601140609040207060e0f1c0c0c080a 70
    0x51014403034a030742d40d00c010b24501101d00744004c0314426100941840300b440101480043d441c3c01c8180c01103018403101c0032031550f40a0200807220150400c80350494004010421b07554810b410b190040400c07285140641800c1030054041c05007445014094540100484e10070011400700329082600a480a0b668000b5280f180f85191079030105440454010800304a0320700700003078001c06403507008211510b0410582c442402480782c40d034640703004117020801184002128080030704a441080440c880c4a1300300380002d015003070f0001d0161040300640d40d50701c18055014160b455004c0b840b0320191110015402c0c041560039290704105c0d00c902c1461f000050784e900350380c410307811a2400b880800c0240d890b05004401da200e01d04015015522400c0103125040f41c9268210341000c5c02019203103400d59100c0030a0580e004170b241075030050782d034050328007101d407050089400d00d08100010b41003028104004c00160280715001504002d61654140208820405036a003d412120308643c01d40c08146 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 215001807 1250 215000557 215000563
    0x509061b0d08011203080903070212070f05010810030b06031c020a021336020d08031f08030d090201050c2b0509030601031202101508011512030806030a0c08 69
    0x2a0000e581c0714000000103001e20450001d410381d20303507a02843c82405191011241c000c0c0281c05401c01c0c1c001040104016550380010030030301d849443c040c2030083e290070381900c12401c09a100714140b080781802c0248060310f44404805507030b4001c1c02810141c440a0100b032522040c60b01c0001c0c0b881e4000e103c50f0340c0c643c000514a82c110b2080741d0b0000706c0c0c1800d21142003669141801e1125007040324007000c000d0f05983e00782484282800e500c8040300d120580004042850014082d10200c00000038840305d00e0101da00000301c0c6240016120b07080f40341c0070502e55244a02c2c0c540c801e10540e60122401168450b00488074100101d80480301c1140c1c40f0190202d81445404440a003141654100090a400341e004d85044032401005044075030700e0740d29204000041c841c950760440c011000d4040d9000014420f200d5143d818109040a25081c820254211852422140400703464118104141c6420318244088a035140c500030030b50362100d902181c40e1102202c0700402c07490726400c0c08110b01c4800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 215003057 1250 215001807 215001847
    0x21c020910050f07020d150603030302090a06020d020606041a030604050102041e15140d0213060306051206060415030b090d0306090504080313050c040f0906060603050601051207050906 81
    0x4407840020509500d00540d424400c0000003503c2d803c0a0005001524046030424003041c040e100408041100380c4031841154002e8000320040707940800d4030600c502744981504054401030008003580041d154000e9921035000341901e10481e21441400c0c0850b0b45018517003a8444081d01b154410f041c01c1c6041400307034020380101c0750511041030200002e1000e444c500700c01c031aa04038040d480792030104011941c00643c81b444082c40c820070002c0350070b11100d500c0180404156010304581490404100070b050300c209501c0b091050b0b00380c0c103112080030b00100d9241c0d0007000880740028001c500200000d42030019a001601e0500381004020405001180100c1080c1700f560b0100110341d1184c01c4803003101c1081d02c0c01307400e5140610001c1ea00042c200f0b01111103a014104485922414200003426a03500d40b91000303a00380c4407240f03042008003901a0602805840c2028000343c9010800240b09020f921003900768442c594000c5040540600103c6034051000740686a071880c0d43c1d041000c04c0030301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 215004307 1250 215003057 215003059
    0xc0403260904060b0d1817030405011b0f02100203090d03020304020d0507030c0314010c0801120c271b02120a050f07060608150103050c06091504081c030207021f03021c0209 76
    0x6003003040c20003504030f26100300c0ea1303940030728507504980c50f44200142030723000200219804d40d41c444c81e440e910303449c400d9081550f5400360307036001080f0050701009081030a0840060704160061050000d12072001c518075138005150b140050b00c031754070790002407654030070072602420600800c0e41c04001c1c828058a24400e590040807501ea0800300c07400d0190885282c00281ea0006601400510404032241003c02080340160410502c13651940c030005070b1180600b0380c0a5440c0c000a500c507580003590f0103032640c4103480150101c20b450709024080c0d20380341d2000503107060900014109080a004009541d0480301c0704102c1c0b901c4080c0c1f46001e01c01001907010b000b200344501d200c0d0122110300b18038640c0c10f0707030382c018090045030312034900740b10700ca800c00c03d0440d83c0030002a10720944a408400030708007d00c0d540e0010800000c08034281c00c0540c00d100741020401d40100910800358448280102a405102408030100e15003d07200714001d0007044511045501c80b00d480100b111003580207000d2601c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 215005557 1250 215004307 215004311
    0x53f030f0907030f030f0c051b03120306030a020105090d0803010f23010c03180815040210020f030a080411030d0f02010507030b010c06050601051902150c0403260904060b0d 76
    0x201ea0500582d25003a521004103946032121100c00040d00c22040c00c0958020380c14030007013410503581d41a083c000700c4038404846010245407a1580d1a040040d00d91440b10000c00900c0d60030280003081c0c5502848402074107202c80003600050760345950480c5003110785c100b40090340341e58450b01c50b070105105a01c290607824400d4600340c817480070303003280e0121505016101c90380e1301e5000740d909880b0040d040c1e030040c02004800e0700000e1400c0081c08900b60070403600c0e41014840c686441040843d0840d00c03154401c660000b040d00340002000822100810590300306032400d0742d103d10344080c3d10f0070100545034050141002281070a504114031030545005a002400656161181102100c18402805002840955241c0d006c030f01d05a10640c1c2024040c904240f03010204140f1810800d14020b405005030300c040103211264801c90049900301c40310009407860980740d901c490070341f2083c5d040000480c40781d40d0f5204400300e0400044511007080940203000c0c49940710720070712a94102012030b0301340074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 215006807 1250 215005557 215005561
    0x40506011107240807021b0301020c0a0302031c020304080703080415060620010c020309061305030d0503010f0504060e181c020f0c040c140703050f0301090c030c020a053f030f 77
    0x41c01340301240d00c42c0245a0080c038456405044140d26012000c2907590155402c002c04103512000b88801c0345028082c0d0000c60765035041d04101c1c20051804003c0c1d104c000d105205200c00682494100c80003244c2520701a0701903101d60401800741010520300403a100d1608030001650794004001c1c1003400e11201442801d481c000700144c6c240d483c03600c1e0300e1005030030401c201c130318600d0540064000c80d10b01e0182d100c15191940003103882c2c140a40e280d03401040740132004003d03101006035100d000d44070030b4030140407a038540001d0862446010b01101890007e640814030020001c10600440c1088800342040120318460007030b4503030512400e1042240166182e100c0d40d810036024a603180c40d203942d12421104900d10303411540d0f8021000803800c100c0b08016500f1403058680186028058032400044c221b18101d4028088800c40008481035400c0740800310f021510224400002a91003c0390001500800500300000304414081d00440e280000700d90f99942d00500245104000c0020654416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 215008057 1250 215006807 215006879
    0x90c020706090b1606060f081b0f01030207050c100e040e011404021909050103060c08070e2103040504050c070302121c0b0d1e0209061e040506011107 66
    0x3a4001d00510000c2403184804010980c480c1c001410492104440b80c00d00408a546150940e04c4551103125600c5080d1003e002107442403041c100c212048c040d91640540b03001d07002c80c8002c407d60000703d05169000c00c40ba014810144801c00c60b801c401459804e03244000e100c00f41c9200304210030180510315201241c90782090520070042d9182c104082010320350707159400c0210b803440035200020405042000056002e5003030140c40c0c040d61041c840403070300c2031040b5001407554034010980010844d51482041c1d0030780b07407890701c500f11a003944040e003c03c1d21b00c0000d0700d08d10304c126801990002d280208002c5d0384d040c942e021b8908144640d09a0784428030f00c500d01c0445006074464140e41c00c0f0f601200c100341000c0f9030b1003aa10810044d108100070b80c40f640b9040501700b01c0078202d02d072300d0704100380140131441c18250342540250100c0f000201c0c0020149004102002440140e0003665038001049581c1e0099050000207421503007100c0015460b0600142d0b00c580f0780c041c105030103800d040b6180398 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 215009307 1250 215008057 215008063
    0x3030a06031e0201020c0409020111120a02061b07030e0f18010305070501050f03070f090e0c070302060c130b160f0510050c09130b121605010207050303040302150706180c090c02 78
    0xb00b074051303004080b00d8601c00d0400004102012040341802000c0c0d5041c03080e40024070024043d2020700290545070313468170402904001e00104054100040415030900c280e40200545501c7d41d0103242280c480705840380400c1e5070111828807203030310400140c815242d06805c0500281a0380c0b0450541c3ca00c0e03071781c2d0801075030749001d80368201441c1042400014038852160a80c0d0324522054941911180d0350b411400070180816074107444001d000080c001e050580412441d17130090b055900c40c07881c00000140c07600101c04180100c0c80c0c0d403000044c2040d0144c9003440c80c5000e003a003103403c3d01225a03551603c2036803213240d04140b081103400c143c0010b0202440341c0940310041c801405a00c0f840040744040001054030018240d488140c403900300c5c00c030001c10050030b4901340f210140000b83e0783c00d0100192a00d5019480103100307038410881413005882d070000001000702c1925855850300704600d005405400e401010039100846034460b0300c05d01c42524144402c5444200e0100102000840e0483e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 215010557 1250 215009307 215009363
    0x108070807080a03091a250b07080103021003020c01110a03020a02060108060f010b030711010f05100e0c071e08070f02010314091c0302121005032e02030a02040803030a0603 76
    0x2000c205d04003020003c10807100e40c4c2a498070f0b40d500d607062504042d03406648114241804e126000c031f5640044074200400301c00c0c0c498005000381009001c0758550750005084420031900d40c400c15401103604500b00c10250400e1020016440b80f040e221078070120000c00a4014015241c0140304241c0000782c08840032400d107008520405000d441c0303038207165009045038400f42a2404010080354088029030007803154010b6004079141c0407445003800281143c8100c01900308000c4a213448091081e030200301c80403030b01c0b1194010b240b903003101d8021203440d079a0701c508c84004d4890400000c6c80e20401c80710f5064402103034403d0b28204a2440c11002d13000c040c450464102c00c480d80000302c5031165000803001d04108030141d1902500d0112114092020005e00b1350700ca103440c41688200b44018a01485007c1e1000c15003040408060200c0110305034215480007600005030340000881c03000d0303d403501181c0240001000f101d41d40d06148410785d000b00001d00c000d403210b01d005040410345540103201c1076 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 215011807 1250 215010557 215010563
    0x2150a0906031d0303070c0501050601020c0108060904320721060e160e190903080106030510030605070e010810050607021509040c27030b1f080102030108070807080a 73
    0x4021414100e068005151001d0f0390350300705055100220800c00208000d5103d80029500c0e08021076403884e0581c291580030700200d0564000400424469a016a13601d03403100d800c0343c8441594940307007414079036101c410105112986008140e8800340e5008004407040414000440d8059582c8905071050010140c551300e6207030011440c4031020460541290300744244810640b05000180000800d003004580d01c207140400c1a041003041c0920020055034030214040380601074038405540c01441004140103400905a4440c04a903104800b40c000e1005503078449030422290400700c00141c0024214402c0c40e0000765442d0006a90b100c850041404442c0c0c042c0071a03040c61102c2e801c0000d04c408480517007412240500c4a0005a0340b280225801c00e5500d40710603106e4000c4409a400d0840d1a42010194a40c810340400006a20101007036100350079030081c403070202203070300251503960f0715504c059025800800082910314000c11164100d8580c141107480d010394403c2400d0b10b4035030000c409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 215013057 1250 215011807 215011817
    0x50c0613080906070c0e09011a030303010e0402121203070503040506151f110a11030607030b060708030403020124060f030e06070507050a0f0308041a061f020a05071202150a 76
    0x20032610300f848800313090700303610590400300160f4480441000c2800700700c0e05810182c0d1191454545c2c00c15120f02103044100680185103103604000c4440b0708640d004e03000074000c01030041c0d4005000300900c00fa154044405481c55600c0c107244800a065070400e50b4155034502070301021070b000a41e4012161000c2d000582803040d010b1a1110040107681452031000920900544141c40b40000303100d12150a481490090044e10802c0107251a149005000d0014146000c100c503032140e4401042c0c58605030700c501d00c00e580e079a0b41d1a0403405031500030740f0382e5600400301c841200924141c0709480107648003940d0f0380100260342c1c1d40450907260382603130000b4141c2061000c1004148500020010700d402801100c081e41e00d5607880403a42c4c41c00e0791040c0e000601b17900900041062180c1c0c00305c010088136914160a00341100040e149013a009800309060308180042c1580707134000e000c4441081c1e04502925060b90303840a440316030683c0b107201284201010400099240122000d503840b001a5070390f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 215014307 1250 215013057 215013067
    0x30b0f0d02030a020120070e04050d0903051b0d0b0a0b030607260c0712020c040f0c0f080601090b0f0304111002120310180905010f05010b09010c15020a050c061308 72
    0x5448884444000004e8100f24106c5d00780da65a04110441c01488988a002c91b1840c1600b80541004110364622080041101b0100081100091003a604104400011610301521000110442030100000b0203441c2944100304141285030300c42a106901501074504a50b200d040403503100345500c01114500c1d170194a0400305081c03515446910245903105140340000a481d94144010900700c848010f0f07102032400c40c400c3c1002d018000304070180c90300610050001c402c01401c400c201700590350811030b800e00010400d0388207080b80b80c01441100d1b580c645c0e440c61451961200d81c000c8505540001103091060700354203045200082c0c0075220340c050f04079100c009a907440c090744050800f00c00ba240191002c1a0f800c1c4100c00d9440f003207150790000030528201c0c60320b5407d403590b42d1030b89001d051410004200180340302045400c800801d02c0e042010104a10740700c0b210307440d0048404413552010400e440c56541000042055070841821a12550348288001340b104480399002420a103041c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 215015557 1250 215014307 215014309
    0x100905040204020c01050c0a1d06043c05030106120b130503120f0403020c0d0b190609020c01020304021906050a140702090702101103010e01060e130903030b0f0d02030a02 75
    0x22006402500c0108050715203240941c90300e096490503909503842c8074000800e0880c00d9000402d12440c1c90180200064090325807002402d81d000c4d0b440340150400308211314048075000404903018411f8408190741c0004240c24804030610700341c1c003e25002c1e40c81d01e10003240400d0b6402c0c2d072902603075105182c450181d4840c1d0600e0341e404500d00084602d48010f00400e80391180940000d0311402c400e140202c82840c0c01c1c10001c1c504920444114014003007030a8820109490781c004580c815285000c2030740000110b901000288509e80c4200304141c40450340305804481034005502890003200c4003e04070781104105501079005104980c0443c2c3d0400c4000c41c0c7d54061008040e10300524110907041c8401c0390042110784c45c08450a44c0107030445540c01c0084005031044400c4240b152024908542c1426180d091a05060142400740107540401e02250b40e5588071402e990f40006074140468420b52030302401412845052030b00c02c1e24200079030f1409080c09600c07902110f80050080041e46041e030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 215016807 1250 215015557 215015561
    0x21021b0610120f0602071a010b0304020108060415080102040806060103051006080103021917060a0509010603030c11030a120c03020c011b1b150e030c03060115260702010e01050108061009 82
    0x200c0c00f00c482c0045090000007141c8144081c00c0410302504040e41c041ea0700c41c3c00c0001c0048160095801d82005006010150f68030100740ea500413400e42d00003407501c4085003002080e95056110042c3c540c00000c0c00318800001088450003002c081c0c84c02e010589850500004200701c138008e03400024620707001003001d45000c90600c006541c0c411020807a480e00c900d42004500c0d000704001c1c040340c1c03024092141403001d9126903a03010091034005c004603405c5540003080c60315250400341410312404030b401c2c6103540a101c0f40b20310070307403101041c3c4800d0305200c40504500705600d0150094010182034400d0355000e82c08107c01101551001c0c0081e504507070321140c601d0341c903183c07280703134400104401b051841e41c003282400c10941d140c9134250805940010107251250f051000e41c082d4002100411400b0b161421042d0b401207103050548040e140b4100089800d8400240007070180407041c148401950194070003205007903094028801e030b0fa2950301d000d66841003540c0d800000c5103421340c1040101c18036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 215018057 1250 215016807 215016839
    0x702100c0203060f0a02040f0803070506150f2803030c1101230a0e06040b1312050705060a030b0409030f030e07080303150102010b0604030b090601060804020d0b0721021b0610 77
    0x5c0900500b0325807102d204070003000e050380000e101d0f0303030000481200340b001c108003090b488200006c0250400d00e00c00d021960020741c01d08054000c681540c0c180c00362030136592201111100741c40d4880c4400d60f4034100148004007030340d41034420418400030110355500c94024518210850804284003d41500300c1090580c8008011401c00c5101c01c3c14a002e503480b100140020104c0c4040c050726010602807201480090b64041401c10560b80c2c0c50b18001030002c24a00101c81049404644038508446d040e00a0807200c010280d208c1d18140426041580065100320b02c0039140e94100301d19814440301554400e40c5c2d02666116a005100103090000005071078401044180700100f02540c01031b010400c42e40243e00121030700e64500f42041011482002800d004020301d00d002e401c541000c0e008204405401355004c1d00c4c4004400009065034000e0100302e11900b2843e0300c4040e00c51400100350025007120102c00000c8120003000d5055060010701e1500541c5603100b1950140d00d801d031340306006108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 215019307 1250 215018057 215018071
    0xd0207121b031209050111060f0414100f0e06280f02040906031a0415090206091003090c050a06092d0306150608040b060d0816080702100c0203060f 65
    0x1018451901614107001114019071140d0f01c2600e460101c840041d11003062a00030504006040805120740c402c00070700303980c2010240c04114005e0b00e0303a0408404484011a4800d4540b007581d90812045040307a101885502031000100301c0c10141c0d5443c90303120f541c192040e920880004a040d030010480511180020b6030161f00003811404008a036404e0782c22540c03140300740c103640366400c1040c4620011100420003d61426120500d8141c3d540345c2840480c0ca4902c1e026591203c0140031512110221200e10380c4c02400e80c041c00d0b859a03801005041a0507084480c02190540002d06051110903001900e040e912495900da090003400840f42c0000c0c503280111000481840540745104202c000145010740400315a80205588545804010703038031540c100b0030b05804110104109801c1141c0011003102d440380810b00e5070411403ca030042c1c0c004200c0c0031030401d0121081040c0c260050102c030384259400300c1504881c1e94207031030031544481e010303405030042c1c40064040b044007445035a100340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 215020557 1250 215019307 215019323
    0x20715050c19020715020d02061305121206130516050c0a0b040804170c0a171002030109060801050f090a030c29040501050a0e03090607061812110d020712 68
    0x100103180d8040c40900c015000b0003603003001c18140003642d6085400e12501d01103000801ba000c07000c0000035918440202442d8000b04446810307170070090207015070140006e0440c2d696465445910040c03070425400e450061081c0e00c040c2c0104a10481809a075204a5103c04510198540808141c1e5a075000c42c420000034050805400d002807070342451030b800b0302d015411141d19181026074140c18195840744100040c1d1015a551003256a00400502655038150b103503000040b9586a881c13170700d04042d8091001c54004400854801a95401541101d8140c0024051a20740c490003405c0200c066a807800e154014200d2a00400d0040c014079a29520814410391000b00002c0309814040044070f0701a4100b81a405200a01409001b203503003100b00e02d0002c028070054400c140b69240325841d512401010042060301c00d10030700d03601840c0044568080100350012503e080c016440f505541c0742c001c650401408a440b420002e5851f40c4511180c00a1041a0401c500c681c66520300340800c6035021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 215021807 1250 215020557 215020567
    0x60d0f020a06030605090705130512010207060c0201020306030106050f0a1a1b0a031d09010603050a020417010207060c08010e06090606161103011b08042003120c01060603020715050c 80
    0x1072141c403044802441e140d640000c8840c1030808010030918040e040c182004814030030a500b2080c03c040310b0f411514115554a02c8505c07402040e4064007030110b0190006290100150707009070190011440780800f240200700e12501d0b10300708921179101c2620b40f0b412126011050001c02a1181d20303c40d040794152007d0304203504051a40d1940d203144a004000d50030030340580b010035411018103111405804400c64840d9540790102d00c040505208605c02c140d00c800202c0e500c2c502e2981102d01400e04800c4a208461246003818041c0d409884216585803400210900304d42c4141030030390503150191120b00803a10340d00d00b04908498040e1590764040c004001c0140d49901c0580340c82c0820748203840c00e68040c0c20510416084070800c48280c8040307284c12000c407081c0d69228005c690311940c004121a0102520001c0a50003001d14481980600c210300d607081c055501840640302c6284184024803405882e000100e0507801607550003841004005e2035007403540f601d50031659111009400d40d500b04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 215023057 1250 215021807 215021809
    0x11090403090e0112020910050d0f02041d0f0601060201021207030b030102040f14030105010b09031f0b03030a1206050a03020a0e07020111190320030403180810020d0b01090806060d0f02 81
    0x5080a81c02901e060049500d401308508100e69816400741000c0500f104032483c02e004122010444a0001c110941e01140401156503650288107041401e1211200801d00f46400320f41e42d114402d14100c5610501c1e000103a141d10500865500704441c0414041c20340b20000250f02800303640c41019070654090002003500c2e041c0140e03050007840000c00401c6002c00240074182101c03010707040010001c50801545141d614000b515290030310710304140c81c03560300d4084082002010301500e080c2d4503000026010503810303801240d012980200c0e07030003040034075551000c00c421100f4610000f50000c0e81403a042040e548110050303603028525000100d981c51079210510007503400f50341185003298000349042081a4184110390000848004d80101e44540c1100b0350450301004000900704000a408412405150305001c5e00170040d410441703507071800e00700d45400a508000011441c00d860714485465942c42064564102c4074100041c1c0f1048e10b84409200306010901c00944101c41d40201138001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 215024307 1250 215023057 215023079
    0x1020a150f2d290a05030d2a052112270102041a0f0409090f060b0d03080a0f02070c080102030f0f0103080901030b0d05011b080a091109040309 63
    0xc040c58802000d450b4140e4403801c10184070100800c0014618194012000c994801c195414884107281040d807002100000a18900c0c11604070036058090001d082c0441c0d9084514801d1840702070702078100314001d070010090b4070324403c40040c20f10b510131703c211046804d1140307a120000103030345005464490407003022907803841e06a695811117904c52080f20400700c00c250341006159111002545007500c1c004896030012602a64a0310904001035112040142002214002c2c041001d0502002829081400c54060b980c0b001380d40b03042c10644062200d00d04019010506070f89030b210313650503440da40700c0b0f10028042d8440c08070745c00b03a08020820204860034070320300c02841244005643c4e403500700c0d603650000c20040d10b00c1c0c103104010f00051001401c98025030318040340a10b4000b07800c801500009003000052440940554a07144803440c2404240305085800d1807241c446032911340340e0059541c221012504050f0211214103000c008030700c1d000001c075402c80e010b480d0191005484007c6495 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 215025557 1250 215024307 215024321
    0x6010905031501030210050f04090b01020a0210110c010e01020a0f1b0e15030304051003020904020f030a02030402030d0e0a030b1008150a18020d02010e01090b040807060305090c01020a150f 83
    0x1400c28000030042086140030003900605200f80c0c40e1031410032002340140182800740e40aa0030f051901d6024403002a442001101801600201104100d054052000c0d01e10011081c00030407a0060f403a5020b41d0b54050000da800c1540180d005148840050302c45203004104418200c03070200794003004040c1118443c84641c054015500000c003182011001c2c42d01020140c10190301a4000384001c00903680c421501908040050501699030142034002400a00c00e0b00010981900080107012541040303074007440c81548242c04654010120a90981c1c103500903083c1b49070b228254080c10320000b00d103141c0480d00059040c002009194950780f11034106281c071000d0206204480007040340200040c050002842511603407041c84601540214260342c8140740064180841250b121071a0391181c1c850350020854000c82c1d9440341d4071001090f49503452841100d0002c0c0c200000300c1c2c5030341d4000c1030310f080d4918160000c000103000f80c0e4039190805ca81e40e8034200030076514182103140040c1c03405540303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 215026807 1250 215025557 215025583
    0x1107030b090f060a052701021c020714120d1d030c0a020a0b0304020306220f1b0e01080304091d10140f0f07080604181a060d0c0b030601090503 63
    0x1c14a00c542854091074600b0003486020b0704c90800061101c80080c1040e84103000783da43c42d15151182d4401220ba000e8429650190f03035035902d00d2003078213044010f980909046442050b1001e051520303801c0042c0d441b01d1402015000600c100320014800c501a40150603560307500e680c104620444101e07643c1990004681e03079829400020032042189446483e100151106501c3c403800d50909030080b940d43c54000b400f14000f034150007248007013200510032088031107502110000c9c085105144c09503180f4800f4182c900714103403c0700d001c104984d003511503606a83c8080c2c01141098a04071100d405043c07071400c4600709204400da9140300c49130074007051840164040c0e0118002d072074808450107a50000b07080d002034a00b04018070113450f495078100f40d0082c03c0d51808450640341c00000070003d00f070708015000d00c0e0076068100700400a4543e18000b180440500d240c100d50707101700c14010700c0301150320001e00c440368041d07090040c003001d0303805107812140600d0008a91070300c52010a29254050f2910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 215028057 1250 215026807 215026813
    0x30608101d0601080a030503040c05030303090f0f030a0c1722031208040b06280f0e1515030c130e04140705030c0f182703040e04031107030b09 63
    0x260480c038161001c03003140550300c005080a6142c03400807074075a40c0c05c40300102000000004a41485180304950010f800d0007400d036036417410440f140c19a504020503811206e8024008542600e10010080d01c2400300305840300b15807405665205407010700f4428241d1b4a082c42030018101d403440c201035801d6903518001c58a24180c3c19030802416259a034610302040042c818104000030301c5081c4940e030081d00540d40001d68521a6088030740401d48d9202c11440d1f41c050517000104810f10504100458458808441e096129603141e803a02d5a10b400509030003881403130851103032081540042d0750104208001608202c0c2c44d07900440d40200d03e0380140074a0245909000c180725585400b0302c01100c40000600aa03131501c00170075100e03800c8141480c400c0000040c00ca8098450202c28503444c0c491900380c05403440d0803030328108419201602941c3c03101054145481c41e110010840e420b58070b584a87d501a40d6803030b48c0c1264070640307402c0148a01c0c028041d0000011300c1101c2694050ba00c41405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 215029307 1250 215028057 215028071
    0xc030c0a0b0901061a070201030b060c010906060506040605120907050d060e150f060d050a02040e070f0f0b1e0d05040c06111207060c022103011a0a0e01030c03060810 73
    0x20000001c0502070b00d40591403d5410801e1500004c0700020300e105000d0f42c41c1c0c881d0110f00040c2d0061401d12070307a60f040800011043d00255041d40901c800354400c6d501000348a07110000d02245010b80e00811001c14000c11000743d11095030340c00340385d11500321001c6038035072910358020407800003840368101c0300161145180808014140a1a850f58400e0400007101c0d117000064075242100140c1103501030b03509614003400b4406e0510111104a80150041c001680340000c80d07030323507000c46204465107011543d401150078094120343c0310031070b41001d50b62410900149040b2001c405020002c41003440c00704440442070034540141403107140500c1003103404a1400e44081e080754001c5c140384050790030148a10a07444111410384000a403c035400140012410b10b040c0d24088400346401040d5186d0078280c10f40000000056040e16440000d0011100d035001d4015101d000301c040f00030202d6580c10749000795500c84c0c1c1c000505c43c0781c6490301180d4260f84030202410100ea9010900b4000c2c0c407903d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 215030557 1250 215029307 215029313
    0x20a03060806190513060e160501020328090302130b01090506131203050702180105010318030c14160e01050406050d0f15140f04110102060118050a020c030c0a 70
    0x2080c0d80080014030302a0006240805040000c3d2103504000168141e42d00d000c14190745240401e40303c19584000100704110144184c6035030782d0b03103107551011a400c0c0800041115480801591100c80612064410746910724204040c00000c25444504101c000704001025070395500c0d5000244058203000200c000740b10f00010441801c907000140100b50800070100c001c1170000080c2c085480f50600448401424a800c85c0c25100780800607500407600143c1148842c0440304007812100241c0f000c01445c2d04140200b044407020280140214500d00c001e030b0040303654031100c0040e043c1c040040d02d0110141315511102d00b00140c03c43740d0f070513035a10014007942c10103100d8500600001c03110000c03145580da80b19040d107144000700402540011401503202106038114500403240e1814490303c502e0016a09c1600711400c6601340c1e0b00a5a0b0001414103500200e905416641e068204034171941c03050103000d002e0b000160090310306950030480c48817240d00c02c0c005400383c0c80859010b040070340d10b682 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 215031807 1250 215030557 215030561
    0x2031c030218060901020d030b0a08032b0902151605010c030e190507050d060e0307080307031a030705011b0c030803042f0103111e04050a080c030303040206131503020a03 75
    0x802e890140c0000c100c0d24150741e07000551404050031a1501042016070300c3c022660360405540203011510001c00c2d940401d09100c0414080300a08907840c0e0b01c105501d214400944612842c088d41100c1240e0303140e000360215000400c400c0111a101d6500505156620360845403a99201e07000244e948001d10b00506040c0070001d402c1102e0300241728001c1007078961035180c41007441401e01c2000080000300c2003145a4004046a0002c0e0b42030320388900c00b604001170f29510484035100000c3c60104030b0070810000d00110036042402a00030a04241814010b540c014455203400c10190b2540141c080040c3c0c04001c003802075885890503d8883c03d0518101040ca02c001d004039000c0c002e0040c1c00d91481c2c4623441003c1d041d440c2460701044078401d034901c2035214403885101001d5256440510f40c1044030364402002210303819202c12000640e141c0c80c0d42e488047e501d6045134107410820210b030140c9408000b0b44504a10480350249655840c3d54500700003511003092008070782c010400b2100360307402d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 215033057 1250 215031807 215031847
    0x150e0d0b07110307350301030b0106091e090b04271a0f0f0c04080d02060105010e030304060512040206090d14010c03060e0f0705040b070f0b01060c020a03060902031c0302 75
    0xd40c140200c603070350500350241403040602e107003a6485c10302002e845404070000e01d0441e13035080540e0f20f507101d040224910400f40a0800444e44890000403c101d001c03203000768039180088020525410003441602038510b03062442d51160b2210312441d807a600104a082c03803801101c7c4a400490228500f01c200c05040010310b000c95902401008034032598004240c0d403100c03940c65295210780e42c2c004d20460a00483d04006803502c04c0d150f03694001c1d41c001a4043c16039400762510160040c40504042e5a0f200c0ca01600b80011030a100c0192421722031a001034005100030001410403168801203441c01c2e5007158199101e100441d00c02d000908223100e9101d00c82641c2c601400b1590408400d100d0f001d4014107a95201c10300d98000803d560b216005a801520703940000ca40d0300c1400d410201c00b003860362101501d8001d001800050054014440896040c1e4003034000074410349562a140c004004080041c5d07003500944006c83d041c0b40070070010305880c0c0b041d9180141c1703690025074104943d8100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 215034307 1250 215033057 215033087
    0x20f0c06010518090d0516080309010c02071a09040506061e0403060f05040b0402120115080c0102010e01180312020705030318010516050f1b060a0504050f01020310150e0d0b07 77
    0x140380c0c14002002000304820038607034006d051644d80c0ba030740000000808443c0030302c090a1035001105004ca2004190092070013224241d08171082c0e02d8645e10001d9005425a50382403941004200e454a1390a00e40c2119610450052005061075518070071030f05802c08212140d002141d00040034001c21189124002990004a00030801c85c0742550342c2c05e03114100a00040d115018425490801c00400d400000c0e00c80b101c0908007818550742c1c1f0055550f0f8810001490141d402c03c1c03090f9242500501c20400c038020400190b5000307007016203003560801c03c0380410503c0a5005c100c0b040103c0c80800003140180c48140b0f106031000c1c1d0580300c103400c45d50080c0107140180021507a40303124a42c00410340e50a0f0034032000070b0751340720742e0b0348161844844008802c401c280144004c2007190540c6500084c030840c0604113480100c0d0710340c40c5180c02c07440215001c1080c0035506409000c000d41c4030120318504000350600800c40c2c0440e5000078101c0c01c10300022203501100e00204001c660f030010513000d241c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 215035557 1250 215034307 215034349
    0xd020607020c0303070809061902062202180702030c071e0b1801080a0905011404050606190b0307090509270706140309010b06031503011103010302030a0b0a020f0c060105 75
    0x40c00103504ea118092014000140104499010342e48050440c0ea0303000f20b441c7d0700c0d8002c80d41c00300040d4542a044444404400020002c8800004840e10700c4005641c0140000c0c65021500c050440001001d024003086200501600c0303480b40c1c2c1001a40050600a01c810242c80701c0d60030f02c401000d5035500b002941e2502423007020040311b1040701c841ca5001003428a090281d43d000e1070f100042240440291807907003070900e41c8400d400175801440c066030180c0e040c0c4402e541e03008103201e40444141101165400c0c0d50034100310442942019503040300040c502444240d6480c000204662000c0d20715030141e5941180b884500d01d030340100001c01035041c0020781134461614101070b011000300321107940369820020000e000030000b9072007444080c0e40200b140d038607030400a041640800402d24094042e40c079202c61803c071140352405490480342d0040060501888903550b02d21502c02c0a00300310201a021302090680303500c041d000e0a4501280340041201d589440100500c400040c204413040344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 215036807 1250 215035557 215035573
    0x60a0810050109081c022503110f0a030b0423060603010e010c0509191a0318010516030903021617121905030405070e0f01060e040e0709110d020703020d02060702 71
    0x100000c2071144081642d03170300800e1114035100e01030f81000d180303294071002030004480350558400c00761803d00541340a0382001c1c5280e4004804d01400005d190380c60303940000d000204000044c940c00381c40c1c0d40b05125030000b2208058030500c2219040306040e04105a4100108200443c20248600c000406100c00240030b0441c255038090f056205482d282070250142041124130070301014442da004001d0710b5490b003510003d62019865540095503064006000490b0040e503a031014003d00b4000c9100b0070718120361025403c0160010085241c1c21019406211800104201b40601000c000c04c01002c2589041c01a01501ca050008207944a07004c05000e01c0032000d10080c2d0702c1e20315030007640750070500e550351914103143c0e03d800710a0f486181003000b60340420018a0101030054100d030f415454005041e000001003000759502015080007036444890200300c1441c0c80d4018001980e180036803d442c181c0c6502190007640c0c0135050940241c1d000201c032001250741080000c0d402155440501462 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 215038057 1250 215036807 215036819
    0x20105071e050c011103090303060a1d070509130e160906030f02090c04090f0b0f1e040518031303050f0d0915030e0a0606060f051303080703030b060a0810050109 71
    0x5241d8544401c42000b9000c581d1100c40002548080c000381034405819450b0b00e4051080350b41c0b0391084074828004c603440b40300014140040d001810f00e405084541034060313907400e0380442c0c03071342c0090f4111944282403005143c60a8202d104484554401070040c001c2030004443c0d0110342952940021000761a01d00b040022554400c088a152030b41140c03000803d444100440409000d2900050940da15240d841c101c5070400b03030b002ca000964165507000004000c030f0200640300450907030400d0240c200a01961f028500343c0d0040d41c0c00140c40b40c2018002d000482000e00e95040041301e0440884490000d00a02808002d02104c0130402401890030040592006041e0b401c684244001d8001180c0c113030075250700030740181e160400c50004654100b4024200400500880c4c441e0300089185500e111495600c1241150150040700d168590f0f014590394404a281d1f208131800e42c20075646042502c220f85d5804d00400c1d8007101950b80031807505107860321343d005c1500e0340d11983c1803080c00c81d410450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 215039307 1250 215038057 215038097
    0x10503010302060901170c04030c090b0105160602161a0609040f03030b04093f020a030804050703020406080d030606080f01030b060d12050a0914032a030601030c050102010507 77
    0x1507a605440d080c0e2500c40d50b00040c0c0c4c00c1d042d040700322030410070718500b0092054400c0019104880c002c80e5940d00055503000c207841100e500c200303502c2c0092410840c0981072204060b001441621604005180102c60110603503880302084c4100c07269481400304142c219540d206207034226508607030085050a155951451003000c05000500b455200c4000002d203603101d41c4002101d5070048124509502d01b0380c41c261286450303807603907a5160360640248055214158404400584d50380052800c0b52598500b96110b010080c0102c42510840a0110050f12503020b0070000300b45400040c000b07010500c1000e03041d03420f00d07003049003007180c05402c110300500c0006001d411a904801d28100344d0b00d600340030980640041201030900200d070b40c2243c170040c1d88080144240d10701c3e40d9030140040d888540c412820758401b00819407644c0042e82003ca41600c445c48080c04100240758501640e0b0a48042070a15034240d009594101204604003c10b58081c00703640c0c0c1c0030b825482c003d00c08983c56181c1c204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 215040557 1250 215039307 215039309
    0x7050a1a0412050304030c03081b060907051e030f03090a06020d080610020c040504030801080705270709030c0b0d0b0405100b0c1e010e12030c220314070509010b0901050301 76
    0x1803480ba0302140c0c2014403c003441142d002d180c004101c41d00c06622810808800e600404c00503070f84071a0304099001e29100030032000d0080b88600040c0035001e00d017104210502d40e240b0b0417211004808281002b80e41c0d4101700d12140015590046c5031030b00004400c000800d1090b901480941d00704c060000242d03030f0300c48601030744800708445041804100360340c202c0c680140f404109800034038090a02c4140341e009500302c1d0480b80080e0496800da81c0758428881e0381100c0c0013005401c1c0d0100002544041444030506601005900c0d004c0301c1e00350b4a8803081c608100f9580329450001c0000307044140d41d20140549007124a0a842c14400c905005088c000043d1441c40781041043c1c0114500a441a06224010404000008000c0c1c00800015a035000f401120015200780c4182d44180413840d21160542e8414180d6900ca5414182803008030042840000c002080c6110b140c200840014101c010854940e01003200820395242003605110709481c040c1c10858020205100c2c55465a81c060200c0b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 215041807 1250 215040557 215040569
    0x10c170610090e0403090305010509010228030e07030f0c0509070e100203040504060905181204170703020603090d0905030c06070609081209030a0f08010609030308040201090b030907050a1a04 84
    0x300404105101140e4400c0b40341c1110101ca00c0f00341c140014543e22500310000d49008070020000d5403140b206a070300300d00c2401c08007114103a0315001116903209403004514102c00d94100420b0194601320001e0902d403050f002200c045010f54070440c107124140d00080040c010a89020b0741d1814032200150075015041c0140c0d10460b00340050fa16914424415600240030140082c0700c003e0f104c0c4403050103480120383c0050321800c440d04060520600248000da01c1c2c0240184900d09420201c200c902c400b59034000035990300c9958800401a01e50800542c802c000007009020381007001b440091011070300f584414426440303200016029a41c0c2b004440f0b64581c041e5000452a41d1803510300e0b0b1900601d000380100e00310080801c0108080403004000c0f810303556884c01c840041442e0305542e0401c0038014800002c1071460309200090207080040e4020f801410500e4042c1d0f0b460507101b8095000303c03202806a040103804102c40e007001440311001d008680300b40d1000c100e030300b6103c41c07640c05030348154 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 215043057 1250 215041807 215041819
    0x60c05103303150906060510020c031b01170a1b050306011b0201120f091401090209012412020c060405011e09120f23090109090e0a060c0908070e0603010c1706 70
    0x1138010401c0390b900050043c0700240a03c1c9940750b0200c0d029440d0009008000d00030b001c3c841640c958003003007c2c0c41c00b003904816101e4101c0c0480210740540e440600901348200596540a00d41d5140703003000107007090a2895480702c1d03680c0b50100004103c44030190041c180360071b01d1200328005030b070040007403042c3c402c0200e8000b6601000304042005803550103030140c0b6070801c01c2107200e40c820041d002128020700980d0380e403c46903a032382d94000c5100840b0390318003602447c03189585880382c07188900c443c000751024805420020304814031781c20030380140c404a800341e41d1030060754079101d00103c6004410b13000308130130411001e16071503c0c44112800240c402c10080210449416103006815013100c990103010000c00f03a00304080c1010b80e50f03122160b10360108408410018241805025408041c07075841c1c054100c0d8221691000701911001c4060001c0c0308006401007404803081008500818039010f10f090181403107006c0c182112640104002001030b41c0100ba460303003041d400c405030012700990344 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 215044307 1250 215043057 215043071
    0x90904120318050d080702030c1b0402070b0f04050f0d02150718080705010905060c0d030c1101020a080105041a090c0a03020d0e030304120203040f060c0510330315 72
    0x1ca005107000e55009140e550803450700d00c1400030004aa013000c050544401d501620340204c01e0f80c4d1b84c000c000c00c040c0190300070310110425500c510b2140a00340c0c0083c10140c01c000302c0c0e070f4030800c90300803c40b8039912090f00c560030801444010440c408810b10403c01800c055075038041c1c001d4035405013110284000b003c85000ca0b00d1745124403015640c512140c02c021010310f4039400301c641c42e4085072103801c0c0000e200c40004100c52512608580541c034000004042d08003010b01c1c19005443d174280d080717003400104041c4108005003800200101c028664a507902c96060100f040115020302040d0214030300440b08941d919105c280070140c00c4450038102c0c0b42c40d6031440c901140a0701c035540b40d40ca4020300f85004084905000009507001d50f200c3c1c2c00340802006030b10400c0340c2e00e000d103209610920180d2032040200c503002d2280507181c00e0050050f41c94202110f6089002d80740c41300a1800b0340d0110011444d01801c5200042750f4880901d0010b03070a5915503203c0c1c0c1003240c07071041c1c41c0c01c001d969541 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 215045557 1250 215044307 215044343
    0x8010b0f071e0b341803020307120302100605061608130e1e0f130215030c040303120b09011502010b0d11130b03030703141303080d0f02090904 63
    0x1510009490009400100041042c9045502c3c01c20603140303008595035040c0e2161300900001800010019066901e100f0007030202400c0300c00d41708010040d007004028080c0400985c5081c411440600302d0110056504202803900918007240000e00c00c04840c5041c1d414416552800b044034600c40002c1c0d0008080441820071080f24440c4411a0652504104d40000c5610740254400d201791485c00c4038420f403c0c0c1003001492024002c84440101d03c1038a0001071418005206603c1d840f400541080c3c2c0e1500324440c02c1c04240d005a4081c988690081010000c040c1e0024070002c0038000e43d50300b8482c00c500500840c000074018012800f00203070100c01749150f14403d40c0141500900205803072071550f068100810000e82c421314150046c000e42a40200200050059001c1010f020340158907119064804450451400c8100c60040f0701c00c00075281040400601c90000d14090144250780d1100045440b0454007084520300d003503801401042071550312591643c0d44903401511420811142d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 215046807 1250 215045557 215045573
    0x23109020f2502011704030c03030519020d020903010c050a020706030b0d05010f0c08100806010302090a1409010213050a08030306010e040605180a060e040203120a031407020d0306050108010b0f07 86
    0xe40d41a1002241502c03062404401032010140c0d000780c9a42120718091101c408181e0000c0f6800703004140d07050760701c000003403007030b40815449a102940c11074115040750b088801d980c00818242440c42d000702d40e201052a0030310480d41050060b00b400c925200c0c6c1d80384041d4849095100c0e03401815510418000305440307030f8481c843d902d0b6124000704600e000745010b01009210104a100002e500f0388002461b0800d81810b200a85000c9401082240e203103500300910450020a20310302c1e20380302c491050b040d1071000d00c080d00a244a81c00984c481c1c40540382e0312544140ca134801e40c45000804020402c480d000702c00c40c4c0e00030000307107030070380b0000207000c0442c018200503884140c0251f5604c0000724042c6006070102e015401504090010507911181c841d01444280d4010b58590441800707114046900030040901100314180404e154140240c00c250190b000c841d0f0002580000d0038101c42070390315100700740c068402400c20b40215410554070038000c1c051032292491140c0005030020600c800d032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 215048057 1250 215046807 215046817
    0x3060c090b0a0c0b0f1306050411030d020604030e04090c06030b040608030301140f04022104290a14010602071a120c07150b010f030c0c05070306023109020f 69
    0x140360200c2e40c1e038035200d40080c0001c0c0d1000f030075103241c06184041504034a2642c0c80900071294110007210b01402d0781c9424000300310142003160400d21007142c0390030548050144070001f804a4025103120b1500d414060900303440d40d00b289110b0741c42e1078a60000203200f480700f481541c440e0328000402c00340020100c0d00030130960f08424064407000c000090703070188074001c2c0c0880d101305640084030f0a902900b4070040c1d00a04400d44403446100c0e052a20100b5500d0074194003602078403044002a03001d40004c0e4040754103c9683e01140005805c000c1c2c40705080c000d03032070304440d0003400017040d41c58035000946660540c000c48860b5030588100c855104034240c00c1c0d4403561180c480b456480d04103e0800f8840358000b030300c11a00c20402d03100e070f07410741c003a18410000b054a040e11070030090700785001e0440040180d01e500310b00784941d07425994046030b001c00079940035500c036000060741c0321501e00110300e0000c68140c2e9038031901c0311120340900b04c170740c03031003640044600d000409610358030940742d21034840c00381d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 215049307 1250 215048057 215048069
    0x406110c130e0115080a0204020a05070f060203041e05060106050a090803030c04140102030301060e0d0609200405010f03081b01020f0c0d090b0322170705071401020c03060103060c09 80
    0x20040100800c01c07599400b140000390620000c1240048000b25190001c529104070407503504418a4200542496001810f2412a601d0f00619005207030396204103a200c118400e0f1990b0b60f02204000c2007107a400c1c40307905c0348071426a051030b00420a80da001d0b99081c0c140103107010400080b48aa60041c000c40340c030400b070325000302a60388910f80781000000641180c807406083c258500c902050301c2d4000310071241aa0400d503100942c50000394141710411008100459005070b4a081d034901041c513000041520030100c8115000801d02c0204000c19501d040e0003a4604609a0b24104009148a800c40c3c01c001c0b0030440081000401c092450b00a00622005150759100003a15545060340450b0301c3c40d420b81242c948000d03054a4003000e004031301044880c0001c00c40c01c8500340c1071121a110014103c0b40c801e511100840c19549800d0b03001350004c510445442d03000c41c0d828806880c260743c910a5850007840144844c2c040d0a00003541c0f4401880064005581c401c01182d910b44198600d078080c001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 215050557 1250 215049307 215049319
    0x20d1103010b040903021507080103260706060603050f0a060b0d051509010b131a030406020d060306020a1701090b03030304020607290115031a1507150e06070e060406110c 75
    0x1184d410007940b2800b10f50566000510036000041c111401145810b058035004840d1800b107130000080282684500700d82840e01e0700c4d0901c0050009541801103c0240c59a0395000c0748c00d08082228a502c050040d002200c684d0901e0002e204101c1c00c04c05a40c0944180303000401c850310740001c0c400e0041d1451b01f100350007864100021520001500040845880845a03500c1c02d40d0350f000d42a03044601e40c4038810706444200302080c04200c0c0c540103801610b000358030008181e580c7e9070b1440b040341d110002010120300704803000c0340468610341c4900e0040100340c0b818000c0c4071240b40001d40780e00c001040288a42c8000c0707000001d0221004040a01c408a440c1502081d03c0c00c5040004c15042403140c008549001c07400b90411600c01d019100f2030005201080341c4404400c010001d00381030310380c200056520144910804079800040080c0c15074010000001c100e80c14061050030144001d080b4010700c40b483c04681140c0c0c540d4011038080382d81c03d14201c0700c10804404004c1c03c000c0d10b1014203034054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 215051807 1250 215050557 215050571
    0x50607031e110403050618070b0d020d0608010b03010609020f030c07170406021516080f09030c01060b090307060203040f050d1a090105090c0d0209040602091906020705130207020d1103010b04 84
    0xb03460000038819280a0011194203035100401616480e12241c598156030304083e108122036441c3d4000b6199034040900094285105500000101c44190b8030800250f91520ba00e005c41e41800e100341c00c0581001c5005610b46114800211786c1c07840050611400f1076000031742002881780120404489414070011b07076940e5a07a400009640c0c0d111240e00034001d1000a0100705900c4140c0c0c031881686407151114609961114180741071140014601000c40c002040a2694040e00303108900103082c00a0b545d0741c481a5810625103484299002181954002c101c10310200c2d58401240341154801c5850725141c2070a860160036490010080300580680501802044001900428414554170085580700c0301c0c282c081081c4030b4401c040280d04000103002140110340c042c3c0040c9180100030340f000a50520284500e03003200d0250713103d0310058001c20000d200b6450181294801144010415800c04c1119000210401d00d02d038002041040410422411a01e0a42215003118401041001b0f40c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 215053057 1250 215051807 215051831
    0x6170601140705031e0408061302040b1c14070b0d02070c120819080712020c1501060f140703050d0b030106051e0a09020304120c03050d0c0915020109050607031e 71
    0x45d42054400700042240c40044a81c0003200100796821101c50308002d15407520380c6c201c854a038402c003a505907040307520b030000d0085c0c4ce00d800c003403641d4040220075001204100307410a042003588058000741c1a41249004110703c0c80d9810546801082024006980d250f1034a4403180703503505540108103000300240c11509022510001d42000072203410300b03149010703010710101c1d8040d000300c0f50140480d00c20a003c002c03c941c1036001d010340400003411100ca0035a05120503810312003d90203400010605201c540d0b0719544040a034105441a0743c103a0f0a190442d40e02500b075000361200290740b20f41c1c8124007411903030f003504441d0080401414004a03017003c0252011403840003200035004003811710300061200000d01c2240e1145030440201070300428540c1d004c07140042c04031010707000c204040c400712400112620802c402401c25845800c3e44915240e28240e41c1c41c0c904050005691401c007085011800119540e5031081c0907140014108111100400012004d090ba0400320ba16001440540c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 215054307 1250 215053057 215053063
    0xb011716141e0108070302070f211704051504051005010f0617041a250c020109050303072013020c030c06010e010f03030f03020c01020d0911040606170601140705 71
    0x1a50000340d54144180030411000d42c040c1ca104090b140c0014800c10000341d245100e9406080f0542c412441e0b442d072a07040c0c4d141c1b9820410501c81e55000c200c1140d00708014240c22038010058200460a4601189030a49885448803240400c0c80e00304130035003002404000040c0001900c0c504800342c10011540c482c40ba140c03000700c05000e03000100c0c91064172881e5038290b40703000c288996400349024162504400120030842409800d0301a6191819409120340d441d1200c44482c0b07114030b03524a0890b081034000146070300110703440725009400800c2440080742c048502c1d51040c0c0203c0710b04002484548003c04e06081743d0f09010940c03184013042510f03000d140032000b04080029841280c3c001d0740c03a5031403148005020b01c141e6150300000d44041000034000d030703810140b429150030010309007103000340882d003aa400348034401c03504c680d619100310422524520300d00300c00c00d042e07404010307441c144100608030a03441c0042c4200261520000f80c1960312611105404107030030740c0385a855183c0c9161860b6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 215055557 1250 215054307 215054339
    0x1b0a052101090e0f060103020d21050c1009050a060e120706021305030d050d0903030603210311090604090506060d06030804080d030b130209181302010e030a0b011716 73
    0x20340ca42809980c2141043c00242c428039210001c000c0c0c0720507440c542c204144c05d001207800301c070054210fa0410482240300005840c03620016100c256644007254034880c00c02d1300e20401002035615040c40c450100750000b0f001d0529035032028002403202500c16059103807c6410862801602c0000f5000341000695005008019910541810000e48800815031100d201c1040300000030028400300d40105940e400102c1904d0182c140005c2480c0c59469460401c1d01c8007440c5810300c522440b01c00082c99044c0301c6d0b1010311000307030041811301e0074007000928588aa4810941c2c4a500c1d000030840307998600e011a542c0891a030010008159a85050b1245410511800c0880d004201c0d03602e10041c0240640d0200c60001003101e100b455000340180c000390060f21b8516000000d60003d07102c080e040302d518a010b910b40c651002d280d420380d440010720403040000000d01035000700405200260381c036440c40341552441912507420010102c0c05c24030307041c600760360307403089440c140000102400b40800c0380c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 215056807 1250 215055557 215055569
    0x2010516060608240702030703180e15100305040b01050d0317090d080106020a030c0b0703090f03030f0b062d0f1206010e0d050615030a0203070f0e0108061b0a052101 73
    0x4d4080345405080c42894041140d408016800c00c104250010b4450080400d649110154512105894164030003401d0001c46641d81e8040754140d000c0d02d2440c050070540569003c503c4e06100a00d02542c1b880490541841001e00135001d214240c070425000714500ca68100708210145404e28244089035070300c44c100c01050011684040000ca2424070102e0964012a0540c0326801388240c2c0e40e0b42d0401328440101040d04043d80d641d8440300103a6138981400d8018082d580106150344141d41c0c540c01c0f0b0f81c0d00310f100c6110711420012002400a07000e040d10550901e2101030620f06e16105e40301c191481a010101820600020302035208a0203010b0240034840a0341e4800c1142c82d807509000004005550150044d400240060400b049401c002202c105001e010341d81d90464603808245040707681c0c4c0005900340311000003030107002c400c80c0000e4010414200108440c0c140800c007440007c60250402149041c0050310300c41c1c26000c1e104842c511178141c9c045001110002a40b24140d02d0203015174 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 215058057 1250 215056807 215056843
    0x5130906140912031b03190609090f0f0305070213140703020a020a0b060a1d010911070213020f040e090d0305100f050f0334080604080702010516060608 67
    0x10303800c001c2129045900c116400001092201c40380b890f40c41c42504020710241c48001a03000c544401c0b41040080d500450103004008402d44800c002442612040e400080e012403400b081c80011039514420001c0701a002318100c0780319013540c00e040328030344541c1c02c0c041d420440d41c00036803c104909a0141060040c22032012240c0d4543c001e049060740300381c4040200681c0100e140002240360340c4c84c020f400c0382008202ea00340603520000c0302201444840400f2250101a00400000c0c00c2400f900c2c1c0805415420b0514100c02540003420808041541c2910345034042910a40308034034004440c0501900c054220692407e00c52651b543c06803800140c0010b801d05000c80da4048011006501380c440302c42401c0b4040d4109805d0040c05030541d40d015334140300364502042e0a80c10201c4401d01c144080300c210303c001c40a000c40d001030200e07a40c4401120303400341d000c00c00403902d000103a5011990910340a41e80e0f40c10404e0a0320f44003a1454040c00940c40c0c00d0380020b44010014403800040b02d49104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 215059307 1250 215058057 215058071
    0xc0b04062a12050709031101120f020c0712020603181f02070317100501030f0f1b11030a02060106110c0a1509080f0304031112010507050409060b03090d1805130906 72
    0x940c0c243c41003aa440004140803860a20014402034400903032100185099980c3d0080810041c09035082c1e01c00545480764002424400c040d8240030440292800200400c1045d0217a4082115840010f02c034001c500030082c60500102400c0c41348100340c2e145030701c411003401d2a10a0050007944082011004600d60502c080880c240b42c2c040c6a12032000007828550841c0740070700640c058035001c0c80030120301d03035900b526150000c0c1500c01c0c510f5002004927181d122108610000d0030f05480d41c5003c0c4000d40c000e00c0f075007001d681d0001310203040d5402031a140c0c040320701c0005a40d1500103114803136a4407001d818000300d035000d4400d41c82c54070643c0342e95810b6021540c50301016110310342c01e148032640d90010081400070072440007031070302404005400c00c08580c0400310540c1c00c40b0700503a83c0d440000e03000602006150a00d000d08000350000c560400d14508010440a03545ca07001034801051000340c044610500b90681e81080082c2400741008900c0208070300600004c0c0541030046038542d141ca80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 215060557 1250 215059307 215059337
    0x8240f090a02060d2d05060607050604060b010e03150709060302070215090a030506040f0302060601030608060f070504090e060103020a0b070b0c070503040f12030f0f0c0b04062a 78
    0x1000900030200000601440200c640900005520001d1980007190b00d611002d802d045911042071070901c0d04840320b1045000f890a40d0060310000341649119880602c07104020650200749150070607406500043c903004c260005035040d90380d45442c00e40c140907056100d14402c480c000c4a51280038035540300e00c030a07a1908801c1d002c0f4094401c0c065005654500ca000c0c03c000c10340c1c003d00c03081d40014458440c0603034a6071560310f44002101d04484981540c0070060400d80c04115894011509080601116040558455480c00010018242c9924001c049500c0318000c2086030060400d0318010701c140044109090fa07555020b10003207002d8007044e000040c14100c00e0059038602603115412010a840d403480f000900d81241d10151404d02041000007242c170440e80181000b0050304c0c1c0744401065079400c0140480c008101200300b4401a00c5c18406401d0344000003a80c44c3d940901d08448032b894a082110080c503003004421101c2052429105d82c03917820b2200c08102908980d100f40074401011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 215061807 1250 215060557 215060581
    0xa021f020c030601230301020d0204060c0507230108070c020a090603050f010203070e011206080d080406050a0e060c1b0604030507120f02100f02120106120c030b09070e0a0824 77
    0x111a0400c20640c100364103d10017800079409141c00301c010001750401c0d5031110f60380e04076070150f402840410381075403180d400c001003400080c004000c10308110a8020340c26000c1402e61444154240c10000c910001902840c011115401c2c2c2540143c410481c2c103896143c088000c0c4030038003003a541d920407a031410360b2a03401402100d11401e40307a81d07105c034180d10080041d14002400420f054046171a8800411000c40c1008050303a034009540d110a4a42420f00b4814100e807809032070642c1c424101210b0020b030002c0060078682000d120900541d441c5110340039000004080345250706c060150b03600b03200078181d00074060301d54680a404c98091001e2403c1c0241c0b80843c1d10340d46680540c00114240d450b02d18030394440030000d5210705016260005146c500031440100360800004111102c1c41202406814429800102001d082c100001c41d840e40004081180c014100d0080100c00004800940c4901081000400300e020440d11604c8482000c02403403000c1e0301c103500c2c44408080000c0d114003404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 215063057 1250 215061807 215061809
    0x9011a03100e03071527110f04060b040807080606030304031e240f0c03020408032d0705010c1d010507030c03050f04090e010b030a08030a020702030a021f020c030601 73
    0xc00030842071032100001e60140403218160400d50000b44086008144920000442c2c2640618009407940c15455007140b0b182c03000c41c0e100c1003c01c0107084c0e2800520307004994031079118100d40007a960980c1400090141555130895550480007150014888400040c040e05803103100003aa078041c0d03a8001407559901440c4006003c030f2501c01c000d20a0140c0a01429004901031418410f0034003d1184480c45111078003403c24a5507540c000e44089400948980d014029245c41c096141c40d01d01203200d6524060060499400344070540c1e10713400c001b01e0302d1319144003c0004200036264002424024000e049444441d0081034000d0b10b1100508a0039032501003805050710742c00c0c20112103460880b4080c29130b44088061000c1000490650031a00e0080d20040c10400d0021400c025070800c1c142c291807120a03054060761040404000103840396065030b51100303e000005840700024000240340c000050406500003442c001050b0138031120051040498030030360211030360f001800c0c05069a031102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 215064307 1250 215063057 215063059
    0x80910180312020102070804060e010f0801150e0d0501110d110f030a050402010c020301060807090f060e0112260304050c101b02010e060a1e0804080d2c0609011a 71
    0xc855020320010b205030811080600d0148001410f106a9540704101640f0980140000c02e0040007000c105603032040f001c0044c469186000715140d450030a181c2e40d4410105040c1081c000344502d0f01015071580501010000d070828003e021100001880b03403460b40c41340c101c00240b1030504584c11200e805200844041a0000a1142c510340e5104c1681c402040003070000c134104580d614080700941da003409010068007018000e440c00344d18000f50101280c10391203902c011503041010402a5070040d07000b29044a060180364040841d152601a50500780a00b842440c507400080d91200343e10f0b144060361065211362300300c03404885c0c0103042120f0314001c40c045200185a90121200c5258090340202403e441810074480d1443e01340e000070b40e590010041180010382c103000040f1081200b401d00880c20f0b2160401405a061030307140c00c0410f12800ca00d408042d915114001080042c2c40c0d07680c1c207540b07000344100300100c056514588e150203059a1200c019800c2160004440700b15104c07013045424 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 215065557 1250 215064307 215064347
    0x80702060c070f030f0c0609111003050112080a1101050a0c030e0c090117030903010e01090516030f0204051b0a02010f0b0406060504140109180903080f04052512080910 74
    0x140035a82205d0144003001c2c0101007000401c0a04002034440c01000c2240e1310640c00400344d05803543c01c1c04559201e80f450401014240001005516541d5601140d6036030020b411a544102225058458081b2000851855860141004880c543d103500c1900c40e110345943c1842552103000c0020303540d507101d000b03040e400b014020040200c3e40161b1070242c0340d40154401c0d07070b04018401e40001d08450601c4000d50351651185030020030050180502404030400c8101c40c0d1509045407244e0b44820b4040a00034021030b0f480e07010803c90b1a804807540f50210241ea04982d0307680c0f000800901800640448490084c1440291121850a40103c6007900c800303980b007600b85482c1443d161060700c41c60310400d0600880b0708011801d103202255030303500c2c403000003400315441d0380500d001440c2c80c2c0d0040100c0c0700070520500f03200c009600401c1203c240a070b03080d8903510600d510f0100126040d01c03584011085114141028100200000582840e85040340c140040000d40c41007039442c0303c045c40f00030001d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 215066807 1250 215065557 215065583
    0xa06050403080a03050912040b120901020f0d1512080a0807210b0d06021204110607030c021e1216080102030603030703140906040f091a061608070b07080702060c07 72
    0x40c0c03081e403103140e06c08152000ca403c184001e5514400035407007504146891080002d61060100f402d401c0c0607003180e5940001c5180440c035110b07580c40c0b0b008144d2405680c648440c402605001c41c1c8903030b40c014182c1880c0000c00005213252003400c5030712800d150000318550f90001544140030704460b40040c040b00c80008455924102a00c00400301d14100f954000e0981000402003881d41c070180c0904001e01c06a01c5503401c003424411180003d084d2018030602040007030303600295000010101059040d07940c0c1a00c0318600301d504060b070021102494002d07030403401880c075036000042d944140303130700383c4c1c00e905001c549907040c0da400e034401201c078940c250340104074400020744a14981103200c1e200c00d01403400c05038030200051240d0311650020007011201d03c014860202c26105480002c005643c0101c08080c0c0d10012840501032030481c03800c4030b1006483c0c2000d0041850440e0842584140a1149454400800b425034001640c4040c0148511070025065000c03010840d81000d0700004040814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 215068057 1250 215066807 215066827
    0xe060301090308011703040b0d06031707151d060403020303071115010b0a0203040b0307030b09060607020f040b040b040504120305010816030b0a090f060c0e040603020f040b0d0c080c0a0605040308 86
    0x2e200700c171444205101c00c00c8001040391003c0040d080c01c807c1c0c2d0f04080f94281c907504194091111ba50000340c0d40c0300c0204040f500040c00031100043d420000700000c615001799602c214480481110b41201350701a502c200301c20540e01000a5100ea503d40c1c440822008a0410080d91600120543c980c002040c0c4014040ca00e8054042d28420405104403441c1940f5510700d80115041550391001094640031180c2491510a03c100d61041c400c0da6824108029900040c0784070800804880c0959601c425541c0e41d80c840e50800146203070050700501050030305140c98409a840303050007400080c601303c00840c204401140070740344d1807194100c450605046403103200d10b040700500101c078a141d40340c04240014032034500842e0010b00070600094460340401015200000e10f41d282c0740b0841c40e1a00500060b50b07030807510044401c050b5000101c9004800c041307040c108006101400c0035400280000340c200c800034101030315903401d442030b142455a8881c20340300340c026400700412071502400300b9046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 215069307 1250 215068057 215068079
    0x4080a0b0a021b0a0314030f07030b040605030a030c05011103010303020d0509040b090f09010b09060d0b0a0f020c100b0d02060904091b14191d04150c090e06030109030801 75
    0x40740d0081401483c00c28407081080822510806491460b005400703e40c4c05e00d80c100240c00d0251220400e124914585040d1024006c2c1c0e00804540501d9543e2084003810b8890f6817046015081c081e04541e1b4176001ca04016040802c81a03040302ca960804508245512543d0180d034103c07680b540040c0502c0c84140c205603010341001240036042595103070b54407440d940310480e0b130f4000d81c020b14981541d03003803180c40b0768295074902110038040c101c14000e00401d43c03101100000003c0d0005100380b1142c80714030b200c0300a0724003591005075550000c103440c201002c012691f010000030408081002c1040300c0103006800403c00000395001000340075134616800c1c143c2202e070040780b00d04101091003003c03070411040100d20350000300058155030101c41c0b1505010201d95840c01c01c010410340071501c5c095086d1039070300b00500d11510300d4510f031b40418108803544401c0c3c1715152108106116000319032000800344002031045e10111608140070442c181418032902039803541554400340c1c1c9a007009100c1e42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 215070557 1250 215069307 215069311
    0xa0506031f03060207050c03061603240b04050901140112090305090d0606090b0a080318030a0606060507060501060c050c041a0607060603030908150112030504080a0507090501080304080a0b 83
    0x5014500441900d00d900d81c060340900618402da40060700e64890f42012407403c00132054250081d0b00075401d0100d4040304216401c58400a4503011802d170a86040d841d01001080d41c162042d140102408683c1301000c90240003660340a4030300b503031141c0c1d1702d045000b000d806880d4068080340307c1042000d070b6102c00d90420241c0c0c1c3d00030f0805a1400b41c3c0f02e80494555400b001c1e05641c0a56100300c180800e0002d0b004d000b15140c0c04a81c14a155410250303041d8681c411a407914640c9548814017010780d4030244010205250003000401441c0d9a038440a0510350209104560303144c60310b40003003070048c06a070300c603030a80341c02600402065459006102c02040b501c0c44c444846200c1004000340e5030350702001040080d2140c800411054690300d001780952586402148044c1c0103a600340f4254080c18150b0741c11500b9a8020303070703070349156414290b0f02c030f1049820540460083c080e800341800000540781c0708481d0341810401c81c503a61072150680300c0c00349024850160f041001e5040110703004200d000e07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 215071807 1250 215070557 215070571
    0x203190c0c15080f06032d070e0709080c0d08090f13020d0209030d08040503072d0506060312040602030f03040c05040c021014060d0206070f081b1b0a050603 69
    0x340c0c01c0c0e250301c190300452031512070710000129100c0421810001030810070ba00a9003c1e0014102c61034007099040640d00c40c0c4c05450760601c88075060100104081007202d0003001e001203440300c0360501c0e00e0003d1000050740100300300e07031140e0303078801406003010b001e281821030300f1078581400c001d08041045230009100320307205c0c0e01c1b41030360303071802c128030f4480c4010017031018007070401aa54224034082c54144107035203d803d07051103031880070040815404000c84201d00e5100541c0c034281c50402c04040f000700b13a00c4c1e8074805000000517000c0e01f0030200240b61030043e00210101d5800c00300f8400c0e4418607109901503000160418080301c0030600b220406180c01611443e480716983c0d07100c4001c0780c122507841a0040c01684103081c04000b01c0e070f03103101d80c0303070840320001d400c020f10315207040480d100c0c4900a6009006a00c00a210b00c28008000c60740aa0190310031102e030364640c009201c005090b1003200e441e40c00c6006051600000c1c0116000900807040040e05043c0c01c94a000208220b0781c01c010060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 215073057 1250 215071807 215071823
    0xb0406200a050705120d060906080601051c050a0503030a050103020117070f0f090909060606080f06030a0311010e060f09150108070504021c0c0503010f0b070f0b06041503210203190c 80
    0x4045e100d061035000e0044412130120020f103152811420f14107503110759000e00a55000703440144081d445058090f01c903010205200c0900c4102171800503d04071800101030014000817003801800c5080e9003190303040300c1c001da8841c820f5030101c2d44035109614041d140c000c00b1448080c800c0740e11601400001c01c1c50030a500344013508580e200c200000761100c00c0c0049031031070f554070414413034039030040d09080e0070060720100d80f030980c079024002c40e5440300700c0c120140a120111a6080c210b500035003101c090302c0070721410317105a4102140301e190840801d80741080301e4000c480030310b2245180500c882e03040702c145c90b0090001310b00d01002d00c4000d61000c00306246076042050903e8540d46180103036030094040d43e8a840c2c0e40d44c90030088200040710354101441082c002c01641d008202e802d1403d6802c540c003c1010001615a50000340080c030100780c00e000c2c550403120001041c04031482036809640011403590441134500d10040340c0b42e11400c1c0c0d9228010b40c4140445200e68466100c1c800c41a00c10009c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 215074307 1250 215073057 215073073
    0xb090f060d0b010b0a030c0507050304033f031a03060a05040503040806010b12010f05031c030f090b15030601080d0c030c0b240901080718090f0b0406200a050705 71
    0x4140b0180800d03008500304550005403195426454441c00c24003000d6864501d080064036562161a8407803403102600080360061402140403004560710060155294a5a103070071140001c035544a05464286000c689000c4400e0f04c111050500c50044201c001d0142100d0790f80d02c0d105030f00802c405041618284020310010680100030005117010307007240e4034041c0c0c80e00c110007034070b20304146d05030400603644081038030401642c0ca00103a103550032000c80140c0c0b094054441c0c811401000c808185141c800e00f0700d000d840922445a81050140155101610070f8440c02e00505986044c01c2c800e400d541d034000c10030900c5507442120012113540c400d00d0040c1040700c0b507884442c3c94800541c3c024030401300402c410346500c1c1c03038981c8043c0039200a40e1a2441c42d03151820540c0c070380b83c1920810078a8000191415410740c460742c40400041d80c006412511005242400400c0c000c00310380c1129200e2070b00d40110042100c0c825200a1800445007040c608000000125510340008008450303d210b0420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 215075557 1250 215074307 215074313
    0x515010b0a12020f210a0b1c060c0c1b18050609130503070803160806010c0305031b070b0115080a09120c0f0501090305090a0632070b07030b130b090f060d 68
    0x104480910f860b03840311100c01c0c04e00d40e80d80d1080b81c41600e1f841c1d100f00c82d80d141c8003241c8841c01c1c1c00603012070b0700711100088010f104502a24080e810172030050201d84070307018250350605400240e2055858140c0b200340c0480700c035010b44040303640a4032040d6002001000143d07a10907404c2d000c0c04c0c0c80d4410070a90741070010740c0d982d0101e5604140d03088411043d8980080c0c000070391001405511880920300752103440d00c0ca49010b0942c1c4005040303100b4a4980032007006480c009081154010b42e440035007180f8540c0e40d6a60110f24881c1c82c0d101d580080c400310080340c628135803070042c0000e094011080a5641400741815039145480c40e001700d605114200009010a00c00e205460003140241c80b01c550f54035145c0200401614140c002c3e00c20f00a28000002003408500e0107a11a401042550003908081c004040c840703000d555001001d01e0001d03010480c00c0d6605030004040254252046581c405817074a01c2010349904900140e004502c0e840003400d01c500b481e13207081c1c0102c80034191410b0102c050b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 215076807 1250 215075557 215075587
    0x1c020d14060105100e0d0b090a0807081e0408070b09041b0906120c0e060c010207150b011e0c020d020609030d0c020a15080f0c0906070515010b0a12020f 67
    0x100340000a500001c004100c54104070b0603140c004445858050346200b2101c000a40000100d90081e2280741080b00007841e402d01023180301d41e0301d50000e51454469206140103000b40d4030400328400d50107940400f140e91034100d0025141903d0069000c2c00c64607040c6913800c03030316030008c0015550040e16540c80c2d0f6085090603441c0c0b221803d0903540d1004950404070043c050491982c0d0059100b0318100c1600705055100007000c4003144222100c40d641d085d0032802c079000e4010242c0140c20010030b0740100b00303140100c0e407060740101001e880d081248601d81c0f51826456409034035410104100c100c804005203042401c1c40c0d074551000304043c0c204040d0300c01291501c0014280c250200381c154600005529000161400610144411480100c0c40170401031100c0340180a4140314415180030032404c41d690320503a01c070042d0141119894044909010303581d00841c0b600e40564404a10001c42c11608a504888104800c3d0301c50441401c0381e05041002035001506410100a00380401038081c241c40b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 215078057 1250 215076807 215076833
    0x15020c10080604270201050304060b04061706060a0b1909091803090e16050322150c02061b180607061b0302030f0c09041d03030109060e061c020d 64
    0xd03640d41e200924001041c081291540345100c0e42401541d00b104150720700183c265001a0360a2038156180d40711490400c0140c90000300b05948142003440c0480c01e88068019061141d031514100da5543e00e4600911950f14001e0044202d07500c002c00c0191700f980f54102d96000c10394910b20f0078082c0399540300305000841e0782040342840100c4960710700c0c1c000c1c9644241140702600101c44101c0c2da90400b0740c044100202d10350403850a20001000182c04100360360710402800319551443c00b01c0841520b010540700c01d07440d1410718658901081062070610004586100742d049100041200305c11a204c2d440e00d4100100702103e48400500d000201e4542e08050844a84603a00200e294406035041150200c1480480300400d4418810407500440000195400034418480d4a036203500150208000c0d041003612603640c200102d0f003400705281e00000031412500000c504102e4907444201048140500350b031003070741c03101d21440e0480c81d5500d50100c80c0b031a81d20040042581c3d04156032440020303610 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 215079307 1250 215078057 215078089
    0x3091103120912070e0f100f08010902100519050309070305010e0c15120408070f08070b090f07080a0219080a1109010e040305071212021309060f0f15020c 68
    0x418040d02e603003041640300349031250000140c80628102809030307807152401059031840000c3c000220354600109035058010f04625105049030903181d0300c050303010348440c04040340203400f004590b50350540b161381503c00c0c4080800441c900030600b10f00895075034101803d546030500408800000082091140b004001007d4000d030496032400000c00400041c0c00d503000805c60350400001041e80c8054510070f50041e03011181c42d07280e1741c05050804240c080c904000700500c200141c43d006105506021602c0740c2500002c40700110006000940ca03010b0500c20401c1651040c10a00010b01e4252a400300e11aa07440c0d41400103551580c03024901b4451907025600f081100c000d550090900d445200d0142c03403442c0c0c00320f10905150380d00400a00c1100c03800381c023500035030400440c03180c0704805410b8409155401035494010384003c00f0f02c005614070400e02c1c1d89103081030025504000003599812900303001c4445080700d240c1100c9044000481c00008214000c0783e04c2213540b030f0b540b04210091400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 215080557 1250 215079307 215079343
    0x131103031204050d2607050d0504050307020909070f030803150301060b0a08090105010f03080702012c0a0504051b031503060a09060e070311060901050d0203010306020306031c020d03091103 83
    0xd043c100b450501c2403a00503603007000342c526900d012a08142c1019250760a0080e102d10065489590485080c020441074030b03061810482408140840000a08800c038000c4807841c1c4d2036201d801b0840e95a074030a00c242c41c1440e00000c2d0030000700318218061030340035140d01c8902420340c20300c1c0006030031550f07690888c060310040070039158030003544482c00e5588a440700d0000c0205504003c0c407041103904600c4014024940024031008690ac943c440203038506503901e864602c02c0501c0c1c8103407000050381041a00881d0760714000038070351403d405010f0282b0201e40210142090800300c980c0180e100034030b41c20146c030a0000c2044941c40401c42c01e841105070000000c1c10314642d14003041907c120401c011b005900c280c42c2800411103001d01c1c05d0041c3c40c11100c003966446028016901c81c02401002e449151010000000707016140d00110320070301085040d9040ca031030161100620400408503640160b110402c808400e900a42c80200c9003401030445902c02ca03608800a41303005050480b10407802 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 215081807 1250 215080557 215080561
    0x204020a08190603020d080c0115080c03100908040506131502060a1a0a05271302011b0b13110904030207091d120a0e130516030b06031311030312 64
    0x1003040c2e01c02d10390449a9081404550f25580004880000b540b001500380540000e100c03e000702d09500c44020790284920310b03000541d42e0660a6102c66110050310302138021100c01d8200c0000794440c2080c9141e0200109061900b0941408000d0b0070200f40d01010088a000209500e425400d1000703402c0c481340e00800c55841c107403071064103403071891905c000d800c02c0c119038244040d51001022403d0314405d40d5002640b40540310025000404c10ba1900310480008c0140f000304104406001000e50013038880e541440c000b41c81115241100901c0030341041c07291808680c6865401021040f2180a4001d40000080000000304c1141c425202140540e0003035034204504019400f9504045409001007840140c00a481d191034800340000e9420510000a140340c0b01070149401c003084000150802c040c2d5600845418000c007000c0d104418102d5100340c81c1e6018610a01034005c2404003c0d01c10380c25501ca0045449104c48880400c45400340f03c1e4001c941552020009005880c107117071003841c0b141c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 215083057 1250 215081807 215081821
    0x1050106090f140409061d0c12030405090103081602040c050318010c05070605130c0b04140a03080702010c060b0613030209090d091505190503090c0307140103090804030204020a08 79
    0x1001c00d66001e8200744400b90001c0000d101d403000d8450040c1000d80380030480701018035095006007111a9400b40c1c17200e50b483e080c0c4000b080054106582c402c141c42203900445131440d2160f0341c0c080d600c04e6a0340410351500500001e400140904690a0f0411101e4082c58940d400203054034002ca0340c2c20001000071040081480c12035040203211076144c4000c0140c60b036030040c0141507124903200502441e40303500100d030800e004000c0c0040b0780d0350400d808080a0362200001049603001c3e01c50320558100a406113031080c5421894074040740ea10826945c0341060340e50054400c03c0c410041a1030065445070f80c5881c0f41c4030721000301000920311031148000f900f5441001990300d0007078244820740e849a4170782420640c1003080503065074407400c8182600c01c0078610460715842499407030100d064017100040c02c0d440e0005e010b1809071041f081a0f408542d02c00e07082c103070f0b5009144540c0401110303c01c81c009040d40250300c603855083c061440075244c03a03280e40200e41660f10049144000071000c004000403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 215084307 1250 215083057 215083067
    0x3070b010e04120815060c032a060901060e0708090f0a0309080106080a32010c050a0806091303050c12122205060a0c0e1c1202070b18030102160501050106 68
    0x601460030140024284003420312805000b40d50174a000344000140c55914002c10015911545000d10381038038086505030500320803811584240c400c600c01c840104030b90503018001c1209641c0003d6003124541da030b20100320352100d400f070b1407400a4052100b4040600704140101a5518081d80f18104e40ca45480c1c9100c1c04c6900c55440900c1a4004031400800220090702d404400c074407418940c00b0800e414101d80c440c04000b02d0348010030f58a020b241040c89038028002c2d0a41d00780baa164110141d990406015600341c0481da111000d101c08642400020b00402c09014480d007118100e0b0f14000c44800641c1d030a81c48015140c51040088041003e440c80f00c41080900103031100b401044400d49998450b40d849010341501c1c032098440c50069a40c1d8826225540002401014159084001c082204140d4002442660900c0c03c2110540d407881c00040c0d41422250a1b40884d4604103c1560610b01100d0350a0a140e042d5020030295504481002616a809000c2d000001c0c0d01e52405e680600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 215085557 1250 215084307 215084333
    0x60e0105030a0f09030917210d0b03030403030806090c030c1209250e100503071401140301090c02070e060105091c0f080a0f030606090e041401020c0d170f130503070b010e04 76
    0x40b5030100c1c41c0059523901e035000d8641c8020780300b00070a032541080c404d1749010f4480c1c918141d41600c0b002c10004285940956064090389090702c01c6249070f220490700b02c80502c400c0341c0c0840c5820f0108103030040004842d65150b800608032040c0d6a84c0c1c481d50500c84010725800d038030141c080c0c0c20301100f8000c141c2400c04251b0402503e0341d42030780446c5018086500c0d41128401c0c80e880c0c44a40030b20728182c0e4014180c0b0243c2c220a0725440c1c2d500c0da10345204c0c10040210500e04d00042c45504000304000b06041090350060005848060911700c1c14030410a0020000755140e10410550b4528000140b1075145a070030544120442c036101c0d501000000c0c1303258102d4032500c040500300701040104075045440d010503140c0f103000076009942d950034050021902d0102000b040e601c0003c01c04410350000c0384286100105944207040c0045122039290041c801341d50344080c4168000c042242c1c940b076801e04880c014030501c00d0700d0900159449511b5012026409445501c0d0340208000c108041070b0b603648 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 215086807 1250 215085557 215085599
    0x17011407030f0f150b0c01020d020301150206060d03210b120a050f07060c030e060903070303180905040c210507061707020115050603191b18060e0105030a0f090309 72
    0xb40d540c4032060344c0409039441801d5030f8600c000344203001454203404459084c107a1203030542da00d5035510500d4001070b04400c0c0d0300f0018041c0d140401c0f502e1814035a000350f910b4156550701c002000c04030030001d0b4081c4e04900c600440c0c0e40c3d4404002e841d1518000260b05504030000340c48210306e503060107400c010154441007240d400c000c1081c041c0c2e0b60000e81c0100c0d69601481c1040d00c00c080700001c100144182c0816075418841d0304030020806034426910307031070544018101c003042c2d65110f4841058500680e001450900055800d1004000864056403078000e150f80349800b050085c1c42d00780c1000c0a54100e0400242d6120306040540a41c441113500300e5614070082081035400d0320f00500000309802030510800b4000f012503008840c030202d03a1052213034007204000760003412440c007107100c803408119004075015044021040f14480c3c0014201c0708251119400c507074112004550070b61000789410080b03a910028414030000c20702c00c030b145580c030a072220310380c0034213011018001c401c01e00151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 215088057 1250 215086807 215086811
    0xa080d1506081f030b10030c0915090b0d0c0b0301061b120c0201120e01020c0d050f04120303021902100f0b2224030606080a0c17011407030f0f 63
    0x400c40642d00691081d88000d0091411211160080c0c0c00c2402e000a58005000c0d0480744051000200c5028481003c8a11880c02041017580c0c0c2c1d10407005462003204c1c3c0e00c00c81c1c0d4465408220340c52082d0445580120002c14000300c0c00b0140c0e41d101084582a0132002500c0f81c003100605c045038001b203684ad00c46021000c401940b10956603640301c000402041300c420024052560011039018408030911a003166030288000c10449110900075081120285804c2c800c000d40301c80170070701610448807014201000d191802c1d042c2002d41c0c0c0401c2d4050401c4080580c00c0202011040c10148182d4842049901800031480200d07031a90a8900d641107880071300d89465420600756403180c11a80ca01e10542d1040b91081c0c00220943d002803030b001803c40070a050543d00ca0ac3c2e01614106081c003524803422041150545441d40c80d642c54652140c01400703091481414410410681c60045038410781000124021850580443c0310600503600d43e8003180e2a2001072180340c649000d0540902c000100c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 215089307 1250 215088057 215088059
    0xf040e07020c0d080c120d0902091807030b13021003090b1503030a140702121c14030601050315180601140711060702120105040c0501121406100504080a080d15 70
    0x103070f00600181000f80440e00009030005110070500501150f034105c101c0082c0c403000d450200c040580b8068400b01d105200c81c500060201508020040c003141c031602c02000e0050550b41d41c01d41094015007911042005a5100b900507520f105401034200342c0b544d404281130301d440c0b03001084400701400041d105207080381d00c954a80c500005840d0031145914004103c40b501d0f550351402c030f2080d200040c1d00420070240f8480e02480c0020300024910b0701040c1c43c184c0c0764a10300c003168010101022000003420400104849600c14000345400071100d58082c4003001c1100d00040361914102540e885042e44039080002e507603001924134604005110507030b803414445581d594030000807411901e200d100080742c050103648861811048901e01c0c500200100d08140c100410b030001e03244210390000700c4a80c07426411a4071400788440c030b546c0f0121806c0c2240c03203e1042000340d2840e600200204a014440010607100c00c01c1403100c00f074060300b444d07a91032400b02c11501c00c0d1141d01c8020b480d903540350302c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 215090557 1250 215089307 215089309
    0xd080f070f080a02090913140607020a060c0e0306040b070806010e010819140903070b0a09111012060b0403050d020703080a0c1b140111010e03120c0f0f040e07020c 72
    0x21410703034011880c07030140b03415a1030b00c6001c0700900400300c400c1d400100340c1040180e0308141050b070707002d0756026948130399202d6401180c4030707520300c402c407550b00040c0c00039620030740028110f4002214000c841c1c105030000c04040c03004a86010000c96003900c40c03618040510000a0b00018005c0d0011020310b44948501e01010001e800481c1c05003080c120100c0860001c828907070ba60384600d2801001080c00c3c401820300d40d143c00d5503a00540015a140d2030640080f8800c996944644240303c0c0d8840030050244404204001c05490b03619200414402c0c408040380b204440d501c1410301a0602c034410b55115425420000d00c0c0c02031500c158402d40d440082d05101140c1e40310300303452120303115207082260300d050351400324850307222960a0300e410383d0340307030300c042030f226681001e1307203082c4200381d0f00c09039561012101d140c00d03201042203070200e6800c10021847c01381c4440621507844144078081501d00764540c03a891a1560103240640c10400000c1403d004910960341c0882c1c005050344014800b00c94150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 215091807 1250 215090557 215090567
    0xe0a2a0203041707050d0803220b07030218030304080d0e03030315060d0608060703020319050105011d030c03120a090915090b0d0b0406020c011401151107080601080d080f07 76
    0x40900c25032920a8000304180f84002c1120101400018102042a1669181c610300f01d41040c1c0d032800b401c007c40d2000203002e10200d00c1c0d15800d103400141c00c032440d8841c00c2c4c1c164000d41c411503842081411800c400c01441d1400c0009000400740c4000421890f200c1207401000302008214181c404e41042003070101c9152400d070400024007003218000e944d402e0300ea84140080c007503540802034038040c00041080b4940c1581c091445100604a607508061f407404c0c00030b045400034000c482c0441c800c0e660242140600d0400c5d20341c241c0000d0f0448114075000b0000a25100b4a5000380c4660500046d010201c2548120f501c4020009048180079440802400c0038200300103011704406181da0748903001d810364607100c081498940001140d1650704060030500040e40c4448843c00596003000c02243e00426500d407030078103e40000a107410350100c2950103c030504021058402c8512a00c503020a0001d401d01101d03008114100040c080c41d01030810143c130211008110001c03190003030302041001c98100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 215093057 1250 215091807 215091809
    0x1915050310051507061b020c0103020309030d050c07140304150507050a0b180304170d1707050304150507030e010c09030218060a030c1403071401080f04060f020a020309192d0e0a2a020304 82
    0x4fc08a455941ca0141031464040c051000d40701c40c0c4002c0e052980d94902100030000d41d4490318007901d40c0b580c0c5580c161564410044010035a030301465100c4003282d9403124030350304401c0c041890550070401800c21490b40d00583c100d168481c0701d408100a200c02e00300031b08e0011000508041c5c50056580c200b294440400400c1d010034003900100003410026031501040c00703105012020049810f121000030014052410810b00075172a20494800032030240c8801310483e0340c02051241055801f00c00c20803135600280186030080300b4950040005600c4070b104801070000c690380305070080c0c024000c1610340349141d8010804410115604000c42e40d10400b12648208401d5680c2c400361146d107031400c010725500301c03108403543c40070403464101079011001b00381c1a04111a80d05102c2c1040c000c03003000042603c54080b00341402045920b600742d0000745581d448210005401d0b4040e642c2c000d4111001c0101e500580f151782c2c036030450301c61491303000c0281c01608404404602c1348100c400e02942d00c0c421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 215094307 1250 215093057 215093077
    0x1505060405090d080c070f0302060f0a0e0c0114040f060503100e10090e0f060118061d06120a1a18210c0106051915050310051507061b020c010302030903 67
    0x20010010340c8417480101150040e13540086145404080c40c2002501c9550994031186030b0141c200214034420160b0081c0001c801a2101800c02d0345480c80040d41d41e0313168484040807540080c0000a4201d81c0d43d45420001c04107501c0d8070381d40e450304010f00102407545402140c0200020400c0c4041e81140302007080c04e6910b04200010000000354030b02c0d103010782c1441c0981e00d03885008004560b2100031880064082146481440095141c0c2400a504000003004140410311701000804519207040c195200f010104251440d19000d500c0d00301406000074840340f00c1d200004d040c000040e41d4a50400207405d42940a0b1500c1100003400d02d400441242d540700b407103640415480c502078020340c4000c00801c2c00a004800303000069420803004400307803042d404610f600d038400076401c03070180d401c5074410115541040d00803400d1404200c030032202c0d00b0a81c908200c0a00c00a4001010b902c80c00d40c0181e81882002d0070800c0010000380b4010191007480d0405006109000944000000b81c0c1c02201c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 215095557 1250 215094307 215094317
    0x150a051e01021612082104030f030f090b070f0c060c021606020a02012f070e04030305060a0614070311061e010801090f06110c030d0603120c080a0e0f0d1505060405090d 74
    0x4000035003591b409100c2590010628152410700c01050b41110642100348000d80b81400000d45184c0c42c07100700d0382106405020302c00758000141042d88143c004d641c0061482c1006080c12070b81d0340340e03203048808100724800540d20000c0c2400004545040d400000e044520082c01e0301c12071503000900381389003404042d480030340c0e000580e0003a00d1400701d402940b403014012140d01c00e554440070840140250340980c082858900400c895040850580307064400b1a222030b2814081c0c40040151035118150650800801324140d41081c1d20520040c1d000e030310140320040707c85a22401004004c401a408900981c3c505240c5000107044c00480307407680c940042c0009210761810f018043d062282283d0b081d1207020010711400d09558941c450b00030343e8040c01c40e08141c000e028000b910132807602c00000d04520028450000c01e248100e1030340e0385184c005814255116043d101107444d40000c00c0301195250300301fa00030f20343e1148521503c0d9200348100c40501490401c8205241c446105001e80c004001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 215096807 1250 215095557 215095567
    0x180d050f0a24060509010e0a090b0903030f010b04081b120601030308040c051c062408070e0f130b041a0a0b010210050609150a051e0102161208 63
    0x60500010300d1410502080e1058400c152920090a2050051450070b6014244035030481200c144219410b4a10140c494a001d9003417540d00c18071240d000348843c011986510041002079484c404041c06000036000560300c900742000344000c14401600403004010052000b04480c000c0081c0340148400b42d1030000ca844003074540815184d801c0c10300e00c0b882512400000208059000c048644510301889492044039180c40400004000d1a1040d4684218420300702c0e0200e0310310390040118400e900b5070150550b00985000c010312200b0780c09080700d034100c4d01d41009400840303524690300602e201c0888003c0d2600958241c2e121030342c1c3c0b130090450262603000404001074090340085c000500c0200107038034549048110040e0201512113030042c0503282450384800080c0c041c07140034180080044500e42e54903040114418006280c1580c804040403000031507071121440b800c0015180030400884801c20000a40b808a000400c1c60005005d250100148000c03840e9812119502403001030707840d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 215098057 1250 215096807 215096813
    0x10e03150129030115020d02010605210102070506090f070801050903070b0c040e0a0204030201030c0518090901061d01031e03020d0e01050702100804021302070c03020f010507050307050106060212180d 88
    0x2c600c81030319180300140000c00030810540710a65000d41c00032a41c01c507206c440e00300000b00d0a0f00c0181c46103580185038503600805002103807040c0030f80808008001420000720b62506072800500351040c100c170b5000801c0b505210b1106020705405012410001e014900746864119039912441001070168440780000c81c4000b903100b8101c0d002840e40b1000e0707414608040407428002e601c41e11040740440d203400c0d4010512405601900c0101d0f400030600c000c28148030003402050b481c01032022056542e20300012441890038156071407a4120106c00002a42c114940b06060340e0b07100c0030030408482c1843c54030f00085da000070207800030070741803410244610142d00144e40034040d0480080d031001100c1d003403603203185e8008030081c8264002ca4141c0c120070b154107002c01c124419054041e040c801001d0050015061905800e4104201858900e107407110301c0e01c071582503404c0003000b1103180c1d440b100100000d5504004080d01d140030803120629040701c0d100c50f00300e400d1071340351100e0045503d09170303003424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 215099307 1250 215098057 215098109
    0xb01030b071b03110610180c0e0315010807050411030c0703020a02090117010b040b0f0d0206070b040b0403080601021504032010140907030c0e1b0d0605010e031501 72
    0x21100074808180c059142c0c9203805840c96a06205450541c811030b000a0041c1180200c50001c9480440002881d6001d003205540030741000c81e10401407050030a59504a034404100c2c445003407451050000385541405000c80c24140d90798411032007a030800500400c00689501143d80200c080c088550b030b00c848920b0706900b00002154060762180621000052185100f001c050460007031800810041c400350042104803400700c190030307030028200c1540f00e80c6c50401d80400c130150f1340000d1802c0c1c14001c0503075178943c0c900021141100c0000c000801d0104041d000080d0f01c0e0410790900140c1610340e596515100881c00003007003c0d0401000184241d4031811a00c0c4549040a50f00c00b40c0384c402c1c03100600907001d4080611914203049014000032420742002c1340031000e03294020001e4107031618103c1e9400116a02a00c00c0c496841081d0107440400c05107002087c24801020000c11458a041c001412440d40400200e000307801050150070109207000031941540d1300108070100b0b00c00003142c0882 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 215100557 1250 215099307 215099327
    0x708090a06020703050703080a06030b0105040222030305040e070e090609060d120504050f12070311011101060609050a0509040b0103140309043306020d0507110301140a05130b01030b07 81
    0x400a440010100f091540c06401001054041c0d264442691101d00032013085440e07034800500303031004600050240b882c003074006000c28000c2c020308000d03200d40c89002c01102b1400350300803000300e88000303400c001c1280b1000540307a205c4500e0403d04000383d12030000c2003031080000c000c0da03c5140b160b400580c03603030b441e00d00c41c50030740e0b4000001b0002d408004102030301e07a5101c0c0c05101c1c030803c000c42d0380802c946042c156a0f0500300c0c0b02d9024000441c03440d95840e40140c10404414140704c0101030110f5400f41c240300b1400240305607030790034045070310704824801756041507040309010341c03040e85c01c00c00032800348040c1d141120362201d00800d203c04280f40050550280e0160580d005041c0b80d00300c20400b00340300f9074003103100f0320100d0100c1221280364103241146040c41080c1c0541c100d681c01421207400740c0007600079140a42c0480f42c0d900c20f10400207007190800d02032110805028420b0024194070f40c482c05034000c400510012102c042ca4550b80c00500d4144030040c0050400f0303000400440c480c2c84065 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 215101807 1250 215100557 215100563
    0x50103090204090615030209091f0c0311070302030712081e06041503060b0a050909070306050907090501090507021b030c0402181504090506060712050a030e0d0507050c0f090708090a 80
    0xc58404807400e100303111522031100343d07c100a1400443c0072800b0204e2008502c00064ac02c102c00510b2445450f0054491100c3c4581850b0b501c40074420400b00b000f00600b240d520039806159106464501001801c88079a01081001039110811140011081e103502c290420308500c00e48654581d00010042d05001c00c0c4501c4801c82c421001040050326080300d06032400440d04461140d461f0000d1145101c4100e8078220b907540803910030000f081040d031000c0e0f080440001500c8001e6100c1c662201503810a901c44c1307902d196102e0800240541c140b0050340c0800d600300c1138811411400000035a200300403003080b841254006142c81e641342604c1500024000003414038140c60150800100351a006442070708030355801d240015190f45030050441c0e4035a503001c4107405100484650841c2c141c0c200a0000702416a150301a2081103420004040c0e400f4040c0d50f125954170305071522504200c2c124608500070902e000c1e03d03078840d56030360601c1d81d03010300d403490280540d944001e4140e2030202000000727 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 215103057 1250 215101807 215101811
    0xf140f07080f010501080a0218360d0807090915030213020301180204050a091d06090706120204140f06071703040c15081605120c1b1203010501030902040906 69
    0x1142407002c20704210002c0440001c0103583c0c0e03200740040d15540e440400a41c000c00c0f41c52a0300301c80442c0c004881d001f0320030080442991960540f042c0701c0d0081e00c1071a040c8401d0140d0503d44410f001c00100715405a01d1a11703a10605011034090301010550051044090721001d242850000b4000c10000464004200d80c81c92060602124000d6100707010b0042c1c081d18072100310306403280e1402117804031400038000414a07407809a840b80101280d0307030200385001c40425040300004042003218003451087c009800d0540c540382d406000c00784940c10382c0c1340d03140c010320080010502081850104004c03d4480007034a105210004040e441803000040c20309100c0e01d40c0000b00b030300040c00745110758803a200510f01140c480b0f15851140701949403403030000301d45070000f076130b00c00072045d0105076224281405800c096105801c0100c08104036a64290f8150114100b902144a980d04515241c08071015060700e80750704800451a10050062905141d250124002151110380c0b203400c41c16082407003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 215104307 1250 215103057 215103059
    0xc2106040b040308090d05120a063222050c070f060b01180506070f170f030a0b0a0e1f0e240103050603070909020d050609031c090f140f07 61
    0xc207007068819a0b00307a0018a2074000611003404c006800328a1507100e4075924100b00e0035582042076035400400049100e078035804005170409148a00c041c442c00c0081302c6071a4030b0944118100d81d40000c1009910900002883c400f05510455400565401400c000320709581e800c2410710300c61141c448010286100c981030b900a11000f6882080710940913a10603003030400388203910488a8040c020780b94404410000540000d841d1900505280d02c1245202c100c03050381340c00d42000d81c1000c88520030400c1c0000c1001400300040c031500b603000708121440e008190500d40511004c1070000e0a41100c03007503000184101a200c05807200042c020900380c00c03c12720b010140444440c1c8400c500201d9009442c0810030158040d0003401d110740b1010b0000e05400389400340100c01344c46548016a0420301c014a440c02080c1c050145511a80e030741002566160420804506141e501051942a50745440c0440c4002814002100907441e00450503089030304c58050a28149403074800881302620070620 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 215105557 1250 215104307 215104313
    0x10c110a050613080607020d05120a06090e1b0a14010516020303071101080603010c23040b03040605100b0c060106030b0102010213030b090d081302010f090b07080403060606110c210604 81
    0x403c510030355824a0aa50094131004010b07a82d030040302d43da03a00412070901c80e0988051402d110198414100c0c080030807001d60b10100b0000b1111070a800490f150040d6120300d802c0d01d004d50300b070b08916205440040f140c52901e138154500384080242d0904110000612020118801900c83c6485400909981d6070b203000c0d1500c1d8a1101640364850701144c0080000b03840c0e441c06215806190401c0c0c0c0b00c0040f071140d68025915241c2c2815030082030740307006005c0818580184009103100710300c10b26000a40307062a508088040e0415070014404c4034040104010341a0040b401034111055400c0115180143d1070042c0d01a010b19050300c0805007142c032001003404a062212409041084281c440640080780111040c0c00101c45000801004008000055100362010700680140d46030900a0b10344640c0c4450341d0b40d0140c001504d00c2c940102d0180b00b844068400c010080c14507080c02000c103032503002015112840f0451461007220745500c40600c0c80d450310545020800910140c500500e4545 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 215106807 1250 215105557 215105587
    0x2031b010203040b0f0609040201140f18010207080f03040e130605090c040506060a1e0c0506010833131b08061501020c1804060b060d1b0806010c110a0506 68
    0x83c0c0a40d40382d000c50300803031840e24042e40f10b507001e4040a003003461256266001501c446402502c00d0042580803c01207a010062802404003803001d00b903039a8075040d8a6000a01d003500a400122998001890100940300c000040b10119081441c200c0029a070f40c10841c0035424603e000904928102800c02c00a150003040e0108e911404071010030160302c070381c0280300c201d01481440c20041500200d208452825481503524003c0341450407a400e20580d075a254140402a4400c1040358014031010341042074403848601c01c1d07034040d845c2c41559481311809205905010303009000e240468182801130003c0003a0303070543c6912492060b51340e150382c0c00c0300c40e642d20401c80d484a00c04d21041c440d80d103158404142c080380b040307004082c00c03192040d5a041c1500c588002e0000c4078441c0c0d4030f040d41c1d07c2c2525140054000b01c0115440011000085084004a4004a4841000c1003030000800200d130782c200403440309594000c4041000054400003141050300d01f40c111984c8440040303055101e0186003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 215107913 1106 215106807 215106811
    0x909020409081908090a03091520101104060906180f0311330702130504080702030d020304080307030302030a15030b16020708070509060102031b010203 67
    0x342d0307561035998032088480c40c22541c2c41c0c2001e07010301d4004584a0b440041e07480585005852a0780003400c8465070b015540c04a6440900c1c40f1000307101d0111110401155501040f00c0790100130ba284d40c40301280c0c1c3e1920914104a407100030034944c1400c0c0d0b01183c0c032030340f604940706040000a0390b030174501d5680d400b1010044800043d5058564103458001c500a818218000c04403030244842042c84a80b4882c00c160001030b043c40c10140c5d9100400102c0b101c42c4010340700c0780319100149550b20041100307a00c00d400c1c0310900060010282c0100282442103040303582840b5001c02c02c1e82c89028910510505070814011480443d02980055030b20036111070300080c5040901200002c850f1140e0801d46452404c1e1041103664a00303d100c0d10184c21460008002c85813510031142d03035a204601601e40600164000704801c3e90082007070300c078401c0510716004420540105014001d41007 = true := by decide +kernel

theorem cover : BRFrame.Cov 214928057 215107913 := by
  have h0 := BRFrame.cov_init 214928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 214928057 ≤ n) (h2 : n < 215107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
