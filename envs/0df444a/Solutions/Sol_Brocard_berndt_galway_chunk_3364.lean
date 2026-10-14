-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3364
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:26:40.921218+00:00
-- url     : https://prove2.me/submissions/322f667c-c921-4c1a-a87b-cbcb6143a224

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 604856115 ≤ n < 605035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 604857365 1250 604856115 604856123
    0x906020a0507021216090e0c0312090f0102120a39030905010e010c020609012007080c010801060903150e0102070b011a040f1502010b060406170a2306010516 69
    0x40c2c0c6090600600c407900c05103810143c82a80500c800200120032800b40b030303059800703600c07000c501e085101c40c0381d038941040d01a07010303854029050300444200758040140701060050324022805001c0c64016a110320040461050703c810402580f0741c0d076417141c00c8084031054800300d06000904ca01d0000c2a9640a003400c101010101e60031040925800c490f030300c0020002480d108083c61803c4000070302e682d070003200003070140e6004560303030080e68090000c40c01420031108801c02100076583c007581c0d0350400d074420420740d03000359149213156500c10014181611115204d81c1412450b607a1032010040c4100071404049542d6075412101020038002400500e0041d060f0b0300503075040c1100e085190001050500d84117404000c00c0007113404600010302290042c2c1d00c4c2e030820007032900b0164058541c4101c00342d88446c0014010480c1c0d40c00c030440c54075002704800301e260103a0f102c0a4100407142c2003042011402014022201034400030052941d0080043c5445410319982164603a000720016004035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 604858615 1250 604857365 604857367
    0x150631080703080d050f072c100302030f070f170901060e0108010903080106020f0c040b0414040f060b0607030c11030c040204060f08130b040b0a090506010b09041404050c130906020a05 81
    0x201c1354881c0d80c02501e4000b001207115007007504100401401c03888540d0741d08480c40000e98154810003180000030081c00d0006001d00101501c40c650040080d032007144c0c51111241d00101203100240329031250b80a0b03101a0b10b80d8400740c882540710054855004001e202035640b2400080b4580402030003003030082005000100301200c036450081e081d410143c0043d0115409150400700076440000c5d81115400150381c0005c1c04000301000c00e001e03141c014040c100f10003094042c01704210840c10700d188002d00800b420854180c2e914200b042900c1182c0d40070b0001a40360008001081c1a0104010303100001000c842c10742d03941c800850300f6604281e000708080b0b030041c0c2c84441d15503084081580e200c041403c1c260102c41c02540c44480803075010300044c11500b00306000030f61980b2507034042546941c1001c110384280d80c0d41c0d00031600681c418820720b80078505080d1036104140d200d189160299030701c003014000e5040c101c4203004035400616480304000381c560640d0f00100c0d6692009002900044d0349030303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 604859865 1250 604858615 604858627
    0x2130b01030e0d0f051e0a0c120302030402061801020a050109030e040c02162d0e07030c180e1b030103261e13030203010c030515063108070308 63
    0x1d012a070669070a8a0143c010f12100184075902c61000d000c0c1044905015450740e400000c218004011100c450a203041c0008041300701d0380c4c01000022005100f408400600707841400d08405034001640c00940004040c441c06c00305014880c2c3c1c001c0643c0d010b10444140c41c4a07626014250f818030311007503001c1012040724080e1030403d4019403003051070038001868070703544040c09102c240c219881401200003400b080a2406800e2082c800c05030050070f000c48441035100c0820b54001103091301c191021a2800c218104000d010b48800c03003c14885009844205152180041125800030f03e201c5001e0300340c42545000a10744006540610f00545110365402c29405143c0074010f1000c1441d19840c0c8180844000301495407030318200032240300801c030703185d071510b41d02500c9941c035076000250300d54200200710a17420340c198443c0d8424030300c86600c00c244402036410b1204920407100303840801c0b2078401500465000c968020204254012078010555030f494403501c0c2094003a03042100c5508002500c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 604861115 1250 604859865 604859867
    0x4030326240303040315020703090308040803031017030a0f05040f12020405060409350d0f050604020418020f2a0d0e0d0f060f0f0207141203040b0c040302130b01 71
    0x400701000000c2d00114942030a5803100d0400c401800c1d400381c00c0e15000551001054841c145104c000c42d4060122515540c4074010340d42c50390000c881b8100500c190382070018040503000340810300785042201540ca01500b140f030449031040e000040e002400b104000018a024442548400034182c0c140708000c0700798588104015124064012441103040c40543c80104a00c0322140c0c48030410001d0b081c0340304100c94900c0035003908400031900d241c1000300b0b10302c280ea10540c00c10b5203a8030aa07203042085980d943c081004a01070390140c00718061000c008060056100d90042070202400501581000043d00005ca500c0609008040c84521150321401300b25108004240d600043c506003581d580701c111003c00e01c0303078901c01400b0b41402c1e0540204070074844580d0240c142c0038104ca000b400b01115a610341c00c007952043c54101c94072040c400c03d1658486000c10340c28001082075000c3c510315105c0d610303401519440682780701064141000004016525490158039866881401042c1c101700302c80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 604862365 1250 604861115 604861171
    0x7051b120702120d1403070c051002040509071103031f0f1401020d0c080304030806121005161809050c12010602011a060a02070e13020411120702030c0304030326 71
    0x101080c15134045032240010036004019201c191000c190060340300c0c0d842c07541c00c841d804440200580b16010320000510b0110b055001441520000e540764402a15150411070707001d14001043c1c8510f820500c0421282e100c0c1c040c10054040c200e0841c4e003006a00c5155845d0701414560100e81c2c61159104d4000e203035601400302c0c80d8000d100e0304028030401c02c151907a46907032200604c004d003049103100c00240340d0394813800d09815858100084407403d0200c2e03074002000b854152280c3c0000d15103400c06500c0a80f040704460003401039051a410381c0342c5481e2400000d4000600342c402000c1c0284001d0b0408081034905500804c4141d00105100c0b011101b1155540108450729018890030410b5100e281c0d0000780031812514090f100c002c46688400c6a052034010441c0000e40c4217040000220f0046c828101801e046080d8804018441e12810016a0340f8800d10741c4004090b0010300c01013000c68002c56041324003d0304a01428046079121244540031a030459910101140c119007810001803504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 604863615 1250 604862365 604862389
    0xa03060b0304050309060d020403210e0f010504090c0507200901150c020d0204060807030b041505010518040213020406231c020d0e010905030c010e0606010807051b120702 75
    0x300a207490750820381c4550303449118003143c0c0360145100041c4540c0640142c0c4c11140115008031082d03002840c00892024600a01228507000400c411034800c140c1ca090400c04152000c161032306890035241440d1b0030058130040700c100d000d000c024888a004544500510301040c840c105c0d04203503001501080210001e010381008280031081e82c40c00d9860b82e0481c030406080e50b01116400708000040c80068080e2000b070b080150640140c2e40008100603041c85000c0c012485541003c0c0300074000700e00c600444500b48a42648581c0e4500003028840451007180c7e00140050540c459440d0101c42e69420b90340141d100c40c0010315207140c80354292840fa2200307024030f109000910f00c4d1003010503080f103185100380c2c844800640c0c00a002c0c00d900a095214607100c40c80c0f60b000784240307685070070456220381280d08200c03115401d00c0305803981c12b40041082e51007030f54140c44018068071607581c12a0704ae003003503501d034903079281c4025592f1082c0c004214003c4d02882e40d1100f9680d480451040c02000b131604 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 604864865 1250 604863615 604863629
    0x1f3b0f011d0718030c08030918040c0302100c06140105030c0a0305100c050d0e07050117010e04080c0a0605010803040929010e010c0c090603230c040f1409030a0306 72
    0x300d165049128281000541142c194a010741c5481c3c0c2c241c1040250403c0c40e03000500e1540c2c0c4141c0090300c60004009440400c108917100c40c50002c4d00c041c000d40b01c080444008000e40340f0326409000500d48822451014001403800c010340c1039103540c0e40c0040740d220340e164151442d480c00041095140400c10041c040d40251800010586175584055941c00e803003804180c0d05843d410040541d40c410000e6400200045200380070013409120385039180da1041c043c1c2130016440003d248000704105030300f0382c121012102003043c1e5642e00d4030303107041c1500304c031440c03030440e0007950038050205016004d00c6029080d400007440c1d84514200041d8111a100012000103c034480410010030f0214140d60190001c00e091030408940032400403140503c01c0c5100034410000480302049000b1164450740035244640c404040e03030034110000104052802c00c09a1950340510110441400c15811900d42880385500120b00703001c141c02c22002c118401c442400c0c41d42d0010407a01c0e8070b0340c0d1601501e0004e05038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 604866115 1250 604864865 604864889
    0x115080102070b180f07150206010503120409020310080a060c0e010309020108060f03030f1c0c0e2103130305061501032f04050603090a0204051f3b0f01 67
    0xd26035071030f50340c0c00f00100321404a00c0020019803900c1403e2004105030714850003603030040b03500c440b0780d16000c2c1d4100c0d20000043c03092100210b0355050028180e84032000f4080707028103041c545080c800c0603500c01010200340c60341c00c40700007501072400c0202c541d000b40302c0c2001140048c0b8020380103122019907044281018206811100540d0f0003101c00b540050040d50700c01580100400820300d14403800d01c42c282c107064000342c181040c001d1b141c408021400701c90414000105100c004031072031412002510b500c038000041e208624a000000d100b24115a0b50503281803020160b850004164279034402d840d140c00c00c40403c41c00c40030386d56211030715031003d09040014008040c029540d40202e80818165035500c400c00b5003d003030500050b0b500401e40242126a00e02c3c050182035200c00d05c50b1001c074000d03820017020a05c4003541601507520790110898584249103030030b80d501800440b80d405c0160140d2a8900d00034688403805442c0481c0100a804620034104801c101a8204050740044a6244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 604867365 1250 604866115 604866127
    0x30405060c13090e1222050105030411010c030c0203010609060e0a05091c1812020103140f070f031506030212070c020d02010507140f0d0f0c050703061e0203090115080102 75
    0x81c904035200a8034685000001d002145440c01d61400c8172040c1000c007040c0303004c11b2510441d01c60403802c1c282800051801c681296460303005458600080d28010310560240700c032a00c065116060740580d482c040d281c4a4400c92150f000b080c00c440054100009007500ca11040c041d030100c440350160001100b0004026a21b40404956110090550150025032090f4100809280704140300c0002250b640d0a10314215a20501c00c00d9003c1102c404a0110b410312010814a03141d07604a00d1159208a401504aa42d552811900158480d50a100307050fa220a95641d01a80041000c050022a03e00603601c5000031007080900c0c1000304442c0801002580d050010384403880c3e07440540354203081c1162909542d01d849001d8175010507165034244501d100a000020000440c03182d02880e6849440c000001000c044400c502e6080c0d01070440d41c000c410820010381d255020a040c5904100c0400d102d2014081e9031060fa4001c2e41c08002aa454206580b1082640c2c1c07082c100500c402d01c02140360407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 604868615 1250 604867365 604867387
    0x18071806090e0609060d05070602010506120109111212120402190b0403170408102a05041502010209030708070906060302030f1303031e062103020703080901020120030405060c 77
    0xb42c00818041c081c000e07100c007198440d140c1c2400b112a190b4001e040d178400035202c5a00900802045550900c10016108241d4000106105180c6805d4101016400d042c0203038090007080d00c043d540000451092001802c84c1e00d81c0c09010f8000d0101102c04a10682050300401061400c5030000252035048540704000081e0107008403022254002c50382840e808a1441e14141e6008540c80315003180101171106000d050306901003512440311011601416181c5034110141140c40924400442c03000c01c014810303000700154050304218039200140c507041d20351021a0502400d940403401d20b62183c1401c0c040c880c510300600b03025101501d030450441c074105520203d8940080d0600170600103140d150740500d03209412166541055556070b43c501c04443d10401e00a1840744188140c080a4840710407110303415064a40d8400d80680c01044600d0071601c41d60555032080717003954190365030f814014100a10b0305452481420b41e0700001612441d0a080c07030383c00d040d0014692a50300c5401c2000ea01c3c82 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 604869865 1250 604868615 604868639
    0x120a140706170703050c13030503091519050919030503070c0b18040e10061404110901021e1501090204090c090320040204030c0e01030507121a04021807180609 70
    0x45803901d40845c16448050401d00d0911802d000b9051030f503034214000c0244240000100802b4a06540103c170304591104420fa1318020400e07000b07140301c800041c1500851156000d0b082802c4000c09807103001312600b0f40301211820b281e00480d83c0c2d80004c600d203000d01c101404240c1c01080192096890101200504800b000c00700301d102c0d21859540b92964440c1e0740400c15a100c1800540341000699100c80f2081c4d00c42c40c4980149200c0da050208c03800c440710703150041e21038010042c1c00810014402c06102032441e08520f441040b00d100380410034805014000c0454002d10044000580d43c9040c072a00500b51440309031041d0500a82d00d0302000050386d004141400c40050303041d003111451072000010040d11460340094900d07441d80b4004a00500f1030240365049903ca042140c1ea6035a8881c140000c02401c0740e400340c094100741c102100041c0441c0c124603072040c401490511001103000144035a0071094401d8800109611100032035881c601c680b40d00a040c0ca4101402100d20380b80c0c005e003030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 604871115 1250 604869865 604869871
    0x304080607110a060f0e0c0429150d092d03031a0301060b0a0e012604031106040b07020706210c020a0f1202011d100b120a14070617 58
    0x10080007090081119905000301c20805030f20000030301441c1006032500d0040e0900c03106c100032900400180c00d806140510401814510ba4007082484021616200c2c0144941d40c90003500080450081c0c48005500c10040501203081e2200203401401c90500c485525545d1528032040707131003845960104000314189040c050f0341881c0105000400e605c040400c890260501ea07050744c00c0490202c1c6840e0008050152103040307540384001103880c81300442d40d9010609440e244102c210b0810100c07410400c460550290107420403100010088003114030b1304404039801e0707400340001410b000c00941e0600100000b0010351818550107a60b000400d02030302d003118103a10313446680d194400b482900a110002c61940c0040d0324418200766824110192145c6200c400015442c2c292404151424111810018030300103000b0146a100c81304c010006005000f21305038010000301d1b00c509030320030810130400428495003080f8000c18a5a10840c40c1910540007081030018284031903102a20728510568 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 604872365 1250 604871115 604871117
    0x5010303050d0b0109153606030c031401171516110a0206070302100b0303040b070803060a0315061802030403080f19050c0405100e031f0e0714120304080607 69
    0xf580f5106040144c5007171646a02c8905003044030b000350045590007080c0b440201c0d0641101e0340001c070704a00d00c0d110070444028485503181076180203101d03451083e4001c1414480d01d00b40084c00d121382d0402141c0d0014268840740740390b038800c1c9903d00e03400740074031096401042810451030b141c2070800c031103c146042c04164400700b1507985049a07055204004000d041c42d00039081c10b0b980c2c061410029120700100540030380702c6040c5100383c419418004211002c4401c4030408905266a41d40c428203181e00240110354040200c1c540400403c07900315552036521180c00000550620f007441c4102e03001200011101c0301303441070040101094000c110203502020307581d074082007541c0d0011104000045c080c1071428640c40c1108203e0402d69100c02001030315002c40d40c0a40f024201c01003115118a172910f2030790984c218002d00841d5601842200c681b1034612040460510030000001d8039201d0107a01822800e008450007486030700340070500120004030040910300d0141004a404d58800000c1e01109c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 604873615 1250 604872365 604872371
    0x11409040c09020d0b040908071e0510050405010e010501140a0b0306060405090c1c020310080610060807051e0d0513050a11040f0510060905060c120c011401080a1505010303050d 78
    0x203803213603640d58003032102001c00500800070f9611500b40001c544d04080c2044500c5000c41c0c100c04144021240c0500007181d21600410703803a131000d0540c40c090840034000300c0c1e503503480382801c0b0049102030040034007806180242108403c6580304001a01d10b595012034241c2400b003080c0038198032050111003d4420640e03850b0b0960700c841c0001509445001001002c04540303182d0481ca14041d030700258014220724440555407602ca0f094a0345648054801060300c105140c010880e541c003903400c0301d90090321420024100407800c614600e000040d01a00c0c403085800140c407044100082c8140c076084a48441a0900000640d403019651907601c02c0190402420400003541580c440d040304407404c7d41e1407020b000505101b11011441c6000d0300440d000303d103500d4400305560411505441043d50120003d04070f030501f920b40d942d0300e68020200301d07400f952101c8801450086400e0500d0003410f2540c0103001560740c90400c60322885900c040300314a41d08100040001c20384c001d082c0d41038002400000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 604874865 1250 604873615 604873627
    0x30318030702180a0510080a1112160905280504080d020f0706060911040302010e031e1c0e0a1e030b0114040e0109031704052103011409040c0902 64
    0x1080c55801464030095120070346682c0d140c0c03d0289004841e000e001d902c00d09001c3c035204c0f41c0c404680056075004a00260740018818070105285c6905812170f81d0b03018262180c2071029610681c104010400103800c0a81c0d01e4070304212190301441403980c000d43e5003010110744c800542039101441610a100007c650712080420300b8080c09204441094039420000c560303031a0952001007003504100003d0f90854540f039400216403e04c0e000e8500c2044040d807085282500f940d0065aa0f2554840000c0e0140300f0000c1500802c54402078201d01c4010303001c01040c0c03c1d40d0b41c29041d400c1d00800440c8000b08800c0d0500c0c8405625454011020f1310304100a001c54540100c07401d80000d60140d1002d00801540e10000411240d1704480040c007240c240c4051101c2203150102c5400ea80d1482d10080000b05103950222200096201158129108105564080324091000a0881689071080302c1f9100c0000c010040c2007031942d140354840c0d5041d52810600d140544840744051a85c0c825015044c0d000101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 604876115 1250 604874865 604874911
    0x70b040302190902070f110904080412050304030b070305011a0f07061d0d030506130204031106030711010603050606091e0a021b010f050703060b070506130804032003060106050c0303 80
    0x12680140c42d0f212811916108142801d1240590088095880d404040c03a0f422042c185100c1891107583c01c0b4415a02d02407402d0001c980042d25000152081d0100f48808030020704a0a00d6a000d01450340d404a01541072401c900c0b09040c4880c405040428104044014240c1060554150710b80120b000101c42c80b1010b00c0001c00440c00d9500b1502d030103000300d0f00104941541c801800380206484420803100307002c05580407841640000341000c054105404103c0c64000020f40d40a0482c1c41c05080a4410780505425520150421600c542000040069506184042c03990040640d0603146042e81c8622032410307066405803250106940000d0200103900404a480e005003003454000c1218811404841e0020318064800c00006420704000260b8200030380c040d604895009400f4180a0312100d081e040d13441500d03c0119a40b03942844000045075580c0e03400c07a42424054400000041a8800c05040c1381d016045070003400b0040c8442c04c0208070000070340e1390000031001d401c1801521804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 604877365 1250 604876115 604876159
    0x1e080d021b042003040f0606050109081023010803030406050c0702091b09030d031a030a120c0c05040c0509040c02190b0405070807120615120809040f020301081e070b040302 76
    0x9001c01c441c0a001085c0020401c910f4403550f9900d014640c1004026101c400440f0803010b00d02c10300e12182d200b80204076011000b6401800c0c007503289004942e071001308240340c02c80c200c026400341c24107404c00301c1004140700d51801000d03407000c6c04c001524a04915a80004c1e04c007500076003003000e60111114803411000c080c40446030240c0004048030084c03000c01030010b02400000003850300b140e040500d212171500340052010b1015612118440112480780d0040f0341100814130141c50410624030300044a864901c01c00030440d0f102e0356050396503c8543d050009803501030a13441c045500070f107402414415007110003180164071150345e040075265030818624050a940010f0070764000d004d00080c3c07944103c11420200f42c4901402e01c05000e0404030300d490348039984903014030b5030308405680300000c0c007900007005104002000020f2a0421201100481c1c100340c11400e00e40c1e125696015101880030032007441d10040c00021f1900c2c0d41030249050b2203026502c8000d0240c1031268403d034030291300d18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 604878615 1250 604877365 604877411
    0xa090c051504031e120807090306020414190b030a020a0e041b02100207080d050703020d090b061206040c0302040e0f0604050703030f0201331e080d021b04 68
    0x516068008000c01d94001003035210384400c0b40c100046404072a01c02d40128110360507140c011600c8010f00c4400360081d11a25030081840040004e6004007000080061010300058043c190305801300f0344c0e1540600c0346040d20700d0844080f100510350104620011007045030f5006000030070160315460410020b03981d00d190300725901d500074108880e03070101506041c01070600d20a01c2d4210350640045800c000224810f002000c0c08004080214148844c815001160001c045280051801e200000760b8421188060b400311041410380c01800054a0801280c041c14101107011740114103050b541c03190711181c10311000340599140e840d079207500b0f5014041c3e0071250f03040000f82d642900c1d2078a019521401c013400100d000c00c071201000001e131441441100c584214082a6004e20b9054500511103807003a86803059200d4000d68001c1044c03606c140c224281030324450680c802c000c2c108404642031900300e041c41c00031940003441c07030480c40c11003680418080c002607031300003100c2da4090310760701e6030750900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 604879865 1250 604878615 604878619
    0x3040e0a020a020d1404350c090601090501090e040f0c06081e041a06041506020606040c02031e090409020406170601060801050a27060807080f01060e0a090c05 70
    0x1510821031040510380040550b001e1540c00d641415965030b01c143d41401050b40252001481800144580c010003110550a80c3c0995801044040d00103240c0581d060742e8000802c040d0080901344103141403642010760800b41c03d01388080b081c2c0c180340000b0418042d920684405c0c0d01c0400c041428071106450481125411031070001140b41c541d68003403d16101900d0300c00041e904401110b51344038050300803601485d8801c0441c103010014a032a500d010b4006411280c0c000d54400680e501400d03460607110082510350080c16036032030003408000445400d0a40f035025034108000c4116004034410303130b100c06000e03240b104644420002000c60002c080310a4003d420924010020915140140b8102c0004d1441b01c101c41d42aa01d41c0005c80d0107540a1051507008410b9600c18803002414284898586041c2054400d8944403d17a2503001d44400d0f41c07100b0011780020200707201d070030814404c000e507465003c0c000380f06103403500d01c1c12440207100502c00703000f40b650f440c200e40401103403e540800070480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 604881115 1250 604879865 604879889
    0xb1f0f2304170705010e090105091e130b010e04210207050607030305011e03110607060f051806010807050a0302041805072d0b030c2a0106150e0f04020c0304 69
    0x114040300000680c0b1029600b4284640b45000900b903214100b4500c4c1510094513603059640b0784418002e05401c00340440b0040d41f081c002e804da05c051109600d0f4450310130552040a103030024245a282d40f007040e00b02c0c034942c000c0c8400f003102240005181440340095010300006010485204a082008a8001e1a40b241c000204401819495040b072030581b1001030640c41c8041041041c4800c260303c5110080c0010045511701005160160142c840c2c980100d002048500500d4519402c42da403c980401d40003410a08031134400b04200180e501410300ba41c01022f1180c00d042c001001c614184c44024411922031481000c506000403c0c4182c960388a4103e400080e100c03034802c0c920380c2070040c0002c100c043d4036041e10300c0c6080d400c5d402011078030751541c43c0f4030303545489000e62a02e83c801c20490a445c10440d44035002c43d1000d204110307480940c6000000e00b01d007800b000710003c483c881407000410402c0c80118010780d031200d88441e1030050840b4011384da4850299041d066005a074070010031288 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 604882365 1250 604881115 604881119
    0xb030105101a0403142d07211406090613030816050c0f06041205070b1b0408151603060806060909250e0702061003060903020309130b1f0f2304 63
    0x1200181b840305400d03c1034921881220813400401c0c49200c81c05551219074081d03401000381c5410004080500714560700710302d40f090140d44840342140407072807039003203d54030460401984210a006003504040740110000514105403001405c0c0c0708060800344c005a003546003605402c4c040c5e4210307500c800c0c200b400d035240a400303402c0d00b5072650030440e0140c0300300100907941d0300300e0b6108030115400e5030f40c807411510990b00d4407400d080950f41140509071490108110109104004109015503400720746994100d620300400707812240b88101080000b49424607105000b101c40100d2040d0340803405403101c100507603405000614040480103508840b05c120030b00d07802580d130550b0098041d10040c8041e04002d8440703a03001c030380d20541216198040510b0399006d02c001070583d0072924070075000b40f0480782000f00d200006105241e81100442e441d5940d08914034035401c1c05030340302103503010030041d081400c00c550344060002000390014a0400c0503618803c24031442505403c03440c0f1240c100700e0341e1150f07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 604883615 1250 604882365 604882403
    0x1b0b070e0306060108011d0a090c080d091d06060d15081623010c0f02060d05060f040504031b050a050307080c10050103021c02310b030105101a0403 65
    0x1103880004140203000305400203c1c594002c2c100349048400c0303180c18843c01c03410200080083d5801401c4844040e03180c100f4500410b00c02e00200c03000d044200e000d0502e075419100e001c0c0c24084203600400551909810402003840950b0400e80d02c044286ca810755680303403101ca0500186814451026520b0302a000841d100c90000340e40110000482c890391a01910348000c4900545081c43c0510509140d60011031907511509560070141d201c0d041455a18416600091081c1c0000b16682040c1381d840003040742c6460000c480c0074003194190750400580c24280c50042810100c044000c601c0c2881c9a00001080010444255250f4024007526200d94561600809a50126500018522400c1010030420300d49200d00b07070481c2c0d40102181081039000071000c0e42d42d4659001680d0140d25603140e0700b0150080c20b40f0315200012458035a0000e0010702007002107900c281c4165000340c4c5403d00304017540c40341e44688804c4c0c80d0702c405241c4012004005103d070034032440d04010208024514455165 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 604884865 1250 604883615 604883627
    0x204021207210501050d110619120b040e0a020f15030c181207060819150509070903020a0b1803030a0201020a03181203053d1a0a1b0b07 60
    0x60907200700042e4031480e009040d101680c800303024042c0c0c866501907004001406d612501484030802400c00c50602c1020100c8982d00c0300c0c1031343e0314008500900c50b5143c903000f01d4031498131540300c220740401081c000d0300b503a96542c1868500080c06005100300c0c140580e51a5440542d104080c421003954034a860302101c03d468120440440720072004030542602840c005800c0489081290014842e052130401e0850341c0800141205c1d1010a44e0840c44490403946d01131030f60100e01015400c408549054140114484001c10704420807180403410310042e03460312080401c0380d01007580c0759110000101c0022086030204003039a40751200044032008107030190003820990145842c1001048030712020040841e01d4501c00a05240341075101c98071260103a40700542200495401e0304441461301e00c030b419403503028010589040400c1c3c0810001c50340303501d00031018083c0c00d520f0400300d1800100100050040c02d40e0b40e014081040032840d16182e2100351002d031107800241d0300d503072803c00a1002d011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 604886115 1250 604884865 604884887
    0x30b0a0315110703050d09020f04110913050c040b0f0f1204051c050a1d060c1005090703030509270c040e0603010c0801060f0203070206030703360f0204021207 70
    0x28290420001c001c0b454000302c20349018035015281d20f40b81001755502c004c000c2c055003a04070b9020041e201c3c041e90a403264411541200c10a413510740e92042c003c1c04001151780c0c0854842c0407a42003134100081c3c4c0840e003041c1c4044450355007045881da80300101c044214040c14000449061010400109141079105614065400b520540d42c10038540c410140000b01c078410108040b4000300b11200900303104a03601b05842000070307010b003007803c0504002b07400c6903c624080015603000c078680c0486040c082c46010340007100e140080620768a135a4000c6d205d40264490640f180000040d0103031900300c1c804a199a10414484241d01c40c80c00600d00030590308580102ca011440420019409080507c01c0c0603121040b6221a80981e01e0660101c500d00340d00c640754403c40c0810300494005849203009540510001d860200b108030b40d0480c0c0c40180d007402c23045419103960000302001001549601420303203d80081031440041035034004038000c0d110380580114000d81e241c0400034807503881490036a0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 604887365 1250 604886115 604886153
    0x1b0a0903170a0f0302181c0c0e0601030f0e06010b0c1002032401231c2c072d080d080108010c0c150f09020907080105240a0e01030b0a03 60
    0x10010f008504030124002e90040082d4030700640c1000c4410f1074a49542010380007422205049101e1a41d40c042d42500c1035032004810380c580c2c0342840855a0103016400041e80082c0041244089014546640c0e01e018458000585000106901d07014800e11a6202084062406669a007840d1101d42c80011010500d014003041510000f401913100300c01b60ba940042101c1c00311b1114070780c2d030f903021510382c40001d20b03c00203c0309044020b00400c09020701202428211207844072004a806402c01500c0b02d620340010f1904009414005541c3e070b154501e8164914002103554034401071200c0c1d1400c1a960000d060394400c0d100c01310903d03503009800c00d040e1907010001f4803010200501c10343d00b11404040c028400d4540c1004019180c216034002c4d40349102170000402c900515401140020074140e41a000281c0c0c0350300144103c2c14504064520500c0c0400c080f8000007840441b1081070081c0c1140e00c0821010304858040e03603200c0e40100701440c0004250304901540c034030b0145403d00700011030301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 604888615 1250 604887365 604887377
    0x804060c030e0303041101030204090f020d0c030c020307060b0a030f2f030a0b0408041e060f1e20010c020d0e120d0f17040803010503151b0a0903170a 66
    0x10305118440d010b82c0d070000341c0c000300643c19525960340380042c4000066445040603400d0000044030b04807809441c15810040e800140d8a0b05041c0158041e910300c840000d0505007003402c1c0c0a110b80e400011101110740000700040c100d81d0030000562480120380c070140c01c0c0c083c5200c016083c0442e1a400419911107840411082c5650108414132500501e1400e580754001d0300001c808603c1032084554400e105510881c981516280340032480c0340c00d441e0b045c1102e19480001d101403034005c2c00c00c0c2a003070014107040c000c240320480e648080b0700c1503550a80821100101c2d410821501c80400c01521702020002d10200110b2000290713252180c2003100b0003e800c0824036801801d056a20f00c00601c2110080c0c4a0000060b270309441800d400d840a9080150300c200111f108109502c0541c000c5d0321407054280c0d01e500d88000c051420720341d02100506a4161402d104402e203d1705100c402482c640d014980e160070400500f652003040c40e1740043d04000c4100c00c55100192401d00501290101d03440701 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 604889865 1250 604888615 604888631
    0x50102190807120b011407030210020a03200906030c0d0e0604061a0d081e0d0212060406091a040f151419030c06031a040216030e03121902031603080406 67
    0x68030a4404c1546400e022a410112010620300c00d40020110140030f8011035060315440b41070a0100c0c0c1c0064100000203a5603080301820700d002e08440c102c5035010b59281e5041060060010300c032072201505040140e8000219203c044129411940062000101341c5095140c54100b05010708078400c80d440c44030010b8003511203035140c40840f0901082d0003403060b90422213004440084010707081d040c24001c110030301400f0000f20050005200b210208414450302c1d003070003000d11094503030305d03000103041c0c1d4201007000b503510318901003044c3d207100308540c08900340800384820802050100d40c6a030ae10705e00340c00c0200700c3c880b2039040c03411043c0c800d4502c0014000102c694842d5100d90b800b00402d50f1030845010000c02e031003501f02c14050a22242c02180c031440c4900010700301e0b404803000895410b00f2061071301c203060f0846103629207880e007a0050f001041c000d40d080780451040b10002d08200071f40d19281602d43e07108009071100980341c000c84a0b006c28190801800c0b4650071201111040e040c6590 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 604891115 1250 604889865 604889897
    0x1e0301060b04061b0516030311060c03090a060c090f030b091b090106030b0a0e07030b01020601091b05030c1303210f09030803190f0e010b0609060301050d050102190807 74
    0x2220200ea44544e5102186084100001c201c1c00184d4802d07159445400c0790325800d2480301c450340c4001c40c4203450394000241661070340c0b802c200c0c1c010721a020510007441040104940810f40c1044254044030004010941d04000c0d80e04624075004070114a1790034101100304400d45001c2809050305200300e031202108100c0070a000c018640130705400240701c100400246002e41c0001d070600c400103068010594a521545144401c200c40101c00070341c55005840e001d5805202050140144000c10f000c036460b601c515444c03002a03088800c1c1040030000004d0360141803c000d81e41501c9008041c0f1400680d60b0030248070031001101981341d00c6490340039418100c1d001d0415500181a03503200c0014a626644036034a0a8100522a8481044078403091502904510031019104003140300010110681040a130858159060715802a403042107046440d0b662002a2411071f101182c1d2040e00b041246055406402441d04620200321040b9408015541010b0078610540042c0d90381b480c0140e040170 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 604892365 1250 604891115 604891117
    0x909050c060901302c0708071502030f070503040608070e150f190305070905030105090303131707030306140d03120506042405040501080d090b181e0301060b 69
    0x2508078040344800c0b040b0080004d12820256000520094050f40710726108810000e50701c0d48030710340d50010803000850200100d41c2c54038a03954080c0c0402070060f5070a0400156841041d4094481c0800500d03140540c910300c00c02c22201e0f05016124881e03102d01113460501e6483d00305001d92000303d103806000072001e034416190001a4140141005122890742d070707001c4180d1340f0051490002c4e180070000703021304c220b600c461030005082c640e5002801e0316000c140104240e4143d080ad0f846641040203000780108004140c0e900b00e250864410b50f00c00803843c2c51010391316081103074407954401144171000c0c942c05512640443d112031f4544800342020100304a0064000000180400d0b172405c00f00e01c40102d82d13400194000409000064444a16010f2820043c04039660500151b000081130015042a018150041c08288028070041002802c00303040c03403086c2d00619071003c81c0071600784d80303000c2c212024680111015000540400d00702d440e100040b0300e4426000c0c003d6080c20000984010450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 604893615 1250 604892365 604892377
    0x71a04031a070c0312092003061e040b06010e09010605090f0a180504030918050103060c020102030f16020307060203011815050d030e0604050901120312092a0b040909050c06 76
    0x80c2c1d0fa80800855560155441100030800c0481c1c10360b21019800058002080d9243c1d440e0000050300415101d001010328001008103503480c154842e040f0755500024504100341c2003640b00301050702a98030440100c545603400110180d100030500000240d03660030100030100101d09070395183c940001d0b101840002c06117440703210140903401785040d20b6081c040d07100f01d070071503c0f0340f6103a10403580d20400389000341186040c080b07007540c2e614010410802240328006840c440e60000394254600b00304284207880000b000c1890300c00a01300f003643c01d644240211108030f5071041c011512941c460081914240c400300855034a82e10304840c3c1b244105141c502d0504440d40101a03108140c011758040300c0d150340302c030100758100c681400007040543d104c00c0c0c02070107420403003a0215909514100241406000200408940c2c0b4200e490400300750941c50f44040c091541c03450341008044000c21040321035056000102c202d00116021409111541102005500590442d401908000c0c10450a8440c84c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 604894865 1250 604893615 604893617
    0xc030a0b010e0c0a141b100b0405061e060705030c151501110c010507020109080a030206040201170103020307122a0504060b040b030601111533090f09071a04031a07 72
    0x10b04a245100d105e100e0007040d20041c0b24100306510b01543c02520303e03141c00c0c0800c00c6907090315070b011981c0d0350030301707202e0207900c80801c0b9501130701d514160103003280c403107110540ea0780560070000e0800140f00c810400c40e1354284070003044603803d64407151400000c030303005da40c403014840c0029201c1400d503110710070940310451808050040c45000c5801034032207612402040b03050080c0700d48005980101440552400c0b07020f50098081460244001805402181d08000d0207501280040c07026032000180402a56000206440c411046043c0418080043d1031401050a003000c3c0146100e504072210b01d045503c191000e08c9003d403240380300001ca025030700500010240c28000a09150301c642c1e500d07106414201c0c10307614800b8060704e000c4961308007140c001c034000c0d003001c11242254500c84038079104144c100c8980d921012079400007070b100304409000910349d01100c0010031001803081c4013040042a645102c0000c1c0b441211181d100ea03006032109480c441d482e450361034040e10b00300c81c0e040d11640301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 604896115 1250 604894865 604894877
    0xc051e010f030c0903060f060602010506100804150f0914120903060c2d04080d08070c03030e03040b04060215060102010c142506020c0f0115030605090c030a0b010e0c0a 74
    0x301d41c070102c004106000404042011120000000c16601d12462415000052000c10102d081400103425903401600701401038020720204200141d0090b05d06412591003c1c04040d003124035000000500310751064208074500d02000d03081081103095480303d400000109840380e0002c0380d444135400b03028601038681c05402030000160303085681c400a00160014581c0d05064803280d0b80242c500d2210310290700d8401c100081c050001960800c610b003c2c800091030030080c00c1c9010341004101548104000303080c10748030290003d1040c0c061041c0c034040d002803001c0076129903540708001d5440c0e08442500740c401800c000400e000394418001c0074035505c604c1e00d030f040f41102662603400c1e4540c420326900710000c030504030803180003030001c0d2413040c468010500503807203090b0442054140f810000e030300c00c0207a1400300c5a12080d102420710000312138110b40001039540d00d03219041d007451713020b18402d036150051072504810007001a4105c0d060381e078030980b6809a945c94100c40b00f07551140b241d40d90003003a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 604897365 1250 604896115 604896137
    0x5072301030f0e2a061317150c0a090b03010803040e090106050301060b0a110f1209040f0207030827120d1409071503110a0e1c0c051e01 60
    0x10081e04050401c0848280020395580c0c000002420854000e0507a68030700041c001c0c1e1134081898440401103000c04031030044c9814000d04180e42c0c1c1d0f07440c0748561118540069144d40752000140282000c03407a003c860004a407034a14050b210f158042075003000401c581441c04181c401180c07080c2ca040e240b5000086141a06000c2c0c55406400001c019584070f640b16840410141c500b8080c05000b03055a01d80d05e9210304415901070501040503e08100c04d5115a814103c5e40c4000500d01e070480711003050071980c40141c45e0209018202c40c01600d443c10f40005009002c0560108480d84515114180c1c9201012881c5085021300d24084464001d50300106045412000d2603008150b6401202800a070a1416800e00383c2000c034210340480d0613030010b8104001301813076030104a034000c2c05c6240c1007009a004404c010b1281c013981c0903044c104004030598004d0358641061415075110007070b170840302810862604840300c12060003031900030000c1114042d00038130b1201100449400507192411814 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 604898615 1250 604897365 604897367
    0x307050304060e120d08011a0a0c0b0618091014010b0702130f0e0a03020106050a0605030c0a0207050310090317071209060b0d03080f011707061b0606080a05072301 72
    0x20400400480e44138010f5030b0141001d507020006101e1004054851905030341c0340003a0752404002c2c0590680001c01e0800085030b03855801a0000300b200d6100a04144c691211000308003074245070080c0c1c0500c11000020301005040010314242c690f40c40e11014401c902500c0d0350300c805008203101d040401c2c07106101c80401494030403c420461403a502d80055250210481d01c4196a2419040c514030b801c108415000d065080c01801c002c0c2809a410180381494600010324910000300042c500c0017011999180303c40c400d01105002307000c000c086540103020084c03810018041c0e102c044000c940c1e03181d10100590b941d15240c51144140751243c00b07004a059003a4006000000c9040b9520b9546598000c030b5070f920b11003440d520600a5031481c0b0140342c440c1c411880700754181c00001d6250702128a180000e100081d07410103550032807030822401c1e03510f0041d00910f030b0054480207018a05103070001c11100300004003101902c0c01a01210401581e48040c15035551a9012441022442907207084a035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 604899865 1250 604898615 604898627
    0x30b0f09030702280b0307120209120d050a17060d060b150a11060f0417071b0b0a0e0a050102120903190f020a090b1f0c051002030106030e030705030406 67
    0x4484500141c03480c101480d0300168509072109040900b0220222960604800f00316503200907020306601c0e18514201044090500d6140c2d486181c500350300003038503404944400c1800c204a00d00001158400e01002c0c10150484c3c100500e12000160880182008804d109110502070130b0054411038400d0340030303180c0ca0050300007000c4c107541205002e0303800000602c0050003070804015070b5841060141c17070040c5080c20140007401d08a03203600c010342408041200c903c220000c00500d002026a25480d03031a28443d041205403a00032b82500d040b0001603140518401032030000c20341d603510320b4068411410040c240c250390160500580c000303900042185200801070100ca23000804540702c1042d403810454030f155200c0022a00002c455039101c0440c00d204911402401c040c8006001591001c8081903801440300030710030846c1c50309482d44d0545401b1703840b64101240c00c407040c0d0b200009642c44200107503200303210310300c0001e1424800158105010054814042c0d0001c050351801e03248c0081281c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 604901115 1250 604899865 604899871
    0x2041508031b0706082e0f08160305100e07030c0e16030515040507030213170f06010605160309210c0602070308040e0a060b12061c150e0c10020a0c050307030b0f 71
    0x41086c0c190641c03200c1500c0c004184005200b4004403654680c02c0030700706810405010f90000d2040c100c0101840000d030041880501c448840a00264a0826825140c941070300ba910140020228042c085456902c0701046481441d00901005078085030305403c80485034201e5030348404075528281c122251625801403500401d65240160808814049240200c05d5a0707000c000309010b01301001e240c0010510489009400a2024240b03a614141c0d018101d40320350801c40c0150f80c8100018010580030b1881200502030003100403c040c0040c1417610508140e107003042e180c00c40200b00000f1153720000d540b00907294440e206900705880c00d20103861515020300402c6074507444c0e04001c00e0080d5010041c05070341c210300c0440103070340c2030400074041d02c8100ca024007515141c3c80107010b03010031101550002c3e00d035aa80710000e040c0e044500030074102101d81503100d91048205e2a810411a4000790f43e01445002c1c0044501260762441095503440c0719100c010002e800010000c2c11010341c0100d0300354 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 604902365 1250 604901115 604901161
    0x3050a0c03092714010f0b0a1713050601050f1e1804050307200f010518041503172a0a0506010306021215030606040902041508031b070608 61
    0x41d402d500c0d0341c1410407020702209003c404809010110240d000c01d03014100c40c801000c0420311095041c03038456851417000b030091003141c0740700080c4039060b41d103d584004044901c01c2c120b0111340c10000c002100c810400c0c441a1018400c01001082c549040a481c2da0000e030300502054241c010a520229414659440540c1c0302c504039141c90000f800458035544181d1280e0003443c1d4804951426000c440e840c1910840f041c2501e031108045a21010b2107a424003800342403040e1940307441115016422212044581c0007030418442da010318030207035171100c1680e1003003000001c43c20750700700365501501507c000c00050a82c1e9034860010306e509290b81410185a030401d4a00751400e980354541350403400c7c0d0089455581c005402e01075610640307841da402001052103410201402400203a4030342001d00128880c80da00c2d017544045585076484622099003060b9807004040e0344401c400c5d00c81e044070202840314452100100414a03011a8560aa4041c0d884100c0d0341c2c1c482040d00c000841142d07003030803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 604903615 1250 604902365 604902377
    0xd09120c03020301050f061908151801110a09050603151c060c091511060417040317031b030408040905070c02041b0927090503040e0a050601030b0d03050a0c03 70
    0x101c00740e1802c0c081c0a00c141491400300011741059000d0020141e00c920856000c102003c006102d00080894407004104402001440c1c41e10b90160000c0e0070b601d010400c0d455586003032503500d82549044042c100806007a22034446607a559824450144400c591141c1d2003100402507000c10300e03110080400491a42650401c410481d40ea4201100c51454601020503c2c1d00740400c1100c20441d029101848035181030212459005201640d848001d44028200500e40d000705802c0030b400e20580d030086410400a6041243c403042c1c130006580f090758080d602101624181c1c0b202c0d5a407004070790182d9070081c1d02e2450686444880402010094040350070404625542005a41d59005000210b006035031120801d00580c14080e0003440c0c2a807090a0201c42d804910703840c02c0c01a0000d01903462650b001040901061600ca4114032458001e074400081542c00e21148a0055102c680300d40000e80342041140f96180c200400c0107010a00100000c41c100005c0540c01d00c43d001306540f40d0304c01c1c03e2103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 604904865 1250 604903615 604903619
    0xf030615040f06050403050d0306031a06041122050901060f11120c01050a0615020c090c0c070f081002070c030809010309060e0a030225210b010b0a020f0d09120c 71
    0x24000d001036a01c807400103032011030144244002884010948055812704001661650369143c0d4021409501080d101d01c00c40001074083d103444d04000c96203001c46a070560343c1c01d081030600d4129120760940600d03d00c0c1d8600040b03107605000e03800505844454031224075503ca420402c0300c0301400086222040d000e60200f00d42d100801c0c0c4090030391800c6010010416107171201c111000c07074040340d00140d00510340b802d0b014145500803d03200c072000e0302074542110540e50544407404910034019019003920640c840040c0e08200e038010754041e1404001a100f03409103185020059006404010b0002d2040356420000070300e5803002020b1980b41810042443c0115450b03140480f41341519440c8103411405035002050b9041c000210790641120f102a0412241a17012040442a000d420342070302c0300c0641c08444032030503184440703215030106420a030707503850b8130807010180c00c000c2c0c000b00507129180c8142002500030802d401000b41c1d540d81c001381030f843c150000e80da00b115403034240d07550a1030100c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 604906115 1250 604904865 604904879
    0x8090f06180705030616030b151902011e09171905220f08150f15120604290f160309060e011406150307050a090e090607020d03020f03061504 62
    0x66079102e07406c8011041c446140140010701582e0100403002c0c4201903081110f0082040c210030344079510109480c0403800c0c003070440140d004002c0a01c4100602985110b04450f000c03d540004090511600841c50030300050b07402c6000600440c400f0700b10b01c00c145e0081080302c41c800c1001d8020071640c00c641c1a02e0b20504258070512b5044c0e5004540a10f068080900100e5400c001e101c06514410b20040e0070b91a107082d00ca44ca000d005032598440c9040401d5640e841d83c0c036040c0b00d100e01c06144058503400e040515224000108100f526450030304144603500e080200755200b184180000c0280e5600c03652841440341d05054000030040515507607099103c0440c100d846001054815600000307511000d07a034504502110041c0983d20502040030781c000705c6080b01c2c0641303803c24801d0500d1034503201c8606003601d00000607080000e46441e080c041010070040041e956010f401c881d000d9440d00d84250310204c05074400c01c4010310402d50b04202107012410310512240175140c5440c00541859100c0f40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 604907365 1250 604906115 604906123
    0x19140427030c060b06090102030d1808040e090c04180f0503040801140609100f03030f050418090b15030a021306090e0a060b0d02130504020d020901060c0308090f0618070503 76
    0x34064000408000d9182e00300300c1c0d24400d1302c003200411503045042c2058100002d42c0c910441d00c0c9008030645900c801e41075024903c100c03c8140d54861507068540f9110020703540c8141d01207e401030544540e000c00240d9041c28418000400f108002084800c0d03201c0e20340348a102c01510301190f952008100c0018100002e06c20303000c2078241521103170505e0030008200059514060310040d4003090568041160b00a021421411070303606007024a40c40d084000c051703403280203651080e42201c00081c6040d29501c0107500c404100d51180c4188841038443c0d48042c0c0790318203100b400e06e070183c0c40100d0b0359000d8680307110300703c203011031107040030030100d17160400070041d00c41c2c5054000581d405595944100501e43c060422040d40640d9044c040b201d6a800103515072100d0303648502040e60324004a41952100c03981240741d580c000d041c20b0a1569078245c0103045014800d001d8001400c0003010504c407600200e03000c58500c0880c0d00800c25602c0300c42d5600291400a513503d001c0380f058030000516034130140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 604908615 1250 604907365 604907441
    0x5040312110c010b09010623160c1e050a050103111308010525020d12091202061b0306030a061d010c0e0109150212250f02191404 57
    0xe81c01c103031103600c086801429200c144080b10b01c5424150018803425900c91182101092040e072207070b500c1002101d80c040c084c0f0903042e25081d103640c1d00c4810760500844d0f02e15001155540c0c0345030580400a6207007000c003240c00b80201070f84001080010400e940c420740104400c0540500b00e0351619103860340819209410380d00c5052541d44410400200e12000407075006051008685070003c2005600000e498803200f034000d1090040f21401c10840180e950f000b00c44055026800c100001003050010355105011030344ca0250399040300010f610384500d0020342c1d000d040060024501d009541d513a16010b00800c040304091048244d11004480800b4000d0017514290798807010450040880010701080c0e03141c20101c2006561700d0800001980001d2035851040f56402c50794540700c010500b0b00c0449008030845c0d05c5101c02640c21010302080a040c0c0018920803540c42003544900e0400b580c500c1d041d80b26408002c1803500d94500a400d00d6044071040d60740301c95141201c4100c0d060a6201d0107418 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 604909865 1250 604908615 604908641
    0x901060f0320061329070b010f06050c0c0609060c070b0a1d1c03140408100c020c0a1205010b0a0b0c07080601050a032a08160f0308070605040312 64
    0x501d00d1203400c1c9044103103111054161a160b01c0e05454050100010800744220346031203070b809005401750410101007003d1012502201c80e500c1c115400e000311442400c0c0200b00310321089000002ea85402041110f91580300240030317102070481d40017000110b03001440702d241c11030410824101a9001807001d28094640360344075541764200381c0c0000b0400a100201e2100d424003000100d141d0340d0341d1140e40b904c00d040060120440180303d16081307507a07640700180c9140c40c28012801240e0080d001c981d628500e0b401801c00c01c290030000310201e0f951a824240700d134200701030302d00600000c91740c10007400c1814018000440c6200080011404082c0036a000303454085001c509484298018442d0300300401c060001425994140400600d80e0203941c40001d0050798903001a2800800c42c0b070254500fa20520001901e06641d0130b01c054484070790400c541c1c0d84a0303d52401007035a4000c5020b9000ba2a0419619818800d1a0360345d40c0003084084e20940a1004003400d03000188161702500780c0051391 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 604911115 1250 604909865 604909883
    0x506040b180405150d0303111801170c042306040e0403081b03160221030106080c0c060103020103091104060b0408100209100c020a170105190b0a0603050901060f03 72
    0x14201402100360448241d031046080c0018800741400c2d070502900700d40d0701100c01c5035080ca0640b40c2500104510810001c06060105081d420f01c1510010a0001102a00c60074003441c400294296030342000c840300e480c0c50700e041c8020705c99200d03205007014115645140e505003940546000441981055100e00070307440600d0204000c040c1d10000c41501710791801c00700381800304401172034079960100400d07040344000303001c2c48040340e00c0c801c104240244a580d0400d1f079000602944130700715903100740250004202040c0c04076084900d12012910030090030780c094056030742141c1c01180504080c040c15148000303e04494440c0d991144641401002403145550343d480c81c0041e41707401c1c00030f0740c501010924414844860745031210a403100710b0030790300d14080310000c03040d100141e60581990040b00f2000210302c00000c482005502103800b039914100c55075540464904040103a5910284503a00030360004410001140603070800f603003001001002140160300c40100d00010074039944140d60382c3c81 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 604912365 1250 604911115 604911127
    0x201111218031603110f09040b060102010507080906150d150f0e0f030301090f0204030515091606020d18051909051303080c0a0504030807080307030e070f0e0604060506040b 76
    0x101c0303162070000a50182d014028452a050b00c04940414621024161801041c000072203a41e0301a221103443c0001049074000d42442c0c24444826481241c920340590300c0c00c004034103007500550341d5a1042d18207800400d4160780e1580940407000d4000091500001e640316501c0001d902012440071114444c04002100d404030880c003c140c41012503007083c00d8001d0131352000c00140120849054441181c4085803810803081c4600c0240f05950015005000c1c62814501620b0b00c1ca50041c010036048003100c0052003141702d10350081e0403901c660005070344014004c1c5206402080e881010b501c0354400b0342e41ca10341e1100810310700b10746a00c2101d00940c84a905002400700392041d00e80001c00c4c00307125403900b68a681c0142196401401452058101040008040d4030500486003e10b502008a075140c034001c0c60501d0b0140c000f0354690010900302802e003501e00308002060000c65500d0400401c0c42407811040204520b4064015500140c84507000b03d000e854000082c002442d0100340a940d500e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 604913615 1250 604912365 604912387
    0x7260304030216301505190b0a230f0910050406081b0d050f100902090a0b030d030207020301061703040303080702071d060607060509070810090b1302011112 69
    0x80464021428591500d04440c0d03543d0a01d0104c040e00c11000b650031544104582030403401c1c0c90300320784500c900e1403d02003009001c210090559810b40c000b5001480b44420583c100502ca9002d4010f03480001004001c0c00900d09000054005070301010300100030008010b804241c0c2030300c0446526102a07414007041003203040038032810000b071072204060140c8860411150300c40d404030b41c0c00644202c2090962409002041c04460203540c04601120b644402080000c2c014001003030003079200f854407800042140301035005901d0f182c0b10007406802102c8480307901394020b4000c04816a0503660300d0002240003c2e0b2144081c2e8007a103c1401941c49618600e0014070b072403401000f1004640144002300400000e921b82500325606843c5031003010b0b554200416940e029640d00606000d00304000c0c010410303401300b0803609960706902a11720300c9840c00442415500303d081c000f4111a484800181030801031012600030510501d054200403158200062400c229041c56040000f80001c2052a41c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 604914865 1250 604913615 604913653
    0x30f140a0e1b0a030308041401020c0d0e060702360411030106061107151b0c0509070c080304080a0207050d0c290a03150510120c0305010308072603040302 68
    0x410034100703035840c0b002c1500105410440500c0300809204e0b0781c0000c5002c1000c044410742206200400854413000401203180d030760000e51010030023180c0004807000303050420300101c2d90040e4028204034248000210405038200b007109985003907200404000d00d503203d0004256010b540a2074484546544880405003140e520b030303100d103060040c13000ba000c005010121f1184100c49900b032b1411007400c0c076000107030384a000c01c7c20914001d41210134a802000300010444044e58001d0383c903090aa42d036150183c8100042041c06403e540c805d01c00200000c0d900b10091452207842c1c410307210f605507224041049907410380320480b00c0c050058418842d4507000c0c540d01841803944504082880342e041c034401404c0c411607140004140c1c0360802981101c0900f10468018a4040d01c1299203005807080103040100801080504d80d0403c01f1200c401e522900031141604c0c0c1042c08103160104036661200000c4d034903402c4500c918982ea020b80e070300761218009188140d00a401400a80154021a41072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 604916115 1250 604914865 604914883
    0x9070e1e06181c03090e09190b04140601121e02030601060908010c021506120c1c060f02130509070216032001080705031303090807030317071e030f140a0e 68
    0x11401203c5003050120754045005422a124201c80d04034a80b031702c262181c10f200000410142c0700d404090600100941031101902c02e0340a489540071810308040010740b00c460078031601d01c0b49010290400c010a442c40e1030f403080c00c101c210810403844802d9000c00d0600750300741e0002004c00c40ca14020406c0c40405e00030008409181d10107444803005403140ea140548001d05414054a526210704541074810402d0a0074100c0041101081040303880b144040c01228200803180c1c1d5040c0a40c01051007180d00980d608604142c0ca420150342c02c7c48107003d1400030080c42002144248406079001503000140c2d00c0145d8010700c080140055600b1ba80d040c1c4940d0442854100f043d03040402502c1076110064981105860242084403031150400322100c1200d60001241401181c0b030010400d60800000030814140e0548110166540741d4140ca1901044208619241080120b200518866481812070309100c220001c1ca180c0180070f8800500700456600403120703a41c640300141c41c00c0400480130 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 604917365 1250 604916115 604916149
    0x23120904200a200a140102070f05010203150901050303090409081b03040e0106081e06010c02130905070e040f060209010306120b07021002040b041412030a0201150509070e1e0618 78
    0xc80c50443c1c0c2c14003030f41e40001880c00350542030303081070940f145842074048810141d08101c89241c40c00c000e04185000303502c140c6050b000d4480c0142480000e0a0896021341260401005181041d84550174400030b4225503104032210350003045a940549403404543c9040010703140115291410000400d031103000c107801030b6043c8100d00b400c00542522519480c048040c50003840926511a100140c50034948500000c0d40b10800381d02031600c41c01203130b01c00d864160050741251110b44d0b465150f45000b08098030003501c0d10b20300242a00200e203407034000703150b401818540042c500b43d07a8400600c66800040d812500e1280d02028412030a904106802c1d103460040ea04519085c6000510074141c81584140c400c03100c0d0002440703d1980e10034a44410030041181640d90b03030011228028024042d840d1006c0c18840400b90101d0b00b400d00e440321034840c00082e2120803081d40c0380b01c00c02004450449204096030949280740083d622520050136214032400d00e000d05240c508001c0002000c44400551 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 604918615 1250 604917365 604917407
    0x3121512110a1719050c100e0418030804110a031509060e0106080712110913031d09060d0f020a060f0801080c0108040210050409090f23120904200a 65
    0x3c5007070100070076180b041e4407800c9200d90341ca06030b52401a060841d501c007820b51003080b00d01101501500320b45040104102210200144c2025090180384608049001780015500100140014024002740811041c00424195000e982ea40c4c9120f00c0d20300010114948030786550341002003003044c1c0101ca5484031a0b200a2000c1410070100c1c60342c680e01440395150550040600d6010700c01c924410500300750740900a030065281c101441c4d4424000c9410440002d4502240380c07882c14914142249100300013030045a49456107030820104070101581030300c25000810011005a40d1010100c008010310b88450103060070f4440040c041c000164003c00d19608005000e4820740c4c2e01c0801c050f0b21030f504449012100314120000c407440e0003aa04102d284900d818180f40c03e0007800344601012500c611002d94040811481009414400e00290b19103948207800500420403204058543d000340030344005070020b0b10190310407079800781160b4003010000004145000b00d5202c0268004084060380c01e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 604919865 1250 604918615 604918649
    0x301030f060c0c03080a09140a0f020310140402040b011b050106090606051204060c050d060b031504140f0c1612090605040e0f220605012103121512110a 67
    0x5d4004c50006010406481d030315140803007007284011245c074080024204450342040305262090f00d004000074168402e104603510030303202c2c4806019003405115040d05940282d1260360900000c0c04143c2c0401d07050100381b90046e050719202e40c1c44000c250b03000c1c10000c41d000b46098480d2080710026082001000340030400f00150444100704a60400e5202d9400a4601d00161085820340568150b22200c00d003417003000074000601e00d001d940030391400070b004051100f505040000722252040d26200100280001038108081c12081540c060641c050103483d0101090404041184c4000201c0e48211018900b40615900411400c00ba1406003049841e160604040f00080c6d900240400040c5002c54000381c2a42100d52403e4024a4014000c10120850303140601c0070300824014101c2e03010b8440304943c02101d041c0c040005490701a03c0b181041e91801c500403001c1d105004503981c074048903410000b0704050060b50285094021014075851292400400c03903036002c0383e40701a420411407440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604921115 1250 604919865 604919867
    0x3040503061f030206030a0603150b030a0b04030905061c0617030d05060f060d0c03270807020a171b03011b051e030703230103050717010e030301030f060c0c03 70
    0x995810103224a06118050b0400804510080c4541c200940005001c07051001c2a0465005401a81c2c070803030140700d500706041c000d40c0448400e1701c401039140c2d01c0312201d42c020030401c441958105000e450034180d015141d002140c0d00341e00c00c010030842c2442004080004010b01d100d01006060903003907944048094200c5c3c00d94034001c06140c0040742e0354940c08212141c0d50040011001000900f010b9100c0070480050030007000d501c0401000310342000b15840c0341c0c00d00705035109295a8040e405480300c0000340ca5000540d001498100e82107031000101050342081c40455607021101440103118034030807030302c20722598031403030030424000c1e81420580207002e0700e903000e0284e1103080c074a015626114600400c003070711182c0c810510034001c4000240000700307030b240d00310005048620481c200d4a8404d80c0b2580b4a030310f400d110140503500021020712507040448a14101c03807007601c00118140c07904030005802c8d40e0081c0c0c0304035110b54580c1c2440c001c2040038041c100ea4040141041490b84e025030320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 604922365 1250 604921115 604921123
    0x41406060307110a06022106030607030209010201091502190e0303040501050306130914070515040e06060c071e050301050f0109050a020c120408070819110d05062703040503 76
    0x204062140300d001c80011005440f031100494984503070320440d015640f80d401c2c28002503114281c05d4200050182040c21410710454019000b56005401080595111401207009400c8500e00754110354a661010b030210b18003499100841c0141c0b540140d540e030310720910640d00340340c040d03e80c418422510b02504450fa4007000343e408a07502030070501d48e40d03036914000907000411002c1941c1d001e842d011443c0c2c244151114054220503456080340d1040b521001041880c203003c00140e03c90040800c418803080c400c03601465003151026140383d05054820a10300d00b03040b09a0040a4100034207049651030880c0c81850130010a820740c0204001e0800c07124481d0110414082c0a030360944030710100b0150b4040c0e504440780b25540200b03841100c8001801041294814030a4550f28400c83d40c0100d05403034040364010011243d00141051000381da0b46440b4083c0300304003003e9109001e640c0e1003003c034600740a000d22800404807402c4a4039810110744401c540940c20030016036109005c02e00060320002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 604923615 1250 604922365 604922371
    0xa0b030a060e0112030302030709090e0106080d0509030c0f0316060f030513030507060b0a0503030a08090c2b020a180b150a09061d042d0b0d080c01060b190e0414 71
    0x2241c00b5950781c9c0c40d501d080d14000c200354090380d141c900d000c0b02004013020661141e820343c5c0403c0107030340c0841c494804c00c0340d0901502c08120380c59080b816151000b4645045000e40740754015040e036000304441d04500001699581c40080425150380b0805440c40d49440f4850707200c5c0c41220104400002520300a04e54080d014000705091f0fa00c02c00070a20382e5501d5444030003000c0042c03c403940c5031a10600142844000d413041001e9104854042040740b40254200a04812500030440c0284013481e01c4070399041c1445d0b0980e081100c0da00003140c2103600301140703007030780301555008103901c1a0300d030038400c024910b49100f03c051982402146c0c509075011060400f190120b00c0c0020304101e4082500f00b5490076a180194040d01d8800759503071048452401d024800410011a06c8201c44a03a141082c0c0b0301a014041d0b0002d800c034160701c005407111003e011091307001000044c00c152900d0841400d50322194840e484101c800100300600b690025001d03806403002c1c3c074103018800b080c1400c103c1980303000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 604924865 1250 604923615 604923617
    0x10c021222090204090f0f050408030c0d1104091406030d0801270e012702031c020316140d030b09070e060f030a1a1014030a0b0a0b030a060e011203 65
    0x5903032002050141c040000d01034071040070119600d90b618111400100403010180b9011400d0030401e84689900d441014881c9801242652843e0b13249400f20400d548014080417a85544500b05d01c50700c210900500050950b501c1d00051541040740e047c0b0074000000d081c24403a5005100340a142540a010241150306010310b824085561150022170f02041c0d21200304054070f8031000110898054220031000e0707443d040c1c10055102e03010101c0d405940001c9002c1e405911a41d01004030928080407076444c100d01d071055a0600c0d403016106800e60b16070800076246014044441e100441c000d000c0b4113046451406c04000000b10314001c5214044024061801c0c04058042c40340c20351600d1085900c0c2d02220243c942d90b13854035480040c0145101540302446406c0202480098201050200541c0076161150b401004d16907030114119840100404101a111a4030507800d07181c06016001134040c1641a90712440c1c0380d22101c0c1180e100303034090b014090011004105100d00301c014007840780d407d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 604926115 1250 604924865 604924897
    0x310c1202090a1a0d09050625090b090f090f060f0103060317030601020f0709050712020408031b0c040603030c02030f06060d1518030302090f0406140d060e0d080702010c0212 76
    0x54a40003d590052070701139a0704c582044880c008111001c00c9251144640e44031110b100352800d410b85040580c40380030030f008500c00900c244030195130000508043c075802803615000301e0744400881c1020034144c070340c04421149003042c06100d252a0180d50181902840c042003a5481d545030b50302400420340d20101e0b1400004089405c2c0e0f41f0a0165414054180f812120125540c040100061004541080000e104001c00c2c0109080e240200d4046610f084003c0d4108907036820b000040d001c02d0000814544a00d80502c042d039100c50284500960190b00d0b0140d40071840c0c014075007080301c41c20703120180350001d20406c40c04e651003240e086111030304041016604103402d00444014aa07040c01c11400c084244201300030141e2540003800400c10a44400341669030740c40c00d0006076084c0340114100000301d102240d250741400742994440500948012407a45295036105007408200000d910000e0754041c00c100c03460b83c090103040c44055a900c020050300040d42c4846005015080c081c1c943c0d004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 604927365 1250 604926115 604926149
    0x140315040f0212130c060807050d0f15090b040506100f110a020d0804180506130903020a060c032304050606011d0a151418310c1202090a 60
    0x100d41d030540f51000c0c8550700c102e5240c02c120300b01400000c1a40c000b11421400c0c1800031032034a101d0a00c041c040c0119403200ca0404080454420151685640464900740d84a604400d104181a03907180180402d01000441c50900070501c01991002401507028019a240400d2820340c08540415080d0341464419030701c56030284403a040455901c4069401003044059100f48811500104112210b8143c0c401400c02c4007404d8a00752402103035000d5104100d01c036582074a1003282c0010482e83d100348107480d2040641e40c0c07054101c900c10488e030000a581c0d030000100c0b02d031540ca52014440458494680c0614065442607078900c1c006048604209114040801510740031301402c002010041a0f40c82d11510380329064404001640140000780001074204d0b004040c4108031010700310020026080108514284144942050340d9849414088404042c0300f441407005180c840702c520f480800c0b0481c0410005081d80181100902c0d5548100040f60403503072900c0b0241d04031845a0a1090214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 604928615 1250 604927365 604927391
    0x90603041e050714010f0c0314070606090605120316030e1807080406051605040e070207050d142a09070201021b01020409060e0606030f06031f090314031504 69
    0x481c4804222028550031030014040010114003202503039000046020130940d120300450f02a1392075542400440e0541d80100d01180c0300c0c0d1030868100c848011003a107401126603555048401036030050345020358a0f0010301072860320201c05112029079030000c0d410244c601d0603112660021001c01000d1001503165403240d929107400c0c10407044501c026009842c0340030070016000702c2089808884803860700300022500d400c58002c16448031041da80741801d190904806031004180607003c181503100c0c600c80043c06a0f82d501200811512039840500c038000e81e90000e6180400740c40d0b100c4140e0141940803020700c040c00c3c10700c0202080c1110310712000d440d00c0a0681c028824550260742c2504218101005540c0540007002124030411003041125030b1185024625601030b16110341c845010004a0240007a1b42c000a400c028000d064405c1c09070804100e07200518070000307402c1c842e9182c400a07002d1542015010034440038410000785540342501d00b020180c441908000d00c42d44c3d8541000780c2e40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 604929865 1250 604928615 604928633
    0xd080402031603050c040b101d0d1704030302060a050c0906090a09110403020306010b042111031006090c180501300e07080a151109090c0406020f0c030309060304 71
    0x28100160524510b25100e0524648500091320034a00071420b002802d60282000d4a0120f500c644950f14414410120314184000a00d802110341d0720104620414000c1100711550346000080240b610f586c540c0f43d403a010b0300b04240140030024a42c505400c00440c040e40408482811100301d851994a8034181c0003d0700700c80c1250041900d4a19100d000481600765100070400e5074000c80403a0805c7c0ea84181958141c4220301a400e000e00c1d804581402c42c2c1422800c003001c0790b02c14200b6803200c0c144000800e1800c100c5014208003a9150001001100501c0c80340e83e06c1a15280f900b10105284410621095500c0307103e0b045c104520b680540403000e442c049901124400820508080e400fa000400058007205406100502030310400141401e000115102c1555002c0d50110000e00790303c00ca00d00030010101d461100030390410000403c0c0c0d0b00c0f0a0160b10910140d00c20176152070900200920f40340c0c41030f40e141c64030362000d520103240307550000580d0101e00040310b24030390f2640d0794a024030007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 604931115 1250 604929865 604929883
    0x7080f010c08043e031002031b030402061e09010306050409020d030f170a0f15120204110c1006090516051c0213030302060601392d1e03020d08040203 66
    0xb000c4a0030131800c4902003c12889018008a088810201c000c41400040348000c0e204440800841700d21100c0d800e000c40040c0da07100303000404c001c1c14100001c502c00d03c420b500f142d00f5540900005182003442da010b2140b0030140400f62405c208181c06580411041800c0d81006418004189441c0407020b1040e0818480c00b420860825101c1c20b10340c0f6604045c102c0c1c644154602070410707200c00040030342003081c101200c03143c04042108a03d19028800148425a10041e00c0102081070902c400f80400003e1491024035100041041c42c0c91070400460700042c2039031480040d02d1581d10610b550000507a401c10300101c080503030090043c90035000a100f0700b01707440f1141e040c03808004145900442c1140c41a2402c1e01d65050015a0007a0440f140c9410300945c2c881035240326034014041402500340c44114401d106e00501132020075402074100100500c82070303540c40e01c841d40104200b2070035004860303800704411a00102480350b502079103442103156003030104540200010107540e020060508 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 604932365 1250 604931115 604931183
    0x72d0e090a0c0f080a200d1103100b220603020402120f0c09030c0405060a030c0e0f01140a061d04050109020d0e06060303070209151f18030213020d090501020c07080f010c0804 77
    0x40d03c06d6140303440340380c00003240021480b0b0300881840ad01c013240c09005440381960014331302e10605260000300e14003656401c00000d88583c1d1540040010303240c40c401030a070720151000c00101d40c1342026001d00c550800800700b2003a9a01401710401d1a00c00007580c01c0d28400440300800c55548504c08600480744540c405000301038030b500700140c14a03a860707115002e00524142444640c0c0c03500018280780100d898440c2d042502218200016842a0282084818011440080c10084200040517903500b81c202e4001c80750b002813881c0e45406140319003105840c4074030260881e031800d0381c006500c0f4010401d001c0c1c0507800d1280012640384078411402940d4a0003805403450300e10400c401b003807040041c0491804190380c01034240b6054801c46a0600700d82d4010005c50104010080b0344000e90007240c80c00c04e8840c0c40d05000c50002d0400c1c0094503007441d19400070080c1500e4201890320b441a80006081d07642d140444c078100301070703016a0403540980c01101c29000c00c15950f1441f00c0300222160201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 604933615 1250 604932365 604932379
    0x7030902061c09120e030307020105030406020910030615021f0b010c0501050c030f06031f020a02070302031b0a120f020f0f03030c1608072d0e090a0c0f080a20 70
    0x8414101d81c40f1025041c001c42a200b000b000031031003550056a00600d0a0b4507920502c541c200540c401e0000350350051080303001600344458600407620746003400100c0d40c0426140e00051286000f6030705540602c0d200c42c0b0040110484a10078040b0410281c2c40480c1078684a541a142c584d00901e003c60300307103601c48000c100704e282404480006070019180c3d5120b240290b00807030b10501e00024280b010008800081c852502075a080100941c042c00031681580100c590010150b0f800f44000c9800701940e04400d4007220051342005500707007040d08035040e200005903d600101d80c2c8020391240c80c980c1030b10141d01054640000880d06442d07083c91562511000130104c0700d1010203d51060b030a81f080c40f80c14140c9484824080c1c4a034094022070540309203001d440301507810003082507020f1074020003921140366254210b4005102c41280e280702c0c0703903000207040c0d4208601000d80c00d0080201d00300c00c914041c02c005200d07455107014071001d02501c080108105030100c11400040003000d006200b9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 604934865 1250 604933615 604933657
    0x10207150906050a0605130504031103040602071701050907090f06180209010f0e0319020f0301050906090d050403020d02040519051509130b01050607060e070909060e010606080703090206 82
    0x2403014161891084624070308141c00319048010034014501501c000030701c40310b03503422000c089000600c002001a0100407080341c0000b0340c40814001000900b4896004d4041d050510f41c00c0c0008086482e800f9505a152100708980c80001090007020344102c06400b14400d02500072103000b40c11036810803444000050b4056142c81840e900801c10040300381ca9901b01d03408015010f4030301c40800180c1c1500343d000360b40322190911403007005061052000b0003649003c888030380031a00716038084a102c40300e64800001d00904400c00c00030401a8010351404514180c00c542c0810303810310094070024041d907101c0020900016030108540c032500c000000c02c0060740b42c088010660000d07210000b500540c00030021507120f1072030344200344078150010782c520003c0e4688000e0000135842110300707440c8140e54800074035010342d040c407420000300281280841c000f030007030602600b00c440d402d40421940e0b1414900f04003141c1c000b24500d5021802c2e0500150242960010440c1480340c0940d4041c07151000c030076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 604936115 1250 604934865 604934903
    0xb0429010f122306010c0308011202041b0504081c020304061218031e0306050f06031b130617150f010c0506011203081803030417210609070302090d08070203010207 72
    0xb6018402e240d94160403556100c074401581d06d0081c101015000442c40401030004410482e81440d03800e1028000080102010b600c40c42c0c035411072030a03507000500016040110740c20800c07844080004060620110003400c07003002c5c3d96445103114400500c103070542004011071966124612070400104103040c4840079280040c07480c07043c9521130700803588002d04198498400d10038181516030280c107141c3d031169040c0400c80719800080c1000c0c01a800500d6031a591884c1c0005413050a04c540c1d1100901c1d42002000f420740c480d402c1400e4070b01250441040601f9035100a2032203111000d4500c0c100c00b810000c0100c800c81d00c014400b8150b40701d03000001480420b86000440c0303980c0281d07240c802e1a242ca0030040283d2400e1808540280d20600103e40800c20072000300d0014142c0225136450700c105001e401c036208032035012090302c01c924442005014105004410f6221459240c00c40c0303010010000501007594070b05014200c0790021036001c017103440943c101c440b0a9000a4260412024145 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 604937365 1250 604936115 604936151
    0x70f14030a030c0305070f090302041107020a140117042303040b040b040e1806221a0708100620030708040e01181a09060307030606090b0429010f12 65
    0x140f59800249403000080c10580705e1003071103041c04a1941d80744407a61654007044054007440d00440387d00f80040080a0040e81c4038000c42c401001d121000900407003448002500301c0001c0c0c03a0528401030703400200000644034004030040340c040785402620482d0752810440c0346000e40e80251256040001d00411920084d00c041c004542000c0580c2034641c1d1400d010850303005040450003940d0388082c0108000b241c01903a2a984101001d42d80f5984803080e4440c104001480a0700c43c0b040c000031810310050a80c420702d45a405580c50411039903032031410b40010904040c95000c0c80780400c01d80000e0441d6101801122001504842201c1d2120b031a40d0b0b69900c0c0c4207081c030444040741c05c90801440c080f1414011180e40c0300c4003070b202021780c0700002c00b0301c00802001020942e01d4040c6001c0400080c0300d500c80e49015002c1d401d0002100d200c1e0720b0500045070001e08642581d18000001c0035071525007801c1020030b11780280f910b084460802c500690300c6803000012044501d040a28100401748a82 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 604938615 1250 604937365 604937381
    0x40f080c0f0606030a0f120e041b0e180703090305070209070207080607140a0c0311060a0b12011a01030903020f01060e0714090a0b0c0c30030f070f14030a03 69
    0xe0549502e074507600b0070581c0c0d6215000000b4008009408004c01250036402140a822034606000741d100c0390500c0014211401c0c146c801619044404807030780074991118001140303c0041c2d0315041c2a4403094440c00d4502002040701c6c082545030030441d410184030300c0a84201e903074041c0c4495001c0c18245000b94071003010340200c030214407400b00000c1049105006050342030004020720344c0b80404003501120100b048480036800e1009902d2103951344c201c2084040d2082403101ca001642c2440c00c1e082202d603e100c010500e40b141e0400616025102c100514401444000d00740045d1000841c03605a040420354040752540c0d52900d540054140c03045100f05114407001c0c0d603460041c08820040407400d0180c5840c0a402c40d6a0440500001280400504d6014100812605070385ca0001c0000e404505d810b02c458100004035021144003140e4107507044180d00303254051414100c034000c10207003030701519202030f203c00c551000ca01b00740400346807501c401ca1022000d0360f54529421501401a104503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 604939865 1250 604938615 604938643
    0x60b0604030804331b030c052b090b030a0507030b030a050a030e0402043c080c030c06030105090a020f160503090a0519050409110603070f02010b0103050c12040f080c 73
    0x80065441e804030701020030202ca60161700d98900050703100f4a41c0121040e0503004405110584d5440c3d03000c00c10400075940d1100165034542c1e46c59200007004403294804480c003074144550030300c041c4403400302c903c151b0340d220200c13000000303850f55070f003108402910280d00c0d01501030107116510024404c1c00b080070b101d014080d07258842a04a110284030491141d4170985042c0c00120a0b6603081c000320001d0110a19a4010042040046208094505011035015002541c405103c0034600e007014002030154010880e00c0c10700303543c90280890706154000b440c030060540e0001e10100e0150507007041c2c500101071400c1c030784808015407400c543d03070303a0240c0c0002d40700300020480041e880c540b00081080703182e010007000100b01e2400d414800944401003040754214000201201582c0b180801342d0310500d00787da152402024154070203400c480ca00000181003504000400c40c5a00100049894105013030342c50100b01e40d91802e0a5405204440d001401c0c00c50002e0303040c04040c00051000c0ea03400e66 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 604941115 1250 604939865 604939919
    0x2060709051c0b15060d09140106080d260f010302040f050103021003020d090f03020c2b081b06010303051321060c020a080408071d1003060b0604030804 67
    0x1100200120040b00c0881d4020711607603680c0c6480040e051880c01c03500400300300300e54540e07586482c0019103642c008246140c0320740d59581244007800601c40c180100d1082d00d000800581e4200080030352600318074001c03d001d000094010000317815404d40d5001161089654442d918284074810300356802084c48241e00c2141842c150800034170742482424102c1ea4010083e0001a4404c80d0650180d000790440a00e00e07079580c020100801d040c1c06880b0440c600c642d02a040a02181081000d180c980400e01c0241e00390140d004081c0b10a081034920300310342c020b240302c1d1b111503800e07130003d410180546501d107082c0038220001040540140141102c8401c0110001000f51034501003003003003e4600388680f00202c0d2741442e030003060341540501242d104c03502c113551400740284c071486640d0340030780e00140d040e0f40820001c01c904032400c1440400080d80101004280c00c210803840488092808041d000d079540e0b8510001540c0c405040350f00841d8002c1110361201d659004010b074019280700b8401d400c00c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 604942365 1250 604941115 604941119
    0x5090715050a0801090f09080c0102040815040b010b07151b021e06010e040807020d300c0303050c090316030b0109020901050d0b180c0702030f0c01020a15110a02060709 74
    0x30003001034601050b859a15504168a42800c0f90040e215440c0500d07070055813401c1c0c11000c030b2010001000b40210030400507a44901c1c2225040ca40380500c43c4c43d40d07501044005010001d0904885071f41100d002d88100c03501c3d219542070030030070f0720b80e030500104041d031806403810110350815801171303004240e5400b42e5190141a00281c4144c4824050052890304150014004070b103c800c00903402c680500380c03880c00d2014903804102c01310300015007600c416118006180d28000400307420306450040f080900c1c9186220b6401405200b860800103090584450000c1c80304402c640070343d888000014210b407000348c8101c401c40d03070baa80d01d07000655045584200100340341c2054021969510010b0351440e140c1060245014000d2801c10700d4982d026204070400c10002850006140c0103418002e03180795a5100c81c4109803606259001c0c000c041d0b0410004070150341c2c0c0100d6200702c15078100c1144606070180200500c01008040e07440c01154201091038441c540e8005499842400070341c98034040f00e9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 604943615 1250 604942365 604942367
    0xe04110405070212070606151211160f061401380403020d0606260d0207030b0a0905330f0103121d12030307030f09111002070905090715 60
    0x28104965160250b4020500034030806054001071081764000c2c1000a4060348070325280b14824000a000070001301840c214425442c10740c401c80c5009201049460324052060310009140225004094075003e05104a078051164a41080e210640d107200d00015a40e100e5400700408502e4480021010312044103d41000f41078804034400789580b01911130902c3d203503908002220902040c101c1d509030b1681d0300000d60b400d40103200c4080d40301031021400f0602c000000145410600300001c0115804060101f0100b600c1b1384042d5009511040301054001243c105030340b50a4040049144601e24115240e850001d24404041a0503100610255a0700c5200320008010342c01e00000d461541c200a05014040c0a41c030301359001070117001646810302c803850001e0102804248407000340c2e040041008070b9258517101c1c40220003003000042101c1c0050b03403030b070324540c1854254081c05001d070006095100390003009850300a008224043c4010b14114030082e4480000d8410400e5511240f0400d00e516 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 604944865 1250 604943615 604943621
    0x3031410080d1d150c01051003060e0a0b070503061903080c0c010c0507150e03010e0a02280e0a0212040317070f0c121407030306080d0e0a03030507110a0e041104 71
    0x1c03240000c60480c125804010132241c0d466505041c2d642607020000044158020f0141600c508080d01a4048061075400c3c42400e981d400f4681044640203034001d0300016821030041c1e0340002151520689942d40c601c082514040f1110007000020307040c0314000304011190740104003420184064800031081c074001540c04080000c030040151b0000360050112000300010000b0f4070690749444004240203c010030700710343c4041488601c80d005002e441096081c0099512003203081d07221030208540e03845002c0340801000340500041c0140c0c0c2d40106094540d03a4040e03d0300c0bd002c0707400c2d41d041414140b8010345407800030004080300440b89400240c1441c040e130112080c6001d5074a85207000052682c66a031804a690380d00800d01c086041c52858840181e005002031034442c1e200040e109091102711450100128817140802042c2140e0440986a03c0c11181c100c99150400b40c0d16003940d07142c45d203104039802d04201e42102c855140020440100080315001e0340c02020b00c0348043c04c04030284000d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 604946115 1250 604944865 604944887
    0xa090209041103040b0415060e010b1e0a0207060e121e060c03010e15010908060a06060e10020304210b0412110c0102031b03160b0117012703031410080d 67
    0x101c140660005011454262400324007c140101c002103040d100c0c01c0440b00034100781c00c40a407030400802c0035500180b550621042034600c1050341c504200d83c92400035a104090b002c0c00007000710f100316101c00c94562000c00307200b942c400701c15240711200c1c20b00500d98540035450303003405520401020401840b80c210032039050b05c1c0d0440c0d800c0b80545e036a4810110180039020a42d0401c0085000050409414401070340100c50004010440303034a0004001e2914112000c444c0c810075031406180a800c2e0001f048408880381c0510b00b81c88603906442c01d1321000c02c0484041e10f0340c8074410800c000c0080061a4140c104c825840e200729031b074509211150758802000e0024050ba0040200e0260740140d043c2401551000c00c04491138034019100080d000c441303e8400703c0317100020b000103110f81d030844540122007040e017200070080c03a17441040154801c0e451800c034480c2120080c01c04410705110381c0010944084081e50706040707040c44d8a00810031800c51141c01903a000d00d207107028509101d5a60440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 604947365 1250 604946115 604946123
    0x2070e0601050a031d0105010e060a09110702100207080106030c1805040c1403010605060d090204052805060f040e070501180305031b0c0d120e01050a27050a09020904110304 76
    0xc140f100b82c500640c010030180d01d420484242d1200c1015944a00340103641c0602041c2d43c000c005414100103100040c110b42d000303204d0349401c02291040601c460002d603501d154040740d490004181603c002d0b4100000c0d03030040c110550034001e02205000d03040007520b0460701c00010001c00c1405c1c2c2001d041c22110260380080030200c3c03a04c1300f00f0001901c42c01d10224004018000990355903100006403055010040d0004130340c0c1c0301c60794102507281a01c50b10345d00044810090503480c03040004032800d001c400c0e40001540e580c440205006480b0040812940741000d00100000f044900e091030f56a5113604c10b103800603a1a904a40b101c9403d007030200708a07175201e4002c42c14074410307403042d10b5002c003200e0b04020988202e1111140a50382c1c82010b4180900400c690b80400281c44001009602402d446038140b2204005459905030310a451869640340796200c03501800003100910f034221035603446170398004060000459845102d40c01004006400c540401500c180c00c45005903902040310054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 604948615 1250 604947365 604947367
    0x1504060f0f0f0f0e0402070b010f0501050c062202132a0c02060313061e0f091109060d060606110105130210121404030504091a09070e030a1205030702070e060105 71
    0x42ca24001c03540801e002c0910700740440c0e02401c1401180c101d03002840f0980d05d82c42c800340108000246440c905020300428a440792500c40060090b580c0e61002a00e44400085850400c22402e03010502001e40103070700400000d240002200050040c1421980c2c80845a024084c484040c1d408400f4078103000c406611030240c94943d9800f04089608000e04010300b49140014410000f081482410600e110811050f5100d0755020081000c40d681c188401081034074014a0340f0204000c0a1140c04100040f64550030707d98501c804100240c0b4071110041044d82000030110b44150444000c3c1c20046c0408000c00607551840d40c0e80417095550030303019400c02c40d002d0040c00610b101d00d004c5100300205603000300d6004501d291800407084100c0f41680000c0c000700d4180009a068090001c13130369107040f151503a1a400780c000500c2504050001c000b800090820881d141d02c0078804000820740001c1e1040c0319414070f40001c1c1c415401180d200e0014081c07102c010807419001140c15015103810795a20b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 604949865 1250 604948615 604948637
    0xf061011100c0504181d070f18021e03090c0306010e01060e0a0b0a020c090f04050705100201180c03030f020f030d050c1216030e0312040219051504060f0f 68
    0x10051084842d4981049000c02011412100c545011a446040841c0c001001402d0300d415003200b280194021985030800082040b2010300060824259911031003d02422048140c02d84002c5c4100c803c00102512043c1c2c580c1040d810000140d40326401c003a00761400404940b04040c2c44000134040c00038124903c1d0300600c2010b1160000108050010b00380c0350a013520750001c0240351f0030200c00a00140e01040041d0304c0c60400700c29503600481d202c1904907450405035145078032170089024481c051070541d030780c10440e24402d4101c1e6030788000c060b0f14480c9929007810b1661945900f03010541c04500b0040714105c0184c40021a444101d805038091402d1507403015220018020203455809000c4061001041000d050304d06580192208405002c0361000100d024003921045014000107400510800600706036080c0955030247e07045542400000e201120050b0306141504280c0e04078040907021402e00002d41e0040c02030780d0300350312150100b100c00c41003141c070f9154510048000500d190f43c030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 604951115 1250 604949865 604949893
    0x40b01140627010912120f1e08040303061e030203010605060306010903110f22110906070f1406040f060b0d0c1203030e030d0c120c0503060105030414060f061011 71
    0x20110070b06814500700c902c80d50342d804952901d81209100b655050500703189100c140c0d81241c450381c425051800c201c814078400640d02c001e0385503410301d101305020080c0001004c05100e03601607009030101c0078800c0c1e031070031031141050180c5120b400f00728045d600c0c00c41c0c04621803410000341d9124900595558581d035013580d44413030380304910025450f041104810180529a03610740c04030808414443c16aa4244d40726000000f9600000c4a00d20480410407202a0584422080310394442c0c00101031400d40c20b85140c006815002070b41400910300403071050004001004800b007000c17078080c017000d11a00c02c6c280100020096020802444081c141404000c14445032421015250207400d0000e10302580319945400c0d58840340b54600d8055840a8000c0b011340c206c078109006e1010058204101901d4810107081440b01801c160705020021000030b0030441002a15072103202d092007580c4103410401e1980c01440000d4610b40d00c503015441452444621480e44080c0e80205a0010100e050315091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 604952365 1250 604951115 604951177
    0x30605180112080708120a3801020726160f0e15030d0320041401030209030304150f2c011b050604082a0d030b06040e040b011406 57
    0x2400f1140c85206004101c0424180001303442492408148041a1310380440203030100c58038840f00f500054280254101000d1010725903501520700c40c458101c0e0308010345d00603032620030140e000c624402403041c031128066101e4008d411200c81c08208540340004c1c41c4100da210303a03d01e8022595650804141040103c0c0c000140c2c540150001d00b02e006050050b0001c281049405405a40440d4490098070804001440000340c261304240c03285040034105070448034242d078192003c6040640100308ac803480d40e014421100140a030b002105080082d01101034108010b0290074000320b00320380c1c1c42080d4690f519041501448503046220540258a0010f45407520404143c1e011aa050b00d03452001440801141c1e019601401581d900c90918640c80c1c150b1414071000c8110201c02c4006110a40d000041c1116010740c031410042a842c2e641e02c0810218010b9a100d00075a188520a0005100c5403240141c1aa24404a514085c11041090001c9445482d046c5a6a00c0d101000401c2210002d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 604953615 1250 604952365 604952399
    0x80904020a09031e0c140d0227010801290108191d011410050d0f2906010e0105031302010806030c0a2d0b0a0302130e160306051801 58
    0x81065000c1c0b40e00e0307440d1901c2e016003103142d0360042c00800c05000180701140d9403540c0104050100c05d0103a24098010403449510105e00038010586400e0030400403c545802070281c89100c3c071444032340d40e91920341901030800d01c0b903041224802d00d15100300c1d0481c4404050648001a19010310f561900b110a10805d440903000c001c0f00fa588008450350200075120042041135840d0002c226840b26a00a10403040050709440101a9409080000392114003c4911054104004003c101d10700d0400740482019010314206000b101000e0608e240c512514040c00f80000783c0c0e81c0b500340d00744000151010710080e1540407075802d00c0c41e440c5c0700640c40361050b2540b000015040e1b880074004200407074005d0040b0340000c2d07030300b480c80c41003030400102e5060580320038032148140c00b007018a880c605011510544a030b4504040d0000f425407028401c840062000302101c00707101c0c610380380406034500d0040758410b015000034203010b4005403528005440c24007141800719010001e902e030113206aa02000d00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 604954865 1250 604953615 604953617
    0x1090e0a0912030204030302061524120a061715060f0a0803040902040e0f0f0705030c0712020c130213050d021206011e08011a0f01030e0a05030705070503030403080904020a 76
    0x503811150015001822201d84910b0580740941c17124210718001c6d0a10030001d20b82800848504c032486010303510a030807900360100074102d08080c908011455003c40c415802c50a03a90714030035061046400e40c0c1e80c400303000c40f050346660300301200c245d84400d034680e2004034240b03490a500c2c001140041c5803a58403681c1a0380000e1101007002c0d0b869106c00e0851f002035100900e85a4049020004c3c80b10059140341d21000b210f40c45195842c142e9030641544202801350020410b011000440d115080401c81d8038181d00f0202992011144a40083d640e0580c185c200d0b00519181c08040c240c03880500070342c2c400050030300039060707d5400d103018070110f40c001140503688040e036a10050940601804024041d006c81c15440b409240c040111603010030142c0d001403040e13890091480a89843c4000d41200100304940745400c803d031810049003d801c01142c002141d0050200c3c139010400c2c00402850414400c0b0300382c602d070715900d004058590056220140c01603408204e030103103618069005007141c00d40c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 604956115 1250 604954865 604954871
    0x1501140a15120c020a0b0f061203071502130308031303030c18050d0602120a0b030d11060a0f110f090301051315020c1c0c0b060a0b12090c100906030e03030601090e0a 73
    0x240e80c1b21909440340660344a259038402c4000d02002e42400c038039007024408008001d62901c07100f0356030b10341d41c81d558501c00c120080d030109043c111101c0f40a6200c004503004031000c2e441e82013010031031031500314890741140841d14007410f00d46c125000b07211469440940b8100441c0c903501d40400c3c480740d8a8190b604a5015608020360f400d904038200e501030180c04040c00006100004c401814501402c44114200307000240c10040142c4000041e03e0743d000038009408110710724050310072006861000340c005041034001c00c000d055180b544000d40103440048000340040c0e02d9000913152500342444010b000c00c0308661400b031408041d50024111f06501000316407140f1070301c03486089002c0003010f40700e001a403c2541c11003400401604c00b50030000840701411418600b011a119501c81d030480254100800000944041c8046c0182c3c10700440c00b624a00e619404944001e04600e0180244008249410b84040d9003c00001c00e4900c5a601038441842007820b140c1e48080da04001004200940e403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 604957365 1250 604956115 604956133
    0x41e05090c0406050303551815031b020a0c090216080f13030b011d0105090712060519031a0105030d08093a02061e0601021501140a15120c02 62
    0x4030110b811842e00c0407d1008003240407841d40031500d808008002404000030a210001103003042e2050f2003c03106e0111210800c94192031083e4043c00707074580650801c4a50309034940082e50042501c07040e80d44143e107894403450315420101d04074080c0c50a074010143c0b8400d018030000d6210f00050140d001c41d0300400d81819001c0307204003e00c1040d41c000b103a000b038003400104030750140c04002c14480342d42c004e4020415070400001c561100d0004042c141002140700040040c0030a81e03210001401000c0e04603001800110f030300420300801c40c881156007405240c0c50103001c103840345d56a4103850740140070b0f02c0507141824007200c1d8910702405441741400b5030303802c580781e07003084820314100002e2101031680303444004403a0b00300b01c015455680040d500940c0030042d500d1102a0264821402194103240c030792981300040346083c1006204c18a80c003031400000c2000d00c02c04809650300e80040703c150400549841510361400058002d03840407c0084004a0304188540c004440c005010b10440d21407034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 604958615 1250 604957365 604957447
    0x3051203071e0905090c07020306360705030f0f0d180819030906020c030304090f02120a0b030106050609010e4608030f0a0509041e05090c0406050303 66
    0x1ca0281d8552001c00c44122042240f4100701805d29445800c003010355061502c190003007a02e5200081ca4110010f9204140c0d001d65a001e162188549c5004c0b012891b2280f10240c0023690744245002d00c0b0b11911402d5a400300100c800500d03402202e6404008d0949032801e51005d035502c4c04680680c0120709039010b40403954400c1000740040300c041c031515400706040241000303070016582d600100b04541104400a409440c00804c40342100d880d1030f80064110b08505001c0000e0091901010780c0380102000d2146415040c1c01c60b040e4070108030020010300e40d44508020f41d61140029003808125860036800c1d4501d880b080081428140c03040c00215500312400c3c0c0e024442000c1c0240c400c407800000ca000c40d8201440480018080c008015450320311074404840c03141c052000300708200400058602e00584403500b2001d940801c201e0001d5a64141c407030480040e2000300c0d040d0840c2e1050443c0030905250a000711411680c000d00511314203400c4400a0f9604504903090864040000d40144400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 604959865 1250 604958615 604958657
    0x1e0203131713050306060607080702120601030f050d030c1b050a05012906042607081e010c02071a1815090901080a020901090b24090f01020102040305120307 69
    0x14101490310325603907544030429802c0000300d40d00040d009501c020304003e45074440e042180e128a400c03220075a1039805503c0028002618500c0c00103031401060000010024152081c070074251042041c1c0701009a4850100d0031143d041c0106400106801da0140c1e2080007030301e25102c031034083c81c1a229100c10079101d41c0d00b5120000106043c2400700d600342000a00345000041203648200d494500d800e181000307601c8a42a042072100411240381515a5800b40801c80203005004800a4407424000e540d12842906c0441c4030340e0604c2d500304905100c0d200d1002c43d81c60161100208504070800344256084085c2e0089004000094090181654941d44060710018001d40c0c04607907682e12902d003028846070508c1030b4054607045d4480840400141c2d185d8034018103450700307410001590490340d000108900800a050680c16903a141e05920b0584501c00500442c9002c3c0c0e244a980141e00c07004a080f8441ca10001e4001d07045810a1246200308400564120005280402d03040404011003104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 604961115 1250 604959865 604959893
    0xc1011060906180102030609040611041d040c120b1b0f0f0c0c030a2006160507140d2423041505040203101e0f0501181e020313 56
    0x590b4450301c100300050b00c2c18650400180c60390300080d411400c00700086032000746c01400080c202070b00d501e00030485421007004d5900402c0541049105906000a030b0131690100340c0d803d60b89882ca007070003c5511070703412507400c03520303075000c201a040d03a03a840ca80081c05640701c08100024100801c1200b242003100c2014101d140c401500c1c0c0c2d91b0340e113048148107281101c03035181c840c081d800080294010030301c0780203800507045090f2007462000b90301c3c0303002440a02c904c0c2c1c0401c01c0fa042000d00c1c038041c08000648071007510186020b00341c15400301401c01c1220441c03004002c0c03001700c90051502d2041e820307180400c0b0200c6e00c4c440118840e03100b407512005201400c2090003014589004000601018601c850000400c1c0c400030801d41c2803a4021035260054203c440a00303a4507055002e8071640f01801209208100f8402005410400c4103401c0c0544802c0c82410000d940f0075460244510720b0f88100d91865080c60005509803004038600c40103908020104120f07441900c80c0e40e00031544501c04101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 604962365 1250 604961115 604961131
    0xb040905031c0c02071a040302040f0e060c030108033004120906030204030305090418060f0c0e1005040e04031704142505040b060d020a0201021b0f0c101106 69
    0x80c94600c1000410031090070040d0255142d410141c0b1980426004100b10040c0c0d101407112410302285000050b041e4425a0310003500b0601e080c0c011034404401da4055015561040e003900c01036281c2900030381d10b6020a01a01c00710b600104605071072011002c0390941c0328030a04410700c5a040c81d1141000b03500300201e6044c1c82020140c11201034090b84822140040c10227400d0031428281182c60050a030300404070450301039640d80b106440c100c004c00003030b0015183c0c03192017482019400c40080c0003071304400702000042a1145101e007020315000041d01d140c07000d40d5842a040c6031400c0042d0500d440c02500a506019000190b5940740b0b440da14030512560041d001c1d0301410b0310380c1c507540c0c0c5003460361075072101f050b84445110042c0c2010030350001c0131500200d0b0b0100d5007601f00e20000e10399100f07002c05021098800074107a4401501074010b46803517088028070180301044455943d440e58149048142c0603003000032400a14981103c0c108103066840c903103001c600c80070403241c0d80390040031340b0089 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 604963615 1250 604962365 604962367
    0xf2809030c0c08070b040e041401050703020d06140d170c0a03020601031a0405060a0b032a0a050a120b0a0f020d0e060907080721020a03060c26040f060b04090503 71
    0x41c02d21440340c44900c0102480001400d01510700f003404940c9020394021b00c4869070700d040214040c01106a8817610921a1100170429402c018101034000e502402105812606080c00000d83c0c2c489510004140d400207040700507920950ba036182410400b5229840007100309026511840e0410010200c0c014030a8004060039415820f100c004e00c164411040d8a88040d9410003000881c086444c1d0341042e180c20340032a9820750720001a00349403c4810310f0049107a80100f100040c0f030030590514a206040e600034607059125028080d0003c0036001e607401c00410400100006031842481650001c40e401000502504506000c001da90007225440001c40d203400308403610010a00629402482e164000c000d410700d0a021a521200c0f80d100d01c0341020340e02c05440700a43c01c501e8000c01c445600401c1d81d10390300e8a074640080140404014440040c030144012521826190071041c0c022034440300c0344c907980c1d075641d4800034501c0b150201221072584034100f04c40e05449a0061000452089001d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 604964865 1250 604963615 604963637
    0x213081002130902032511120714070305031204060207020405130c08030a091a070212060f16050702041802130c030b040c0e010507031806090303020c090f280903 71
    0x54800b810300c0d04804440c0344100309200790040c1002c5040090144120640320070381c041002904c042010515802c610700800c22003c0c0d188051300700418001d40308179810000c10380960120380c0d982e07925010003842030f070041003080300407009502c1040d4001c1c4901000340c94025281d000c20140d4100f600d050b00800d004c90291010000240c50380d0028150b40c400548c20041100d100070104509882103890011050a9082580724444215540310780c01511086480d9800d0f103d046c2d0b100b13811941042a0707007410b07000c02c4030b041d40f502020903028110350314182400c2070b03a02000020100301084007001c03118805c9903001138442c81d010140d00c00103021300291503102284043c05407041c020500344620710341083e014209403c8103801e0020307042880e006440d407120f4a000d41d40401810784071034100c090b0000008400d076005505005581c400e60964001e500401c0510500150668448194403255000100140509442c892040c1c1440c41000102d0044000703040848907100c034181c0000c2c1c490449 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 604966115 1250 604964865 604964887
    0xc160c0303120504030801090c02030d02120106022b031119020d020d080606030109090f060204090b010e0d150f060f080c01082202220c121508060a0213081002 70
    0x5550b42da19000c0d101804185401d90b00240810301c14041c847c20350341c1d03c091040f881c81c400c10903145c14803c000f004568400001c0c40750440e2402c24451800140708080080142503450b0003442c00c02d041d10b0200981c00f10155030b042c2c02400002c1d424a6668a061115003c518070303500d445000e00c1c0182d006800751442c00140241410709a1b207030704060041344018030080d6119001103038111545c5100000c0d00340386030b140c407181c484802e4902602070b60001c03c002c112404c4035800b4001e9a4826240c80d001e110860060100290b48000701506201100c440d02d42d0140b0150040c4010300e0b00f51100040190f1900d1302034003d0080c982021005500260220225503049003850b5040140040c411580c21003850a001071101c241400074020a242000f4640d8505440500000030101e14424400c4000541d8020300003490015415405814441107074100e54041d22010195600300c00a42081c1d40d030075200f2000f03588403840d802414180c0e03001c00100702c1b00911064030f5801080102596520308540c2c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 604967365 1250 604966115 604966127
    0x5301003060b120a060f091703010906060c0809040908090402042405190f1403040b0615131a0d0516020106090b011d030111180405010e040512030c160c0303 69
    0x96058000c3d64121003028200e40300150404019600100114002c10784001e41805003403090001800441c80d040e40c0d8007041a6440a5410388200c01030801ca4255613500c11540030716212000381204400b00b240c240c041c24184c12080469004500e0140f0341144180810100d900c141d0100745c070004000100c62405000c40303080e082640140c40d005d03007001100044100309803035142098050018400d61448104d00400c1421342400c1004049500c924290500400264040340c2c074512444604030b00b034080a1845003602c0d408c001c2480002c51385814941840c200c0604500c0d900004070302440481c449002c82d02805116540020010b11481d10414001e0f080d00c0903504180744031403c0829800643c0d03400204886543c42c40340b0300c1e610340b4031950040390050110903154458034070005210380760411114080c0040c020143e408000c541e07642c000340a40820b05603001000d41c0c004400711540720706000003964000c21401c2e8601d20b807011204c010072003459500f17003c480c1010901ca0402c14160082 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 604968615 1250 604967365 604967381
    0xd020d060509012d050d240e0d0c0203010b0405090a020913050318011101060603061d010810270f060501060f120f0e0304030b01150f0530100306 64
    0x3450381011941002003030303070451104080d800004c44200c2d01c080c080001e441401801050081c04001110010381050b21070b41c05003040f240111031640341c100c5080340c1031f8447c02e181c070350108026090780c600250b81203030a00c040c85000d0341d0641d201d261b401c285544512030180034400c204014168058a0710502c11211070003803540c18080140040704010540110407552650300c03031492840403003e5200140c400342d103542c0014905610344200802d61903095884001030301c181c50b194030347c403140c44e0350703240c41d10802405606a02d80000c0240515401c282c1c02280800308030403083e2209401e5120307407851010302500191110150010f0707841c1803080c43c0c0310385805085070303107846140100c02c0e40004c3d1188529040040345190f0702ca00a402402e1a40d11006d00407a800091700d0b40c80f0750302c2c14200017410003806600100503548072007604080c003507918110207001c251641401d0000c4899542d0040300003002c0c60804540d02c0220300881200c0c581f1051090104402150003e82103040103c01c1b80c10319 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 604969865 1250 604968615 604968619
    0x405190f1e06140712081008010902130903050c1b0f1206060904020a1520030408100902031501032a05030a020909150405030403112b0302010608030d020d0605 70
    0x150028124001c40a840c100548000d8140041c094140c01d0301c0005500ca0502c02030400c2240b4010780f10469400f07002c0e1030168035030000300e022140e00c908002e800c81e4040300c4001c0d07009808550030300c0305c00300c16045825400d0207424014240301075103131007a04000c0e850403540c41c90710b8015983d810502c0e0600c10464100801d403a18100d4000350984503681c1c001c00b40c90544149480d03000071b411907890402104c0a841d16180c002d44480030404090013641c4941c51078820b803280251015503140e40081034800325031555005040c50304091007880e00802481d50240e07054042c0b80301400c014401d8075803050003140b081e4080206050750101c00021405403409450011130255810402e550740010051a241d40448103689a40c40f911302d1146403140c0740c8106078810401c4403c01c414800084080c0003141e0081076001d101007500020410000c0e050255040d482803002c0c400e2040e108030001d0300959034801e00001646076100c05859185400c00d00821a9507038000540d51000040c80c000c0d20020001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 604971115 1250 604969865 604969889
    0x304060909050127110a1106090d0801170a1b1d0606042c090a05060109020f040b09030c09011404060501080c030c071a0106051b0a120f050405190f 65
    0x107111030340401501325500c200c18820204201c0003018410f50000951000c0102e130642da42c40e10700300c0070300800401d210103461030060b1000608001404900c14030082c6055894070450380c24501000c14003250035540505030321441c4501e00000702401c41c02444400f48505460f006c1e440d00c500001b5010000301d17000300c0c88001105105e2603885100a441c1502c03400c205141840078401d401c040564091104810070240000c1800706041000c245804094084c0003a12020380c0c8840308081a4424007102c52140b15003004100302c0410604050845203a004040c1d40024584030002a080d807030a03040b00d052040c0340032101d00649058494000100380070300b4a19200c3c50020031203106800000c1100340074440000d004420050a900302c00000e4401d0007150301c955866800041040d00301241d026a03031b00301100c80440f40500000c5188120b540b003040d045000c00d1908044443c03404058840050000501000c42d02c0e5482090005194500380410300c0010b01c2c00c02410390b5010340754031180910710 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 604972365 1250 604971115 604971119
    0x70210360c0e1902120114011d130914100e0706020a02060c0f0a05010c030c080112150209030106080c030706030b1503100e0f090d05030105060a08180f03040609090501 74
    0xc80d41010004840040d402d0904543d1100942d41c03541c40322110301c11200c2d200160101060640301503d81c1a501c900000b01b05100145005568007991782d98010080d02c0d8540c0c41c0d801034a0f111100c0b20320415141800f107207010440d81e4605d0004124443c0c20440e1300040700402c450210b40c810346180742d0303156000344801d03441c00b030003c1d4a4200341c100c00f0380514400950002601c000708800b5880303070490012603c40742d015040450007003091130409d87c00642031501310400380e032040b01001c1c16503c1c04220b88010b00042d81c0c0b440d4250803039121850740650240089100399a0a00ca0800206042030251419030845800c140c00c114007034001c0ea09040c0b0b0031f051046a074481c4080500c15054031404c00c0e95a46901d6400490f17102c855110040e19203401c01082400e41c03403824082d0194214000316050604401000d5500f4042400742540202060001c694411312510600ea00310020680c51000300040032029420b04d003400100380c4056000142c104509540720900100410b044942000154 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 604973615 1250 604972365 604972373
    0x11010e04111b0f0a0309030b010e0618250e091006080415090804030305090907020607020309100c0f030201020a081506040306020c10060f1404140f07021036 69
    0x10003030070240c0942c80d1152103014225141000b101030200499000c81e220359000303160080850029000c00c03a08a1041e800000d500294040c03814000d10000b0120010310346070354001c00004a004000080c3d45070f200703400c410102650f404146040070b00d580c4803d180b103461014040c541e480030300540c65a030160442004126030056506030000d600c02035450902c00510800400f5003040240070340b440e000090000109500700004001101083c0d0301512285e072085010380c0c44140440d10a0b0142e04200a0b0250603d8108411000d800c0203003001418039200740c03190741d80f4015040040703003d40e5002407103041c4581c00515440c0e12581a041400d004094180498500c1c0514800280740f107802003040e44a41c401400b4000c11501c1441e0200040ca82e0754000c1e1041c0d40b07051040e01d1203824880703d540803074203141c081c8581024001100801d9520b0781e854051810000604c040d0841c040c068409452803014002c42902403900d0700040c0080c602c50340c900c540b07001d146a03450303d00720540884600013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 604974865 1250 604973615 604973617
    0xd0c0e15071106030414011406100f0815220e0c030703050d030f0204080610030309080a0f080304030509060a030608060705040518180307060f0506010e090c1c0911010e0411 76
    0x2d1400f03451064a9803a00d180211208a82c3d03c0d50100f03650920b000e640c003052920344514803c0c1c170100c1e254103040c80342c10810b440354441420402c0c00101c9a900090401c2c404042c0d8070001c220261484070904010141002e516000d0111b541c181ca40b2030300304000c040c000704040c10313040408501901502c2d02d545c0d502c2c5e560380d0f2440401c02c20700d40c64503c0c41c4503201d03442c0c0c1650700400400b82510303194500f040c50403c40c034090307000840219143e5070000c0343d111400191444202d510210041403084242c4654100b500005c2c030490412074108010b900350b85400c00606400401901d000c039500703044c20156030820500502c1d070b00400c68144410400d540e45d0050050082c4140020780845460b08400b81e018401d05501030042031000040352820803069074003103c804c602c024420806a15004011116103440ec2c41c00303540404d180c8085a13082c0296001000c1d41c98110051910750803101c20b12406440f4040c80c1030b50750700f425401c00f40136942c00026038071000c401100d0030000d281c0c14a030328030380c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 604976115 1250 604974865 604974893
    0x6021305030c100f0915171f061209020307030b010906121e020a050a0602030406021203010f052209060c120c020712080f030405280209010506030c0d0c0e1507 70
    0x400c501c642130300100602900d481005403040280010050f03520307880160003415040c1c0c90300090b0105600042072000c480961004524010700401d001610f0b1030f90032191000f001e1848260240d07203440e90700c0166003c01060004620483c18288550b02d072016a10888200ba0b1012500040c402101400504000342900c0c1f80c064024403001003c0050011941c800140d070000c03500141002808118650004003a00c00c0754980d41c02c5602c0200e8840a02c5010f000031701c00c809607074686100608c002e19025035070b4440003605844903141400308807080c6044c3c8044e2881a40c1480d62200481c6040d6400798182d2141d51209205001080410f0b0009695080d00d100e901c1904030307000300c0702d000c0080030743c1102c81030b00b1250b600f180c49042a0514544a07103c2c1c0b10f18075002c60201e168602c80c10103886208e110b40760020680881603182c0002e1103066030006000c1c254140c0c041241526040c058400d50100c1d582503501c21304808101d10900400c082040b245505000c1c0901000000402021840030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 604977365 1250 604976115 604976117
    0xd0801061d0a03030327050304050103051b04031a0f0411061e0c032d0406200f0105040b070c0807021c0b070c05060709030302030a140f040306021305030c10 69
    0x101e00003104180c2403000301e05410300c070740c01250201d00006066060700080388400951000d40342100585103000c001c480f19242c000c2690b007061108200c1580694001903218403c0400500d25400004400c840b41d845900100c418000e00b2000c4404072001c0e901860384840850b420802c1401c05441c0c5204203201180703150310070400050a400046d607210880803083d65020f088030b48400c031001e4060f44075000740c0e02103085120401c41b0480001203020b6102c3e206500b4040051401e82010b00494070806800008020141c0070b00000c0c5150100b0014000e0702c24800c00005494209442c0521074000c0140145c2c0400080b61003100c04035a55000312074400381e0444207080c0c500c220450b4440340e020000c80182024583d2000c100d0125007294003882d84074030580560702c1c5541d44c294281c500740050701019006030300501c060383e5507600656100c952140c0c2c1000240c10040640b240c01d4840d03011f078104a03089034022400031000342d0300701810b50113400c0c21000740080c0920714001c00c3c195500005080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 604978615 1250 604977365 604977377
    0x1b08030a0c03023108011103061804020603130302010b090a020a0f11100b040b1f080106032a09090f0c090503010902090714090406091a0306010e070f02010204081b120d080106 77
    0x104c10b6060b042404020582440203100c009007691000300c0e10340003200c40b02c0c001c800d400500d40c0d1300b22407a400588140d900600e0300f400d54460b280303641181003040c01c0c200c0956503a800c03000000d80d188603816210340c0c42c8a40250341c40c0070a440c0240342c0c516031032042051103959484a0004900030815035060080346600040c0c880c014030004001d00445001550465170001085056880981c107448101d2420f0f10341f2003075a60703070f404100c0031605854520b180c015003044050b01c21107046928009590001c0c034200100c1915a805081101c00d0110030080155444c510000700980103d9000000c0c54218000c2000c0360b120340202e40d0454005001c1402c000000c5404c0c10541540d0058a204d403401400c00c1252a4450014000420f9060900ea414000007007400c00540f07000103045069074058458848140ca9020b0107132a0b1782c0d00c400003c0b0070b42d50203100110f10680200401410307400748551056044080c0c10501c0148400c040c0741c0e17005500004064020303a500401410b04542c03d5240c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 604979865 1250 604978615 604978687
    0x8010f090e10050405010c0f180b0903010f1b1706060f091f081512070506090d08071208131a0a090203150a05060d0f020609011b08030a0c0302 63
    0xd040c02c0507107a44061003407402c1d00344418880150f120219002094645035003400c01030806440c038690403442000389008183e001e10a415000c80038044a00014001140d5004e4140030f4000307803018400800304031070104043c03c41c025071010005003134040e10b1044020354201400403032034034881c2000501005c07000042c894820703200e20001c20a124031044641e5698895090b008104071015200044034a15200208040f0301d480c8081251100810f00217000081c0742c03c090140700d0b0000380b96164016005200321010440f620000c00c0d165101c4e00c4c1c02020160f01c0013003d0b000b040c0150051012700254414080002c072820244a0807002c5039007802e8190f5218500600500a0410004c2d09405040015400c1000a1034094000c81140c082800f00b81d94110501070680000d134400340c4100d5421035103a015085c00e100411038003c042c0340c149034000c1d9019000080003100c900803180d81d54004104082c0c011a80710b01c2c04980001c0c0380c25480c1c245042c04071004c201540031020030242c610451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 604981115 1250 604979865 604979891
    0x603022814040303080a05070e1c08040b18030d05270f0a090b120c0f0103181424070c03052d1305030303010f030b0c0408061302010e0108010f09 64
    0x2900303a680c01c0c61461681e501e07240d02e00181412016940010f1130750034040803d0009000d96000f030712903030029080c00c1540c8180740801c0c0c12642c1215050f41d030404100b1001c034039004000014a590301d1641c44188011102c0e5081c1441c0c45440c41c0307440c00b0400184405560780f4070409a40404c5402c1d5200031582c4c3c05c10300000f8218142c040c130303041d07030204200740c0015407101950002124100c0c00c541c80e507440c803d6014000d44030bc404005541e40501d50420f005e05540c029889241c0aa54000d00302003400e44951391103004510f081c1135004036910003420401c031174000038000400022840f18144150900b40005000100107040040c140000401c0c1c86200c1a8110420081100860300508900c05154182200365000641000640c0c3c0c611b000800c0d82d090000817030b81200c00361401500401c0c510745030500c3d504009001c1c21a0440304100005001404100300ca00403c05500d00c81c901010302d10000d00a052142c0605040c05610310040040320f850001c01011034254400c04510030b088054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 604982365 1250 604981115 604981127
    0x5060a061202130b030d030905010e150718090606050408070909050a06050601030b180114030313170f120a110d0c020f0406091107140f030702010302070609050102030a0b03010606030228 82
    0x1085a405d03128103085824802d40c1074104502541c0580000c0044c4c110620003161241103c10001e03c40d51103440201d0310b000d2007a000c0030301070301e14540c01001d251340791401d031360075240aa4010000140c020809000c804d0043c8840401031440032400c1100350146d5442585411a00501400e0207907075800081542e40250008058141c0c01007031141401141c0e1119900d0081c01c1c024992000030104440c03050b82070003c21543c11a405406d044401031400708a248551a010301400300340c01940000084c0310000c225030410b202e00303c0103041d2204c50102c401028110390100410940c0d006101d003014071600700300144412a01590a030403081c2142005c1030103809558071646880c0d103088a00e0f42585826005401414400c40c070b00d040845500d510103a0703030141001090010b8004001110040d8000e0b4000c04445120700d5010407981426100c2608a80080b21902e0115403501500c030380900d000e01c44d102c0988110b0500318207160017800400c01c10a540302c000c0710030b864102403540c45079010f14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 604983615 1250 604982365 604982381
    0x30c020405130302010f020a090e04020f10020c01030c050702090a050606130803040e0a0b010914010c060c1d0913140114180706020706080c0315040f020705060a06120213 75
    0x180052045040c84003100e094505282c2003a0015442d200c05900750b001c01d4000c07a00c03003801e282d4410300307482d081c0b80c0b1042c0da40c503016008903030020607420355204548901c2c1e419150840950082c001c1502010005400e840c062540d01040041c100020f40c016902e0601864100b111981c001400766a40800b060440c4242034441185850344000001d0a100000c000c20030369811500315006500c410883c07000f601c03280d26145000c5141090144515076070b5134100b4007d0031052501c1040280140c540c0d100f21815011420005420941214010519a620f8020b407010a840c0b6051914205108202c68020420000c103c1c000c280c42505d0003000c250012608020346200108150528906520907500d1000c000c404500801000013007050000c01d0500485200380c640c0005541c0b24030410f14251301c014094015405803c281041320785403881001000d121481c00143c4d1070b5030b40c1c140946000801030000c0400c80c1488002c0c400320508803020406980d040d02c1100e0108480c0d510140a00174135 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 604984865 1250 604983615 604983619
    0x32f0a021e0102090f0402250303020f0301060c050c2d01030f0f022d0a050a02160608091204081020070c0e061c0b070c14070303080708040c05060304030c02 69
    0x15215107080e40c043d401824031200844680f8050f5616606200130780c00380f46582055003c0d42c6d250308260404400304911110b102e450014944030100700d1918054100f03810aa000400090800c0d08120f020804001101c408031081d5060f880d09640381c0c0c108002070300703600d0702c044264041900c50342d001c6e8100b1585c00e411440304ac40320150303041c2500001e4011f45140703058604e200800380c10b50110310044040c0a90410b0b03180f80340000e0307000c05a1f02e075800340080380c086100e01801c0c41c80d107040d14010361001e030600380e4400445040400c0810701d0000344500c02800703042c080000b000001c400050b44ca040d525103401c080740540f00350a403404943c40d0190070401c1e54400043ca00b00304441c00b9072600548200640098403901d07020180f0004451a20807081c11a940f544484041524211030590008151400d034960b4811641c95005500586025911640c0b081000303000b0550400c0700c003648041c040c40c00c4540f5103055201c280781e0f40103c0c410240035000c00000b0400745031080459075542d50300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 604986115 1250 604984865 604984903
    0x7051222080f0a030c140919030b160e061312081911070e04110d0c0503030408010b100c030906120f060816080c0f040f0e060412032f0a02 61
    0x940411a0620f600008003103000a142800000d800c03801010360f0302c500c800340c40703842e420054070405001640c00151108003820300e825000200140740c44413158420074030400384001d54a12031002034004286020f2052192505004c4400032112145030340341224502d501414102c0c5590910160920421410001080c010484800e0b9190001000342d00b941e4003004694046555a000240c22141074400609031001c144002445140a40c56600154090790041490994400000b803640c1c0c001d5100d00800c1c0d446284c000ba2502c0d0101c0401802120b82c01c0c5114100c0159070b0050014080e8007444050081c03441d81c40200600030346c40031800c2040b0b0f0303004108844c2c603504000e42d1600e10000c1c410500803041c90111b018900400c85403481e1801808800b0310452007000c000291460b007110141055070f842c04c0c01c1e4200000c01000b40200d0280d800031011050081d402402c1c3c03241c0d80d03584041d40c002c856210b01081d800c110020303401f6038031010140e11005250401ca040000c900840746203010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 604987365 1250 604986115 604986127
    0x2011b02122107030f08040c210318140d0609230d110606010e130204030803090d09061707020a0c030507081005040210030b01021005040c0603050705122208 69
    0xba24150400c1c048030505101c40394800795407528400c80d039004001402d0308003014592805800300a4001303110f000c1010f040d90301d601c4204030b02c00e0307a0380401d1850300e0003021440c18140c0001c0e00700000c0d00c0101000100c10f040c41640300d40080e50100007405010703180e800c10309010300b95000048a65007c1d0201c0803207918400c002601c1103080d8980c200a00030100c1c26604c46018551000b03200c4070402c00703040366645074801500e00c03408000002e0341088004500d045022002e10003040514411111a5200c0c00d0011041d4030b04802c5a10510034007003d0101400001d070410210341c0b51030000d604400c259694190304904024080030700401c4204c6001c4040100070000c01c040c0241d5000c8411101c151864012013020355030244e80103504400c0c62042d80000c944281c01a00622034180111808952007240d020b0488400300c0c0c2c281d681c468920b2091150316458011690414000d02d003540c2030aa004510512541e0007620f60040030080310759210b028110581d5400c041a08240d4141d02c8032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 604988615 1250 604987365 604987399
    0x708030a02040e060909060402011b060513050114010e01210f060e0f0d140d180f020301110f0d050415090b0a1d0601030b22030c110a1202011b02 64
    0xd0003e00600d18102000b40020b9031604003860801c0c455440c2d98010482502e441e0010745a80200d00240c50140c60340910b11408124580100d600a05104504450300119820b18508541d40303000c0d0320400f28980c400401031942c290445a064030381429840000e0b291030003410441113100d0300c004103040011800001881042c3c2c0c41341042e50106415202d001c01e0303200002d91115442044400400c0c000a5174961400206000e8450304150001c0000c076942401c15104440e0b00612044481021110074802141401e008025400f141074401a0414040300b0040c41c035409000c81e480080351762500000c003481441c07184c001803031b08e1f00a01000741c000700341410780070b0081c111070055166042001c48008003403d2010b000c143d070b4414024040e180d003955101c420f919009043c0958284001c10104400d0200e080980c1717015109849620602c0c2140c0f6044400903880c4520a00c9a604554100180c2000511001e241d40c0d0910700b00c11910110041d4031030740001e064000e5048500490301e0310100b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 604989865 1250 604988615 604988617
    0x30b070e0102151e15010504060804050f061306060902031005040207170a0e0a050a030308131b0b04061706100f1407060c090b031302040e0c030f01061802040311150708030a02 77
    0x124440f0404641541d032030300300602010301c041102c51300040c1f00700030811140344110082034100d84688292100e000700100054904002500c0c85008401851000e001300030640c070443c030007844050819421890510010120314000d482840d0145030001518000c201481e002a010020101009501c409a55074000e1208484241c414060000d000b800701d121302c0d0032141c00c81166415901d1a0303050f5035a291150424040002c103d5008512a40707001d4a0145640c514014024041c0c81548851404ac030043c0040004d0f4000b51421040c1014005961030f5010b43c2c0c03088540c203042500c02c11000010445501601e103c04503401140810241304100c01600902c603250201d80d20740c29100d8603002485c04512066480d00d40c1008070400300c0006090581000c00e40d05000d100b42c81152a0307110200742051044602040e0a941d80d0109114904c940b9000410032000344004600300ba0170341c0c1d00c0c0000c08505c4a0b8a501c2411080242e0f00281e1030074007126082c40c0d0000410780c132810103101003406 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 604991115 1250 604989865 604989901
    0x150103030905091f060905030c0d1106090303070c080d09050d0b01060518150703030b09240a0302060307111902061b0f07030809030c15070b1504020c06041b030b070e010215 76
    0xb181c0607165270b461072490800d0400a84a40200f84500100c40e401d04103d20f507840b0380d2035a0b4060005014403030104003001c04020013401d81c41c020746070081000310000c2c5181001d801c450300c5a464006000041107c40c414141503c24904061b90380e0b9908480c41c940d00c2802041c03080d4000d00c0c09840c60031014860024281592003a2003e000310314243c81000b840e050121500501e00100303250000340040c40d0881c40c0801c2002811402403641c4a40101d01039070300456200012641010705407110010410807403000d0743d283c01c040004417041c0d0340010490302c2202440c125000c045490007a07020810f100350b58501c902c280488441655a01e072428140d04a140c05521a02a80c680201e06080080085101200002c0000c5c90948640d40780f0342c0502e0041d05c1c1c2c110b038500080e451102d40d2650301c014034120f060b0400615551625240142055605040d0303002d4205203980e00f000024034154103150884400d05210b612400003e0040b03207000c04583c41c80180603810420b00c050864941503e990b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 604992365 1250 604991115 604991119
    0x13060504030b0109060b03130303180311060105120318040e0d090317040b0a0f020705090a06080705030a0201080112050a0503030c0406390212061602150103030905091f060905 77
    0x2c1580c0e03900001400c0798050320402107880d134200001003d58141c8011000510302c40d0900040c0300d46d840d2001103041c100042d007200418490340307844120300c07020001d81b401030104803040102c02c1c0c0180505ca4580c0200002000030004201c1d00d0362403940c6940000ca880041c09048801c0e001002800908502c2c140c40203440c68000345140c003051042810440d0b040e60b07101c10009140c41d8084108440d1001c41e414400114040e811010a10390748901c0590b0003040c0100d4041812804e007403446042c078005a00043c400c0d841140c1c00401030b6001a0708504440c5044000000c805403800c02d18244407541c1c0c001020750000104102c1540101c4015005845d440d507102040c04035200d84403600e0410516602e260b50820b050b130551103c0d1114015410f43c2d1020f0190040f140342040c031585016000d8480520310f0b05151b400d8488598108035001005c000011000181d516603100a0000c0c440d9000d150b0140415000107094510310000350b4064101d0b500060009036074901000b000000e80c0d015480c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 604993615 1250 604992365 604992383
    0x8090d0308100e0f040f03030f05091606020303060901050d0c090c0c03030b0609031c0e1203040302180415020a050903150402100c050c04021b030409022d03150102031306050403 78
    0x10a20220f0028010704c51501040c0912070b40d110341e03c600f0001c0c000c40c3d004504240c0c60305003e4041c59011b0041501920f03400b4010100e44050035042401400c0d47d030405070841d4418010001035651302198541110000d40d42c0240e241d101d42801c09909250782c0001940e01c5c10f01500c0010594064500600c840c0a507404001c6c8400d00410003406d485429046507055210480c6000602100d0403100c00c44110350030410025a4141c000c9041c94201a8400842d40c0011504000303505240f24203103804000d5400342d0102d407405a0b07450303007e12041d515020b003803039001c154113840c103029000301d80e042d40004003155044000072032140d0005904a5040340161108047d14039074a014070300303006409500c207014111a0005100b44402034200300260715000f651201e444c41c2002c402c1c0010310140c029400c0140c0e4603906119214140e110301c2810040031a501183e1100f0300341c108003680d800404491070000c400380c00300c004031300d140a40075003200855080100062a240c01c40004d00803a40300d90040c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 604994865 1250 604993615 604993619
    0x9050d03120c0f0c02120c10030501030605100b041202011b0501020d0605040513060b032b080c0f090105031302040213030204050a020702090106050a03291c05030a0c08090d030810 79
    0x80f03802400000c0c118010643c885150380061a00046c4100b4420700713a012910070024500001d4091500204a240841da84000600500669010b0307641c0c00a24130b49081085d0f443e2a0800350a4861403007402008030282508030116841004101d40c906461001d24106100074207120b07000b54810520340d00018601440042c040c10140100e40c840c02c3c48510302c80c2800c1e03e645866000c1c0125810190303040c00340b6400c1c1d10400402c41541c900e008100301210b601d9400141c80030f0030748640a4648002d10f141445103009a8440f0400c5400203802841c1c005d8a030703110042d003540620345002000b5445800480c0c00d80c1c19881401009045034000c40b0207101c00c1d12001c0d1040d003244500748002e0341000b103d10040c40320f1800342e8001c0215561600e00011291310444828621050b2064820801d00b104c544210581c64005080e40c0441a0482101d140e240355980780c603607034451001c0103400c2c040500c0c01d103c240b00080d0140c8880100140040d5401700d4a4903000303018a0084900300c8400001140c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 604996115 1250 604994865 604994867
    0xe0a020405100c150e030c0118050f1515030f011e06060804020904030302070203030d050405071502010203100611010b03030d0b090c030c040513180b0426071209050d03120c 76
    0x185280d5260804d200304400c003041d40c100806000e0000b9407203902c0c4002c0211580981092061200c400c202c194013504001442c9812414000701c581c9528869202407180c45010304444006a0842040c0c0c910b040e4804060001c01e0400302102c0300c61800d0351078083c6080010700c41c07510301120407100f80c0c02041116141c000944114000745c5000e0b410844400000300024001e5000f0804580020100c81c01c1440341c103080b2040d160200c50403590760304580c2082200100d014141000100d50b40001c1d0300f10325090b500100741ca4031300c0c0305010822030300344148028803000313502a8040210150540340ea60386c040b140070019146800380b040c024203ea000080c515500b0704c1c1540e000300303070b00d0f8011490123150100300b0402100c03160000f541280c1d41e0a5010400312920280c12981c0d20a41000a0601c0d050400c0c028845020b48118039070880c010714540d4000c1a04102e8586551101c82c240601d00c0140c01110070b03801c01d0b00a160400341c094000d40034950000c0c0d03040003846030002c2c14005c2c01c0d98440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 604997365 1250 604996115 604996127
    0x90a0f060b18012a0f0c09061d04080f0d0f0b0609060304020411090a0b030f07050c0601033c02030d0e030c06070614070809190825020a0b0a08060405041e06060e0a02040510 76
    0x100300c030701080fa00500010442049c601843c1c00c03d0040d12010b00340541c811460449910042403903508958072008407528912038080d0100c1044110351407420209210080b034610310008000071310490344d0703110032003d40c40003a0a1310b44080d0b0127042d41c400d80c4e40b00d664060f040c3d40705030b071042580c031411000509840e01c588103d602040d050400341880781d1842e9502c58034034100c482c51084650b07140c09011150004441a1a445020043c0c40464aa65801070504101c03100c040300f42000300125880380f16403400213804100003c2510780e07503507c40141c10b21400800c1b0000741c0e1b104040f9080207004250358044851802802c010041e45c00044078185020645c0342c0301e0030b005200c550184581401c501d01d07001000030300407640307410324681b031283da002441029490700060305500d0003040a0101640c0300f1040d50748000c2c10385040003107045c651280101294010040d040040e8209064010000281c10030b00091000d0b4a00e8003040c1441c10117079000e500140038041c0240070941c0717410725041c0310359 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 604998615 1250 604997365 604997369
    0x5090105061e0c030d020f0a2006010506091302030a06081c120515030a080a12093216030b09013305090a0f060b18012a0f0c0906 57
    0x520020100c50032100c1141076085000011101d000911174410044054002000c0c22444003090719a2034014400c050400150030702503800d1015040c045401940001540505441017140c0e07040d22a10306000142401002091030081c55002000340b0540ea00540c01c0070f01511640419030300c1ca0840da0001480b0850011005000038120030745102010310190b00451300085400d210004020031140481c1c540540820206e4010100050781c40845034008140c030b001c110342c0401444400741079207410018840200c40c0032000d5040c450b108008080c0e4101d1140040a800c050b54101c0b4800201082a48014031080c0c1d080200d11000500404040c400d000304a68a510701403100c203000b040300160031703500b8080000082c00801001c2250740d14035506500c035044408000ca004e6500050803020380d82540e0004880307060900c02d48541c040349040307000c00010203281160070184800a07200440408501b142041144480c0c80c0047c03000443c155450320380070319820002180c0d80c240c1e07082203332128 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 604999865 1250 604998615 604998637
    0x30c030b18030a08070305100902070c0f060203070f021504031a011a03070c150f021b070501030605091f0308030108030a02010e0601080307080c010e03210901091a0403270509010506 80
    0x903070000d03280031b00035440580c00c440b00c07160b9086155200d22600007203034040307103042d10b4002048d80200111400c502024029094900c003950502d403080d0796400d0b07207200d211710007480350344241e00f11600b0640d00400d4030010343d0040094500ea82c22003080242c100307420300800d110060500c10440d0520807400c112809000165a90040404141c03500324031481c1c40c54107402d019440c2d165071440b051070b9001038001e880c002090540e140d05065052841c0c1419588818140f60500b002041590380d00c0460035880402c1c003c01c001c0d49c048050f40742001000682009152020120001c5800ea00c000301411003040d02c2e070000c21048071080d01c46580d540e000d10440b0100c0d4000c20031140001e00b9480900300c1100d00900105030400c8540daaa400c40d0880302c00f5180c0e4002c0782030741cac1046c2400d06007030300c5d0861900b9000308250344082d264034030400300109050008041d501c010400309803250401c280d060b000c0d0107808140036401144201d42614a12515104154000c0046113900d800340c00c4940001c0c01c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 605001115 1250 604999865 604999877
    0xd05061e012102130f09110306060c07050a1206050f0c03190f06060e0316050102060402010e010c0b0c0d0f0e06040209041a010b0325091806030c030b18030a 69
    0x1030140111000c40300865102c40a007042104549800071900250040c03c941c015101300c0141070400703424910840d5407081d01000c0c10920880e40300c0e8400000c41e42c0042d026229165258050480d062400c141e550201e034110130768800010f200504c00090501c07503803143d04103004980300c544121050841c151411206480100042600c9001c0303a01d01790b400c0500040085410111340713502c1d10440b0b40640c0f0610100d040c0280703e503070914050018000d4070b44038882c201c3d446401c02c00000d5884000800080c18040c04052203422a80640000d01031140d1020310783e0310a05c0d003501250750342c1e00310700518103d580c00c1c005540603d2045000b0f1000154440c00140070654541d003c00480c2c02000d001078036103260684100101c0c46542e034003a8040d100e8004466901e04003229882207100040120324800100c030741c030000e40c113507212045038111074100030002d02c034004089442c0000c0a041d80002c000c1d017040d2800004104401040038800e2000d00032015403120a0502d041c1c8030305c035220001c000210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 605002365 1250 605001115 605001169
    0xa09090b0a021c020d02040501021920011e0c021e010804080318030d05040b13111e0a08010e150c0d0c0909110909060118091a150d0506 60
    0x703001d502403c0c9294031010343c0d0344482c510b10b400c1812684083c40d8040f0464000606020035601040b04284960802900c213107e00c00300c0c3c0301d6140650074200910780180c5e05001c00861a07201e10034000400c5c440e052010085403951601900d029400b01e8103d00404e101001108011040c0c068140c09900685036900c05503580d0b034908c40c2d1948010000220341d4058410a020407504101902c0500160301d07000510b4141800c0005504400501106000035000030b0880043d0103501c1030081c45405032008002440c0340d0443c50b0b081c2000705126900501c0a1b000003c10701015085418121034003030a840035243c2854100150590442c0c1040030390b8010410405a48840d6010032005041450301c5165903884000200c00c0c1c500c0c44801e6550800c000c50081d507117180100303a680c2c00000c242442103134070142c4103c1040340c0126116096104da965900b50445000c0041000d207850801050421058003001101f000782c2c001c1c1e04a202850301e807400040c03140c2040c0074a00180550b651490310260 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 605003615 1250 605002365 605002381
    0x2040231051e0105030406060b0403200a060509010c061d0a060614060406110304030b1e07020601081b0a030227010b1c05041505010f08011a090a0c0504030803040c050a09090b 77
    0x45c0c00907104589440c5c0e03443c40010501c1a40d009000698451140450080242c1400003000c100b0807080c64821100d01104200b40d40e000001c4a11248080c2042c418090071410150020310700e0300c04041104c1040f00c00b0303048464000c600c10f10207900c1400c04109042c1c40310720382f648070142c6540a981008040100340301c403070300405520340141e1708041240e160984076039400788807180a858001c003540c3d00d4004202c02152400340b80d680041140b0081c060b946c900340300f050780c3d0898804d041c04280c850350b818103420b031104e00000e009180c010b010720001b524042c00d2085011162640c0c0000095060000700f0303814494012500860000082c0b002224500c03080300008100280c000c441c40100c0c0c1c050fa01841e000d60081600030800e002c4a260020315126003035080d030304000300c09010310038041240007a980d5191002604080b001e01c00080b800205803054469101e140c002800d20316021040000b0000d151407203005492043e50911a1140e641079901c0a50f0103403039000300513880a10004002c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 605004865 1250 605003615 605003617
    0x30c0607051204080c0a0621021303061a0906030f0a0206030a18140610120807052104080d09051011190b06190812030402040231051e0105 61
    0x441c052000d07544540e840c2000054141d10560101d0001e0b0400e200c3ca011a01d8100c924800502c1c0d1410111070450840844424041060304d01c0e0480a41c0800c0e14400c00340c6001d5a030000d154001c808100c4012119421820800e18450052144008000094090a011460a82d100c641100a041503c015800c20a403904002e155600e000d0391807800d0382c0307148985c000110501d030044d0301824021031008000c03802c010b4001c001d20080d48045200f004408182d0310306024440d00010413545521640ca080350400a040ba04d56600080c85419070743c022100100800c12203540c04211001c103545050103440c81002407044035401601c04814000aa01a900e40c900100281b81a101501d441043c0c00d035400300180e4054910004480400c100703030070a80b101c0f13520b120580018240852030000c2d166a1890420b45581d9000030120106086480d9501650307000c182e03044000e00070528007003440d075500c025181344650007102c00070700207080e062180b04003400c4a40c0310940d40c81c0a14480040d05d00e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 605006115 1250 605004865 605004877
    0x60a08070509090f0901110a0509040e0c030105040b160207150809010b03060106180f12080a02030906070609030e040b06040909050c0d03023009090402010c02030d020d1b02030c06 79
    0x5111082100d1002943c540451600c60000c9198074001800c000b4041400c48070801c502030208201003081c08401508141034450001d030072603000c5138030001034030381600b002030310714500d0740540c00d007010303c010000b024080f50701c1000b103408010a541640c1c00c04a90326007442c031071034040f1030382d0110505d00a441001000c0d44140c0203400031178409130800110386007840c26401200012811300a050b000200420258004e020800c01130304901e040c03242160b8801003c04004058802c009103405403140213005035801a00d00030b10890701e03480103003004c0c0c000e058030010450003e4142c40310403016291034030425822050143c03405041c1414940041c0c000c000c03250099601d071040309104405a61100200b40116102780d0103000510001002d51400051b0401216900e0b0440880090415103640564030400300480b68044e1907151400107948041048201030b4050080c3c41c0d503416541c0d00094200452006903480810128240402d000c464052034402940f540011215806074a410320103802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 605007365 1250 605006115 605006117
    0x231605160807021c0b060117042a0801020304030203091c0f0206030702070504020f130522020901030f0f0603030e01030b0604121e0326010305031e040503030408070e0a0209060a0807 80
    0x801c80020724000c001003a007000c00c0701c1c4445c0030000c02c00e041d40d01814061040700c0d0014452a18286540d80b95142c4240b0600c2e0001c03503c06c1d44541c40c10464080440e401040750000842d580c0c10b0908000b9102c3c1c0c44500c1c460f0180145154403410104a60072451007160080b4500030661016030801c8016400074025004500c40c20101043d1a55148000e001c1460300c940c40b2607464101103074900c40c602059005500c43c02540c0c0d46d80170100d0403c60b040000d00900d90006036500311000041c0c005000d07513406102400c1c40c0508a40b810411a0b0190050f24040d80b03d95a2003541c020045054a6541c502642c000c18140410000f200804040e180090304c103012194010034074855098040d50300a50560005011041c0c800d100c280c3d81510801110008800320714070360654803100d90300c0c801c1e1501c187d0907001808104002d04070000035540504801800c3d2561079555054032560340a982c091a00b5080f0468081118600b5510848500f900064505802c08068500690f005032000b85080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 605008615 1250 605007365 605007379
    0x31b0309061b0c16050301050601030b0907050d1803020a0b0c0c1b0301140c04140d0c050108090a081b060a0903090b07030e04050c1207090807120623160516080702 72
    0xe11400814040c070180580070030081309955240004040c00c2d1030700503100b40d051600c0c20080d043c032030310340c031000a5000c1080d0802a41c1d4013080e0304200c00406100c0c000403844000040001e04166003c07172000c10303240c02842042900c4d11051210000b5105c0c181c1454003a80c400032180400e180300c000c0c0c0702441c110040c000542804907100c590203a0310111100b1a4100c000101440341d1728084030000144c1301e040d0361a403d8000b841e40c9030303107440c0708a00686041c02103140008260700d8082105030402741d0f20a62440d00d070028041140c4608201ca90f41a819000d040e000650261003403260440b03054140c1c2d24402d1703113032130811040150303070242e14107404005181e1843c0845071036a0007942c0c001c10f20041c3d007a03a038078240c2015406118028018004101d0000710410208600281c948141c410055080c60441400c3c500314004014845010300d03180100c1094081c4500d0780d082e094458900b41c2da07207580c1e50040c000c00311264440c0c0700401400203001c02d44000422075090103440c440384050144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 605009865 1250 605008615 605008627
    0x170604150f03050106030b1e2212030f0c0c0c060e010c1a040c05060903070b1b010e07050a05010228020d0218040c090b0d060f20031b0309061b 63
    0x20300c07410900d03800603545691120310400c00c00c9100d0090b581c4c402174481888a201e528100c140b05081c10240c0005850a40c400d481604d0322203040124181e07a51180010404050000c001303009030400f400b030000f80c68a4030b100240003902418a1a803da544002b80108030350800300c040c0c0d5001c080183c0c1d24100b2120b8000b120008541c00c00f14139400e81000c1403080349103000d24290700c419229421050098206102403459034030000340d220300ba83c4509404907120041d56048028584a01e06500d6030f03982040080040e072807012031306005a41b010760307080c0f079001d85400040e03036a8070003a50050b205d40c0c0031a94040c1f500c1d54a10300c028005100a12031041000300341c0020b6811102c0820401010360706a040c0020414a501f100c0010420a50107101c617090b8040020441040410040e03d0b280d107800005410145036402030540c00c48504461103003d24140b184511a04110b441b102000c0350340808080311094001034034440d048640007002c0342d9548500f8503942d9820350002c000000c00c00d210b6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 605011115 1250 605009865 605009879
    0x313030c0503031e07140d0b0402090a180c02060601090603050c090a030b1602010605060706020310090e0304090e012013080105070201090510091e0c0305010908120717060415 77
    0x294010034014001c2865a10010340310440c03804050090014050041980c00d42d150340682642c7d0f0b403025114000410410301030102d4003030722503084915031140d0b4680c40443c0f411113203c201601e000c4c11410400416401e500d0990390342c0b205580c1d090200780380c1d42c000c0201902c20741046511821078000136082a540c2c401140c0d828402e60000c40d6001c04640400aa82c404040d0440000000d48020712004e0b02c0c150101d40346100381c950107844640c00000041030b50b081c0b141080020300c0a10341c01c010500129078010f403a50400d008400096007802c12003400d03482d050042140402d8000e480040e0b4400c1118441c0d41b96101144040c0e1415031520300140d580020321400303100b0302d4940c0022540d01060302c1d002e8100046100c60b540d00c646096580004194144500fa1400c01c040510000c070810030308000860302e981d940010702a60800b814542045017071000ba081c110049207418201c2c3e2a201c40c141c40020400145003905001c00e0002041d07407501e508044e071041d080c07a8070400768a803070b030301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 605012365 1250 605011115 605011117
    0x110d03050d090303060302030613030915450f0506030603150702010b0f0102160524030709061b02030c15041a04031b0803030408070c09052809080313030c0503 70
    0xe8150080381d51505c0420640c00e080c0005903101c0300c0c21100075a0709180e60303800fa000000a00400211154520300703000031a019500550764668040d088480401503410002e61001500b82d01480c5028100c2041007525400f40500c81601c0c030400c0d000000600344401d0283d43c3e000140300700e5140c800d49104c1028910301044e000c2c012016a80046000c4082d4000c3c07085080701d401c00c0320704651100c450341490070f004410080654004544902c101d00c1e90300f03150725000c40c0300d0100e104200700c0002404640750304506220200d40301600d9080030140001045110746410300030203901070b000200c81c3d145500e0840794409a0140c1103031201c0c02d05403030303c00714800080c140740d0204041000003828000e0021064101e034071250318100120003107080010b041d46134040a40300078242400850386408021070030200300c02070841d02d030302040107142000b99855592803140700c001d84256140412801c00c6070314060410201d8205021030300d580c0310521400c400d8903c4031000d40030446034411020000e0710606c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 605013615 1250 605012365 605012381
    0x1e1b0f060906050906061804021002070e0901320f0604021926040c031401090b0721020306010c0825080706060f0e07120b03060c040806010f03110d03050d 68
    0x8100060710740381204c9002e25003900601130900c141d0000341c50030401c04183c139915901c194181c2d60400c0f50051038a00364035245154001003680209070301000204041540009507000301c50500d0701030500359010300f9801c0210b080341c9184481660001861440406110b00c0d00b2403005040103190513045c18000c0b813200c91001291000440428103010806032801c07070802000c0101003610810f0809a03592140302d45148401040403100d40f0070000d080e2000e40c00185610b40085680b401d42c80c01d5100100180280348101c9069903601c0340c0d452a11440f4800ea0f807043c5010b84421040110680f00d1801c650040c41c120780c21401290340718007011926010188001c2e04ca680d540707480e4402c0d8a04001036824503040801001c1003508200030b25441c4c12101c6820001134240f00071010286855a0f0240c0a0000c000d501841940140003588082d1402802141c050070103580b41640c8503880071828010622004c0d10b46060758200d010345140807e0b89242c2c0600c60f00704940741101042ca00403c2e0b51213a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 605014865 1250 605013615 605013623
    0x120513050f03120a0e060f070c020d061b0906120207020a03050a03020703140a050304050d060216051e0102090609060919090501090c0314190605060d0c1e1b0f0609 72
    0x800e4942c1403d41d00f800711500004021000c0c8401404080e14030f580c0c5100600700e081e00e240d40008117000c1409900700f4120950068104803045420313081c890041c01d80c251005030000185103880c440c0610995030310003550440d60340c000d40940304050000c0650462482641d000844001c00030000c0d004014010603288240c01a207006455420100d11903041042c1c8546e6640000060300c0010b2004030840e0b00395082159424440301044c02c00c08024001c9042c0807802180d0703682480240721001034014511594828013001d07000328003915509034094580300c039800180905c0002d0b03540c54203d002c2c04c61110040c211521400d42900e500505c40929406203d1070f950700e00040c89200298068414040c0c21420188840341c4140000c15401c2c0340209403a0b5140c2c4000031800036203540d03030854402084002e007403945660141e80c0718001805d00d90080c0c030102d1100d242410461800001c03110780518903454002d0440c45050f10700c1da18642140d01160794020f0f41d06403800144842c81071909032805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 605016115 1250 605014865 605014867
    0x100e0603150307150c060f06080d08010e0a090f08032a0c0c01050307120b030c13020903011a0a09150918020f0109052110021c0b010f120513050f03 65
    0x510240360410f10700350050645440b4015544030f025402c000b4200d0a11391040001483c4d0b254102e407031000345140c1d00550068010000141000f81d4800c02c0d0b581a11050000f129150320f588841000300c030050880103200075458240c00700421410400b8551042ea00d1070b010215200488403904600e224807041c14031380d440401d048043c040d0400c0002c8600d0741c28203004e855401e141c2c034064000e603c81c10600c0a0036452340020b00d91900c00703010201030354802500800b91003181401e550080e400092056010b907103480d89000407450440255500e80c81c010b010243c0250508101c0c202425406d503020901d102d032500300080564452190030303107415000c0c3c249101d1002e1032041001010b02c03112410b0400410640600c200e5813043c180408500303540030f580c0e5000491662450a1160407880158a58030200d00600c80c80c400f423400f42c8640d502c20104200c02c0e2241e5006413911a40030002c0c01c00201e0040c3c15460941096001c40d030480d01d5440c58030068401603469619104030030300c9404003900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 605017365 1250 605016115 605016151
    0x2b02120607020708030406120b1807200102070804031203150f0510020f12130e01090e07060809030711220606030c090503123f0702030711100e0603 65
    0x80e040c80800060a6aa0041c52901e0324147c00141607131441706401034856503548142040e99207180c01c03c6449000d80420840354505210003905036401e03200d0341c50a5401445440c414900306108440c419076000c11400e041504580350071310051845d549807010b05036980c0b00d800d0f400c03c6045a40d0001d2144815012000e420941030006d007640704104002594000403102c545040c0100d003040d0b00486800c951030703c60246032103800010040f030380481810303c055000443c4001903a00408100c4180b0300803181200c1d03641c50b04070392002c4200c500f025103800c207000540002d94611420200d10304018401c0000d02041071042556000105152021669900003081134603014081c01341d221105060445180b46404003080d140c01803c15103003200b50340040c0500180c40c6400b0203100060040303801c82940b03100881030150440e1204141580313100200005400700f48004200d80c0c140c0d81c031040304488913209505214901501d1a1600c0912015000d440b25544178040554460307000540c07540034243c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 605018615 1250 605017365 605017367
    0x51909020310030c090b1c0203070b0307170c030a140103051228030c02010c1704261b100504021f27140109030203060c03070201021e03100b0301052b02120607 70
    0x70052240ca000c080c41f80007103010241c0d1300458194102d03484480c03000c0d40c070303a100d540c00c40301c0386107010356080780440d020300344030403412054040d510070460f600081082c6001c1c82c0948005060911000b007150341b008141107180076001e0080c10320710490820b00403440030700b40c13140714110a070700100d01c0c00203566a1620f03049035824000c8511852030f505105071070300203149100418a00040000c2c100c04c00841c0075020140726455022078a14401c1c8006423142a4214114146009000c0c040d60a02c038502041500d1344c010b00c615030080e58001c00f8156021000c100c441c00691841c0c000d4001c1c803800901c0783d95070f2a00a0384a0428105171481c9500e034134200012080040c01840c2c2d114100001100d0600052714000f07917158004400715082a100d1fa41c0400403800780c030640554101400f8580481a003248480c80958007480e10161040e02860726080d1040d030b680400d200301541312250001801e609a20651755a00d03003e1450f0040012004680210b08141810070301a91280d1110003040317505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 605019865 1250 605018615 605018629
    0x6050907030b01030b0f01020a0f150903080f16091203020120041a03090a39080114090c13021e030403020d050708120c0d06140a051909020310030c090b 67
    0x20b045030414044c86c40d50000070340e18500250001c02c000c0ba0100c22209001403003412002d00c01a98000344100b0350245030051695600ba01c0190605c0c900d200411000c40800721106444070040d958003803038030314000c0b1018100a00c10f506400790f560703c030140010b400d2807640d4460025000b4039000c0e45c1d03918042148418945826091314200e02c04c0c0244001c0840204141c4940d58110b084e898040f4071840b44501c0440c01405000544c490a10b1610000c5041040b046c007285d503000003c11405000c0ea00c0c4603403106044030282501e8101c2c500d000c009141540800c0c2c44095071110041c20700d002040d525282e03148048a1840c2c514010040208042d81003000720148662858800d0070410140c1d211069070060188031403001020500103040000b4031410b407400d04c0c00e001800c5c8649079036120000c9030071028195040c00b41c400641c020a060a000c58a05840706120079000015403030650004000e420180041000c2d000685000003c100800a4080070306250540014155180b400708105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 605021115 1250 605019865 605019881
    0xd05100612140103022806080a0b10020717070e15041503080913141f0503070b0304140c06130e01210b090c061308060108030f0a030e0106050907030b0103 68
    0x1d41d034205207450406042090019044035410381c2c541c00700925044104903580608001d00343c1e24031401d03500003215a404804d5030b0140d000400100100c00456003840900e001c030000301c0026a0140100300038802454070b011780d07059150800d4440c031035100c11341c64803132100595880741007034084541f00917586014403400310010484240050790380c1c03650340c45a195010708503c41c2d2140c58900c0040d6690070707140d00449050340fa1045242814070b40b01000230081d01804d81046200e03c503490011a050400080701c0080e103480c10350813400c6649558078890b200e039031104080368500400b14600540d44462010784001007242d00c04904160600103184840a8168000700300130f00e43d482d1101c00300c503207403100c20714158000c10004192b0f900e42441e1854044012441ca401c0a000118106404002044a0151511303c0103aa08036661000c201d42d690144048140038603104000d00c040c800c0c0240d2100e40c104201d00004a0002d070f07940b0001320195411184007010a403120160300e520360303243c854484 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 605022365 1250 605021115 605021147
    0x40b090f250215090c0d08070c0b0301090e060a050712390f080106090509041a15041b021507090312050309010b03010c05090607060209030303040c05011b2004020d051006 75
    0x240c83c002d170303800050282480d00c10252042000003110005e1110030b03020203001d000700c40102a0b0301e59550000744020a025180d40c10381e07000c2d44000c11402016402224003848060351418a15041044084005c143d44015072080210f210701c0120b05103c84000140080c2c407806102100e4041318101a0115110301500004c2121442c0184000b5070003214010549000307a46000340d5a0741c91610410342c02c210000c00d5000c4ca4540200f01da060302143c4000300100302624280b09400b0341440d01c6000d8034841c200103000d41c101c010700c8401144049056030b400313442407070481d450603681e48591800701c1d528258140040d40000c10015107a000740a40301501d04103400800c003882c03681000a0050095000d035501c074034000162081800702d00c2e0140d9a5106004083e00c0e42e0307040500e00006800514031070305020031078040351041001c43c009070880003aa0880711116490241342041c80d45040d90320356440c1c0c8142d0a01c64440111541d1150314800c008000709442601c5c00c090300941303107215040d01c0742 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 605023615 1250 605022365 605022373
    0x15071803170c070f03021309030513081e070e010e22050a03080618010b0307030204030804170d080405030717160b060f040c091802070819030506040b090f25021509 72
    0x10041e280e107904030501c0300c09007c00291100c0d0f940385c22107061140038050211400281000b0500c1c0001046001885009004603031400f40c0b0030941e00d440b0034582c403410150458203c0100a4000102002c0e5031282c07215202ca02600100d0000070045e40d0340d8031040e2040c2d44640b13841d10400d5048001c080d0090000c07134034140c900b50181d0100880301c174140146490440040301082503d070003070301900c01070742d404000d19072079a44030b0580c244603510703100346000c0c01d200321030080c0c5010b03001d000300b240101c0c0c021000e50714202d140c0d1526181d2103080607090f00f40c03d0041100302c3c0c0307080701c04540d11101071288012103624101101044858641c060049106900c3d003500640100c0e00080307144103c4096a220f80f1040201608440003402950303809400b9040c0001c5400710801c80011904408480362030070091a225403060004503444251015000346002d0f021074000f8084540f81c5901848000104c207114041074071480c440c17050b034006c036405030b0b101c5c052140c442ca590f402e00540c00041c05c0018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 605024865 1250 605023615 605023619
    0x9010b0708221d0a050a061a0a090b0d0905010b04050603100513020603090d08090a0803041506031407090b09061f031b080a0e15071803170c070f 64
    0x10016910a20a00c50350300c00019458040d100e200241a200401c200301c0c030005a94070707000f6894030b490411543d111541c2e15010005d00310348614840d03032080e07030041d1104540c01c42d00640c000605a00c003003504004d124106200107070300403181008001c211080c40c800305180304da52030b10b50309442c0f03000d085078803640c1054200060317501c0000e0f080f8100158100040341503140e42c1c0e05500040d0168402030f410503c008200140520009201c00c04400c0a070b13100d50003551141c18054840f012854000c141c0f010410100300828a0052000d80c090689000064540e03925940d400980e06c4541a000742904008010800003580f48180c065015007551010410b150031000145100c4008400300308580c148081410520b00c41ea01ca40c0d03813000c0b007a001100c1080ca000000e800c114080b168820034500b48640714081c08004164070316010500c00c10301d1116280d03480c040c3c45a00074841e89070390645042200002052214021100081b0142c84190791400f1086200d4104030080c0c2101504148007041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 605026115 1250 605024865 605024873
    0x120201030c0c02011e140a030203101521020c16290307030c1701140913230109051b09010f080709112a010e0d05030612010b030703080909010b07 64
    0x10602200c5c030885800030320740c008150251056459207841505911010078a040782c0354065006600449a50075440111551000c1410300700c101d0b6a410070001d01c07041e0320400d9605014080d44d0010803486405414032624485892405140100040017981000400c11480b102190304805500e101108151540d520101c0b801403844080d000c04100741d0388900000c0d01d90b200303140c482d8143c41829004030281d46d5038000d0f10b0814100c444014070880241012444415042c0030003d0202d0740b0040030284491504601078040c0810300c102a595501c034885c3d0800a00107015041545490440b449500120f0b0070600800300303016003101488161190741445001c0c4005502c2044500d8001c010441006501300d0b0740240c010307080307400b45168181684020050300c04a04086583c0e00d0f800820100e062180495a20281e0303490301d4000c40c2d07003000440d8060506610440f1070101001c0040703500c3d400d03400441d180c108940d200369419880440c0044440c6404035500380180714a4060034103000803919 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 605027365 1250 605026115 605026127
    0x9040908034f050a2001020d0c030c030f1101060e0108160602070e0a1d030d0f022704020f0a0c03030c090b030109050402030f010c05090102150f06220204120201030c0c0201 76
    0x100c0d60140501189a00c01040301c02c0120104c0c0e41d901081800f5459081803c0144800d003850481d405400b0b2050382800c1d240c4070305501007445070942d8640300100301c10b46060f90201520511501005610020000380e02002d00440004002242d079111440d0b00d0700c2000f906000103c0d1a1002c0020040b404001c01d950000d850800d540b189013020360305440781e00503031005202c4072103079604035115240600b608140120181040f824152410300c01c148034039401000303c0c42601c003455200c0001d0000b484051584698944c2d084070b000d040180f80000c2880c0c090915048400e0a10000761400c0101080580c180500040c69440b8200303002082d090541d0303064180014007039107008940d140c7c0043c055580801c10385140046030701c000c002c01c1404c50b81c0103107268081000c00d40544110303a104040444031107007a0f8812a0003020444598071908104114942c01440b642ca03011042d92661030140300f0740c4020b000030546850100a000c00903c0007409031801d0504400621808d0a0000e0140c0d030055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 605028615 1250 605027365 605027491
    0x2012d0807050720310b0d060e01050601090f0e06060a02150a06140a080703020103110705150a14090d030b0310060f17030c0a03050904090803 63
    0x200301220599503410040701e10f40a9228050800d0900d51120500c038844101410128441514807103d142482d410010f00d181341d2281c480b41c00d1090715090011354507564810707040c00f80010146640f000b5540c40c0c84040d1031004940703641c00d941d10003d10070b02d907030000400b000a000c0c0d504144100c1d0b1900800c01040b82c0010015401002c1c0040c16103003041c424030803441a0244510040514184030701014010a110f001d8142080624420041d980c0382c013805210031240c4400041503aa41540e0044010b0001015400c00208043c4242c50010300705206845194501e003a14004919211400e0800d888540320130740200b04908050007102d0501003103001d4404030900300800c0740807180300801e19024403e172a140e41149804800b03e83c0340058a05102181c0e9100340c2c03581401407600c41c0c1a140c2c4a181000f60302e40c2e10009004000074020000303001c501c4002000000c062505403182e000c1e50740200c0e90300c50122000072546000d140085104620b811101a152070030011a00c0511607844082c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 605029865 1250 605028615 605028617
    0x10e06030d1d1e21010605033c060f160c0f030c0302101103040c090b011209020a09110d05160c0b1b040b0a0306080d090e07170c0702012d 61
    0x2015110208a0800018003c0b614050400c640c10801c0c51061441c01c200465005215420b0040000f402d00e40010f098411084640c22500301441c0c140f05002d10f454120080090f0058100302241d52540904c042403241d920f00010328034510300001c1245000450340001c1702805084403405011400032001c41d09080c2e854280042c4075205400c090386070804850a0790341c11402e00f485a0041c0d50101c0295019034400e641c0d10004540f2440d101e402e544103104414002142c80c034041176822455000760800c58009800201d8107516403403c002136880c070315010000d201000408100706c940d1441540d42c411440c7d851103100001852006240c060305c000701502403120703a00480c140410b0107000c84004c85510242a036100d98982000010780c208601c1a800711b0700e4040e00041082000c00c4071552503c01d03580d4240c042d0b0030040200c503a0300300508000d0400107264810705921052102c41401282d00800d60341e284c078901d20005043d0031490108010600c00400e0780c89541c007100300a10141081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 605031115 1250 605029865 605029879
    0x11a03010905090a201507111005160804170d1b030e090f010302031b0a061d0d06021e120a020a111207030e0409030e15040905010e06030d1d 62
    0x3620501464080c201901030030a1802003051225400d00151001d800101900c2411405e1541c0310044800c1c06000c41c040e15103007440c01d240c0f8462914245801502700c032800d080e0306000d60b0040d00f48684010600c102e410351000501444980411a41208100d500c14000c04101d00c0c0302d500149504242281c41e105200c00c440b41d5001c04d4041c1c26203041605002d45481c03080d152440d184e421000f0284420b82c028021030712104140e004800e1081020034001d030001c004d86142c1442200c48180d0b00c1c0310131083c0140600b51000c0c50350740c010109100ba004078005a02e4001010350149581c1214810400d102e401300080022185507030803190713102c1401000181c582080e144103443d030003440141a00c2e0360013061500407203010032101400e0450b000c0c0d602c09144030040c806110888007aa031020700420540f4004100324030786050300e1000201c61040300c6040c159110b40c0101594000c1e081080d04160020801645080801c0803440600040c40c2116400c0400c03d80000310301d840c0c1003441d00a00c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 605032365 1250 605031115 605031121
    0xb030405071e0b27032a060d02031302040c020d02212506060909200d02030312071e0507060f0b03030a0203070b0730060b070308060a0501021606180305011e05011a03010905 76
    0x10707da10650705000c443e40000c0d50341c0e2420703400591481a9115080340300305d1400070580001880050b079032890303203840c0d0014240c000700c100003240440500018518245c604106e00b0800342e4401a2090719180d62000811084c9224580b480c265491070b04a0b0503400e18055601c00843c0c0b4641c07058107000700e00120070350b000f000c2c200400c43c086941e04000c2c1d0188800100e00c04107108281100f03100791029610304d2a107891000c1444d500848416099001541c140400008a065548910386070415440006a140031180101381107410002008000d6000800d84100340445141144e6006045240c00803081080000213158500d1010b04010035241c2c507001883d2340300b05903100301c001c0c02c85026159282c4149180040480d0400c42e9094080c003d06280050307194000a40084150101640b5040880c1001070458400069986001d04841518000004141c0c2031007901e82060400281e55041c1c1640501d850031395006920000210008124006007040c3d200c06490541e0012280411103807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 605033615 1250 605032365 605032369
    0x3390d021e0709050106050703180f06050d09020907020a03090f0605030435360f0d08030403031b0c0f0f1113020a02070b030405071e0b27032a 63
    0x100b80c1e5001016003034501000400c6003608440500090b42c070075501d02041c000b050f4003104651100780b0914011000007002032040c82d000354058036844c400784200140e00e014680004144807015a0240d0250700030003a40070605500104802c090b100c031030f41d03401040d843c015000f0200c0c84001e001420021000d0300403905e01000700740d500d202d040b20320042c0070705403030129409200d5400b42840440c00c0c9290ba501d00303100b00c4003481003440d4241082c0342249206003c010300c0081c0043c650b441d0340c4a0502d83d01b440c0004d4555000e140200d029540000340c40601c101302e4150440403100000c1846400c3c0c06040008030f0292200700f00e10f600c400c5c404201c100c685050288107400d0100164400c12561000965000c1b0b41d003d80541d4256038211284079644010101d41c07884103440142598000c0981030181746440058040442c8094454015659a17a01d02c039800307412100c6012a40c00381c41d0f84450302d801c2c04440410199100718017030b00080000d820400d00401c03440d4035070a070440040c20041441d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 605034865 1250 605033615 605033623
    0x110703080a0c05030418140610080a020403050a0b040b22291e0a1a040207081c1a060307020607030b1f0302030f15130e03390d021e 58
    0x4154014200c2e51100d0711042402c0301e801c6c03001c2d040b107201ca181a080401d107141c000801da000f43c0010780100c0c000c00e0440d004940072a401480384031965020440000080c1d0108010442c00340138102100080c01c1c40e2602440300200070307140000c07606051794115011400041ea883d87c80d9840041070050000c0c0500c032001c100720318440f10900300000410004400501c80400c40c1c000b4240f1544c1003103942e04c0100004070317080305101030500413200035003407070500b031640c02008880d0054001505001008105078000088030003610b11040d101d01c81890ba401003140c103502e981504461042c1103240140340295141c05c010481420187c803036030003800e1611091035040e2281d00540c0c4404003006411400b034040e500c1900e8001380c8070300c060700083d4498184420580b0b40c1800405007000c450b00030791000d024181341c2000044a0008208101c0301100031a225160700713000081d0310440d617805109502c4041241c042c03410035074220451861030203501240003641031036211082c81e41a07200c2c40480c1d240c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 605035971 1106 605034865 605034887
    0xc0d030e040509032d070c0f151412180316110a050f011116090c0e101e02070503030a110706051908070516030f02010b01110703080a 59
    0x404c00401000800041d4801250030440e16440b187c1c0c00d9000340d804045650a4403604200101c00d0340d051080b0056541480c0004540c00951400144940940d020b8507120b60310010344404030740c4824034400b0441d041140c0d1a80e82c0c982c082442c02e28001010b85440c0380600002d145441c0034447c841c1a158054034401e8414880c1f001540c2c902110740d9500381d0b84c0500c41c21500303040c8403038505e0380c01000f4450700400c1c0030034503442c00303481700c4c04019030b4078060340103c000c0001254004082c12010200c24003240000721805404034100640760b081264103003c0051740442c0b00d94004448842c107000c00c0b0964650982d1040251802d00c5100392010706282c00d5141442424060f4503a01c1c0e0148450426600d4103009900f0002c6210350340c04110046000d44032540b840c41e609215202c050030003820840702400010007210703620304080c4402070049100154102c4818800c0c445081 = true := by decide +kernel

theorem cover : BRFrame.Cov 604856115 605035971 := by
  have h0 := BRFrame.cov_init 604856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 604856115 ≤ n) (h2 : n < 605035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
