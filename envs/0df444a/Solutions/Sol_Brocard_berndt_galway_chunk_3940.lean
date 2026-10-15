-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3940
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:27.042297+00:00
-- url     : https://prove2.me/submissions/2c1d253b-eed5-4280-bc7c-329586ea6fdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 708453237 ≤ n < 708633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 708454487 1250 708453237 708453241
    0xf0307120b0604060f090e0a0203010f0c020606040624023c060603030301090902030c100c02011409100309020402070c03031e050c0a0b07110f1605030f10020913050a02040e01050306 80
    0x451240c4006040b54201d03500020441d02e01d0391868100759023400065859440e042c0403c0403032105810481840980e9400d480b00d41c0d81d04010003044803914041c01982c483d916960b02c440c14180858411616050b00454000210110030031201064441844032a00c98903106c6554030403400d8490040d080c1444040d0042d441c1c07440c0440c2e52404144203462483c0c3e03c0359200303020354805104105013014003900c10942d441f1002c2d07010301240c2420404900052200446051920191303050300c1403100c0042080c11000c6800c10201c01500b48001c0a9902580c01c01185000503194201c240086110f9111440c2c0320b840824424942242e81c440c2100348002045003518150001c2842182c8507407105c03010740c00e0340701d0080071200c0c105029103040070781c40b90000c2d003801c0c02c6c000204000044c01c84410140780948034020315840341001411400a68015080310b940e004080d0042e008084000c0c00f6849175002e280b00400984000b9a0480304056000900b40440340151070414098507090300248514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 708455737 1250 708454487 708454499
    0x140703021b060c060402040b04021308010c11030304050d050304211e02300f0307020619060e0601120209030703150c0201050c0d0506010320130e07020703060b0f0307120b060406 78
    0x3c4d00000c00080c4255a180c0c20b0070819559a030588900c80c041c00807440c04591603007001402041c05625a00104000015112110100000700c0b8411580f00c8060b25001140d15000d5880f03030000b91084078004411a09283d082003942e0000d075230442c0569904400c0d8800368011a0740d01002c00f10401150401755031041076440d100c01040c2240350303480c1c42c4240e082c0384c00012051801503207412101d601d4000f05200c4074541c0014000c0c01022041c04100c03030810a6032580b03007100c05da48569002604240b0005440398000e01c000f07801402e6083c0e01510f0b1404404c0000d0502046d5001161640f80a90000b80130f1200c0d481402031800c0680001c00013802c281c0d101080c640031b25250844074030788800010300307581d01c03176000000e032001c42210300005c04e100481c807024030fa0040c10841c51040d040501c00200d403100005890301680064000d412aa8215186c00015103808003099420190f0b50302e0f541c80b9528100030607002400c018040c16030001c1c00e40303068500c80c0c5000e040948076034200392041c020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 708456987 1250 708455737 708455743
    0x2041424061603170c1905070f12050409050f060d11040f18031416020d15181e170d11040e180309030304051012050411180c160201140703021b060c 65
    0x11111b00d0502603120219480d22141030408104001d04000d03881008424054008000d0416110703520b0040c4030b00e40d981c06601100c0401121400d501c1184d80002d44041003900b26408040c100140000c01c0300003003020441e059401c000c407081003000b501c01900c02407692164010503409000758a0347e180500345810303107014081c20034019210b0700d041500d84040184d50a40e004050700c0f0901c00340302204110b038076030300c000104400503034000c0c10a01800b00501d44c40c0c0c046054566100031821207138488030345008001e4012005850700d10345d036441400c402c1d401580181004000c5407070085150720705451701ca61040600e00380c2d45415481408041d240d90f8011065800740c40c8242c50030742c1c40b0740f1a620b04641d803046050100b200189004144030034450390040701c042040c2d0542d00300714030400d14011030240ca48101d5854090070303000c0c045c5020b2050440051202c0600500d05149a0402148415660340c0700e404124050b03841800c030401c1c510211741240d0030139042200c0f0305080100e0f11000c0d1b03031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 708458237 1250 708456987 708457027
    0xb040b0d0321050906070e030307020904150605030327010810030b0c0d0507090504061e030b0403030209120114010b0922200702041424061603170c 65
    0xd109809503032180341c061507500c02c0c0c0500303145603090100341018146261603e1081d55914006840464018981c1c2000421901401d0b0301402c5248503540b00d4a4041e260380310b0880f000d041c5600d03070b01c0000f1580d6080016082d4502000c0c528a0200c2440c4040100003500c80000360500c440c07481048045035070206880300700c0c1d03007240c81980f0a9a818072900520300c40c60142000861402c420300a04690190342001550020b680c20400503403a159403010303000c810091300000e1000c4020502c001070350703100d5450f0014032908000d81000341803c001801000c5d0700c0c00b07039241d582d51659042c0d081500c0a40c61401420200d410034981b084803c00300d44103030080e900407200100d41e000360000e2401194811a010f4035540e810a010199180c1d041813103510240307059211b242860203000100300130407900e41c041c854010f2102a021210604081c41450034036900c0d41c0700c0e20901218681500004941100520a40e51845000700351000d030450038002038030704003030400d040c07040400302c1002da11307404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 708459487 1250 708458237 708458243
    0xe010807060c080f040e0103441e03010b2101060f0c051203010915050609240702150901110a030807210e0c031011030a0209130e100b040b0d 62
    0x640e0b6166561403c141071185d035101841d40c0c824900000140000f80c2c81c5003a03050300300d5900c01a0115440303484c091420b166041d90800180c82005d080414401c000203003000c403913040300910f1004441c0b50f40c51150b04242c1c071101407000001001c40022150702d040c00c0d00040e00740142078081d4100311006108008012404090111040d81101400020401e40701c20100088030030f5600d61b1034500c020050700d4805040b0020000e22400031401c0d240140039564824000b41c69151a0040c194488000e08c03125540d1000c0e07032100b0000c03480941c48608244a0b030401000703c2c0c5a030f511495000522315144110030507801c3d080f003011900080d038000b81554101c03446140c2820b2448129403292000051083c0541c605803074485060080d41000c640c00c400414210203a07000641c2a0040b0070945564036101301a640c010000268164034690281101d0f103400340420814031448540c4004841c0d495100b42c0d0f140d07000c0102d2500502c1d5a0003840018034080e1030a106041803480411100b80c4500001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 708460737 1250 708459487 708459503
    0x2010e0c01080915010312031404020d081e0a0f0801140112020306060d091b0e13061a0d0308040209070309020901030b06041506170601090b1801180801060e010807060c 74
    0xb150000c81c08000e0340c03002c0c41340800c1c07040031540d403494003807000c65040c1c4142004c1390800c060300581030f08074000c84d44200e40103018001c035005e4654810a030342c3e218103032424600402ca845030784035041031805045078010a466020407665040380260400c0c4d8141d010401440b00c024008a20382d074009107841950200000240e142e80301e01c4005250f84c01410304c00342000c1d00d80012036040c004812051240320200e0244a00c02d0390302c45151858100d41154010a815008081500001c240d5030020a0080300e508a49401034820000a55400300c80c0100f80d0000b03100078184019807600345012500904a03040401c02d4002c11350100d01417507014030003d058220094005003040d12240c02458150f8440318100c84a6602c58a003e400e9004440c540d880340c020b04400901254010043c61003550402c1a460f400c00340da24404c80813281c84104002d04001c01c290111042054603415100548401c40c008240b6074140305105442010503406850242e0242c14204407494004502032590b50b001258 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 708461987 1250 708460737 708460741
    0x80d02060f0c092407060b0907090302060316031b08070807050306030a0209130b040803010905090c0a0323030d020a1d010c0b07090e100e0601020d2106080102030106110d02010e0c0108 81
    0x2220307070203007008241c220450b44c0000d1440400c1183c0e4000042c1c3c2204507429042a11846400c59050845000c000e40000003007003c200c0007441c0c0d1823204000303100b6240103e00064003d0b00d45404199010484003c01c20303004c04e11403a103820101c1254000703554a019820342c0790038400a07554041803000079000c1c031500700105a890581d44072000e400c54011002242c1390825140c8600103510034821030110510304030100700e50390804100955039100080042e0506411601c0d814213501841059000d0b80e030420016446070304003070001d4030600034503210044e01e034240a6406090b0b80d400c072a5000c4a4180004503103401da0304010f0340042d1680116400302c1070741e920a0141c0d2582003a03004010f0303001d00b078810400710a245514400a0b24644601c054050700c480f401661b40d4804120b068002c500084407111480780766010516107540300160100e042c1c0d90700c840a500720380c8203030081e20005e4001c14488901071030810000d100040e0b644000c11041e8480c59005031620708541c00a41001001c7e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 708463237 1250 708461987 708462019
    0x5270319050f07082701080a0e0309040c08010906060503041a220605191a010f140c010b030715020606150d051302041a09010b0a0c0507080d02060f0c09 67
    0x700351104031040c0c12549580b08210305081c0c41075008290030109402070030414000c121031080280ea0340c50f030182c4550300d154a0340c0071008003900d2000f01e98001880140601d450982c0d450050050654594640c88407650605d540b14090b80c0c1250040c00070b006040007813200240c0d0051015410314005000c43d0229105c030900740c48004201e00355120303070041003144402070280550219000307040141c918161203031045081c400b511501140e00c00d002e50403440c1c0165035406000312001100e40c5103020078400d401c8480303001c015004499807c80c244e5681c905001c481c02c04105c20b1000d021249503405491500780300c02580c44a0050886004894911081c5012482c043c2616030060f0320600501684c6400d0000210880c50480c06910950601171501040d100c000c511205665024100040981c00c001c00e03080f095001c03c6031034080290103c84140403039003d10854004d021000302a01240700c45950080c54500d01500c1d40308810285001d10108400c0b841c2111803041050368040c2208610302 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 708464487 1250 708463237 708463247
    0xa0c0515180f040b21010c08040f2004060e090d050306090114030a0212030c0105100b0f0f0c01020c03120708070912021210020c1002090a06080c0d09030305270319 72
    0x20003854100170743d131070400300c041c900c45034101210b22904001c004000c00740e90120342c0f02c0020781c2c024240b800d82d07c4801012801000301f8030100101903054103003440790b000104044030300b554040340c14140100180b0440d003109001818401c42c9514002c0c0c1107040a8001594400d810300c2103196001c1050803c1095071824400c0c00c01c90340d0001e0191207401c9100210907140d07800351501a900b94a001700007180c4040c001c482038207644038a100642042024040107420750f01c821424181100c080c40b01001000b824002040c4541600014648550b40e803030201d072110b00041d261906000c0b10302c0820100992100c2030702c0444000d9190f003107200e12a80082014540f903421440c0440c01000180820820250001e100480b0040101c0b0400c01c500d010410886c02075041c1c142d0f000c9050782c001c0000d03512941c81c0940010300d4021551600c464290210f0032a0007407101140443d44a400f0801011281c030320680c143c641d400341c0c1400d00401043d8254076441039661400914111041e130443c22440382c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 708465737 1250 708464487 708464501
    0xb0906100c080703050403140601031203020a0309050304090204061205010803030c16060c020f10050f13051c090609050303031e0a1404390b0901110a0c0515180f04 72
    0x700314103696910b40f90800400d01e610500058400201e8614a0760081e440001c01d94100c94100001c000b2102c1c0b82c4204a0295101444c102c04164480000740042030085c40100001c0080c82d0005030b4035494894090044841d0086e14441e641c68400100b0400f000441202ea00c00c400c145020765660a40f01207484000075120064010342c548080d0007125a00001d410143c400c10500f10b50120300a06400b00503660b003107030740d040030007020030208013000540d4040b2101d007031180007510403400c2d6001900465071820050040059030304941000707880d42068000c00130705000c0d0003441c654904807581414100c845a02d6800c8000700c8070003d82c0107015035201a005902c148850042da04040c02d000342502941008180d84646002244841c5d125801440042d00740482481108520340080c80000f078002202c4a81401406006654902404e009143e410344c801c81c14410064240410f000d8604c2c0c4907c03510021031410001c0751103404810302020401c41c1d0885d400c0c219050312030085000b502107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 708466987 1250 708465737 708465743
    0x6030b13020313061a01020a110607150b100329040e01020c150601050403030219051e060901060803090109030f020a0b0703050a020d020114131b080309040605040b0906100c 76
    0x10100030f00c000e8802114200345140d0103580e0074025100d580c56080c02c1c040d80190046d0259220014174070004903603a03101205060010000c03420a2070700c1d2545030480c0603120b0351503a125541c140b40d00d103d24010300f011030a42c406250030429120b00d001c6d20101c100c6649044042807070742011030007865955401501402c00420002d54450707280d142c20179600c03a5010460311500000c3d0000034444e52040064a04407a016402020140a030181700144d41b5008030013a0ba0501a01ca1149100b00c0b03442c04145a4000c258028082480e0180445007107aa940d0046681d6401c1003001c01d003140c1e4050400e400f0350350040030340341e540680d500c00100154090340c04036000702004514030040c941c11601401035000660203031203044401910403400c0b034050421070311341c10707003108040b9002450b0007201d2003815215180e020344110340c0f000d0310000184964003120b50790344001210700144c1014010306000f04410781d81440f0b4000030340c0c00a03520040060206005907a0381804ac00d840307102c0d804441031150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 708468237 1250 708466987 708466991
    0x8010506221502010c0e061602130906023903040513140106050a0801080604051e0f1b0307140f061615050417030f0711070315051503061006030b13 65
    0x904882c0640a02030f4405500c0100c1c0355540d074002d9074280107046442a403ca581e0340300040d01a0750802c038020801c81c125440c05951102000000780d042d100421400e076400704904c0c0e2070900343c010007604014449a1010080405074805241c480010a8401756103003290151101f0700c551f400d4100421581e000c2d44940c007894400002c2e05a001402083e592a4540d0781303503d2aa00c40420555401040d02d00a200d43d20202c40004c0c0904800b070070700403000121069070802200c100346d02d480c02c4146d49001c010304035144005010340c50704001c504014644900301c1c02c0c43e0a050707000a48801c1e9404460390140d1030000c0c106414005404100062940c48a00001040c0244501c0d41c011f010484088030fa00600f950409035401600c0c040c0d0340b103140d20b07025100303440c4d655210413501488440300d601c0b0540308240011001034030741b0440da0240d6419850008080c60014810082095200c0149010303411800c28403015807042d11001080d10396034180810443c80000100d81d025400070303a0b91146074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 708469487 1250 708468237 708468269
    0xb130203070905013609060b2218050a1203110f030613022a0304170303040c0e010501020d0f02100228022d10110a0f0801050622 57
    0x500c3e8055416603052032002200e14464078000501003005502c001c040d196900c410b0301d44d5150035040b10000b00c1c802c0c0c07030104e1820205408140a641010010420650410303003280c01030304d07580f00c0ca840b80c02449040074036108040d140c3d0f076221692010040c040351228568403190138065000f48100034000900140c2e9400d880090b880c46400070745000d0300c00d42c0c0d5034401e0448101ca9000790b032980c50a00e0300c0c0c0895006240102e90704a80600c441d07145c107000c1031200280b0515003200c0d054002c031501d03002c0d640d640b8080c0740005605500d504080e0340c148a810052020743d82c00680c0d08502c18290900030084150040f080e481c00855280800303c8900005000c9000d042c480030b85044e461100c400020300e4001008240e80700c0d45041c1e100d8540a040106004c43c030001200b10440b500c114400b03490b0404900001c81d0241d43d15020f6100c0365420010310031403102e600095241c075030002803030400c1565060500107109881281140004034000c04150302500389107074101e10042c4103160501c0400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 708470737 1250 708469487 708469499
    0x21e07140a031707030212070c0c0f08070e0105060f09011b0f030c1a0f0c0a09050301051302090109020708070602030414070602011d060114010807170c09040f180b13020307 76
    0x1003110704112a500c3e0540e0104009600034002d46146504901002c0026501c4e10400c076680905e0200c01d0320304001003840001d0040070840040c018084502c05052a241000c1c2c3c8040c1d40181a0320403401140708110700c0180078842000c1d29502c803400d1a1040000a2965003207008280801010b031005a04071920020550040004500d45119200210070201181c00c619402501119203602c0d001a000c0018a00e844840040c1031800050400401540d102d0000c00d003102d0b800c0b10007800a030032400c0c10000b54500400d1582c01490300c50015403a026807643c0309400c41c01a2140201039907004400320b010006903600c0d100110078090101c0d1109a41ea02009029200c440304030b11582107190600384c0c0807035000ca281030580344880c8080d000580c2685c01140c02410042001c0104205003d20b540301410010700c10340120405e03071086403241e00140c00c0108a49440200d02d55452400d030b000c40c0c000c0d60b542c810a11140c0c002c0800c0d181c2d40d0750b080240500c1c0740c10700300c000d500d4003541c0340c0440e40b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 708471987 1250 708470737 708470747
    0x70e0a08060426030c310e13080c07090b030604050705060f090409060b010f091d070e090403050406020601050d201f020f061003150e07120f0501050a021e07140a03 72
    0x101d0306c40b18401c4031030201003500c000e040d01101040140005840c02d0118034000c1100795007100c460260321450841648401c069500f10724408907d9030400281000358003a280a4100c0691088024001c5c90070990749043d0750300c6481c4682c3d400b407400400d0f620031007280703103058030300d20500540240303c81074a46c540390005002c49400240071590741c410030414540b05842c070101f034450503035160101807a48a140102e55000030700c01001c01444a8a0781416201c11035402d0060b031003074444030b031901d09040010f400e0140580005000c0c541e0281080c0c04560000030340808590502e0482260140040105035150400312500c5007041c0e980300c084a14650008039101d80b56400416200281c80f1000340902d8180341e03201c05000030182a40c1e1640e0a01540d01040007c184041222a190f07615690703400aa407e0210030303261403492803098414400d0031301400794000d0405004501d44031921a402e20041d0b1a110220103c0001048140410807017075440203100802c40700315007a00307a403403034000c107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 708473237 1250 708471987 708471997
    0xc0c03120a1409060a05100b0906180d030503040c1509050105071110091a04080307332f0409020a05040308031003050f06062d0d030305070e0a08060426030c 69
    0x217002c0c9800300103040c4a080d1000c08003500c20050700645004003140812086800580c0e060104143e001440f4100d0b9460450408180e48251070381500c070700e0941010b490240c0c5c1540608407003912119080800d651024011056030b000b400c0040d01c0e00414141410b5100d000741c0001d410250184218080f90307002000700c4103c0d1900f0300110006500003000407903c1c003c82c86004810760042c09441c00068503100781c01120300c07001da50a101710100c20036102c0900509051948030175039802c000c1e54070508100541030320b904d08ad008030301c46a100003144000343c412407040c840b085030b0100d12851028403c0003114021504202a1520390601f92002401c130ad069110407540381c49049a603610903580400d071148202c500900c00320800303c504c107101c4144520514800c001103021000155036030340d002d000503a42d50190358009080e160200010f840f140184038154440c00080104110f0440c000035443c1d030059110855040d0540034003054500c4014070040c00a440001004111800714400d001e42 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 708474487 1250 708473237 708473251
    0x9100e07150201020c060a2423040b010c0b09160b0a080106020a0f020405060a080307030c03020d14030a0b012303160302040302130908161a0c0c03120a140906 70
    0x140205403001c400d81c01c034401d1009034142604404000f0300b0066107980f111000174400d03c80c40c01038000c410307425a1084581e403c840342d250100340b83c41c8140c2003007214000d01018240c2e410010800f03600000303062885c00b0480249020700d80c00004141c214244a10b0204903809203101c40b05648488040085070017104136400050010310001860701d2002541d801450b0b0407030410b003c4504030b5000c0c80090800180381b103800c0b00c0c5020303002a040c103081009000b514040c2d87d90142c0c0310800d00e4000e00b00300114a00c502040709014085503510b1180c4200c135041241400c0000390b0403e40740050b20343c00341c1d90134003107000d0a02009440c40d00280b02c0041d403140d180340034030841104030407006a00301c4c0118080607411031900215025409156070200d00f0301ca0103292841e05103681083d140c0d10207810410120303520f500005a01c102119900481600800a04500e03401c0020b20040340e41d482c02400c10007071100d5085e5000c11746012840d0b200901c00b40741840c80c8156494410401c03543c0703c005844074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 708475737 1250 708474487 708474509
    0x2090705160f02130b0a0b0a05040510050915091521040b0103031b2a050a0f0503100b01020a240f06060e010c0b01062a26090d0b09100e07 61
    0x10100c440390034440c03030a01c585c1c01842c00190b01d0811034a40807a0300140840014402c4c02c010224081d960256010301e034404c070760f6849a54080410034008902c501c003540302c0b080d400501049071039540e0f49040c0d12098960f40c00d0317203840d03c0c01e02c20302c15007001e8501070500b0a0300e1038501b8401448555107100e41038a008e92210507005850b0840c207a61001e6007c1d000d80300c44500b11070b01c00c4008100d0340c00c18140030814500200700d41c4420011311a8101d540c8903104e2085405020001070409002d040e544010b80304041240c0711403400042d4a81700d0714000280140e21000e644141004c848034018040340d00c1502c00c000010000304036100a0405014000118040303010350f44080d0710800f00101200c1d40042c1c60141da03460903609841c2440d42c4601d4441c2c101e070300018052250001c21000c1c059074001d00d0b010b10000304402d409000841020b1420180c0c41d8204643c0c00d5940341c501c80c003016140d10080c0e0b170a40d980c1e000d001906204025000e42a800e0600808400c80f5100080003001c0e100c0c1c42c141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 708476987 1250 708475737 708475759
    0x120105071107030302030301030201081807091521060507050715060314060912160f0f0b0106090e040807030c0503030f061302120114010c080c060a05060604060c02090705160f02 78
    0x601580c8001c2c0303100c0200164030400040c801544504242a004070300d620502000d1880c114150f42480215001844003660ba4900005110900b0000c10001c01c06108004440e0003107400645c46080d90b420090701c0191607d001c250014429800c5504941d0800300040081a200c1603074030103841188010b45201e03182d0082100807203030210b0038038002e0f1010001070002c0785000850902c2c81e0080b950040841d0000212803000c5409400d03545480f42c400c0c0c0322044443c0039460718011200040e0884810001c1d060028230401b05030a902c641c10507008442a602c0d1202032504940b88030b486000104940008001c1c4070124140e81103043c0690000c4400d801d0308010b44030702c04128010341402080c8525004010030528600c181e03c940100c00614108441510303035218180960701402e202d40b9a60f01c5901005039082e00b900c14107400001c101d500f54501440d043d0f000300303000e202900203803140711500c0214002500840032651072344840340c01103540a141d42062440310840c070307006900400c64102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 708478237 1250 708476987 708477017
    0x10c17180f09040b0601020c060a021f150915050d080c0c030c0307031412070302060a0c0f0c0303050a060e010f0e06030105101205070806101d01050f0111030912010507 74
    0x11100e0540036000d002c0760400da03202e88401200c80d0340a400c1034154081c0140c0f101d4191101d0006007004140b43d0010b203c0900102403c50710f2103403181c80e0006480c600240c00002c650a06208402c60360b0108011030308a03200800d8265814032940090782c0814003603122010400058094000e404c1305a040c0c4103044442c80034152107000c0380142c2d50381a003049a01303100044148070010720034500300c822260750b08900307807486441e58440349003a07025910405c02c2000c0d030103003400754041e51481842c100a00400500303000c0c1a13a042008000d0a050b12100001c1c410f604036401000180400090460113503560850030000241c140031781c650030160400000c241d410140501030041070032400082181c0d20f000c400351040b110000c81120240a0703d10b0004404204120050003600c8502d00e5070a41423a100000c86444183c2d1414203180000300010800c03a690a44420000381d02800d020440f491901d0310141148900e9090030782c040b41c0b0211001c5c0c00d1a055103c544220f042c2c5e01e4460b59030392898 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 708479487 1250 708478237 708478249
    0x5090601050f10050910090e13050a030302090d020d0606081b0a03080729010509010608090606280306020a09081c0e062503080718090b010c1718 64
    0x10040340d4201c0c0070b4403010101414040980000420a880c0c0f490401300701c2d0000510800c90507506200041c0320741014031010f004c614509402ca560030a5100c0d041102c0c1c1d460a8944040304005030506078049103d481d10380740d04603071000c000d030f0040c81d55507503152502d0424010406406040b09a01c18000c94030000410014103001d16400100f00580407451581c480019500848080358042c40c042164000003504024a50070340042072141070480d0305110900c80aa40c0507403040d02000380c01d800b40546d0070f002040c4e56421480544d001d100b8034041c01100d00d03031650b01008022515420003000014444540d015000c1c008a5907140b410043d901c22901e83d440e03466519800d242103d0130441c0c004603020354403000d04060301520582c1803030b00c000c04804184442082c401800e00000944000301036122002c65030045440c1030089500080660300405200e05006081080d0b40e5a0003940b0107030b009200e20003595078444070b0018024030b000711560041d084101c2d80515060740701c0480c0d000c0d01c0c00d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 708480737 1250 708479487 708479489
    0x906070903032307020916020105071704030807020c032a010c050615040908030901090302010f150608190c091a0a0c0206070f0b0c07021e010206060d03030608071805090601 76
    0x1d5030f900c5181036030010340030180074034000c160500d619040280000685503200d800e84100c0c00c6015603604448501da019007554030082070f010030810502420700f02d412030042201e4010f41c00d031400d28225614600c0c160b10701108c041c40303a03606104400c19090706464045c00c60840701c1c07403607a00c3d08040c03a803a00155048080110024801d40018000074148500c100d000304124078001c1c000320300c042d01e0f40c540c02d460382e00a03604030754180d440c4c4510405060b02402409aa1303114502d003041401c43d102d08034000010203004100820414101080400600c0d2200401c003840320042044030514050700034180911a101c1e00b0803903083c4801070548100100207441c9451010303210a40344600f43e03420130101e94030103041201c240721101a040e012480b015512849003600c3c2e03401c0d41e03070340e01e850040100054101d0b81c01007075210706607010003442c1d90100e485500300d0030a94401e0240485c51034103902030b1103a600040454401c01600140275022440451483c181d810002c1086880c0c1e070301825150407003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 708481987 1250 708480737 708480743
    0xa180207140f0624060d0606081f060e0d05011802090a0204080d300b190807030b060a0312090510030e120d0207060f0504020a080a03080403052802060906070903 71
    0x18000a18803060300e41106410304406841841c02000381030024409401129034684001d1f6194004d02c0110f4100c10550b421201c20040ca0021110351040341d0030075075460182c50100410080c103025140c4a4050180001d07610500a1144081c010040c201845910b002a0320031015400405c038002c03894400c0701d0607100602d02030a82801c1c00d60b03043d47c88041c042e48280707400d48403000c6010041c8085003c0c1304044c1c0071110124003550310208008503001c60000c9264646280442080351002c00581d10003101d40c0408803403120380c0c4103c005009584590300c054282c1d408000480c2d40543d2000a44040d140100c030000c800814009c1c0840032940305a09100b01d55201e220890b462442d5040074282d072000d01e681c054a00f070b80a545c1c003820340e04244d418400864441050104524010884230302034039003c8010840511161002081001c0203040034003403080c0040c0900d032014810308102c100401c0051722860003038903610001d40e5914100c0790b026140c0205070201b0045807044001d0421250 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 708483237 1250 708481987 708481993
    0x60509011509151d010c1b180c021b0a0b070804050306130506070818010608030d0c03021c0e0c09130b011e090e15011706010f0b0d05060a180207140f 66
    0x80c0300040140c07061840d10742c0c4d4140843d00500ba000501d90b11000d019503d450040c001419180030820805d10202003c24030480b811f201c0c10020b1350307034001020601e0b038000211006030020100d001c41d034480f0181e08011002d0000082c000309008080c0d0090040794025411601181d0b80c190742100034542401006203203400c4400801d441c6849180c003181c0111002d0300b540d40649501ca02d06003180c0d2a035201c07a085400109415641617a01e1040691b040000d0805520302454807040451080d95941c4100c000c2e59900e1903101004405c0085001003840985074058034100791a0f4090303041d06010007168200a0a000452106140075087c100c2200091720314800ea810042a107001c0c01422522058900c2004c00c0c9000b07150150707110f10700034030f082c031099003810819001450600703d0581204603080e44e900030421005111004858641841200c001116180c05c000038007604401d80c002c481e64012000c1d6442c225080343d0080c80e4103442580100301d0460002002601d0f0b02d0003800d50011a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 708484487 1250 708483237 708483257
    0xe042f010c05010e03040807140a03050601150302090603070806130606080606071e08030708070908060103170c070b090a050a0503250803040602031306030504110f010306050901150915 81
    0x3501468040c84102c1c81030001207245001249403034655007055004810551204408022000402d040c0400e484016142c3c0d119060454070754035a81c8506209020060302d10141041140f403095058650b03424005240e02ea49003451840140400310503502d2507c10351058019048000040c8155401c0360810744130782010755994001c00c00160040501070f5a25040c000208804400380a44e001130340380b01b00b0240d502d03420030f24402065800000c00703040c14480100c20074844200009101811250308c40007842c120000c4030481030b040c0c000c64524025504c40c12001094040806003d40b190703d80558808548135a03540030444104464410713036030550000100702c44404da014400084000c0c84d124000b41e200d68079140d0910b1070780944d01c031000580012690803240c90750081030b034000300414901444142815142c0c60f5204191404c01441030f6414580096240d0082e0071003070041200400d030624a41c1c0d9051f80c0c1d880300d821107031803400050b070300000822500c461000860700e8810540c0c03644401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 708485737 1250 708484487 708484489
    0x150e01120b130b04020c010204080102040311180103082803050106031a1309020a080304060e040b010c050309092205150702070f0308070606030b071d03030408030a0503100f0e042f 79
    0x43c000c10205a80298081084900c00703502400100700038402c2d03100041e500c1f840c5042030b118400d207026115101d603000c91080d002c42d180d2103c042d03064940140b08640d0b603034007244e16400c0320600480595566501c2e00d41d004070750b64255000c14102c800390745040c0705409021041c114501050b83c0340d55800b0507880c1180032034107010ba111550643c0b010345400701d1940c95503d00391454225500c0340340052030100d01140142054007070100c1042080c04d01c0c0180320f5807035984540340d0040c1c0e80329a014003036882c00144544a01c1c558103041e2100c2150b0800441264140f164461001c108010481115840800d0846100280f80811584000c0a490b8440d0441c0d40303d198580c48100251540364a490001c00032903c101e2003070b40110101c1c1c49059035454400d054241c0c81c101c401c00d180c0702e5001031008100d0000302100b25607640c2d5061810f01c0d80c3e41c0d40c0e036003561080e05070b517040401706101c0b01c607000c600d1804030f01170140103a008600b103030b0062007609100480701e00b100c44032a075200849c100710300103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 708486987 1250 708485737 708485741
    0x50412093606081c110c1e040f0e07060206010b0301150f020f031201030203010e07050f01030b010207170a0b090c130e03070f060b0a0b030411120304150e01120b13 72
    0x1007440c0e1401040031a92044414074007020b41c64a255500040e40e0024001c40d007000158034501000c5000e80354120002000444412000030b09101604034110410603e584603800b20010078811203080040c8840a00500d50741c04a90080002610a0100100304105a0000d40e0704940500c113024005c07d803540d10444118a14218040c15882203a242c99442c12042c00034084ca8100c400c070007022580f46004142c20f440d96003503105000d0b00007410070f20071500c0b035100c400d51100080c203011074900083c0004034036142181e4028101d0300c980b010040703da40c90104860030490701507612501240c8500c0c1e9220f45503400400d02d15480030600c0d10100e001801500303e1030301900348005807824400652240d1072a035403048012a032086c0d445020808600c0c04c406820043d12040c00a5411460650350b8403d01e44c4603c0d40c003030b100c0c030165040b03644000f00800449000d0b1842d42800599034281d00e10103040d041e034564900e8081303040b51800740e0072403040b0700c5540b507503410003052400300616507001240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 708488237 1250 708486987 708487079
    0xf05011103040f06080717060901050108061309140105100803040315020c011b021207022206080f160b09031c090b040b0d060603140c0c1005041209 65
    0x368001031200280400c01801044000c00441c3c03180100740c0f03007402001307203254110710402d10026001414407070507440c3c2400040c1903c00a080c0070a0545510f00011056444000d610908c141007030906020022401c4610802c036503803400900c4140c65110740780195030300d10700032101d0039401440f0810101e650002c00b4005500842c20051408140c00d000e0350964281c0d400c41c0790720004250840c9803883e41046401111132a41b240d803400c0c401103900107404600a0b00c4074035220310407001d001404445c2030344008000c01c4080b040300c46419004054685904528020054500e410500007070300b10032003400c54950060081c0940031001c2c0e840c080b40380c842000500c50007041504070b030214001c200d6800900c00351520500c55901c5110b40003c52094a00c0742d0401020907042000c541e03591903c0e01c85607900310103507041c2903484502c0e11b0043d03450b159021440703001680c1031809020a015458a00b0540d41d0103540e14a811709854800c140782446c000400c010400c08000b442c2c195101d0742c29a408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 708489487 1250 708488237 708488267
    0x1201050f0f0403033b03040b04030f17040e04050d0819050901110d0603170a17091603080909090a050d030b01020c040516020d02190809040f0f02041e0f0501 69
    0x24030404084c1001d00262030b1854a4101c1144d4805c204101400b0705030030340d00350f0381030030021464203041014081442c0502d200c0280602680041074003002400816202040c0300083c40341e80301d9541700101042c0440580d801c0d111400b401c0c1902904901c01d11501d131291440d91071060900401c1c621010051400616441055607500b412000c2c026a0318001c007600000f072038000c00c0050440c2006a401380190741d11101c01c2d081040448429a0040240d40c0340e1103104840310050b94415a1392802e00c1891074000b0b002c8060701101108101804004c1c00c400b100030f94410140e6030755000096610b010705403028201b540f0069010b00080c0c403d07044688141d60603c180c951201c03007140400e003565030980300d5000c442c0113080766410044d4108002c03001c4400c14802880c40b400315810064001c5660300e4054001c01c1c0c0000d1074580e80c0c0301d41e0040350340031140c00e100300480003050850340004d4210340600030360b000d08800211403000c11b00c03c80c2c0c01522002982d041a107880c0500644a5090b032240304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 708490737 1250 708489487 708489491
    0x15050a050d0b040e0c0310090f02220203010815010501020d2c030114152d0a05100215010605040b030f09010b09280c02150a15060e1201050f0f040303 66
    0x6580355484030f0090b1403130400d9000082c1350780500d03e42018100a180581240d00601d800309600c01f080160603c490a150180d0344144204031080c2e1102c542d81d010f001c01610b0500001c000210b080b000103010b005480c89081303101099807102c00481e202d0342c0d4000000c0004981d180345020b280c0c4002032907544582c11402c0040301c1041200860709580080c5540020f11060508000003205480d0204a40c8081100c0800d000141c2401900c100d841c14080307445140503556030010705440b081800000343c940208901b559040e0400e00075580c548501c90000c1e440140d800000f4040e005500361002d50f01c401c0704039419951106408010520300402025140d900c0b00c0c00c0d40420b4861682103809811118082811200454441485806645024402c040c80d25007240311503035008c81d15448a80212404003c2900c3e10b00299010f007410300c42c101003c40200000042c215080008041c5c0c80c101135441402c00d030782181c24cc42c02c0754012543c00b041000c0c10300000381128681d00702c080d84a0310078200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 708491987 1250 708490737 708490751
    0x90108062e0c05100b0d1b12080304050f010c0c02040506040617101413030f0210021903150509011e031709011106220c150801060915050a050d 63
    0x4a40c1d00401185a84000c03529001502e02030010038440d080c003c41c00c0902c10700c45900c8240c0440c100302600d440140c8088143c0911001c408020070b8868010139440205410780e4a860600040c10b0703209550480e21482400d40c48180c062041c054508502c0050300c60160b541840e40034000944001088030341c0c40783c0e640c0c10201d54947c0e8043d44616115049004180000821a000040303441c4595400e000c080880708005071080c02545803d0b900d035052419060b0151105405d9182070200c0040015040c00420103458802c000185000904407540c0e082c012070301c000d48007891051603401615003000b02c80006209102500042421801c0c00b115952005a501c2c0c40c0d06940e07810602c0c00461400000450300c58640e40404140b086000d068050a003a09000300581c40713000c0c001e00194002d200c14625042804840740c00c10000f00304a5103007100001e0240d60003000000c0034082da9000c01c46030740c00030507105202c03114001003200b540c6031035180685400c4280c40796000b18003203260103621111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 708493237 1250 708491987 708492049
    0x9240f061404350c09061c0b041202161d0606190e0a0506031e0a020d050901050f0c0301061b08040803120f060d0c091109031209030d0509010806 64
    0x1078042118925100c0c0042c0c00c3c501c004074603040382006840c0f2a59034480c80e803414081e03407102c105503000041110100e081c1031102e12a46407100d4550001740122040000300070a00c291034150b05820055507017944e1980545003003080040032580211a0002d40e40da401010740e410130300142e500319400401c418104100c00d90852400610401c0344000182200002c1081d400c140707200001409080f0b074003d003103241c400050155141d8002c00a41c04842d4000411000c000a6040f01d0209084480c148420301d02442c4843c0a00740a842580320f5802040028904005180949050b01c4450307a44403c0703806c6800350380203280b400b20380684001c00c2c1000001100d1134104021310106401761800c0d245407500d001c0c1c030080800000d00701e81c0280848079150001a0060b0a4501580c181900c000381d81d4902e444075101c20f01076603400c0f94047c070450400c404080b5403c8060700200c0c034120203d51a103400144207c030640a80c6c1e0025000c44c4a850104889103406450b858041c0d8680c2003020101001e81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 708494487 1250 708493237 708493259
    0xb0a05150319120c082b06080606090105030303070f0f0513080c0a061b02011d1005070605090304030c031227060318081c02040b0409240f061404 64
    0x10b80c9440a0501da030701e084040207103007650071035a806142031121000d0300c030342c41d100786510902948111031110381caa20b504041841181c40004111588104070a41d00c0d07229896441e40b094800900c034030541c2000181e2440c00000312407103900e05aa6108000039011015902c0f1003181e00c1d0380050203030510072801d0911000c0450030080044000804000e4a40010300000814541120080281c1b240b1700c104101c1c284603c100f04668203103400c46140345030803aa5000240012260b0ba4400c40e01081c3d81100b81d0b0001c064001c0c140180710401460700d440d401076a803440b0364800101409043c1c203040010aa07000310388401129a800c00c800d098009941d0300c0080420f01100c503003114a45001405044d9141c03150320343d0300d030203440c80c1d800c1c5001d03944864805000d00ca112501d00c60720305203501c08401540e015200141074184130700d521181c85400090203804202d004000000040c15122050b02100748140c1c1141c0380041845141802c1c0b10040fa10140e801445100840e01080001084c68041c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 708495737 1250 708494487 708494503
    0x7170705010c170906101a04090e030c0601120f03030b131418010915050919240207030c1202030c07030b07090608072f1e190b0a051503 60
    0x242e035140c8000004480154054101801c1510309a02180c10028105100c030340d42d006450180141280301c0c05c0b07500d4140c8540c408c50700404c2407035050601c82042e0700d0002001c2c090b03034005401610305a0f070f25005840070400300c8041c00b41203070044d14100008240243d000e00c003401d201a01c80e0702c11441c9041802e0075500c007c50014103040502c4108240001c0740e008489402c0b007007900034080461207440e003500d801c602c860a1142a9a10000b02d00b40420801c00300c4104c06402c3c402500450070343c2040c034002c403e42c042c0c03207407501184038039036644040c1c40c800c83c1d0f0042d034940c0314840703200c58039100c03041d0141c0b060942d08250f1100f00710502110a0070412070000714420b14010409280001e0000c14070a1140d00050510011005202019401c08900b440300d01742c100742d038040102480014004207805100321140d901640c1030000c5100f840c800710503a0380d030003101210504bd81d00a0f81e1402c0a2000030701078225072201022030305c0486160000342e081500c85048880c218103141c0000c1c284184 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 708496987 1250 708495737 708495761
    0x61404050f01061703031803091210054804090614060304030f05090109171b0f150304020301020d020408030d0e06100608091029150717070501 63
    0x40100700600d609001d00c0c40a04100c02101d400342101c4044580e4900004e8516004964100d420f1400b0f10710400a803030220000a045001480400f01d540d601c42d03002400d10240c1d20704003800100080f000c03509030121121120504505508480c00403010042d084403815242280d403602c441411704010081c20203000b541c04000744581c81d0940c200d16800c1885030071030041106104200209800209541c0001082c0c1441944c440360350b40100d8488000d82c100f10741c050b022080c03407043e0b81000516040090503886114844219503010480c450011070300b01a401203417958200e011080c05409190071902c05000503092840b1401404140e80290304003810681c00440c0813110040180219030b03400001030094180ba040901400480781b01c070303000b0003050290080109907107007400c0001203208403600c0340030010550001d09260b0485c0d46401803401c0d440c206041c03555989041c4240003184140c0d142d00900d8001a42e03a0004040c06020540340c16038028031411010480a016440c42251 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 708498237 1250 708496987 708496993
    0xa060f0c030b0a0b16030507020301050106030603053d0e06040f03080a0b031b0105070204050103081b0c0f0d050f03120103060c031802040e0f1f05012102040906140405 74
    0x20340020100c40748484214441c0110300800c00c00440c00404403000324280c40303a40100380301e46040941c2c5a103e5008025010341c41c0038000a4015407650026054070710500540e9007031480401400002e402d011441c6d40709a250980d002950003007604070120441140801042c05a1010480c5052001c1140c058404422040200c001c00d0752080314540c1c010a06a003c201d401c800d40046542c03000c032172402901210299100c061145c5c00350041d40c0700f00340c0c024814002c0390707100d20749103180750084041c000140c1c01510403644542c40100b01c0700615200640b8640111004404010341c2121803002501c0c2ca001303004d041c54100c107050009024100070b039401e0b80c0441d4517619240302200d01240300c400400d45440600703075410324070040150005030112004219010740c03e07092818403d4448110041e440303203000700542c1c01801410307011681e00c283c0d802c02040c0e0342c0b000d4007a40488410001a808583c0801075401494a039005120a038012030000a00700e6400c218040c3703505054800355011340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 708499487 1250 708498237 708498251
    0x204050405011e0303030b0d0609030e010f0e181b0c0a0c09092003070b0c1c020f0a29041505100f090b0f090f090706090308040e090a060f 61
    0x1040c940195070041c4403480d83d1095500510740e6854088841d40002000c041e00c0e040b49103400c0e69440c010692140d04802c00b004040354900d0b0260610703c860900314040b801c140380741102c050150f8807204080e24041c10516240200c1441c082d4101c00080034151414008458074207030001c210040c211450b9880003c1c005445203080c90a2014019408071040604203080a80020644000311090481c400e00d00c004034040440000e003020340c9600f0a0078100000b003056618070354002120a00300802508038621501112400c0380c880038960807e03156980511040c50011f4070030b5a40c005840324003080982e038183c1002e000d542a01d42510f0580e11851002c5800c440a8407600c2090703044104036200386601854109000c0102c00641b140d000d8469607141c200c801900c0e1000c08041c07120303005122154034a8400781c110942c9600f40d80d080c3c60b9200b014008602540070307401481c107580d0081c441c1414503160031610040f0b004003c1004600e0b00903207030700400050031401000300d54202001e005c9501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 708500737 1250 708499487 708499489
    0x7020f0708210a21060e1006051b03040e19051f05212d01060602030f03090c1503150108100b160f120806032428020405 53
    0x20400d6a00464020b400a075084401918010110b0503420240c880341c548550640500307403071100800d180b11121031030701044004c4e11844c0f54455030548141c0d0300404955103a01c1d111240d00d101c4d42c0224004900104840e04001100700c0301c10480c07070041070482c0e14081e200c1000c00c00302c0c54103a0b880c0c8081d44240004851117101401200c0e4051288400382e481d100f80426240022035041c03103194001d00350f03034214809081e071b000303803500c50440020110780d002100d44603845220381080404120f00e080d00b10060314808818000c140445526074015030074050b8656201c04aa03002515000c5188600008102aa181c241e00e40104518503c29035490b403030960402c013080e02030a500c00381003008074410844050b180e02844401c0e507046030089519604102d4070347c844444c000720054804000c018040b420080d918070f100c1307420b151b2653b50201d20345a003814580e0b2040c2805070580607410600b26071a44031510064154050043d44030545000c011051319100d0a601e0345a030504582c00003018442 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 708501987 1250 708500737 708500743
    0x140409060e0f150117092802011b150b060c0a051e07030305120406020c06040c03170405061b0102250c0501020d050d0e030910110c06030c0406210507020f 68
    0x445503203212800b42041e0074400080111410181c2c0c5e1035800c0300300c008584024002c20180340414281410940d40d1031a49041e02603280b100b481c2240041c61030b58404004200c0b0302c400d90501070780300700c014500c51003004c0102e024188041d0b800b90020001d002d064002d003000c00c106142c40c2d002c1e102801d4608800c40744044901c0c070310884110580d0242c40100006075002045400050045c00c0a103c40d84562810300d02900c20325885a8440c4541030502c024030888500d400110380c410002045840845500020140180e21500703501c00410b10030039401010f03d080d21507520242000041c42c102c801c10b51650f94007200c00410b0303485484450108208010262420050030f42400140040034040310300600314850074415605250315007451160014041060b0344100b40000c03c8081d03110118407008003041181464119203102e6aa0000c00341d050802c2103900800c7c041c03243c01e181c80d062a00c2902c0f6601d1444141401405070071041100102c00d1080c580204516400f91001d004a5960285 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 708503237 1250 708501987 708501991
    0x519090e01021c0c080f061e031c050a0909110a0f020f1603110d020603130c050a09050702010c0306031101030e070e0c070b0109150603091406040b1b0f0703140409060e0f 75
    0x146c4a075401e01109a030b61003481c292a03002d440303070729038500074070030100c1d040c40007248003110250142c44045100c0e540000203441e10b40003e9440c0030b1034903a83d0083c5815141090251100740004006464180d40b00d00014503583c40d9900448228050408826240140c00d4501c40c000d1681030030180200406080642c507000e0702150f0903581d49080c6d4001071007520000e8080040c94170089018000c12144000e0781c0001c040090a0f18180c95580c02e441e0302a003001c58141005520300b504a5864901a02c90344040d0380d0820782e0150f911103144010740c003c00410800d0110b5116440c0001012901c920001b07100742445c0e40c1494640c0c0c05482c0c070b00079000341038000c64601c50078568012008c2c60b20f180c040c01103071250726010480380004d0812000301e40d00841e09441d14001c4030100014004501c030550f00640c0d43c100c8044000c00d0000e8000217a000f502040c01800200300150401300303105001c1d4480c0300c0310751552185802c1da03840716101141c0e41e9a10800c160301040c030410229500d5070380b03199 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 708504487 1250 708503237 708503251
    0x102031209100b0105040f170703140d0801050306100e07050d150501020c1c080a030905060a05060306150619020106081519051512031303030306050a0519090e01021c0c08 75
    0x1a0400381040c00c0028400d01a002d20044502d5601108c13a0105040058000964004150411090220f120366032a9072034159901c010490303c5000052504001400c94031501e1044403550440d41807190103440224042e0030081003000c14441c0c1e6480003400d1040030440c5d0403110300d0051040c5003400190504a41200310b501c940e0300d480d40200e0501e03101000c0303811141e008490654900540e1019070060110a401400d507100300f03030400c005044503034001e9009070022012580141e45e10340200003070034840300016030000d80c24010ba0801c0c4c926814403d00c0d0300d0352400041101074940c41124500400301c46404c070118820310501c44400035003000b0a0004480070310038015840c01024090060841d100c0042c000d280b681240d5041480034402e03617521070b00101b40c40071900e6803401e0040262000f07000f542c0c13042103d03020004031444d002c01041030031030034050f0403507941d85009000c8009280420b0002002d540802c924800c6540014a291002110302400547d00d440428000c0000324010a44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 708505737 1250 708504487 708504497
    0x2203050715020a03030902130203040602030f0a0b01050720100c170304020a031b0b0301080a020301060e070806010c03020703240e01060e190207050106081f02270102031209100b01 79
    0x12401c99a010811004050309428045168100d40c8082901c1c6001001c030892090310220070b11040003102c0d0011030142c413560302c8204441c0c0301c0d09152003c03a0380060155001c075400b00303c084000f81220404200071f0703130002514444028507a0114103080344400510000640f655140c40803c605540c045411040e491075240c11490a9400304040c40c4036400041e22940405081c50382240110081401500c00c5031421616941c1d9002d0803582c480e91104203c1c480d50a01d2070104407101e50200c1c1c00e04c05e018655450304a5195200196044c100b505025011406101800303c0410355000e61410f000003070580b8440404000c40001d011120070841b0a801641805020801c852070b840c00190850b05805108003581886945200203100b8080e00030129403e04000155000c0c011803000206ca502c4c00000305000c441e4110ba0040340720751b20441c100c0d5460382802c0c0c11040d0826000a01c01403060040340c2c90072941c410b8110080200701d0b0040b44650080c84404028461030041c0c0444101c03c1c00e00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 708506987 1250 708505737 708505769
    0x209120c0907050c1e0d0311030f010504020f16110405160206011707050a1202190b040905060f090405250e0105040507020a0b1005090112020904021522030507 70
    0x1c0c464000c0949003408116010441884d240c8081c810428024542e040c21003200c00340d41c4e119519400d1134100c40c3c000c28680003900783c20140200031a8400e5221032200c91032a03080c02c00b00b000a41000d6141c00d031030748051088110202c209072220f00e80501070144940c84a881740d0070402130302e1004012522448818070170322140c3d0f0b00006c000341940d500642c41070704918080e000c00e1401c0c840f0341c812944078120050010b0f200e0b5540c102e0301001402501c1ca030051241d1001c520b00c585116215919550030300700070400400d01c540e4485138009030010510500c042182c000958518400d89090340d013a007050f40300c0b4282203181c9412032009042e941700c00c0900d5203800080c60141005215241c002d80d25500080c80c180e200340002e03401031360701c21780550440c02d2903810031080302c41d680106800307200c503480046140004e41007007a220340d50007401030240e40e0729a801c1c804201c0c02c18900c111075060920240020030840d446c980412010800c910b1074851460401c0c614000c9294825010b01100c140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 708508237 1250 708506987 708506989
    0xa120e030a08041e06080415110f03091b010507110a05130b181005010e0a0305010903020d08010902280e1f021b10081f0b031501080105030d1107080708010209120c 72
    0x950b11b61003500f1010b0343d1a2101d0b0514004044d103110701214809c840c001800018561021000d1400342e00e10030115000700b20003e9102401c03400d1083d5050120307000b4003861002502e640c5240951000c00740c150241c00d81d890002c1020202c1c0031100e20303000c3e5261800e05001d401e0060804181000383e00c80a6000d00b070400490b503203906140103c90410810381c41200b00f0391101c10403400259800070003000101c005003002074030340d0700c00d021040018020000000318864640247c078501003d0140740c002c41400700018109800c1007035a80c1d41800281c0102e03907510342d1070801d900a0016000700e0309036600001c0710000d0610044230707511501c000c1a01507000320b80e2101a980164008181032041c0b03070f51a6010045a400042e184402c614003900a022403100404400786019805210303030440c03000c2d032050064824407000d0148035055804801400030561140100450000060084d925115142d10000d400e00841d03410000311a9000242e485c45410f081c103c0380480c070001307405442e0200f4450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 708509487 1250 708508237 708508247
    0x40501030c090216020303160209010b090604091d0f070503150114010f17150f0102010203071e09030501090f020a0509010321030608010905070501030f0c020a120e030a08041e06 78
    0x102842c80d009074082840b02d1551801200355800c69002021039458481024880c0c048403c800b400f24000c1e03010000010b0140da41c6801e50320b18420040c480c47c00c1c07900300440d4400400e00188250042040b0307041c8030f0702003c0240003541801440030080c0c6223150900d81450f1034850404070a141540f0a00300400803050640c007510710510092a01e1404640801030417034510301104940c440403840002130200384220340c0c800000108098590358034402a44005a00b03c0c08100e51080c04201400d05414001038606d10000f0340310702e1030404039040d0340c80f900c415003103ca042e082190391103c00c945104c191310b071140c5101c4c01041c0890300601190b0560b5151181e0700898003240200c0c21403010000c1816000790460000b81110a00030826903145042c800e036903420621405011915103d8444030a8010780104444484079400501e5000c0031603881440341e105110900d01000401580318100395002e024941e600c900601341c5d26129400c003040039540b000d4600e403040e4618420a01003203480d03000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 708510737 1250 708509487 708509489
    0xe0705031b060d06180207021f1b17040e010906120c062109030c11031b090915070f020c01050301061b020315130605180c1315090c0806040501030c 65
    0x20b0780c0460f11450f82c000110054111608001d020341450408820003040f0341d03005c1c040b034500898200c14103900d4582c0217060303440280303400c000041b8a807400b03c8a91041d40f413100045c4d80b09400e201d048600c1080e103c46280c22a8000b0701c840c00380c1c20010404007006008000207000d42b041d100c80428004d039a8208045110310480051002480403042101190504051008295003007405011071920f00248a0180180300701d80080c10524003050a080c00690b04510100d4a8004494001b40d00304001c030140000b40803019610486108494109200d181140118480d0f02c0302c4160360860840a41000a203083d01e904000003070004000d01d070303440200ba40b108001d43c2c44000c01142d650010a040554a50180c11080784407400e21444072110840c6010b01802458100030548805100d4086110043e412550755402007041c548146401c11005c003004184a50004410308c00307410600380781c1081e40c00354011030768840300c1c550303c03076085001e4030740c0540e0840b000c101960448d80d5400006d405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 708511987 1250 708510737 708510739
    0x28090c02032a1f2307080a0608070611030c07060917060c1204140a120905090f010302060c0a1b230d140c0901031b1a030402130615030e0705031b 64
    0x20700d0110f0700d004119680714401c0303c0301580c11200720103040c464071222114141e8000d03002078038040018101344040d125890030b8490381e2008d01103091038107030200c46500041d1104c070f103240010020781072a01d4080103140024000ca4664811240c0b803c003240400384250203c80c4401c0c1c0107030013004541010002241c2030780500342c0c00c2a426807130300e0409040c0034182050b0034840c1d100d01c00c01c4400b803005610340744000e103480ea0b9231030300c030300d6101c4050200030b440a84000340303540c0382034005000500c3c05d03c02924943c010303e003c40304607c80d10707240d03066900300c091807141c00000c015509010443c0010114170700400040000074120b84524042025060255006001024490709015014105000410390f00c0c500400040d640d50b142d090484046507003000d40600308040420001e03261900310101c1d1200c0380744421040c1144e950f80c09000c8104c606680d03400c015555907a01068554114100c148288d0380c0d83d0300007800707001020b0894900441a04068820b91000c0d0100805003800441403405480c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 708513237 1250 708511987 708512023
    0x50924070f050d0f0506030609070302010e040c0c08210f160c0203010204091517241003060609050a0e0606030a06021b07120512070228090c02032a 65
    0x49140300480d05406103000d08160f80b0704090b14101c2d0f20040382c000c50b01803442202650801e4035251700340ca69400c0c140c800240411988003c0c94003520b0107a2104050000e641000d000c080c1c80f55642c0c0c800740d4014030080c250900340340c2d01c1205495503602500c0d0300891802030011a820902200107400546100710820400754142e8001152000c0d0155401000308001c28064032000d1014103034250040d0141d5031101200500b40d030490703034000900000b0750b405c46a40c0c0c0c0006140034460031301040000c00291500701c4c40c18001001840e64400d100041161001c0007820342010300c01c50003550090700c08400380fa806401840704554011074007400e020783c04a0300503500c0152019500e0804482004002c0c640201040022079407840d516080e0078500c04c00990300595400d0041542900907820040c0d003189032141400409110a4291545d081c01d000190050540d5912600203803607910417441c00680021910324a98020080449890030101c1211001c01030f6500c94036a40701c401e4400c904081c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 708514487 1250 708513237 708513257
    0x606080c07060b011103040f03141c110102090d06090209060d17090d12081803030708070e1f09050f012109140f030a080a0b150c03040b040905092407 66
    0x185c0160014811007001e4070640c3c3e1130f580e0b500c0c60700001c1c525911040d1101c0e04c03141101a065040451784401180304001c0075030541c01864800c54001810040d01c1100c4e42d42040b02407103035aa1528840100c41c0304080c082803541846c1305012646201610380d03030140c115154500001441c102119101100540c0400d071034045070000101150000800a0800d0a440c1c2c0070350040d640c03049140d403288030307100141e001202d1170389200c540e81c0c4803c40b0240700103440e240209420701e02c00c0b591103010400c0280303d4061824840d0180a100d81e405c0740400c003058915004208509002c0003143d40d125090901c1c480c401d240e2942c2c180303c4509101921203090b0b65041c1001081003401402e10030401410803a80c1806284001d10303070b21781c02028503c0100c0c0039400040c019a501d40200c650708500607200c039240e0740c8103c400141c1600042412485400188001314440480c14040c1006103000c100110301ca0405d00c01aa040280c240305e8440c4c640c185403411184c0c0302000b1550f0787c01080c20300e4956480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 708515737 1250 708514487 708514489
    0x1505010318020a060311041703040303030e0d020a080f0408100f1107020d2307120b060a1d0405100c0203090a080102030c0403080c010b0d03050d0b01230f2a010606080c07060b 77
    0x5101f1034101a50701c80d241007003d05042e000002400070340b4480d4a0400c5141418941035940d0b20075403804030300681c8009031080005403c00d014010500c6d20180c801d0800d070f2243c0200e8100301d402d40c40c541c90190703280c9130007401135064007031091400400b00010780b0302401d5401280600c0703d01980581003c014400f1589002101c01c074071000d0f11161001e0303a11180d04c3d8401083d1840f003040d41070351140028030200741c0c7d070704c0c03e400303880110341608000da1410340c00c000948044640040c0709aa10307006040c030a04000c075032801030321015140ca90149d682d98020310200b060301245504200101da00c18010003404e0809181264217580d04014800c1d00d50800d4500c1d1800344c0071440c00d40f0340010344900c1080806070480c000e01500300132594203210a00155004468001d0b001c20641481c09000010140303450540c0005c0605000d19010799244c1114564107850f0140d0740101c00400a500c0d0042c1807a022081c0300340405002c0728508090b460504030354160643c01040d0014011541c1e0710000d03511 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 708516987 1250 708515737 708515771
    0x70e0919230c030109050603120301140414092a03031c0204050d03080f07110d030b0307080601030c0e070c0c21061a0f040b031009020d061505010318020a0603 70
    0x41c10180c00c446401c5454081d902a080c0d40080c0b144d80512820240441d20610f00407515042c28001c2c00a0b060540c0e00e00015400b03420304e69030314680c22656070419160700d103500c0c880203807060038180000c01c25500a82c82940c0480503801d01d40801408100d00102c180d600071040382c0300854840c035240920350f02c10014800030b1155034002903000c6e450410820801da0000d440c60310604a48881101c03513a14010281da00300d01408041c4450b401c040d0849820703030b000b0ba00c12500d2800207011181c00703a4841c3c0510f0714210080e0000e60310031625200420815440290f0143d00074010300c0d0030318030b4090035613600c484c8c0c614600444000c0c1c81001c140090201401c0340800360300b5001107052000d010482c0c0d880c0b500380320303243e2518060051060300c00403505150191020164001c1d00a043d8241c0c024220b00007044000303401c9a110380c0c0480d24401007100740c0910b103540103001d0f1541c1207091a2400141c2100c0403e00c040d00c040c182c0215180145c1d846006000889509040c08901c1c8000c001c41112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 708518237 1250 708516987 708517031
    0x6150e0316240f0c0813030b0a05180a082b02070309060216030b0402040b010e1002030a2a060c0201020903030a032c06011202030a0c0e070e0919 64
    0x103006060701000103840120304220652140084100c8200d1030858000300d98400e410044000814602030300e2000181010b0000c0083c1280514440d15464a030b68070301c081c1281c01c4d209070b00510f46410901103203280c072003000b61404c0704500007000c0070a41a034801c10140524000e5500c07075250103c400610042200d02201c1500000c02c045507070302c4a038075000d04202d459000c0c0d40014410810741e6008844080440c00a0360303040245198641e44690070080980340d444502c80c104541c01c1c007035000755203c003a00b25100c02116000fa5403a00b5440500509620642d1007404030032481008a0000c00c1001e284a100f0383d40102000c50031180b0f07400705a001e0310582440c00d8161000007191845294140d0060000c400304c50a082040c14000d0800c00160074285140c800c250001c078010014403c0308284040d04a10160a80d5080e1003d52580100c685003a07100d803044100450400031301580c424817172038a100003140c400394107007020b0f0321004107881c900c2143c845aa90b031380544501d070140b4006800d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 708519487 1250 708518237 708518263
    0x3071203051b0f01060b0c0c130e070303110d021f1a0603161803051f150e01031101020105040b06010c03170a0c0207060c0b0c0315040501091a0406150e03 68
    0x140e003401d200c21060f5036650102044000d5443c044001c6036804a1004403030280c141d24004101c0140c911040050118501d00c2c245442651246010f003d410b050044400860203511240a19444000154200f92000740340f001150003092060b141402c1ca070f1500400b04410060000c0c0d455403848980b00f042c150748049944c0310380f02004101060003400002e074130814142d41e4100c7d1001c14203041007440f90b224000108a0340000c4c490041d035603403040d14614018044003000c142c0e26214243c000407001c1e1600139024040030100180144800307103046081c071140c20310003084a03103455256038102290161145042010308980001458400c0c01240760414103d4009541c40c10000114001841c40d189800b0141c010400005103a0380603000c013144064100c81019000e940d051040501c5902c01401690b40100d04078030b50050741c943c1e10606010304544040060506044410443d1000d001081a03120394109542800004030b64510b55102450314240109004139060000f800c0444001400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 708520737 1250 708519487 708519517
    0x140c04050f09010c0e03030a080c1318050606160b0a0921020c010c0305070b070c05030c10060b0c07030231060f060309030f0818010e100501090b0307120305 69
    0x21042600600000901605560b0001c0094912003801500c00e0410840385a134160001c3c4500c056040c00f56400796800107060544604d020300200941103001d4440e003080b201040055280b610f2049203100d003a82000c000c0341c07100e04096a0480d072450b80e4005120050606480101244e000005a000711104907030046e103900c11280107110a000c1490500003020041c49102542480c950140c0003107403920b605552924a0301e112760302d42d04070300c0d14040c00b618100310411540c40003040090018060f0b0507548000382c40d000801b4000301003510000c1d0090b44103644100600a130781c2000240304d6040302c2e41962181c0d01c448c802e035205d25064080751251241801c903044526040c00c2244d200d8002da07a610348004040a88541c002c80840300c80c118010701189c04448001d4500d80550303181c591181c8000c11006200d12901000750079102801d4401c00d00360711881c0714101c0c0c0405400303060b000d005441d1007013106030b914000181e602c44487c40303802c124440d150014030900d40b26904540c400290780d00c036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 708521987 1250 708520737 708520741
    0x40201021005061c1b060c1a06010534051e0f0304060c050c0d080d180305040e151905280e15180901050a052e03330203040b04140c0405 60
    0x1c080c04141400b842110030988c0d8034007901e4051a48140b150090b5010703503400303042508507801d030002030f0301e001c079010012079500034000d58101410400e06170740da110390058603141d4418107440301c0c5c81e10b50305c0a2060a8104c1d050a15507040c00100f59012a4010f1405001495403402c0050810703002d24101c5c1e40120040c00714409000198000f0002c102c51a1401c105031804115001c5c8100300c08071006000440401007007152001c14100c258002900900f82080380c088140000e480d203688030340450a80c040d06504000701c3c0f6124001d561a5011035140207210708003008813482010b4180200503841101e030313012848040b004140d41c5d40030180a040c410001184968040d90741c0c0c000c60701c2e840c00d5802c0c034001850380a243d010b51401100c09407000b000e0b810040c035100d103444e00c1d0458500c68043c00c100002001c900f81260b050201070000400080303d07102c8081054910080703035080d0301c5041c010028003001400380d4004139405030b080300d11030394441c026484841c2464400310b8240d80c030030b042c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 708523237 1250 708521987 708521999
    0x1609150c0209090a08040b0f0d0e100e060c0417030c0304030803040c24080a020c01091b0b030403020c04020901110303100f1409161e08040201021005061c1b 69
    0x45040390503008580e115120340c3c030310b181c055a400011100400c0b590080c070041018a1203c0041d0071401030102c8044c0c2001150400e0008480c034101011a04c1d92064420684040d800e00c182c00b68080c660001d011a0f00d003141c00380401344981e2040b10641c9600380301031250500144161034030400c400054964595407410310348440e0300305980c2a2a004500c400020704125a1911071240410700e0800096102c0c0c2e0030310a45005100411803040c4603000c00811100840c2881035658851187d2017461013100c1d51074a030288404e968001200c00702c020014000800c0e000258810311a0381114003607900c807a0513004a03484415050107a0840c800030041c0010440704090140540314041c18031300802e550784181102e403900356541e0941003000d850118000c881034560301c680503081d030304060301c07004400b4003070840074085641c141c8000f40004052004560707051002c809803110038082401681410341c0040c0d038030800f101100d45e0441100b04142c04004103403800c61450013052480704041503580d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 708524487 1250 708523237 708523247
    0x30403050d030b100215040305211b07031205041109010801021c0204121e0807143304060906020a050702030c0a1a0313020307270902010206160915 65
    0x540000d002c6418194000074505010b040703134000c14241d900030100084901c1401c240804041d0054080005c10441c88101114511801c2c1c8140c4689041d140c1c1841d14294140007004a01c080e4084681d0070010180441d0748007110300c0710080c2c0b82e08002100e4455180200410961515107900401c0503800002c0008065003d0f200c0b5480d20a400703022803000321001012441680542091a40420041d20104a00d428003808008400c1c04030003030881640c0b0f908055400c640000c540d00d581f82c150068160a09210f000f00176071400e000f2400604480c0c0b90100c1c3c0b00003106020841c5100e1b01c0025007440b500b40c00c40031001c1c0e080101156603042c0802c00600542c04414103030f01078810300e120f4480d01e0070804564411151111b00b0054201d030003510041d41e55202070600f51710720502e503401c403015076000d22800006020805400c0384143c2a185080246442d04010780380140c64244ca0b01c0140c0d80110b1100c0e40704681050000100540c00740640b48440181c018180703001c1d101c440111404d4200c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 708525737 1250 708524487 708524503
    0x406051c0f1814070b2a0a08070c210807030e120105070e030a0b0f060102120d05060913020d0201030203070201060e010b0304020406151b0f2a0506090f060c0a0503040305 75
    0x82c02c900345000075007a4880e60b850807513100d00305ca444420803601d59010190307011048841100c400d80300e0352400d9480014508031200350241c81000000414900700f04e90143d40900074564003048108003140d0700c4a510040c0c0d880000584003810000300c0c04209403188035903210602000300006429500c003c0c81a00038a01194180003043d43c00500041c145030000705843c0f030340c0d07100c0035028242e034505907a900b1082000e032941c1d056200d64108448481d60090207814800d000440008080c984401001a00032000d840c1120000c100014100580c41e00b0782c0700b1180719020b08015981e600d510100302c3c01020b00e0341c82801500301140003c16007610040045010398001c480074049291541a858264034001d1b5001d4040b482d425540b01e2180c2080380001c030018041d109000c03840c5da01d500c52074104101e09400d1a5142c507654002180c00b5500b80108016180a0f01c41c80e0030654850081070314002c07180300c0540302d1040070030803810a8504000300a00b442d44034040c1c80c1c0300c2ea941c0c0b8006503600c103a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 708526987 1250 708525737 708525743
    0x120509310f021201050f190312020705040b0303030f04030e030a050a1208091f090803010b07020103150614090303070212030a110c1f030609020310030302120406051c0f18 75
    0x410000900c0c0080310b00a4035907807481c0000c02c0c00564600343c00c005c91030b910a10501d8105070b14203c81c0008010a100030001180602000c4101c0b08101e900242000c005400581c4120315203209105e441d00c0000a0301c1e1b0050340c85107405110745442c141610010402c0b1302e0700d5818440e00510780d00f00b000c0400c200165074869031740c0034101c060440c02a11048001ca4085500703a000903e8440040c9240c031919606007604100000c04180d15250b41160394001d8018010819001680742c0441d42c0c58410b0f804034160340c410303a00300e403401d003480206440e5800c09840140d20010901c1256a502801203441065006000300c5840351207a0000c0d4880d0071500181c40030810440c0c140d11031010101d075022950030010441c03040c1e00c0003040740281401c07941e80c40c1000c2650364100818041464401180136a00b40100815000d186160082c501239100ca0402c203d00804d00082044c950490b059860071050314400c680e08100705042c2034000c0407401c0607003203d1402c100b4041c0c5001300030300518040c0e40c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 708528237 1250 708526987 708526991
    0x140d08040f030501060b030c16030309080a111c14070311100b090a050103032a0b0c091207080303010b09130c03051006030912050309011103040c09061212050931 71
    0x55034201e02e20b46e9000481e40003007072040400c03e00054004d203150300c1c0b0f40c1c07504c40d08000a102c8000e0b110700c2c21540158620f800401c80d00d030003200380c154040008100e56100810fa1030034408203c9401440c0f60703426030200384500310220340d450406010b4200c6010303c2145004480c40c114042c00b8035000b5290002903180203500c1c801c00b14115815031302aa5050b83d416848010821051403140c0c04020b013940841c1300340007030003401400040c0d10b15003054003c00d91030001980318940d100801c00c030780100c039919040583c0000d40402c0260008030035681118142095a5182c810700d00104480140d0140700b010b49a2034603a011102e150560301482c05440c0e2031034806800e9440c1c44c802d8044500054000cbd220044c002c0110400601c981c0c02554030150000000c260a0035040540c207180d0010f54003201c00c90140041031080c10040c0c490b0000801c28141881007892007601c403480c030800301a442d00c04100300051003c00c5a1101e1070700707421803041c2c10300c03050702c0400d148001c1c0d220a203203032100e0090768 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 708529487 1250 708528237 708528239
    0x31218070305070e1003021002010e1b0d0b070309050303100f150203070f08090607031d04090b040305030702120307032003010f0509061201290d0309140d08040f03050106 75
    0x440010315203050700da11500405056041000d56040804010512021a59100008801a144c42c002003010b10b64030740010540c1d071302d07005034a4140380350b494075214103200b001400b0b85140d45641c941e40310b141e08800a40302c50740b1074110403006030100040c05001c42c0705c000140142504c0b503604034000c0b619502442d4001a4607181d070009080032200c013040040c1e0046c410b050104034046c20b818212071260846528042540780403402503000520305401044031040b18040b00c640f44055200d044404890800074514590ba850141040190024041100200004554038001c104c02c03e089180b0782c4c07040380c030f91814400080160a41c0c1c10a802450380e55000341c8004040380d403c0d81c0c1641c010f25000d0720b02c0380c01d000520099103801026198000070200a45101e00c0082c0320301c040f10709054914200d010000311035200d181038201d084070701841c1c980901c030340030a41c4028214155403042d00940550001c084c0019010281c0103005810003070001070000d0307441d412001180480c2c1c41344009000c1c2d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 708530737 1250 708529487 708529531
    0x4080a12080f2205010c0e090f07050304140a02091519050105030610030f0504060b15030402060d09030e0907050a110703051b0a120c050418031e110312 67
    0x1e40800e48401c800c01c0304900100e4041c581450841c42d00c103c1d5580c2100580c2c14a444d03040c02d44501c40e030b0400206504081078501410403080b0140e1004412031440c41c0380c201000024a0b034031005001a06485e11030130311241541051020006881c1c000340520214208141e07900d80c5900103503803e61080c1940c046502c000c440c803030b944108880050311180c2c210354480d403c0c0220903644640001c00c06071389607500c00076107506200c3c1c0760107240903d0000071440d41030020304c00071085c494150a04490188100401a0b03076080440300740d101d5640c40452440610b280030390b0444005161954420180b01c20030084607444400b800381c041e4039a40f100c15010046070120380760403003030201408981001413111105500d4503000c02480e4400750050441d0307503031000501040010500204c0d402c404e010b03400c00c064603007070166410314648a00c808991066650740030b4201034540000c00342ca40085185410403a0040d00b00400041060782a20345c2d8580070100000584012038021004084901028076a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 708531987 1250 708530737 708530747
    0x30504180605101814030114090303010603150f1a0408030a02160501091419050a061707050a1d040605130902030106120f030305090a0609110f0411070303020c0c030304080a12 77
    0x40d86070b0a40c60b5407100c0c10310100304000c041e9064051b42643d00e500598141030484103080344900e640001a43d203d50505a000301030754800d101c000d8403000311070414071000c403c1c025028100c4d1188200d6002c8560340b04c1504145001c1c03a40510a14040805c1d902ea009802242034a1481184180c0c203c0769510380340155801c400d203000d03c2d400c2d01040072074080c044c1441407c60701c0051104a4204240e0760307490004014071001e03002400050040c0341d040342c484d84607020302900000c0c0d9080c5542400c0780c80754000c10705000c000106810b03e503061795812050319103920070805014080c1034050f003505540199001b03804007010403802980307031900000d1309200d00d0cc01ea601e030a501204d90b0120300d1041c0c03000c8024000180100402e8010040c4800c0000c00c00c0c4960fa0307447c0d120700701d2541386d41c44031420440805031401c410744c069820040340d00c441c031201c141141c3e02c040d81800c00507116131451607020700e891001c00700c140d058400003a012400d00c2d00007511000ca58410108041025072001c0d003120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 708533237 1250 708531987 708532007
    0x9050c04030201110705040e0d030e010501150e0109150e1516030c05070f1d090c010f0f2f0609010e0c120a0605010b04080127060903050418060510 65
    0x800040502081c8015881642d9511941d180a0121100c1c681c40b0310002d800c6075101099245680c1c05910f0441c90541c241c09a03000881100008002a40c9050a6480340e004180c1c0800200b05110455031050383c0540b030882c015144004003618280c81d144800380100822400c100e2041c0428400d030002e003c003400844501708584110031103090916035096035080da5850301102c05000e03490000c074030703107240009a00040c40c06000c2c05040014048440e025403901a044500503004000350402c3d87c2d030007400c02508540d0b40e00d02648405012441255000c041018a200740800540600000e4000c00625490220001b041d140390380c541880b6075081b1001403030010f040d41c2002c0f9041d800c5260801035210304001e15000d41c0c07910405540c40104a5009030441083e00001090501288909101e8000b015100c11028aa41000c036141d504c5850104400184025210081101010f102e001a50002c1c10b1006c5004201106d0410f0800508154000c541c00740140c0700707140b00501e10540002c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 708534487 1250 708533237 708533251
    0x5070f11070b0904050c0c060406020d0b010e01020d0f0201020408011a030609030a0e0f13090609030914031b190305011a0f090f2707030b07090e0703180206041503060905 75
    0x180c0741004483c180000303403034024103a0042c0c06083c030004103030060a12100384118032a01c40140c2e02c40c8103044040031a0b20320b001141c100941a904200d0a903000112000d6030100343c10014011403c40c07804374064422b94010f040254245404a8070a0314006503540c00f000084040c1e0300c640da0b030319088656a00600740c09000065000030000510b081601420104240150944c42a0310704a420b038401d680c20002c044502594680d407c0040c150b00940781d8026121b010003030102400c4a200080c0d40341000d000081040c40c50400d19034065848460404a00d05074481c02c4030355a41d00d040a50003491302102072803980101040280b41c0c1e1404016101240400a04040341a140c3c500148407010b001491441004038152081c04900c414000400c61003580a0040030480d00314a0b005042c50030240c51310302803061480c410312000c154001e015900041c241741c0012854004c00c4465041c00007500702030b40012002501044200e801b4200c0c4d440c0d0283c9840034800e040d13032011900211002110070b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 708535737 1250 708534487 708534509
    0x8012f0a0906050c032703120307410a12091a0a151701060902070c2d0308030612120313111008060102060c090d0314070605070f1107 59
    0x50182c54002c1000d4211035816004076401e048040142900140010120150745030f4560b113925132928003045522204001c401c00c0c1c9045080a038005864440800d4030f8081c5e10341c00c850912818aa9030003030f080c0704160b00d4507070000b00010032841402c3e5440340701d04100145140c1c0d0340114001e601c0c003405013240e40c00524102c448500741c0b2000c3c0b9002014103821840754980444a2600b508040030308080d00f595440203071b10f50500600582190841c2d880303400700c075006210010100c1c0c1064541002c803800c01440003803460000e000c0058010f0400c0c10303018116800040030007800300e0030000e1441144141ca101e8481440c8541c49591895850700c0d0012090040000a0288130840030090b00d8078803403c84010280001000204000910003072040010100010010550b0b410000150014001c0b82e00d1443d0441c1e54000c070b00a0104c840c9d016050003240301c035000d0341c941048c08031906141c020200300114205208003e14001100d01040001010b66129000c00c203008120102107800c10455 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 708536987 1250 708535737 708535739
    0x3090609150a05041a09070f0504051b0901140d021201080303060307061d0301090b0609100b0a03090f0b0702070e0c0c071403010209091603060b0f071b08012f0a09 72
    0x5220252000400c121800f40170040d4a84444124048a5000b0f0b05800050000d45080251014109000d64003062190303040c04244500b0488409596015000c40c001d81c0780d0b680140b200503600f00c55400441b0707202c0030000440300c0911201c2d5020f03281f9a070b016001207100342d030780e2610711340d81740000c2c1d800715419000301d642004040d001d420481c01e89a901c034503c41e2034100c607400203405c550b4102c4040c0d44490203441000442e190107074409910030100030200400074204107840b07010b805001c142400345550b070800706040c405120b909000990707004480420f0f914010800035206c18462050b45240d004031400314000100080c10399131a00c0058001705540d52501001e00621000c0200007a0076560800c102c515075291800064410300c161543c010700c0e0405618001c0445800c0d500000f0040e5090100d20b40194801044400307650300185e10100c0803d0012082c103000c1003d0340005440c0d0300c1e0002c511000702c90380d04602071926440340d0645030024070500082c8a881407902000c00280150702c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 708538237 1250 708536987 708537001
    0x1140609030c010f1e021608010c12090302010f02040b07020a090203060112090c24110a030e09041b090c080a0b150a03091205040302040b01090b09150c01050c0309060915 75
    0x7501c580710b00926102c1052820100043c071102c01000d07005c0016040000301181524031100b810000300484402000b82c2118404001c2c03502c002c8403548c1c40e042e40c0f11000341050500c01d400902c44540f919408542d20be0f501c1c00031446c0ca6205501c12400b0b00c9171080000b80307a049510a9920416041e1202e10002d00e07a21035110007042c0c41300084510580a030404078109140d100201c005402c0b2100104200c070355000060640b4420034011302c4180d000f400d046000952000a040502c003054030100d1980e151442c00c551130100020038000d8100051200041360721441c4c00605004656480d0f003220794845200c13210648041030000c981101007464a4000b80345000700a2510b8002c5140c00145c81c41e881c1d4a40100c0d4000705c80079000602d000c5814001e5141c01d110310b40c0c0414007401c21140461070f04125115600811240360310441000c11110304001c43c0c0002c4451690b0804003c1140386070004c242c2071035030400d5601c08100d2182c1c00025089400001c2d60300c000301c044005000b08c03070f500d4503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 708539487 1250 708538237 708538247
    0x2a011220070204200909090c03070303051c14060f120a030e06130e07081f0603020c0f010213031403070c0306051008150405010c020d12020706090c030b01140609030c01 74
    0x7030070482e00243e981400100c8600740040140c009054420150798855964041240c0e81c9005411f21800c3c0d00003680b68461590f001039808100c1c1d9044c10140e468085804860072920709900319102994101144c0c08200a551001640710311021500d0b003040140c028240409181801e00d1500c8551244010b000801d009a0580d800f80b04000d09035850401100c001d00c2030f000443d80500103011216040c09403183d000751503d076001e00c0706405110040c03c40210414804918031415041c59030018110400c03001c24444c00700c580c0307104402550b82c0d000c802d0036019003010501c02601c12101200b45000c68450100845200a07009030641036840d0558035100c1c0184805030210114104065001800354018000400d04000c1030350800e00a103010304140f800d44070403103091011500300b040b48404c655000100814400a507110058441906260200050070803000c0601510000c100000403c010101c0c003905aa031003980b00f1403d84012810b02030a8040c104555505412091000c006540701e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 708540737 1250 708539487 708539497
    0x2030a170c040f0e040209010b0304050a060c090b070c091a0a0b09011e020d180819050109080c0604151a0103020309010603080a02100605090601202a011220 69
    0x810a16140c140d0f212035242c10300b01c0b60b0b80450f010300408070400c03003503142040c040740c01003208a980354a10320342a91420348940c40302100810250b595101405103a00c04e09515001e80401c075013882d80d4016505103440341d80e41c075114440d0554105440300003150030b2a808013070365000141840e00d03101e00380b5043c2049a04000b0071241088106040b0340418407001510721040400e6070068034802000700300040040031303010000091915072001c10000c0f0180041d081200c07200842c0c48549140d010710f000c501501912a010f000741d040030840031252080801c429018034854090240301c0850343d1100e40c15184803840b10055075076901030300417540d40250011903001c86800d0000501c56101d41d1070718000c3d0012110300006901c06c4510200340f0010b072061102511040790f102c160b034900100007c111b002007080d1400c1382268000d180c1c0b10300d2000c0040302203d1400c0100500f1151804d40d1034102c02400b00c202c50700141c83c0200d1221085800d100ba4500c410304002c01f11501d02c6107610100d565844 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 708541987 1250 708540737 708540751
    0x1e0c100f0e0111131809060c0c030e01030911040e031c0629250b040303021309060e0604111204080d050c1224180603010b1005090d02010c080d06090c02030a17 70
    0x1c503c0001300003040c42c8940c50b001840790300da19042500505009016002f101f49450505192445810108120740045a2520800c81d00441c2418084000508500808040c40e0080c041c21258680404558101c5004d07580210001101c915500540302038042c0c40008040c3c45440402020f03130001c00d4542e0000803100e1454050021429541d42c5000c0f000040318140c000030781c0850030314130b004100002e200003090541c8007805034608080302103081c0400584014883e0760307a841d020540c0c0558806413112641400d00003240d5140a041c61030155001c400e0701c04c1c03a6444d00c3d0004e04185500000d5502040700c4000d1800301c0c0e6184a81181040122100252000c1080d03c0400e1981e9401250a8a141481c070f00f80c401c0b814603006246c00d54440c03100040c401d000354401d03000c54551080684591000c11580d0f04007000103800180d501c039040d1705003d458094006a0512204103039007141301185c1c075220040109950304501281c41c0d010b00c00309080000e00c0b40c01d01002d840004242d064214074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 708543237 1250 708541987 708541991
    0x231605040b07060b0f010f050d02070201110d0c03020c0603070e0d02031e0304030215030708040803341e21020d020412060609021e0c100f0e01111318 66
    0x5201c1c01003040d2504941d00071a152600e03640e80d410f003402c0c00581001110030a081101000d01500801b030305502546000308000d50b0302140d9507085d6032188a821051095070406e03144120318080c0e0040100c1d40c8030109801521505150581d641400c40450348a031140341e036048005910401040020181200c1c02c0e6403621a50301203400250403915410ba04941c26401580c1c0d4501e50700c1071026581c0040300340c4481c200144200002103402210269010380d20114907592603a61241e500245104080442c440d0040d68140c1600d9402c111a2440d0b41074a58443e140301c0e140008982d4062002481d4260005550780c00315590122030500603643e005000f0409801c151011601008a030001cad4070a500840d209030a88c01072160034421034014000003070040d841c04441344808091650702c0322890202003000120001000d00600c070f034030f940b4414900705006100c154031550002e0514101c00140f254a00f03540910305001c3c14003102c110a18800c494820145014100c0d16070303250800c4074150281d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 708544487 1250 708543237 708543239
    0x1d07110106060309110603040c0e0a06030503030429061c02060405120c1207050109030305070201121e0b060408060703050403110a051c020c03150613061823160504 72
    0xa10a00801c40540381a6400040d1918181071040310310407501c4410340a40b804009000c0072403424001302c003d4650048038221541c0320700c4039000040420f030380094040c0c0030200512041100b000110f5029031485d02c20000b9810201c072803541c1180b400c1d1a04c950006000e07416150581030042c0d034103c0726000a182601707090744c800100d610385a920b4510511900812180c010301c1c07400060308005205420f004110325400c2c81c0029014440c0d81c000034050100114011045a108100e880c1401c40f48500500c450311001d8004544924080800c0c03e085040040385c0c481400d00400b0b403001c55050200808190300c070010240e0060201401c20b17420440742c1104980c0c221f10811810710000c0c031540c01001342580d0300318110700c00044035241e40d08641003046990000d980009840c440b11780d615a078406244c64007000500c601c503102e100320f28424200b10000400e4005c00084500003010700c0801e00003d014004a00900c0c0f40c01e109114030311100c42d01181e9200000e040c41443d038811810725a1410f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 708545737 1250 708544487 708544517
    0x507090506090a1e180c080703120908060105090c270a060302131e0807081606110a030305071101180203010501060e0d060c0c0213020c0d08130b09011104080f07050105041d07 77
    0x40e06c8036811054040e4400311040080007807901b5901e03c1c130782d0140b6184d400e05040605041c2c0328641849014400c14510000c40ca02c60040c01c102d4400d64044c0600f1020356a00c080b01110b2005584511445600b520000180d45030082c002c0714210310102c4540c015550070118204c0d441d58410300720000142c80083d0224280000b08400703030140c6201e030b00030b004209282590b10001c544d907800036010054149020049008005041c400066142c1004285070b5940c02e02240d580304880c07000c10256082090507403007c68183d40c02104035000b035000f400140e13215002561409894003100b50004c190440d140046401303a0702503a410503107841c1c040d144070259000215109007031032a2200460780040c40741d5000700e081100030600122400c01c08030600c0c2c07605844000410454001d485c0c142c001000038500c00003940124400c0b10481109034072280c85845042c3c3d1b07506443d03008400e600c00c006010509601481c2510100c0b8001c00c0c0f03241c0507031445070044101603000b07849941403140c502c20041807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 708546987 1250 708545737 708545753
    0x21608100509033903190e010e191d06030a15020403050102040605040518060102030f1e0301240e100309051614040b09150d0305070507090506090a1e18 67
    0x241c540980c004d600702440d2118140300c41c0844442d0100d5580208034900280305c1c240708601030500141800b1162121650068a8510030075841c1940302c512204002d01000c01c200300c441c2603030b8407204043d24007044100424090f60050b103c00d40e141e4005004140041c00454000ca10300190f0400076003810350300d9036103d080e80c0240e00031802042c0302003802e000b6401d12b0b080c21008002006000e10150401ca030000c1e46074171a003c0322503190f03d00001e400d58010300081d259094010a0b28086a6075a50780c0b0031102646610f0b041807005401442d40411070038032030102c111003224010300315076404000800c241c005081080d805c807000d004202451440000705d000c20802003490051903404202c0c11010002243e0210440c58802d24501c1c0500c64046201d100e00d91921509494004140000e030400303854a0140200c000c01c18450844080344a950308d8102501a25080e9484400340d100e88481c5c00980d01aa07031644c0034422403051000342e00140b60031540b90840940c00346a0541941d40f20945 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 708548237 1250 708546987 708547027
    0x12160b040f0b0a0f0c05030f060f15120901140c0307210e07050102010b15090904050109081306170105130c031506020304150503040203061602030f1902160810050903 73
    0x80c0d40d40b51040315649401d40100c0d00a205d443c60120301d546080011070411010142800b801524500220000d640b03405aa124051581c000c03800e03240e002c12070704090300e458101da90248035401d21920705501e0701c00b40c1c4194000d40d180c460080c1580d6500304100e030f00045a5852507606d07591034401001c404941d1081e01d41218000c0301610b01030381484006800e49440520070f0f4000c114040601d01080400c0b0183d07406080111482034281e00c59003400742c050000184080c0c440840010404502e010580c0ca650440c0c003140c44e04507184103600c0d00c40190003401d21aa40d003000c45a000c48107548200d5000541103410750400040c0401106074101d036416464000d40050b0380f0026052120703c42e105950090a4103c0ca4564554a02540800c3e140c4070081c081c0c225260b030b5030001380c200c1b0703009109482040c14071244043d01d80d407244168844c40a1030801140c01341c05425420002d00c1e440c9034044003603503030000040081c04034421f0424010440200202410301042c0600813000c140401500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 708549487 1250 708548237 708548251
    0x90112030e1206040209100b091915080906280504020301110a0f08061002300f1207030504030e12030d09030509130209100509061902010c0212160b040f0b 68
    0x1119904c0c052040c0260844050070711f40d04050b502c10200002d40e0f00c1011145600001e540707075403124040000036209800b0030340105541c189000180c101141e808058603201e0001c0c40111032482d05d41440c846100c200c0048000e080c421440071901c005415600080d070040c0c4058000120b41e43d251549051580000011200080440e0b074000c1802c0d90200321246c01403012164800b21903045d00c0065540d15040130411190700d4203021000d000303030071003a0300311070031402c01c4d07010f03945040807044a40d050b805003038102d4a0300502c070003044803076110740b107000d10031a490b85800d0940fa075131000700613200c1f100c50500c0c1d1003844100b00c030000420980c050b1040352407080d01d0359915682d1017400c110303d6004442d141a80c45106014680142c2c1d500c54150b901010203007003055982030780c003000c21402d10401e0030101e180251a10b010155550546c00110b8440917982580c040c544450b01d2180b031881a890002d100511144101000c40c80203507042d900b1902c5072000b82c0280b01250794400c12240101c40350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 708550737 1250 708549487 708549493
    0x1507230a031104090c02010b100f44090d05070305183d031505061b06010303030905070b040e0703050a0f0207082502090112030e12 58
    0x1000419422482002919890140a5044414011012445000e0111440101a01c0b601c0300d8190414040c01c4a0140c0380440050001040030000079020305031100880b0700400c400440003c0607403103202e080c0d080c540e090351000c1c41d4180d110405150742c1a0b9078a02034030744024030740181c18204c1c501c102c0246400351164100c01450280100b60070315801d921200140f017010003070840080c6d8018200c90b01e070340c071071152010044034510101e444070242d000750022034984880342108198901401845210340e0403404500c02c007818200718160703131448006801841d02080107201628140307010700247e40c0c0c640c0c0040c3c4490b800040092030a0000e90080c0d0100c0d07070b01d1640405014003803000c5c4028106461542c3d16092070405208100c030001814242099a0788000c1401130110340c00000442050f4a011f6490b56081e0402d10000d50100f002828a40d1000403a080c403040110710380824a030b0010b00e15442a071070b10103800d0051192003022002c0044880083d5450f49d01e605070030121443c4e071001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 708551987 1250 708550737 708550741
    0x7080a03090f08010c051b010603020909010e070501051806090d0804030b0403021504032a05011d1006060e06030a0605041e140402090c09010504030804080a031215170f15 75
    0x501c9480000c25006804980d050440d00b0f0712041d0898101d502c0c1e021054030008407030482c0091203004140580000f90f00c901c04004dc0098240150403480c074940300b0000740c6000c181c3d43e40042d1540d01c1807004201c541080e004002d102450410040c103070000b4007420b15a00351505503903294040c1c0c0141c204540c0500031000307000c241641000402001c040706400544a4180b548019164241c0345034045403014802a04444007041001288000c603440341c0240709407000c0f0b5480e44180782d21603062240f648141422407400c9449400b8504c2210034503282e048400300303003405110640d07000a0429080a0301d80f24000340917100e92103004041400180702e00350902c0950900c100b03403807070031708ac000c8442403070818000941d0b2043da08680181d81e00200359580c0701c5500060f202d500955102070901e81c00484d00060040d400308a0b10321551090f907440c5407200d9606103002c21600d04000c08078089941c44000d111210303401100c0080450500700311082a1011088580340c0108407084803900817907002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 708553237 1250 708551987 708551999
    0xa0203090a030f1b0f0902030702010b130204051c170c070f03080913051b030915090c12030a05040e0c19020a0b06030a110d030302070b07020a330b010207080a0309 72
    0x3085000d101c84103414030a06840d0076401500201e49001b2a16050340c004080784515000f540f00f010342000107000d028400340c4001041d07000350814414140554526400c182061001c1207174002c00e01d41c000d50200d2410011218882c0d10f40040120b150300d8030900c13101142150680c40140000c52140c0c80c078651b141c2122092000341035075040010825810071007070100d101c80d002d24003d504200c1c2c0c040c035600c070343c4ca203292940f4010b000c005185200303401d0360074400641740118800500010540d088402d1a0300a02c5c400e0b44d0384200c01c01c900010340140703c184040ca59100700980c0201c0341000f828106401c00701c913000d0501400303a4440250307010310714003030421a154800c0c69016004030080c00c00a40c05490f00302c840c0001101c200d01c103000941740d02c0c003054020760650348400d820078840207562501204c0030703680e000460010b4a03619840c0462607200588941c5041008402c0310905804080850102c0013911048154a055004442c0c0204410038200070f5061400d01a94840b005a0310f014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 708554487 1250 708553237 708553253
    0x6020702010309080408062a0a030506270105041d250e07110c0621041b0303020618160303181503020a12020c0c0909030f071112070503070b0a0203090a030f 69
    0x1400080c1064160000c15403c41820419030364001d2a608001ca0744cc1e88560003c0c8800300186031003542600c40301c101c4980c84407a800010b05840d800c0c0c8040203440d150620b070500902c210900f45460354400c074182031002078030300e10304403c8000101c10151091740790401d010142e10121011000294180080142c0342010440c1d1100c5580990b40303140b800e5204041891a50000c07041c0429a20a11022a04025100d8610b00d40c040c3c4030f506940c21103440b854001d485100603169034142c010284c2e0711501e0b101010440702c407044401100721600b00e24564013524241d0140c4030406690101344000100a80c42c10b07000707105108290340050351030f0207140c1c0140c0b000814200c0186076502c14800007808050000da0b0406880045500d001d45070340d40b039070003443e61103404542d180c00b520224445041000080340c90303415103800c460b50b8840fa2000f811a50713484245100f05903140e407241c02d0400c80d5081ca0f00c0100f007006030500c103403440d007990075000c504441c100354011144240300345a001d090000070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 708555737 1250 708554487 708554521
    0x902040c030b040c21200c0309010f08011413180308101d060d020d061103010501090914010905270d0207081203040222090c051215040602070201030908040806 70
    0x9040043d0a894041d84101c040000302005030a0703a41ea07846d903031551400f40e070611a800b01d102081a0359855044124680365004140c8035030100c2d0004085420543c01000514180e0386c04540600007201100208141400e4001d8158280c0d0707952008118203c00c03401c24011041d0103074483c5a000e007030010f0494841d04465102c414800c4103030b03a170183e02500d44007405410500460301d001d54080c0a0000481580b42c20b04002d140a1801c1e6082c0405004a0301450407a442602c52010407640c54104405541802200300600300309200148208229a841039810814144100c8001592245a0300c040041c0408520083d07001020326407a0960420000c4040d140c06009000320350510f07400d1481e240009070009125501d800107012802c90040400d5805030803004003409a4100c40c107001855008501070709000b01890307026400660f01c00a0306901300c050f0003941d80f4050743d55842d1100290000c0320200d0401d070300e91a002001c43c80201c060001b03800d0401c0545200e0800040f8000c281d410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 708556987 1250 708555737 708555761
    0xe18060105121b1507050706090902041203141b0604050105100f060e010c0b0708040312050618040606050d05030a090609030b0406020c070b0c0703020f031504021002010902040c030b04 81
    0x10a0b040644480804250121464403030191640c039000008009240140d00f00ba043c2c2e80c80c2800b00342e100901c580020720b80c084070307481d487c0c040f41d003911a88880140e10a50141101a0707a4448480d80020703c1000e10f00902460034085509049803072944a200868031440f102c41a405801480709110007807040582201d290307012008240d20f450724620100f5058443c1d0707028441601594140ea90159100c9503280707a0041e6146000c2c5004140034061320780c25201500043c01c0740b1403a0020240c503100d440d010700300080c4841401260504070741c041840080c402c0300c03c0c5845010000300f540f5000480740c034861040c0040d5468041d1410000c100e0041944102c08011564800300040791280340b0700d0b07401903000000980e5409401507040e1520000d40d111950740d51303000507030611300380c800305030203050344d1080340c003d145060f8074801c06035076241c1340e030203c080300d00742c1ca01080051900140700c1051780180c0c000810240050380000381123030040360a100220f43c039803998080a1030548108108840c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 708558237 1250 708556987 708556999
    0x15210f020a200601060f02010207021332061309150c110606090c090f03060405030c1005270f1f0b01050304240e070f0306050f0408070308100e18060105 67
    0x520b407400543c1c2d10030610800050142c0c20442c512454402c0d0102d4100382c1d000b83c00e4265040d50800040000c100011688075025000704072441a40c10503003a440445040e2081126252140c0c01044a041420f280c050102907680407100005010b4414040d590a521400040c00c10b5820034003401c029070700104403060350440c204204041d80c2e00b00c00700d03800847c0744624a44070341c81000419448000d41c4074660707252144900308000c03c0000001000c0d00a0150280d440035050b403250f441c2550810f480d01070036442d800e8503e0f140c0f084052074503410a11150700700c440c100d80591006090074078406c0220b0152040c1c404060130f11100d8019013945000a1070700c5844c1d031820307884604503154241402e03078561044c00c0707410495180380e4002d8643ca91801003910300d070503900c440d0501c94100600c4100c0b1001d0078200080d4400b4281d001551013140c0001e11a840d1058950b82290340d048000d005058071000c8000c0840d090080c0f4004d9032061b4408240560309000001c0300030310b40308059203c00d01c900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 708559487 1250 708558237 708558287
    0x140714030a17030601030905010e0f0c010f0e0d030311190318050604030e0a0f0603020904060e01060206010308130b07080a090803090f04021303020909031e030115210f020a 76
    0x2420401c2c1076001d0b6000180c201d40c0301d442d80c1d001240680720192000d07015600b8035411000f101c0021600000612003002211082080c003030065074150f100c0003501c00031441a81e1140362505101c405403501600c6407800054059400c28002607070341189441c00f96920020f03421340b100b141c040c0304130003149010f181d07503281d00c4940b0364503240d8540e002403005041000c1200200000d485201c0508041c01c01c0c403401d00c2001c0e4403500001c0013904205c0c81d0310322513814544c1c0001ca034041440040e05942607540036141d20381c25605c6504060340000494207a10600d1880080c1440e000d60141542da03202c0c0140035075690b4075160050410605411410158204000c10b90312a40c0da0350702010844010b90300942c483d028031140f021810110342c0040c1d0061014010480c0303900000c8000c109134402003601c018800782c4140c00c45960302003400b41c1903410094a90010409021340000c01c0007400281c550480c80840c1d240d05d00c10340d80019044d00003590042140041c0c1908040d000d5061451300801c40c07000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 708560737 1250 708559487 708559493
    0xf0c06021515190504050108010b0f0a0321020a020a0f050108090111090f03190821011202060c0a020a0806180f070e1b070506060405010506090f010813140714030a 72
    0x1c1c403182c80348621816504104154038502501d03c5001407074002d008000c40e41c0c0d51600240640522440d183c0301d500c1000307256180380b421108032415250051a007100380100180404840c007a11341a0300250302c030f80340031140166148100c000207403059900388602585080c001404900010382003043c640d0504a6043d60b0441000694041080407a607007445445035030003103803c080344480c80300c4566100c16420001e0141000c0141015000c0c20b800000340ea03018080d41c69002c03020701904a42d007854410900c05072801d1400340886c50070980030f4405207801a8001414206c441e0300038006034001008100140350840c159010440060000c3d0280c2c010a02245844920034051001540010380100344000d4091001b801c8404c604144180e6428080c0ac25540d45d03c07040300c500d40303d05e042a001080c00e0411000769540e000d03018012a0885400f00015154024003c0403001c00c80118460071000c900303c084da0314401c20760b80e0040d100c01801e100311080c615249800b514000c2d80801103540c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 708561987 1250 708560737 708560761
    0x2d023a390e010e040906021602100f020606010c060f180c0f0f050405070314190c03140a0c030e030d150501090e1504090c1403010c030e0d05030406090f0c060215 71
    0x6070701001d02e46003000c81c02c0d0a0000d001080c1c42100900f8092000c1a600c2804000009400c0c20078000c42d1403040b0068880000c0f1031726140007004e90010382003040828083c0d409209001640c9210302c0c40071410700101c140e41d10484a80c150594024207003642e000c414881000705500c09008035060180400d4146500d405101c0c0b100d1085500840d41e82c0001f6441901c2603001807500d062031985d1002609254082c456880d1403800000c0400d450011441c1c641d42c003d02ca014160300c9107042c00031141d603a998403103000b040604620401c0c952100c403024031802c0c0c144010f16405242804c0007c60010100007110400c0e50b58210700d0520400013020705c00e03a203a00301c0669004e4201e621740c5034804070400c0407401801014500a0104c01064408a447c00c07030344c008090010310580003046055001001103054076490007000c20706411820246040600c1200110342c058050b400c0030a4803c00d81c3d0b6405442002110195500400c20806101c440d6042c040ca090b8004400d15000d0341e81021921650 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 708563237 1250 708561987 708562007
    0x40501020c01080c12041a09071a090a05040c050c060604020f270a0303051209010524180a02251509030e042d023a39 52
    0x1c14000441d0010f130b503c06113842140c03441c04243c43c2080403070800d0300e45680303141c0b001c078080050402500300242c1800400035800d0100c5004500c0d6640840fa4540c44000359030214659a802242c442c9010840303484500600d104c5000c55642e843d0341c1c01ca810105810150041d019501c81d5004214581d51202e10f001511042141d068142454a84080030205408040c0004507002120f5240001c103154101015280b80d07808081e159140b540c660038840d003243d60446825004200458042d007454880c1d4404894500c405029075084078140f0f1f0702001d00142c1140c4140c845500001c0313401c410300031058909031802400c80003401d050940e64580c03011b24840030703200700050355503c0b00e0401c3c1440741100c030120031000303081001426140b00180703080d04d0301c2c410110a0b480b01d455170f580b5984503a100b180c2003c07213440c800340309110403180b075003800035003840b01c4401d00c0103083c200000b08003180c82a028941e40361001c07403c3c0180b9aa08840c44039000c10015031001c904072108919481e00128412 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 708564487 1250 708563237 708563239
    0xf030a050306180703050a05070c0302070608090102310f0315020d14150a08070614030901091403070201021002030f132109031b1a0f1e0d0b06040501020c 68
    0x30703031240d803442d01250700200d8101d0980ba4580143d014001c0c4940c040e84402e0003a1103820042c030641da036004c020f480c00101404000c0041c0e00c4a941049041d10641050381c1082030300e00090b281600d52201c250080c0c40c3d1080c0e103511451203100400640305003d0403500203045042e00c013042245503880d285540380b03401c450130498680004050030300050945c410303081035006103039007500750428401501400790742190180c01040018000300700ca02c000907040c1c3c01c4800342c4e611401c018284404c443d146030401740c0120701c83e40d01c4010312000101da00c0b50240040d0301c250001c580b074010b41e0000a01e40501c04000740200b51040040c042100803108586600000f4025125900f050704d00d00450104070302c259441d403402000c98102c03845a80400c07000200c0f4081c1d01c0020505c00d09a4004e500040e00307200324141c00f00c82c98103004001d00c5c25006090091490180c203402d183c0c00503174040641503038201901840314006540785248020b4880d0384200700055034040c0c20a42040c0c00070350380f034860341d03191 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 708565737 1250 708564487 708564497
    0x30809130e190809090420030f0c01030902040b0919060b090d03050a09030b0109021b121b1c05090108070e030c24040303030917130b0306192301020f030a 68
    0x2210a0103070b24412540c13103450140a2003c10314003400c203100303c903a00c60300c59281c4031008500180140f80019000701c540500601030911342c40f2550054004041103031007280c005032a20b00c000700c203075548040c040c4903c0e403511142c0c04215590b6040d10407210950400c0c0030100091214464945542e07134003091840c1e041c140640e541a907940192440111580000d2221182d20000314440c807154002c0c184204c10b0725995500c2400c21611281c68041d900c0e1180c640c0da80500180c08140000c900320104030b0621415a0f407074881d040207118100001e502c00c04040785000422014559202142c0c5900c0350b418034010742c10300310840c00079449050480311581702c1c2c0741a00c1640d521540d1165000d80070030b01d407000c00f69035603030320312340a00a0144004103803440e0004808005c1016141d44c1120604600c41d9207000d44e8a081c941000565000600310f00c2d008448007602100307000e00d5000f0040507000781c50000c0c0c40403402e180d011104001e500c0344241107400c8503150501469000080e195070b01958102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 708566987 1250 708565737 708565783
    0x120f200909281506090209040b0a2301090b0a0302072003070b0a20071a1303080703122c030708030c1813140606071115040906030809130e 61
    0xc03403140b034100d4551400f4098504040001c904e403107079000b001d0700642076506005901d03007141001284c0220f40f0601d442c04889683c0300951302e048007204012007005040040e0f4140c3c0310410495281c02c817500040c00300703500242d0541488045245541c0810b46102d02c0051201c0040c00b00352580464844c101c2918400b00300303e2800d90081140c4064139040311410f47c0c10b01011540300350340d48101e21074001c40c8040c5c41240e05071040d9007000c480c101300039560407045d15455039807661201c0e4031264050342044030b50250b400c1d220101d802404420343c4070342203c10501c58481550040107050300040d0100d5401001683c0016086c0d0007620307441100100c0e0b454550b000400d903080390080c2240e20b66440000d20610b540c901c1c9907a03115040d07014501180400b15a589000c2c0400c92003003500103028003000b00301ca030601d072400403c1042c04442c0e1100ca01e08041d81d510711030381503913070301e03001100c1c00301e008200f80135142842c12070440302d2070840400384080752420001640b956400c2e542c801c0c100c3c0300405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 708568237 1250 708566987 708566993
    0x90b15010f2d030603060e0a030c03050309010923010b030f1b0f03010207140705010f120b15030106110f03040e060904170f0306040f0c09120f20090928 67
    0x4011010466488010001182039202c010002c0806000c103c41aa00d004107100c001d00000500d01066030f0f25032520703403d00c03005850548068000a0000649648030300503980080c1200c41c44c000e030449031541c01580c110310214042d0070740d0160080d844c001d503c20b0001908840b0000b55103252a54030b08403026408070301d10042204108020703c0703e03030190700000390303041088ad403104851044102401640c0910b926280119013000940065900043e0a0011043c034206154032201052000810040c00e201002c2ca82c0c2d40c2c0ca401c242d03c050003140c0e0303007420181e501e001402204030426152010314581400c055001110348005480c0314041c3c81c030440082c0801101100100b011391902d581180c45002d141d115410540c0201c60349030046007091400b0030920700c07e0060301d50340e0b2903030b032141710809041405c403d10800d1101000d45040c40710504660102c2d400940c401d15160559001102c0410101c091240f881006040188a980410482d40141c07101c0380002010354200c2c005101d80c080541 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 708569487 1250 708568237 708568277
    0x11a100302090d05061e04020102030a1d1206011e0e0f0603101a1206151003020d02030a020a080c13050d020109080f0705030d090f1703040810090b15010f 68
    0x80031050f000b841454181041c403500040c01c5110313680c400c0e440d42e440c0c0c81981c91003071221415540240075038020b0007924441b070300625140d1a103581d0241854910307010300c0000f99076041e1844c4200f040380c206100600c07000b400300d8040d44075011032101d0401514504080c017842d4035401404158071400d03900c04100203039000e01800b4030701048a0818409022000944035030844074604892280c80d481440d01050240030a21b03602c02c51038501c4010300070714072105021015148000324010581d08003e1050303041f40510156005610070280140c40d09460000541002c1c0d001e4810b03080c1c0002800800400001c0107080f2007901c5040c0d814106003203003840184c51a02d101d4200310482d00501c501e5054031540000c000c411904100d04030380e030001e60a0825900c00b5458040d054003894410313020b100e240360040c0d90b001c900882008070703442d180e580c0344900c2c03c04400c04241803146449152140900c6034002c00c06030801402031010807003502e5500081c00c0c83e01144100010f0181c2401480c130882212 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 708570737 1250 708569487 708569497
    0xa050c0406050706022a01051501110d030b0f04020d14070c0b0115090e0a1e15140307080106182d090507170f07120209071215060c020102010509011a100302 69
    0x60700240d41c41e03954206e105001e4441182c90b10703e120701d1805590800d61180d140c1a80c000360801c041c0040100b0118124040c200c4650482d030000441c0201c440c080c0c58902c003c19240140d00d500041c050904965056a000041d01c1c00c0f04109075101c801000c01c0ca2036021504558021440c160081d51003107058400b83c10903405440c5080146040016000050700419030998118415440031741e04844440102e03140141c1048540c1010a001d100c40c0c52401c100c0307034440350004c0440f6002540c60024600b580c0c625080a030040417000060008201103008007145140d000a40d00ca01d001c2c80c2010300c44840c40c40036030b500c0f81c0d901c540b55401444030030300040e03000e04065080b210300d1804402240d0342e00d00481850801310706c100d25001649008819843c07105940c010400c2c101510380610440c0c3c100419a040030710503030703150720014640443c90046002002c0d03e4035140300c0019980000382c00c4550040081c0399503410100c2040d030380b00610151949034801114140d005e0042e81d40114024011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 708571987 1250 708570737 708570787
    0x60b0d060e090312010e0a0915060302030c0108010e070c050c0d03020106030201020d03020a0f0530060a050607080d0b03191b1d010632030103060e03040b030a2d050a050c040605070602 81
    0x5000400610000340340c002b070702942d00940448141c000403000455034224240305034800b01650744042180c0510408501c94038030300600c201c9044201c2d4100044a040a40320110050f03990342d80700304110350301400304541e9490142411810f041c4202d60141810782d4202804007000030010306a01690b0010500c003524081018155003a10b8504032038801d00314060361681d2240c208800009940e00d0801c0440e4089a031004040d400c007940d11114a01809490310202e5141c000d4450856040a40050f480d5860703000b01d0049032448500c1d010403444080b5508100c41c080308140c002541c140301d288030581195903600d02040100d403d801140f400d81c07510581c894120a030300c009444415000000343d8140c9006403010041940045441962071280340300e4402c1400c004e10001c0c2d48840a40d100c90320081103c2440c040d40f450341014014610003201d080742119940302c4c14000f1110307039032003240d500002a50080d850941001406007180c0101e64000b41040d800003800f0800e00c0d10350b0303141c00c8883c030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 708573237 1250 708571987 708572003
    0x40509060f01351509011a0906010c050609030301090c0e030d14041e1e030314070203030f040308120604060513020c01020c031b1009020d15060b0d060e090312010e0a09 74
    0x640042c12075219031302c00c0440c0604805030008100030780307410710504901c0c070001480048940e16a4081c0018210010129818040500f4588000c03420a03c90710b84501404400780d641d80d81802800da04032a43c210070303002003015054581c080c5450000c0e10040c5201c8038204983d200c0e03802a001c41d464410b54100c01d010440c2d8590303001c40101c00c000c011082d15052960004048681c205126000c0154400500020341c46000c21301c50050920041110030b0020b0b054a14080213003840240b961b0103680215a0b8110001c3c039010b103d070000c00c0c003e801800c212420700c0070615041c006510b108003c0708101000b64000340c1c3e0482c0792003d41c110340d06030705420141c075152020b158601034007900c0c0ba0204070305401503030117480300030780ca034840c5038203060f4001c0041100c1070300c0c1e8507096940d8a501e9089400503a640401140718544030020700f0015200c4800401e0180c2010806240c03004041c055002950060064a4080c44100300003815100115200c01866403034107200c0d0082e291009010f41500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 708574487 1250 708573237 708573329
    0xa0302090a0b060d1509050f0c0f12010b031807030209061315030506040c06050f0307120f05010308090a06090305060a090c0b030c0d05071b030809030d0501080c040509060f01 77
    0x2c4910317040110406402011150280d5680d403840040d80c0088500340305501c0c0e1140080e85040420018005108050003254203007101170842480e07050b030a80141c00c60f00c40c04407c10044406c2240300c1c42c40c014148018121070307840c66000c00ca6800e8090143da100b03292200328030007109000c0d402000440c0742102c801d166103a407824820380f10308041d03d054800a402c00c40c00700d41c0a002e0000c0701d005c1c2c002c0c0038a05155964804080380d41d00c55107251a00036948a41a081201c60a406103d01031401440344541e10006c1000f04240e0100b640d1007141409480c102c20070201d200400c00300e607c40c0c101072011415002c90f1401c1a1400501d4200d00d00341c401c088240520076040401a080015009004000c82d4441410582c0d03110b40d041c201069140c00c442030000041d102d1040250882e108400700d0303003010304011245080c0c0780240c0204440b030344050705400d00c51030039014845d0401c0804d0050602401c1038140d00c808144140194600116001450072a4a450030807442203600d412131829190 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 708575737 1250 708574487 708574507
    0x1501050f0d020627061603081008010524010908031606020702121b04050f06130608030d0902091b1602130e1b1f1d06040602030a1b020a0302090a0b06 66
    0x1401c2c5060448544114503880f6802405c01034220340784500d8400c1e40c042c000b0507035641100e201c0702c020004520703528140c8000074400024000c0c1ca0003084805d40c1000100760407a6101443c190101c0d88074104020982c00b00034400c4040b08030780c070781d004010b01600004a5410040003070311404000a4008148800d4980610f802242c1d46511608502050f00a804100104400c0d0342064918a0001240c040403460030324003002c92505074581404045a560b503645d4401d8255002030840030086619422058210300c1c000310b100b80d124218220f0701000c50345024a2040500444030a44100d8050168100c103561f00e81e0100120040c20f1401440f01513811002c180e141d2515030f00c03500c0402c01e0a084e5446623301008201c860047c984040c0800f00c0c104181219080c1c0d0100122410b040c01ea65012150384400e4000c0015128540041d542d41d514104000e02c0070702021500000e855058081034016603c28241200b12078045540943e01e0b02c1d1101110000c00c251242e459102d000091f101d000703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 708576987 1250 708575737 708575767
    0x21040602071202030406180b0307050c010b04110a110d140a0c0f060e1c02031c061d0414010608102c10060b030610030e03120a1d1501050f0d0206 64
    0x46d03074116a180c2d0f00390019110b88200028003030041100104c0c1c1440052110b501c100e01a1400303100315400481c801c01400d010030102c45504052000d00c52001400810607600010101115400c842c0248070805034103500078070101c240c40d40e503101c46000140302d420143c4100f002c1440d2a801c0b0700c292807041c0c403603d0f0000084c0720805070000f03203001c0c4003d002c14001800c00061044416500510300d45420261030314110184503095415003590b901c0b02041075003c400c510703003030504400d141d5921803c0500b0880d2005000e002d03022016810100180409080401e044885080c01031001c5800e01102c001c80e4415550482004400741804240c01602e40700080d220ba01c02d450401d04200c12611455030011038072003140c5940c0c21130751040400407000e10070f0b4440c003082582c60f001d4034200005103600051107101644c0000344543c8984581c04010311400040755000c2e0742c03500600011085100108900070141300d030340d10404000101d0140e685801c4802101c0d164000c108a550345800d10520a03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 708578237 1250 708576987 708576989
    0x21801090605011103070201090b130f2d03080f030c0d0903020a0b0c07020901031e0b070c0605061f080a020d06080105012615070e0607210302210406020712020304 72
    0x3c000b95601c07011901d403100210481d80d2903070301a590484800d04102c10012943c0c041d100d20041e074840c000d03000034a0101185038202406100114541070f01c0c0c0c814020f48200910854564481b180302010800590b90b101202c40016440010036101e585102900705c541c015a0007092100342070200400030594003050380350000c0d00c0341c04014490344070500907010382d004194009420044120050011415240304c4403841d0b000c1880040d0101c42c2590349604000066420601045000d94060308101103405100d6100310700b91400b21480c5030700d290030032601071a00002c2c0c0130300c49100b0100c3e1085007140c0468200c150001800e00645546500a900904091003210101503103052881d41000f06003c081c44049055001041d114201c5a000050408050000c034180403540300c855281c0c3e1501405042c095028076015003240e805101003600361512205042c04040c4100700d03500040a580415200c00d80d422850898581e4507490002d000340300310100904a48107036182032961540c0000148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 708579487 1250 708578237 708578239
    0x4050c04271b0206100b0c2a2706010302120609060a0323060c0a022104120b180105040203031614010603061e020a0f0302071a04060501061706030a0b04021801090605 73
    0x6103c040d590310780000140207441f14940c0e00c0d00300d01554102035544d48a004991101560349120040810340045c0b942e01c0030382251980b401005812042c4a1031b816200340d40460203003025403500100000161510300000c02c400e224900383c2c0c000c514223031110039480c0c02466000c80103550440262800507103820f50400100b00d1031007a040000c03180f21140050303072880d00944c1c00500d04409641c84520325071901d40710070383d00c1c02c0060000040c01c01040c0807090f08980254204d0000f81001841c040c0d04821624180d09640e050405210042c0c80002c01c403010307002c1041031f100101d410b0346403590060000a8210540cac0d03090610100900c20300703a210070094481105668050000f200203034082c0e0050310342c00f2001ca4140c03c0038031a4540a82c0040c04103e11034ac00d000038403030b03e500031f20300d40c1b000540c1c00381c0b0701c103942c0d800600042d60054603030310040c407041ca540b032810701e0202d0000c0d0780c0d001c64a400405001c19800424110340b03030904030242031940c5d043d80c20340541c1c54180704c85c000e040c03030b10400f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 708580737 1250 708579487 708579511
    0x1b080f0a0f180b092a06031806010306290f060d0f020315100807090e06010e040e07030c050d050c040e0c0901031119060f0f110a08040504050c04271b0206 68
    0x201704405c0780c407a0301c00c0f41e0503001d050310b588000c22042000303140d0b0001440404441c0b800a468250800d040c40428041c621031000061110181070004030800405110015150580c9170700d0314035a071302d4552040b1401000c6170080d66401c03003643e26101900203000c190868500210601103200e200401000c80b0000036101c40040010910f0111506d20058031500e020030007070003050112203200c108403503100c0c0c0d040c1400c02060304080042012036980c088400c010ba00048010300c2000141c200087c001d01c4222040c508190854481c10703121501003206e0f83c0b08a80e243c040d444050001d000100d44100d0080c5203402c50340c5e50f820480f841c0c005070106c10b8452040105032000d00c6619650200540e02d10f0754854060510303003903040d9038181ca484039a0b400e1004204e00c507074005500700950b541a91141180d59110ba10300000e0106039440640b4038800745106002c1404400b0000c22402141d82e0582105082c001d070285c0300800074280389044441c0d06101f0440c2c0380d41c0580000307055000f0400c003014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 708581987 1250 708580737 708580753
    0x3040b060108130609020103270311010c0e0f0a090e0d230306010c11030d050d05060f060a082a0c06060d02100e01030617011b080f0a0f180b09 63
    0x1120390081c1224081c01c00310f40b01e00c107200403c0040d40070020300b030320606002030074440c883e1b40344818140315400f4186220700605881c0070958400303807160988030690001d000c2c0449010780038000c43c40883c400c9005081c1803107440031170707074070018448000c0107400010444204401d00c03050b03e642400c414031012980c0700e0b41d909680030b43d8a42c088441c240b41c1d1006030440c0c840e10011102c61240c640103658249002c905142c003030341c0610814043c0b003103d40350035646242184081d4152800101002d01c58048078003480c20640b101411030344600070a1800030129999100030552480045001070172101b0301d01c07402126040c0c1d50b0001c0174030b81c81d14412503a15075165400c0010030548003600940080c0a05c2c20601814042c81c2590344406050502040791034503010341840da9100a800010f40340c0d104c3c12a031550000c200c10783c41c010100e910701092246002514030030540000b030304620145554840c00e020715078040e80109a8580740c4400100056003030b00b061040400259406e04060084500c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 708583237 1250 708581987 708581989
    0xf03061d030a091202060c100c021b0a0603050c0705030c0105041e050a11131803080612030a141903050a051302090609061c08030f0109060b090d060f090803040b06 72
    0x40d6150618943d581c02106804c0c00c41c0340b0a0320448400403030b0028030500220300c80301c0080c0455000007005480001e83c041d0341030300c002d1030881c0003007543d940000c0e03540440e011034642400c3e08040d40c29600b0301003841e448007425044684502e540c054100d00000c500e031410910107400c00b50107240650058507400e00000420080090503004c0108a640521040000150308154680c800303000141001d051444c0c1180da441928000701c20080c0c08000085503004050f0041015600240c0a4906101041c0003a40295681c07007205007101c18024902d4528920b04410000c40310b07160b1100451000c9007040c0361000c1c0c050703c1f0944010040f5411301d40060341d6803107030452400030703640c0040c4030310f0481d21010103000d000f01010f4011a003040d511030709140c0f00142c0e035203031a581c103200c0c2944554902d005004c81c11041307010b2f00504202d5040400030011200300009541c1001c40c115507050b119211072a1403001030401d071454406041c203202051044c010103501540c0f00ea4013444040c28650f079110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 708584487 1250 708583237 708583243
    0x3041101141b3306060405180f072a050c0402070305270d0b10030204060e0702010b030c0d0b10150201020a03060504060f0b0705031e03090c0109030302030f130f03061d 74
    0xf8400d20300000031007000f01e204811400425411401c0544030034545030715030005c01c103615001c2a045001078250b8080c0410380d003203c41034031b6006d80507141003c0750189208803035070010044c0c1c0158041d040251504400d01400303005241003000000c1085540d941c5519000e86907070003e070744050007140e40c981408000707204032209140c010002404040f401381030b60b840c0f04403020054103103080215500c0000c0b005803030381e10501c8040c001d0b280800047c2d1a103a103000782966240943c5e84e0082d0004c03884c10b009030f1900300075950040d41c000390f000c03010b66400c000e89442e1807080d402012600455401d0340007058040d401803490307402c00c0e50305202e11030b141e20910050710914403508104c805094010041c1a001c3d201510140d88940103592801900440c3c4003500c0c45880541c00f507140001091181c20302e01000048070811081c00e0520f005461910041d49a00402c0743c840c016400002e441c0e11101440da03078420140100c0f2019080c001c0d12410120020040c220760710031040305ca4941500040701c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 708585737 1250 708584487 708584533
    0xa020304120c3303020d060503190b10030b0402042307030b121b04020a090f09140105031506011b05160302010305181b060405040903080a050c0c0303041101141b 71
    0xe1103c503014501500d8214000e601410340c11540c0ca80e541004110b43da0b00b4005541248491070265030707504503a01b07000b02c101c200988290f908148035002040000d48030a0590790160f0101c80004096122035850030500d00003003100c6ca0003904103820080c400340c00d940300c81c2a60609a030f1902d080c000c1c205d09180d81d50105000440c01804d500c202c00020326050300103003e600c2e4075252500d40d2039602d01407402114581e03086004400d0300c8800c100c0004c1e10b0b04075401c2c01450100c0003043e07116000c4401c9864020050640b03410841c51203205600451101c1107880c9480d0b2002c12106c11000c01d8001000a60031404202e00080c18403001c40c501d2491036582c41c03d401032220140c84001c000c10881081d6940c054079894000f80c0c02d1000061540e44c5104000c05140642c442c41003900c3d18120400869000615105140c80c090000000203680041600d5011798020480d030b5541c105000103a411181d410741c440c07101d031000039481000541c1444410542002001200c9901c0000c0340182034003044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 708586987 1250 708585737 708585809
    0x1701020a05070b04030516080406140708070318050312030a05070509010f08191d1005130b0a0609020f0d050109140c070c081b150a050702060a020304120c 68
    0x8140420004220030fa00703202c1d00300f8400c2c10410701c0c1006008403c070804078031002c2580d507010007140410049811030032421b0782d217800703951682c58511155241d912a009102c4007504108152100500d1502a10034007c09014014110340e80548400310f008041d40c0101c0d0b0b400b0109040101103000c9a00603410303900c4280f070584038081500d03840b0380216000400203101c4060200e02c01d84000d48118288200d0b40080d82c00146400d6081707032501c12928140314040b01c41c00d04c0e0304c0d00c01003040000c0041544600c040e0310481d182e800740c41d4182203002800c032a4000f00c94541c40040d4090000c0c07034001c014858600c0950007480a6030744c0f00b0301d01c0115900c1c92105107604014100140700c0291020081448a2003000d00071001c0740c403055070303074a406a15901d4104101d030340c54090340036140c100da110480e40d118804662030035804820060042c01100e000900806022885100c040c3c000d00a0b203020301123806000810742124100b030035510246d4412840807040c3c0340700d02e40705071401d2a03a801d66452 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 708588237 1250 708586987 708586997
    0xc01021207021f0216090e060f0c0d0b0a0902030f01030c090c0212070618350403292505070f0b07231306020706020d05160f0c1701020a 60
    0x20b00343e0080e00b00143d500700020300314010304004568141e04030f000c0c04003400d0300c6900041c1a000c0340c507480f850464090700071594141044100101c8040c0b081c01c039500c22411060114583c00c440d000f14074a5091034001081680c0040104401c1205d00c2010300d040301c0c055911228255a1102100200c03410703c081e01c001a0010050b40e0700c21780d480d900603c6124812003001070f403d00c920740001401100401c00715034603038099020b1500036082c2403801c200c0f4013820301044803688041e1005000761080d84401090007000e0500f20310550500160900917100142103802c052805ca4060034204804511083c0c4625110030400203680c40b0302d00b540e082691100303100081d240d07540c54140c24498000c21880800207091007001c00d180404012030b50300024140210344880f8861040d0002104503040001158401030741000000d41c0056040d501003500e04084d581d402c2409000b000d01040c01c03902a003070f075840d5004003080000c2c0c000c048084a60040d12540101115154103081c1e104142074a40020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 708589487 1250 708588237 708588259
    0x10b0d0c030b060616030c0201140a0c1217250815013b0301200a0f02031b1e0d090b1303350901120f0605040e0c0102120702 55
    0x2596180c0140d08104000d086509144c0c11761220003115503583e8013200000c228000b90800c40d60020034409402c001d80070080e0904044610081c44050007000c0940311065403040309509038050149041c42c00349007104a0320354903020501c601400c0d4503100182c00024502c0203144210301c184403132030140c02e4201000309954403d0004641c0040c10f030110307480380c41c0500d036042c9005d4a04c4c1607440040140c50007118021818000701802c58125800d8450344400381c42442040c400b2000442c0c0401960781000404909000000ca1541c007940391518501324451840030204040002c2c00000c02c00e0907015002803800d032200c25512901100d0b8500040340b8400300a0110b040f050016100c901905598098030b503569440300b45a20346508810f80c0d101c0015640b00b19000720b00102c41d10110110b00600385841e2601c400204001c40c11220045000c1e500e05980034620401d4120500421000b4802c1c0030081c03621242d291074080510b00203025110f0420003c1c071002c81c6005851b4020740080a4881107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 708590737 1250 708589487 708589493
    0x106030c05120c040c0e010e0612071b050a0b0f0702010b030c0d080f0f031914060904050a050607110d0801030213020a05070b1315021303060b0a030b0a0c02010b0d0c03 74
    0x305003a202e0100c42d400344600a00c0e054032144078842c4450500d68030043c5803003000c0009454052a00c1400b4001d84040022945242003200a203411943c589070850004450340004800191000001001030080d2429601800701144010f401942c0c58041802107851307038007081e4200e4090070b81107500354000c01c415403042d03e01048140070050003042c5051804c1c42c200c030104d41507071104481b07041c00d0b507000c020712502e05c03d0001f010f440e2403641c2c0070811000598003021380c0c00040040c14584110350b03840000742081400e22000c045542d03c1000c44100c2c0c1041140031380315031020b90034030025125020044c2482e41c403c0180354100c0e40c0107849965044113514010001c0c1d8003072602d2006118080040e10005040800f84900c20b4078602d0207000d0890315458003002110350792941441690040c46500d100c450710071a2030b030840360f1050002070800544004618124110f610280003000305e80e00b000303140310b600e030494040c0350f03040d41c020481c4e030032500100410f0310701d240c6000d8132401884000f4400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 708591987 1250 708590737 708590749
    0x170a09050906060403060203010b13050312041e0306140402030c01030b01050f0309151503120702090a050402041d0303010503010c0903050a080a0309200102060c0301081207020d0203031b0705030106030c05 90
    0x40b2901030300d03480c503264880d00c1e040240e90081c5d000202070140060181074000c6868014000b9001c110068154203039107002121050040b40220f42108440f0410340720921012080035004685c003410900c02285054200003075154100d4043c0e00a0184800409807584640301d840c40c4144140c440c18100750055400002c241c000520300700c658454103c900b1003100324441014840c24804003000c120311020b80a241c2000031030f14104c4d141c0d403000c3c442c2c00d0042c0d40d05508142d002819800000341d40c1d641d0700020340034056082e840d10507110514a1100300303010100085050740c3c000e400902441d20309800071101031401d8030002e4040c0d0010110180080c0500c801024001094900413641d1115915410403414000200040b169183c228822055805100c21a881900328480ba4115850030b049a030b21400043d82c511410003000940200310341d110413842d8091900502141e03120381820360a0740d2680047d05101a8034420340b0301c0000c00c1d141c1401aa0213803540300d0158100d0034a0070050000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 708593237 1250 708591987 708591991
    0xa02030a11010605030a1407060206060607030e01020c0a090b030601142d06030a0609152102011808070e0903030c0a030513140d0f020102040305070b1b0d0203030103170a090509 78
    0x201c15501c03443c2c0014655800c1004031241409409480980c102280381c2d0380c81d00585501034401c5d5040941001810b80e100ba06030740c10950541405540c520180c00100d0500c1c0e01c00d6402c651151542c0c0d00824011180e41c40708440b00b4050b02180d999903210076090300525422641c25900c542d01c003400099100382c08147e044000c50303604d6120007509100300000c1c1d040c0c008840c500d01c00b640d500b038200b108400354000c500c8012400340712030340c0c03160500008007000282844400754640d0302065010842e44240400300c480c0803c4480c1c03c0300340c1e886a00c0c0903114241e41c0b1400e4408460000442d600081c0441124050714011790721500c4c004801030142c024001c0248032242a0100100c1d18000c00d40e205850b1207811081409024400382d60803018080d07590041805003160710500003131001440008555081ea07150150864940f8100c00130301c1c1036481c000000e04818016807a0000140d40c0010185042e248280d00f064482a80c0c088170404502510300fa01c1d00003a43e9040801103800c0c5031342c48a07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 708594487 1250 708593237 708593267
    0x1020f0c0f0f030f1f180f06200301081006120b0106081b0f040302090603150a0b0d060f0f0c0e0112020c0a02100503070207090203040b07030f0f020a020f0d080c0d0b1c0809040b060a02030a 83
    0x1005032420241109d5141c1090b03010090b1034000014410074080b6a21a281c050011901e030088025aa6240d68084200c14003030002407041043c0421310016074a420b028030448003610b450703540e001d0490b001000b40c10074842203000c1c20881c400705815160220300c0040210001c08092030720b50703952a550005d0407940b19060b40000c2c1402c031080200700350380600040c82c640aa07000c02c000e00b000c907402d401c854001c0ca4407010072200c002d441d01070360780c0310740551808180154003580b102d950981c4181040d414010007540b00d1070318881c0ca600e541d00b0001540c4600c0c412f409940391130341e80fa8240400d0384000c650052140001400191449009a005480c0ca192401c00011005844440441282d00c00c030300740e030f0150344100304c0f00c100c20f01c0401200c400c0820754a0900480d04103002070b00c00034007854850603441c0b9100d048410740368481c0d281807080d548200039210788a010f1400d02e4070301da40c0100d46c820702032030514800f4100e85c2444c0c0d003140e2110360389030300a5240c031b452510700300c6007400a15048 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 708595737 1250 708594487 708594521
    0x20a062109020123070213200c16150908010c121817090a170a0b1f030b0604200f0a1707050901020f0c0f0f030f1f180f06 54
    0x104254040307004088034016040304d501c65503403109004004000402110740000c0c1400c0020042d8400a0103898844d0040410389071901e0300c117a0b5a20609085110070108040300c8070410000318114001c1c0c0c0359144d000c0903290faa0300c0e66158400740c1d080e9000c1b440020040f60354900d01e62412045c5034480024544810080718031580b9545d22140c0ba030401070034100036082d000c01c0c026400e1a280c180f100c000c110040e12182200c100d210740644440703014101602c0d5145e1040010301d0202d2401c400601c007400c4403071740b04000d0384a1400210441c000e648150203075240c0244560560400160103404168901c411420a2111184103905900140001d420440411030b1049924046c000c1036001d500f0540b02c86484550f00ca000a1502110f081c6030041030b44094500540c5031540071900c52054410f403160082c40107204007082c9040b8124031020b00c0da220f440002c5049065081c1102e80b20003204a0620251a81101e20300c4501031034180030b84103e54050f81d0300c0c002042c1d58010511102c070700e0b00c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 708596987 1250 708595737 708595757
    0x30403111f0605040e15160c2f060c06150102101d0114042006090607060606140414211501091404030c020d02010e0a030f020a0621090201 61
    0x12a00300564015052084540700c61050102d8540341c02640c454000b4a0002c20401c00007007907500d4001d10240600d51078420707c0c003c0d2000141b195000d9503260b5005580c0d128210001b802d08090340e9840c0c0d0075462030250010100c2c2103441c01c01d003142c050100c010000c19081e1144801200040380080603e41503202e0030005e44c0c42e18034240995401c52600c201000c0000440355034081c2904c01810404ca920340200c01080300251507006022400b00c60190184060f510100c00b0862a110b04107c00381d00100126440301002815004001501d14641d1054034168904426a505000341c0c0151074902c0d0140040c0d0403070f410009070668080000e0f00b0998076610400e09141d0421000d5525030341410b038000010f004002040c000c0c028041182c0d80d41d400145055107005006022411000780b0074201408109c0c00d582c0708080f14848440f000300811400c0f0340c0da1818207103804070300800724040c010f462800074003d80079070566080025089404848824544480d038000c01c00345204030306000c20318403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 708598237 1250 708596987 708597013
    0xb0a0e0a05030c070b0a1b02010309230d031a120a0b0f31060902150d0204031103060601090501110a051204091d07090f14040b0414060103020603040311 67
    0x30009034424010006035070340b45012881d26052040c0798000e0321014904000b41880158002a00399182540b10203e60001c503452004030050498020054500103c0c04000600800b113001840901e006420480b60017511810b0160155405204140c1c00c030b80c0c1c0410a68582d04054403240042c409000955040204590301c285548800303a030380103001c5203e8000c02c13003442c0001812009400d403c0c4d071102060101001080440c400c5901c006004503100c004510454070ac41c0d607800c044030700003c6469214080e20070b000009411901c8251050354404d001074803142070101d0403d0040c001a034554491600b07002c01564400780320801e03003075903228003041000400c0d010b02000b03c01151060510350f5a5150420714001d0704c58034000400c4018000800031651880010510f0454220780c20110300c4066884902009054500b103548003500d901081004005809003500c0c401d9103c1d01004070a0400603100740e68484e800d010003034000c0c9040010a012900902400418100c0c0306c08072000d50342e1b040c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 708599487 1250 708598237 708598243
    0xa06020a0207080706171501020316031e08040c0302091e0f150613060f050c0f01091406010b0301030f02040b0d0b0613020f071104020f040e0a051302010c0b0a0e 71
    0x4411280160416241444410018010313400200224a031648420b1048036050346240d20240c00f05a80c41c03040c5404200c164001e00c156404211220400b000b03548060501a0001081c502c0c1040000c4405165840f0203000d0000140100c0c1c015030701900050955092020002c406040103230004090103030070201900c0341a610f88206240c15800f516810054500d14001511640d9148a41c1d8140882e041464294020300304540c80c43c60b054004414490f01502c00b48501c0500903614000c0c000001000c0105401500850384503a0341081c0400f040082140c4a2000f80255840340300204010000705611440d01ca98590000300700041030355004c0002814150241c0c0200d41800d01e01d000c0184600d8840d114440d1210031200c150b00e00300b182c0c2090b4425105102e401449000401d800340e0040c1c0f10307a415101d002c01084110b551701c0b502d40141a6143e0422a216041c00d070500b00015007001080d04078010172941078640714030034002580e4040344640c00070080c005150b550140003400003010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 708600737 1250 708599487 708599497
    0x90f0a0e13020a2c0c0910021605030309180c09060a120f0c0e01050c01020d05012301050403020109030204090212010203010611070e011220040c111506060f0c0a0602 73
    0x10501d41100c10040d105209000070f80e070348a12040300580190080e01150340c1c1090b0421003518450764802e59600c808543e813070168200d42900150340300e00740c421890300010f09078031101c0303402c010861040e951000c040c0d40f07110f038140b2580c01c2004200d00e40d00440d401421550040308a019480c242080100420035035002800c504000804d88006002001c03650310890303ca025110f00140503003800d404016211143c01d00c0014104180040c03d01481c1d8000e6069800300a180b450600c001d594030818540c40a05003490148022410219080517601030000c071412650b041c0c40c2c9a00661840c4c00300b00c02000b90705001c1e0303000a00c0d0a24000481402e10085020740074640301c1d03440e102c522403025840c1024540020045004440040c448240c00540c9060300703c0c0c0c400404138911a4481c100d0602030710000d40d081d002800e01c41003009498000d06803810310751541c0c08076901003407001c1059010300303426a00190007100c10000c140b903050300c640040c03030007142c180b0885075890312a9444004aa102c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 708601987 1250 708600737 708600751
    0x18060515031f0506040501050a03090b0f0711070311041802030706030c1404030b060d030c0b070e01030507050a0f031d12031509010b09011803021f08010603090305090f0a0e 76
    0x20000401100051110b45a012400e0080311080980c0c00c0c00040707100e074030440c0101d90610034046a0700005512076001882460b510802921355410540c5001d195640103031542400700d0b1600d4484a00d00030000b545d9421250484944a20020b001040c800103102480000050704074844019001d038a0800c03030031005000d9580c1c002404089604000d00191204450841c0180300b00410408100003e15051304442c0441d02084200100e240c140d40c5001042c0c0c005000d15455004c01a00e03580001d0509100705080e01c06218944d103044048840344900c210000209071901c1011021718881e501403209103881c2c80e02410031031030b114400c5e03141c5000b0603860202d00c5d400008001c1c0030103003c0900c210710035041e1381c48900742d4140b2401050900440da58141000b103070580050700d0858100d03100c4010360300a44241110315075403050b0084140c0c24801c000218560740000160079100b4814840a50307010341e100e82c2012040700400041c0300c11074001c00d03400100d5a001103244802c010740c640c004c81c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 708603237 1250 708601987 708602029
    0x1715180a031808010612060209040608070e011401110d140c011802180609010b0f09210616020c240f0714120306120106030501150509010b04050a180605 67
    0x100442502c10085258110741816410400c00300715600da503803040e80700705601602c05615240e2100204009010580c80030003503100c1c090000404540f446406416503041800b01040144c168006440c580001c0c1d503d00b8003a0b00405103010081d1050300d859240640c6030301800e1800c06607052050954401e1014040c116007111004011071400c00c0c0c24411011081010000300d1825800141c1084414800e1300e007103010000c1c1c02e0b50340400c0d1404031303180100c0040100d0400b2128003190032585081c80f4022415104500c0440d146020420801e484202298002d10f0f12107120004d0200c5412085021078012000801e0841c920400030041e10540c0d04d155100c6407a03000b00d0602c9500c240348004c04030700f19002400c2c0780809600350012a58003120a6415014140802e80400d0041080b0b500c040c0181d460f01e8500002454441c814030119101158412516629807911b031005204510880394480d20340d42080002201400f51031a1030480c2503070001c3c18507134800206110007869800810644e0f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 708604487 1250 708603237 708603257
    0x11040308090d05030c0106140306041a090703050327150f0c010212130b0106140a030c05120708090c0612070c2d1205160228080d02071715180a03 64
    0x102c00e4041c2380300e208100302c0083c901810192294440181000a41c608140c0b40c48001590001d00300300580c01540c1c440101ca41d034140d038551000c25950500c8002d01c0d0746c0480c45008120740390800f0b030007807100002c95440f0300d05900d281d96941541e1240e5100c90b032654003841030180807a0203840c5103203e2041c00c00d42011560a6242c540c100200582020301400710105030b41c4074280d0801d0503149112400c5c18006503041030000c4c00c0d2650b001c1e181481c1d0041d160300d0100072040c0d03440003416000c3c903440303000ca48210aca01d2003000018007540c8800b01c0b40c20320280001d20074030302c545510b0032420b004502c2038440380360700c503001c2004c028280c44540884141c900c24a0812000e50665168056945070190810110000c03400704036284040c0a4440c1e607006000c8440d1f8100440f80c0e1454405000d02c01800c240c0e0352102a440c1c0e0a00da030401c025010304400080d12401ea0070210b5881c2c8800c0e000f03081c194640d2203a02c181854060710000d0310391003c490701e56020b07000b00190040c4601a451707240f00d00f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 708605737 1250 708604487 708604499
    0x3010501170d1b0803100e071e020c030619110703032a12050705041205010b13230403021005190501080c3102070804030c060311040308090d05030c0106 67
    0x404040c000748401c0201c0301d1a240e014489402c00003400f15030100b201c1d81c0c1c81d107803440301c3d10702e9610542095543c50505805e00031300c0c0d9041402ca02042004206801078418154000d0ba02c03403c4940a590b0180c005a0006070b485411099002445480000001e02c1100c60402c0d4003d81d04105812004aa07480c01000080031280c3c1008145443c0c21401c0000b14241034002080300080848545c042910307200402d60140c000c1c4140c801070f1075003140307160304001c19007020741c06031080034001c60250502070070680b01034080740114071584040a8040c054810308024000711178000502c143d046004171101c1d2907624600340a61130003101140c10030085029065038010403902c061b0301ca9000755000d002500400d1715854442601c0207480150078800a2021030740401c03003801e505c03901503600c0c03002500760100241c11020b803040e01c4c003078944525515100c0c0c0c1d00790100c604440c03640480410034801000000c0b10380300109240440502071007441c11040e40c2d5149143c0028940c0e07500369460310030030300007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 708606987 1250 708605737 708605743
    0x304091803080132030a211e05090114040b04030606080d080f0c071a01031425090b0f0a09050a0b030313091d071509050d020a06080a06050301050117 66
    0x2414499900c02c042c00c0514610202448001d680c884d82541c0b5400468242c1e60144052004c00d50444c4459100203105a1540d0b04103003448420400b1942031103116442c10861105e466072a05103450b118602803020340191610f0a0b12240b42c0001d200400c00071401074504406000114803d02021405d2400d120a0301d05103c1902d40c414104200c410801c400d80e20760220050b00400048140d99990f0a00e09010171344c1c00121803688c902001c0c44000000300003ca07500500340c5600d14040d13800b000d151b42c0b40e0011401100c07901c9198941d41800c180a8500746d984810800c0100500945034540c0c01c00c08a40301c004564040d043e0340b075070b803001c101c003400c0c06010744061103c041300070307501d04103001c815881c403501e46000d010103080d542c118a03c0030106010b60300c0410b00800741201c03109681e40d0780c0319014a0b201c66041d40002c80f00e110004140c01c1c125001403019071700415a001560520008541c001070003040c1d8100c0f1a01c1c3c4400240b2a142171151501038540d901d88018000010741b0190f04d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 708608237 1250 708606987 708606989
    0x1e21071506032a0501050904060f0b03040b06010c030c1709090a06060210020f120702150a020915040806191805070914061f020115091a060c150903040918030801 71
    0x10f05408110080030000004420605848007400e085845003240d4010a00502c0303140c1041020000c68071020030620804400f55100d10700c60b101e4440c13986e456100455084800b8107008002c94100068800040c40720910103400345413401d40c0314204540540010b25104003a1819900c041d0754070014403c4543c180809111405070b52400d40c81c04030014402040d074400d0403c1c14043d158103d000c600141d10070b10551540004065001e180d81c1400040c800003940440c00851084500542d02e040720880f00d420b640480d06904098590707540c034203007104621241002c003000103a07580c15414040c00b000d00322014000b40100001d14605003031196030310071680c2600d10340d200c44806000300720071590b84810703264801d0104058a00e00c0380d403403041170303024141c001081070702c2510740b920100c0c41034a603a000c80f08102610304405050a00e00051010b148550003c12204d80c0118079042e03108211901c80c25000729540040f40e01e8156107074401030442e5406c40d0042808010044624203140d40604030300c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 708609487 1250 708608237 708608273
    0x240b0a08070306081908070203121216050a18030c0825080d0f0207180b1c0231140613020408060708040809040e060105031e2107150603 60
    0x2040d1814001d8041e45c0d81580301d261061108046480c07010001400140d0b1804c96014040f1031482d1307518803c2c00d400e41c020401c040c20303075101d080c0040c954503a541404186d50405032106032400d090400d040b20401c554107065440074860080000020b105d40d5440070051103030324041c2103440c000441c0c038180c103040e111041d400340500d00300c18420380c0c20120342d41c80261000d00b00103840000710401a4100780302a40f00c01902180c0e08444110303882690086010ad820850308240c0e03041c11012030011070001104080d400105950a0a001310b02020140c2e10401489254012100080010400340c3c0c1038185040c1c07501c4081b00601806040014840e91a0058441d0941c24141444203403a502c01c0000d21150403c07003048049400d014050046034800540948284070100d10503035030756550700f000c0c89840d0080c03083c030005081500b100c83d03183e9020f80301c2201400d61001402c44110302c002070300d050070007490020804031000522061644895102064001c501c040c0703941031031450040c80320b03900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 708610737 1250 708609487 708609491
    0x9090902030c010c05070b0a0905010e09074b020f061b0307030b0303070614010621021803060a1a0a0308090d050c0607030507020901050406080a06240b0a080703 71
    0x16907022421980c030000c20319080104001d5410710f9441c14a02da40403419031200050314081443e07005405201307480d402c0e00d5051a0700320101c00c0c015540401c4a1407000601408030908645e5840360a201d1180b14240c20b24401c8000e010205006080321409192a2603017000c0841e507460301030141a610603144c40c050b2030107140c0500c0c1c141000b107960081d542c0c80240000010301c0383d4000c0d40810001507020701200d4849030301c0c5c68201c2c001e241d011088022001c440000158540c401c0c14410a001401da000200e000d400484403c0a50001000c1110100c45200c0500054800b0000c161003a00642e4000c00c80280151080340006546a5614050700c0f141c10180042080340c0201d4003007a400b0344901525451134181103080050b600e800f9980f1690001d070310414141e01c04080c040060007100d001a050343d9500802c0102c40c040c0c4110403507604020550404642d80e64006240315603400c5004003045809a40d0031510503807034010651402005c42c006003c1644144101d5018005042c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 708611987 1250 708610737 708610751
    0x303042408070507060507200604060609021306030f110f030f0714030f0414060702070807051c150605060403060c02060a2c010608030d050618040c120203030c1c0909 73
    0x300400d540704c0c040c00503101310f44070b102054031244a4980c070510070369940468900036007080f4403941c4682e8255400d0718450704203240402c04018a108039480090580110180b0310718050095014108083c6036002c203507503500415240040c03c6000703080050b920004283c0d280381c07248076038110b02d2019118008000072128110b58940b29407080340c0d004403a9040c540610307900c619200000a41c64200c10f0103601890050100d4240c00107140000c0d5a00e0500362120300d6207038014028a40f080f442c42d0050020300d95083c2c00441d40145900b5081a0b48000c042105520ba60118000b070748981d03c103d850f680d444055130b107940d50501010b508242d140001340050564501c1050402c611800c000c0c0949a00c01c0d000407c00d502584203800400c210401d60383c4841c0c155030410020501221514000c091100300e030240107144001051042c1d40c0401e86801c0c242c24200c01f0181207030f40700012a058442000b41c13003141d0904000100c40000740070380e003690158504030300030a07844c0158010480c00303041c105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 708613237 1250 708611987 708612001
    0x140f04030302420a1e0506030d0c0c090c2006190506030604150209090f01170a030906120f090b18030f0d1503020a082103151504050303042408 63
    0x20b0210f100144010346141d500c40c0c1141100801900d2502c00d034254421100b07910000c42c07504654070170304045082e100c980d00c100609071880c010f1107000030080030364a5006d0080c03440d91340c0948c00702e4000c0d1429a0101c0b040441c92400042402200e0495621401c01c10002c059a4440700e10850b030048800c1c04541490380120f0f5692401038001407860410b4103580c180d030681766041d120000350040c030840710b60400d40503808614000b8014a0301c00440b2240319091114006100c422032980b43c0c0c3c80d150803900c4d100c01102c0b11681111711f01c411a441d00f03481c0e0704c100e01d18043c4008944c01141c000503141040b01c0740a50340d10325445d02900982080c0082d140c21224035055900c3e00c1200d80c40483c40310106510140880b0f11904000c1d0311003e2040b010405020000355582c04015240e101c045002c3c41100032030f014042111183e007030b0f00310441c602d140d034148115240c0c42e401c15040132608040c0c580c000241103401680155880b401c5102c8070036000b0000103c403403008000b0f030910441e5420720305 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 708614487 1250 708613237 708613333
    0x41e050307030309150f020306100c080703180509010b0309010605030d090e0411040c0503070212132d0b0c1c1407080c2b03050c0901140f04030302 65
    0x81c6000d001c0c10307640c1c8206420720041c00a1940002d20200c410062003001e241e807000207400603218240560503561103da0428020040c103d032403500202c05c070b03040c10191395045a1540f9041c2c5440b0040c1185c1c5000249922044110ba003e4a00350040c1600e074a0301c8000d0901715801a80f14901c01c1c0d1028401001d496041504c130303000d030b560048007040f185e51242410b00c102a00380884c1600940780c14105803220ba400b2001d14006c0c1910303802e50303c10803103032101603910b40a0900b41004400c044101040751102d55034113410010040d411780d00d000901143c40034031240341e42d84a0f14017650001511304040f0001e1082c070807410080340c061160b00c0e03400c0000820310103846161440360480001c00d4000d2103c01d00658035008200c00c12510300407210350406c481e88040c2100034460103a40c8040e40a1a4024007070707107204140223030000e410304e40da60004469441c8130080042e1000da00f003000610b011091f00007000618026001016101d00050000c0075402145003115030803008840424400382c624 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 708615737 1250 708614487 708614497
    0xe060105130c0c02030a030503091e0c090402040e0106031b090608031e071b0617070804020f0103140c040503070e011a070317040303061403150c0a03110d05041e0503 73
    0x10840008001107050b10540c2d0400300400069414881e021100742055400002581704030200b100b42c90302003540004003c041c0d84120348011841d00401e006480c1c5040900080c1da000d40000c002080c11410317000460708544140e04243c40800d415841743d05031001c000210300090405000420400d494020303620348038003c90500c006c0519044c280c145044000070260707a0265013103a10b08107a80310200368401c1c2c4003954400c00c0d020a05031200c030b04148240c1c000c0d503449810640c0b243c0352556215801c01200cac1d4401e01001e0305159030380074a2400c0c1000c0c001140c0c403402405014595441c00d11041514009150b0300800c4600380541c01030201c40724100c104202080c22558454851210307107407e030366583e4800d81c0c04006241f03c0c801c02040c150b0641111045518003103100301e01c5060301c41070540b18a80380d1a02081903404070081000308100000510007407100c3d00c4d00149240c14000718a09942c4000c045011032a00c45041c0414460003800b209500002c83c40c208034030190760741e00d0030707200d0040d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 708616987 1250 708615737 708615769
    0x51207062c0f0a18020301080d03061d06011206301a070903060e010902041a10050f0403080703080a0c0201140105010807030e060a09050105090a0308012c0403050a030e060105 77
    0x39000d0b0700c800340d10790203031960240c0741400d0711030003818000907558000d4200340b0802c4000d01c80e600018520500034400c400681d050b040000c2c1c4076143e181c5048251080c080d000504020f411740621419580714403c0c0c00140c108200c0c8540c0c00340340001c10710210380c101c0060380d07807012540915400040360861022100201c0c889885803c0ea15280c080e03d50325084d5001504903410440b1000c44c248040d8400d0b0707032561007110304020138020030f0700340740040e203540100981005d0003001c507030710060040000c1c00c00808009009498107031282e88a1000d50403072201240030036445000d102d00389006000e050201c4405100802141582030b05a00340b1105c10722502d414814503401007a4410301c00e400144a00c641c4008440341c0e03081014a083c0140500502a030b0b40d5480c00010900c0d00360301252034045036802d542d0310a400d90901c5d80e1240c0119080c02c40544940ba403201240c50b41d400424110701c580c1c02a11215150304501d1000340603a10303c04403000e2181c00840041c0515a14003107034142d1240c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 708618237 1250 708616987 708616999
    0x2010614030d20160501120917090d15021309090201140f12040516060905031e150106030603110603040f060c0309080c06160504141009051207062c 65
    0x1511a004581101c501580c4840b5004d14803c94010720101003204040b2202a41d0f0103018080084c0700a089a910740030060490781d407408107040309280c0d14003400d85010002c100752400c800700d503540c00d8520409101c540070b80b038020541440440a28103803000400030680b080c4840c00907a4002401c075042c0110003010701e903022a000032034490080642d00b090440b038409200d94242401c103140d0b51101c0381680b0801e40d07000c00010801c0380c410600101140d2020b40202030018801c900d02c107075485820541249031081070300b5440c003040c07074503101c0307008010315240000c4070703419030812002c2c1110090180780200703c10818800060407100c0c421503115000880000d540d001e140088018244081001d0120b89010421460004020030701500031a8180e03070500d480300c034011081d240ca00940c81081d41038101201c04524905041c2c0c0c1030b41c10314103603280082d005910744000841c000c078074a02e10401c0d40d02000d400e11031540c00c4240d22100c4e4000c6200301e82c40c04846040000d54002a88040c2d000300c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 708619487 1250 708618237 708618257
    0x705120c09100312080603010e070f2108040b0d0b0409050c0d02040b060f1308010c0221090a09150905010b18040b040507020a1a06091f0b0a0f02010614030d 69
    0x1100503000b0006943e00881d144000c0754000c4008040c0007003a11814400e519000c0d6110800b080010241c04459010410358080340c5005907003140940d64411418481d031000b184000000d500100620107070801c148241c1e11100c04600c2c800c101d42c5084250350040c1e03d80310a40011540014024100d0350303040b1510340405842d480418040e00700408001d8220750040768a2416450700c1e400b500301994600c0c006590240d88164507401d841d59014400701580101060207040d03074030510402c403180c1000c0141840d048414010032144011030f03100228203552003055498468481c08000e000340480001801654100292100c2502c251942558411181c2c1c0303040b14587c0b91034000c55415440100700300040d00c2d2645029403505c0700c1c400111407811a03049075000340c800c20b004150160401400020b030035960b500b81c2034150158003020748500703d5211000200f01034040028030142c0d2082c0d403214507408080e480642504d840b90041003001200c00100b403042d03200082c0c4140760624601c5c03d401c0305 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 708620737 1250 708619487 708619501
    0x3060303142107030c080c0712050d140112051b0307140301090b011d1308030f0711060403030e010b010e060d0203060d080f040611030a0207170712060e0705120c09 72
    0x2c0c220044001c484002c000402c00d40b00c2d01540030000788080c1c1d494614050f036920014101c1885101c400030304036100c1080141c0854400c201034001c24000540008030403200c184090621402607000098031806100400f0410100348503032154200007020314088455020006038a519040c002c1040500a40e900c00c10070340d80035001041c4454100c3c030b460f011541c462803421034401422504052003030140001c140416804c912080b01c160300000310b5800e546424046050070200500714208002800c0c40a0031017020602030580100c2c400c0c0c40001d2076040404686082d51182200c0c01d060003d200310700001501c510044400710396980b200180d59942d541d002600c0d000d00e0300c1010308203040120f034603025200104000c20036230b001521001d0000b82050006640c80c445c00d440c1c3c02c0180c010400070824910748494042c101d0000c2001da4041d2910380360b2507855107640c8030082d03601d5902da0741d80e02020745062102101070882524940f1000504200302581d90141041403070040e10850300003400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708621987 1250 708620737 708620767
    0xc120f06181e010e0705090705071b1d180d0206010306091e0c030209010e07050d0906020d020d05150306010312050d091202060a06090614040b030a060e1c0306030314 73
    0x2101c00000071480e50310b40c00c4078000e000f0020251244658825814041582c0ca0800c0f141e40c455550303942c4580c5002040e6a48480300004100b0421005a030180702107450300416030304054444000a4110703243c03500a841684102120030310f0b41c034981204c0400040d940d40401c8180c10b40350090b5011841d0b00c1c1c24680030340444454080ba502030390ae42588841009021466a4100c1e4000c03905003025903214a616125100e041e1810300100d07108100e0842103646039044410290f000e10303401800c081c81e001e2481c1c2a60302c038017880180d003941d640c200581c5006900000d2000c94060b0010005c5604643d0340980210090076594280980800c00c00080382103500440009544450544024129000301941c0d0300d005035000c8019604054010400000c54031600d01100c4010303080004464210043c4401464015040c0e034060007940c0a840c00710f080c50107120b02d620403c3d4010240c183c600000010b0315502008020201810868100b0110350300001940152800210f500c1c0d0b00c41c007010000300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 708623237 1250 708621987 708622003
    0x90b06090603092d0601150c060b0117010f180501030302060f221a090a03051b12040f03021806060301060e0f090106121503081608070b090c120f0618 66
    0x40c3d000644008192401800c01308440c0d00301108072811641c031101421040d0382da069000700020800202c22001c1002600030350441d500604100c0007502080c100d810480000342c11a0410001c0050308121340081d03043c444102d0300038403404201c0b95040da0f070000c5d03c420015003030b4019041c4080c0403c000002681010070300c0b04412004002140c168900a403a49049102814a82c403895000480903240840d1a040040d071683e2071904d0300d0411034094040c2e420039039603220180f00c0d46a580c446c03c90742070001c00c0074080c00300603a00f45070f02e103104005044021100e82e00884c0c00e040c00f4408a82c42c0c1c003050781c3c150b1703185062040400c3c41c0c4c0c001042a020b0040303000d070b610003181000056200e8100039a2000200400018080b060311540706000c00d10711803000030070300003040000c031400b43d000741818032003648120a001d00e40002078694104c00c4005481c4070900f03400c03211003c485440e0a0710b0010031102c401000c0e0510600c0041d01b41d48401c4018507030790800c00460003111425009118400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 708624487 1250 708623237 708623263
    0x50c1614030c06060a080d0c0303020a0e0904140105060d030e060d02120f04170406170c041203030501082a1014070b01030c060c050319050d02030c030709090b0609060309 75
    0x303440700c00b101c61042c1e407070310240d944501950460201240c42030001c188aa082c02042e10382c000e0b81c40d0030b0368049000354004030f542020003942d10324010300d96407107803a00381c01107005444c4081070043c1d0385503150844001400e09032140f8038150507540000e81100302107449010484400b41ca401005110601034071a10002c021000181c0701000316201c4510481405079024805000d09142c940300540c1c003610545c05181e020813610643c1001034119a4545039110749840d04050800340d9902820b0101c4905c200100e021a032580e00500401030204104810094418094040316109090000418401c00005070140840c4680300b00d1042c00703a1a001029200b240443e0390b186140e0405981065080c00308a0b1014102c140004007107210710040c031421908030002c3d52910745c0110356a0768101d481276400d800c0c440c040c88184540700705d80c40514401d9201c104001e640e464244002041c201d03a903040b00d501c81c1d1030529440403e80b00d11055501c11841645c0716692a2280d607011441d20340542081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 708625737 1250 708624487 708624493
    0x40f0602040b0a110f0615041d1e0d02030f1b01090803010801060518070215090c0a0303030203070825030b060c0105011d070c050c0607061e020c10050c1614 69
    0x159120f6a400581c60790600c0351881900c0030540b9803c000d41d01c4940079038142c81101054810203655113415844035407020550b9552041943c10f0041d403d04110fa4802d1011111001ea1460f09200505100c10102c8214903c060742c0b03440b81d881070306900340c019111842c0045040500b0000c0031582544040141500045104e480b5030b9118452400b0f001e050042038080c0360f40d2509070340060101d01403980240d0761500945680c107011f511742910b45000a040340850f1040d944030009584850640724051b40c080c1d540560b80c0e10702245e0182091001900c41140645403c0002c05400c0b02c8510400a072210ba14000c509500d110700001d10310700810840c0c410551070100009561a29070010713880009071403c0701c22081d40c0303404082c3c0781c501e55000c0c05001e9800c040054070580c80c2040c0100b02480c810280000e0301c0a4014140c850213038246408200e05070300088000c03140d501009605d41e01c280f095400d00103883d00001240b840e01914050030040107144419808000070004812403406403c070403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 708626987 1250 708625737 708625747
    0x10030f11130b0102070e01050603150a1203030906050c1201090f1d0a020127050402070f050f0a0519170a2303041b0308220807120b0702070509040f0602040b 69
    0x881c2000b044501e40d2907000d07204a00c00051021280d200c61412108010440ca0071959040d1140b201d08406070407165202480200120380315101d0240300b00214080ea0380040c241e441840d0400840c0c40c0540800c894420a00140b50700d42d50a5104a056804244003c42c5403040c21a882024200c000c1441c1e0300d6000e41070101c0d030f21102c00501c202c0d03128003d80e0f070354014140c5811420f140700403a45134000803800229060180d42070940041840c54840d882e80c1c5c50700000c40e101c1508008820200c20030340d8200d81c81d0b0071b050100c1000781b0318055403801030184c5040c000303644201c660b841d08000e041b10035a0200d052020305001300f64200c1c1d5480103139696964503d03424500c0c3d030300740e004a42c00c464175041c0020b10074030f864148010905590f8441c042e10b290050860394804d05102081a0051080d09040046107080707060000200030315171a15200380b07641492070003220315203000b400d000442d4051441002140c5d84d40e101c9542045d044844280351403030700c1c200f41002e8891a000204a80c0e00011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 708628237 1250 708626987 708627019
    0x1811040c0e18040b0f060a090506220207030809190209041a04121412010311040915021e120735090f0d09180e010c052110030f11 57
    0x4940d0344118881c070892004d542e2820000041c6200c1602e00640110039a08240840c194540c404ea401031401030048900c60325034181c0301003100705080c00518140d00880e6045c1050303009071529070440c445801034140300822003031001002e00d4101c80688a0300ca04030100d000c0c08042c0003404401d04076650903444500c0d29062170a441d4101414400004411b00c000b001200d01c0349055810b400282e03519008071b03920319111107809043c07803a0040c1d440790344c1e940502d00040d44c0d02c102c244d5100390b80c0c4006d40c5036000445c402580c0000c0320302c07042001e5410171542417485c01d050040da1348640c0509001800c100240d8102c0c2c1d0016040c00c0240250141c1003605400400803521607128035201c100716041c0740185048541c40300454403010012880d108024000c0c0d00c080c80e0b841182020141c800514014039100c040c0c00c3d50320071900344000c1140040c0e910309000301c560090008035000201c003840c90400000703100111485200161100c01220340500030420705601059468200030134800304214080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 708629487 1250 708628237 708628279
    0x60f0d050d0324032001030f1e2004050402070317090a02130e0d0e12070e0105040501080d120c1b03080603060106111908090a09050105041811040c0e 66
    0x115441c00002c0880310440844a0382556010a490307204407000240d8002541c00149034005d500d2203410315031a01e04001d440342142c846c600f05143e01070083c0043d0171846030351200702d5410b400082c5a8092074100c0100403a0900c045408a03401601c005a803006107040440c4d484030701d928040307203801c5200240b1a8101000414001c1a4022290100d1001c5600f0042081340da51580b82005d9403c0405000c051074000c0c007004d04401e0003d0400b0011380c0003032216a0130039038640c2140041645501c01404036080034490240500385a40c000d00c815400c9802c06403103c8070041c01301c1c030b02d0b64403041142d8050b84640c2503814500c0c6041c0300c0b4462204203207000780c8901400c880c03050003441200c00002d020b0b440342d07000951280040014190030702c00000b07407030041d000c0c104041c1d031038210030054903d07140c03510300144004240750040000c1c0e0f07504001c104403d0301d43c80c54404500788400140e1801180300c00c800380c0c03c1c01d00d048900040e00709076800203803071a240045410398005050080580c03c0100e030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 708630737 1250 708629487 708629501
    0x4060504050606040e0c040e16030c0801110c06010b1312081e04052b08030903030405070f051003051305060106050d050f0c0703140c060a0605090906010e060f0d050d03 74
    0x400a84010b9914403044c041100c1001245143d10707030002c98505141d08103a0b2029500211000c25101805124000c2940c40c40749540116000090020b08011224081c41a8402c04401d012454079003130b0052241669410103015140760800001010540c09070b12040c88002405009012010303a0442e0070072403115089641d0911403c0e0240c4405050b8109110454060358002840c064800c031071043d55030304400300301803400384182c0000962804241d42d00003441c400c552400045980749001d18080f400c0c11403075880700400f40c00312007040c0a55980d1500c140c0c044031003031600013215070320f112103080c0494003008058454011a000869040d80c4040100080e04500d002409603843d034801d0b003c5842c10860702081c0c1d400d02400800300180c820180350a1580e41d803103415023000c0f844540181000002c0d104c0b08807955480804001ca42058800c40307500c4602000540483e616040424500d0800146198401c2210b142400d005648004103440110340080840f11000d15907080035000b0450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 708631987 1250 708630737 708630743
    0x13030c0602010c0c0215090105070501020c160801020406080105090603010b0409030221070c030201030b010c050105010806010e0f0601020a260d0614060c0a261918080319020c0904060504 82
    0xb44a00110201d01139201d04001560141c42915030403410740e200f880640207440c0190401200b08240c00c040340003400603280801100b00070300284440100c1c8510004141d80c440c0241d030340107010400c51103400004a82c1100c60030303904081c0c9981c4150000380148500c030700c200d41c000d203402060303803c4c10350000e60040d03040e44400311800c40410800c0910b800d801601c02c001d0501c10880020720055101ea041140c0c5400103041221020165907580345c29641c09030440c1c0200d40c03003440100601d14484940c281c000012443c145080d040c0000001c3d2a01010b80001e0905102c0c05036041c0700d0340ba0f0162840c21026006149602d8845013004170000d09441d00c07400301507000b4141145103600e4084103c03081524400700034000e185803036031000c00300305106c0170200c1a12550700d600d9403e50300d544006c0044204a03501c054a0002c1440040c218420981e111011100c803408103000700e00000017124400100f005840c145200c407501e0481c640704c691824590003a000c0d605000c100602900050700070f030702c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 708633093 1106 708631987 708631991
    0x616030507020916020d0c0f030c0201120f05090c0f06030714040e130507090c0918020f0a0c060c05090109031101140a09031b0b0403080f13030c060201 67
    0x2030201d401d90007140503414100b00242c1c0c14007031b00820f00d001d404d00402d01d041c0c6455052032200311020081c140300740d9204170019a0700504210200700c900607000e00c25031468040b040702a00c81a00c0c0544c4c40e11403842014005e152042c101086004060241d0b810755892190440c1c0071201c0ca00c500e032080904000c08602c111480c0689403046292603c003400121862401c0351400200da030010a800c0d2910740304012172948080450200d81c13409100c1c070890741c400c03200c400080c4a08414400101d00010700510b0454114549112060180204014030b03017498100313075118890010303031a002640144041c4000f070100f8042c0300b2902c8042c50440e11600f81d40810402d160700c02405c107004110030160410801c018445044018401c4003080f80c4150301d130a2004e0060b00450000910011001c580020116946410795a407096000021001e8565904111044c00342138062240154 = true := by decide +kernel

theorem cover : BRFrame.Cov 708453237 708633093 := by
  have h0 := BRFrame.cov_init 708453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 708453237 ≤ n) (h2 : n < 708633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
