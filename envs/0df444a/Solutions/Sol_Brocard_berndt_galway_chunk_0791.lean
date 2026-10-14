-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0791
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:49:18.916986+00:00
-- url     : https://prove2.me/submissions/d648c33a-25a7-4d68-aa18-cec91a91ad22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 142086330 ≤ n < 142266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 142087580 1250 142086330 142086349
    0x90a0311040902190608071107030b041e05100e03120f0a02071502250f0b0a0608010c05030a0e01020a09140a0909030c02010201140907030201030906060b0a021506030c0d02 76
    0x40544000b800880d6600026041c5a07600d1300840c3e4191040f20612600380d110b482981d00c8181400e1a0640d08a582c8010762703a11000d200103424081804003180070000700120654030ba1a501c030500000c9111424803e031182010b0f2001180203241501222100c58080f00796078209901c103000211f1a540d5143e00d01c0d8102c4000c08440040398200450000544610711101000121400058a48440019541c0420b0000081e01c0422803a0418400011035010034110b01c0c9520804141494075a84541409001e40b6009510f40b942000343c40d0074110f5010000e54802c07a022041480781481480c0a14200d01c502441c10000072001c007014080c41d80103142c49602d520001d0212a5181e81e100c21250856108185c12030005807201e691109560382400360200100304c05020320114144145000c0e0b450649200007418191601080c00a1003280c0e4407003401402c0003c0d49540d5060900e20094840c03034002c0c07a03a007420503500c011507101d08002404500a00000d03080c905250015001c00004c5072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 142088830 1250 142087580 142087613
    0x3030510052202220e0a051308030604020a022811090c162409061b09050f01020a06051302190b0a05090301020d110c010b0913060b2b060c0302090a03 66
    0x850030001d001d0800704c0032600030301c480319042105052041036101500e40180c80d20152040300e00142c000710710758808590300a24126001641c2c1c84176590f0680c14000c01c02445c0c41c00d02858a100b001310315000d402d02c0c1c07a4603c5a0f1440100340c0f841c1e000c20008072425542e4a40b0810144122071064640000c0e1070007103400f074045e2807600040d07005d40c0d5a0307520710743ca0100003854891001d1810030144e0b014030038405501a195201003c0c080700e00a0070040c8910072644504031f5040c80c0d04103a4000e028600e4610b420440c00d00c524a4101789941d100702d03e8440881c0282240004403aa80d070035580c441003940e4040c49180c0c43c110340084219504e40054880d160315550802130288140058400c41c0d10b40c801c50000380c1c3e150503e542c40b0320300b12841945802d0154513240100035000c65015200f0b10307080d44c1b0101c0003030114081d0000c602c012503291071242042e18401d48540307841110400425543d88580014400c0c1c1e10a60011800e034010b80f403003560480c084580a00016200002000000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 142090080 1250 142088830 142088857
    0x5040e030d0905010b040608011a0f0a0806090a0318061407030302040e09160f0b0324030601080102130911090d03020c0604060c1703010303051c140403030510052202 73
    0xa0124107030301045540c4050304461983d9500200101c1c0d082a004840081c0f403110020000c52903003140c41c002d114040c4c9605481914082358000680e40d4404000d0b0150021000b00c4840d841c020743d000c4d558a09440007600802c5202c0c0000314075403905500c0a05680c1c003660703044414051504509100c2e04900d100704c041c0b54091001064074080521002e110705072640c001e164000315010068402e201642152942082c020014055a00c4500c01c40b41c008403001846850000501045051181100c40c00c6916004180c000502e4120540240036811840445150a035a540001c80d08a481011540c40600010b000c035219a00e0a03064040d0094002d00640b541c1b14451000189261b00035001000031401d13950120080c03100000c5418012040180514a10350458401410300c0c010103071441c0c205803444180044403500394101300140d076080ba82e140c9180c20285405006084200c400320161489101d0004d070781c0c40c1c101d460b00c46541030000c2c910101d0100c0d031001d0010b9071184010043c2c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 142091330 1250 142090080 142090087
    0xc010f0e031b390102010c090b2805030a050c040f0b180a0b130e010f120305120a02030121112404030b040c1502030f07030c020409050706030c0507050705040e03 71
    0x12401c5582e91000e100c022882100c1105249400c943e501c2400c2042281160314241c04051026007061a50003a541d02a0b4129120340c0304409000c14911104801511111042800340a464225020714041c5407980e01c207210581d9004101c034050700036840f03189010b2440e600100240c0b01d41500401e8440f40c0c18801c40c0e40f11489001055050321030381c1c0101408100011741003480c00603c0700b00005014560540700c460f52400b440080c019106004850803922401a003404040c0108121040000070a031141060303d0090a0fa10080d0400d100302c50070301c6500c00281d8220300001c0e500c01651540061203c09014900c005e101c1003040c55039032203c4040081c2554820040303418090070046110b1003915030b040ca0240350404481c0d50b154410000c174040c2c6224580c0840d00407007950180c90542042d41d449102e0b03424100c550f5003004501a40043c41c0c18035200500501155240c15144151801c0c80124038044040320288105000942281c12a441c180494a40341c0c1180c88002000800c5a05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 142092580 1250 142091330 142091353
    0x5090618040501030c42090e0c0301140103020306150d060905040f02010e0d0c06140415030903020607020c01080103060b0a080607020c0102011409030a1119080c010f0e031b 76
    0x11502c0c04c0c1c0094541c00580340042151619400c590102c11001501078040340180b5102c403c06041d4042050100900e00b0388030398401d40c40392010400a124a0003503035640e042500603a0080e1f402030180581071090684014820b50190080fa4007071000a42400e10703800400d0703440141030b0040c1002511803030b11800000750f89a42402101d000da4000e9120f250b25035458800944101e100a005078043c01d602c04802020031494805502144c00604102c5800e13001e5000c589428805c0360003000110f5441c411983c6801c0d419400001d070750b40300340c08030b810035151800141e9441342c114240f00d00040800005000242d1942c1001201000180c140c2d14100d40b1828802d05111080301e00304c00580c858410788010390b909000d480c065106000303590301d5501f000c0c5482616485103960210920442413101d015810040003903a038030402001100318032103803a241220440e4050000300440d5824811170070440c000521400021854180055141151044c00da038401c5004102400b428002c2044803070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 142093830 1250 142092580 142092589
    0xf0c080405132906030c07020310050103051501090218040b0604030605011d01140603160e03030c0304090b062503020705090a06081504110d02030a0203010c0e0307060e0105090618 79
    0x10380011101c02141c028808184a040660600d0034420001000b00d614103190b101c104c100d980001c0c16490040e501c0d01c050010a207012000312404201c24a403100000900c54042410b188010b40c0e03010454150341d0316252075040e80162a03864124110003d81148649000d902126042d803000d8101803c207035907074460008407042644031109080c008070010449071504a41c0781c1c050079402642d403146110b0403004c06c006000003400020351440440248d92014015069000d01803401021a550341c00c110600613201d401070b210340d80009061180110750381c41e00e2000da40e108240d80c0d00c65001c45861200f4100b841034207040c1a400c4d4043d035a008a5962901c400b002e00c503d22424010607800e150086151401d01140c0300918030341c00c240e06100c0000c00840e030b1006000d00c00c0b206001c02212500000e0305040e40200002e500d0761804202d42007060f0400e506810b803483c100c00b0390761016a0f40d54190381c01000d0504290005004020039800d41c07601102505071500d1114600001601000215 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 142095080 1250 142093830 142093849
    0x109090608010b0a080706090b030603161820071b0e0c040303080c090a05060a0516060e0607020d090306050a091a0604060b0f030103020906030a050a0605040b0a0207030f0c080405 79
    0x1240360351584003d84603400e00261040c02041044010150140307840c40040c00246d0302d025100803a0f900102040184e94100f00303102c0c421074107000b18802683e54014400308400c003146980307400c82c242105540070092014000e6619190260750501e020704a5603035188585400054103060414010003080c08080e060b200e521410145005668442c110f05014046000062a4102010381000406541d8070340001520884030191035550b11803a074500207403058055000398840c2c1c950850000070030700440350040c890b000701384403e4600c586c58055003240c441003403614010214a24001c200002050b41d802581d000c480000c0002c0d20700720666400341f11b40704541050040444070018080103240034401e0b40300408808480074603100c080d1088d21294001480081c0c41f0b0404a40061503d0702c080c400b000510b9484000d481368194685822402400d003980c0c1030710700166560000da1990805c0c82120201500b54403100d6840411100c00c4031201286001103030942800e01c00043c198541521b803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 142096330 1250 142095080 142095089
    0x609031501060e03070e24010e220b04060302210a02120f010b0a060c030809030d050c03010311030613060b0d02060a05490207050604080301050f03070503061501090906 74
    0x183c0343c0800c5500c04151501000e50040480600c014043c0001e80b0803d000340034007904c0b10503d6010b02a50400160b8582c200c60481d1900544a201d00006031800f40081d09000110304504000456038001400100d074000d000094102c0410302241107540140e5800681198030a0112881201940d001c1480031070401d030817801c694004924481c0c602c000303000d0380e181c40c5070513a0400c840c41e00d0144001c2c5a900d8410b40601070100002c04203074075110610132200060780218050005007002d0341c202103107a01c24030043e0b03008070f9040e080d01440c1c03401280f0315002d48102c01c40c003900c1041545880008000500f816540f01c9542d610002c01a100d10000d44000b030000d80340d031903c0d10039280042c1c1610704803402181c0e190000c0c00e0503011034004001d28061015640c00b94070b40b40742c09a81c0c0d000080c0b20700b4a02500c2c0b44240010031040148280085051340c100f41c0f002010591684145640c80b590b41c003c1907455080b000004100c0c4900700010206501d0503d0444402035403030340c00b00c0884000b50003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 142097580 1250 142096330 142096337
    0xc030a080403021e060a0e15090d11011406042c010218010c05030d0203090a051c0906080f010302040507021501080105061f21090204020c01050609010f080606060903150106 76
    0xc0200340b40c0c05101c80300349181014411641c0b041100da07810348401c40104203c014503901c5d900007070b1400041103e94104800307800248008c0c10405402c5580b104140c1030a00001d038640c80127808600103000f90070042d02140c034000c005441e50710810014094507415600e44c400c482c4d07420090710300a6950224280814000161341b1488d1075001184a00d00e003407800d040c00b42d145c20100001e0000011940c041568a000584a03100e9010302c60a0114a03000070300680b1031815412900b0900501410072122640c0b1001e00c400c0d41d030300003901c5100045603d8100148417900410140c04e01e80c01a681c454142d2041d1610b200003031110140d900400c0e08000001d0b95140d041003070500b40852a5418030441403113a003080004030078024100d0100c140006d000c3d0103929020340c5d094013242c10811003140d00400940d1140301a246580c000c0408440340741c828001c3c1000001c80256080390300301543d41000192107103079102400c0c000c1507804601e10681611601010041090140300d003213002c0c0c1420764 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 142098830 1250 142097580 142097597
    0x60b180d0218040b010906080106030503030f060a0308071a01090513030c080f0c010603060c030b06070303150f0605030a1104080c0d08130806040501050709140f03010e0f010c0311090a1205030c030a 87
    0x406c60011201c29070003a00d016071401e4002d001055000054a5009400c1603c1c84841c1d601c0c90082840b1b4001680300422064000c40c109040148030400c0c580d0030780118058040076a6102038080603504207071640500100c008902a020a2103205d422903080e0080750005e10381448242031040643c030150190030141d42d41c52080c070812026011708c41800a851406004000041002401520402e1801070034503940e248034428076024106000300070804041801712982d41c8a0001e40075038001c40300491058502920070066110280c00d031000d07195068001c10744041c4840c140204904a184182c0d10b030380041c015a02104400c030910005000e04e030014121a0400d03142031070035501702921160038010203403410b010b0200d41c502445800c0400b200c080304032146c0f080101c0d0050078012601c11307190282ea60002c0d4103d5054002d0782c160303042550b040011031060355015190b03003e24800564040b640036000c100c99854030656010741401041924600040100710501e103034024110040412400c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 142100080 1250 142098830 142098839
    0x1a1b0f18311406060d0f180b13080315060c0f0a20030309040c0309050d020c03120408030901030902011205090a02090a09320f10060b180d0218040b01 66
    0x70008000c800c0410b024084022542c0c03940e842c001440c0744e009000100d03c056464000e60041202ca604500702005a01080418400b450094103000c0d04c1c2e07000700360045984107100c40c81042c070264001032031a0940d281c0a12118501808107a590b5102c032091001011810302030203903481d08444440100180d6480b03103083e4081403102102504042204031101490703407004002c4600100048400082e0001405420b4000301280ca01c050454880d9146020219800180d02c5a000c90f040b012940c43c0b10a8806000e00340c45140208207194000344030f2a4015400303070308420542e030710504000744100f0f075401c201c1046403c200c0d503080c829400307003401c0d0b0158240341103401d4100c24080300030300c0141c2d03036501d580710f80101442001007220302074071007401c0d0400902c2c4901c90078003183c41645e0900342c07041c40503599805140d98040c0500d140a20020301c80d14601c2c121501c02c44504244e94512041c0350400c42c0005051000380d810194103809a0182d00f00e051300340e403040d44200c01600c441d5060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 142101330 1250 142100080 142100149
    0x302060c07030c020409062a11030708040e0c04080609030a080c0403050a03080408040906080f1c0c0b0c070606090c090603060b040b07020a030b01031a1b0f18 70
    0x150103544140c00070040040401c1c0c0c0458001d50f29a0191800b0400811034a4003000030094030f9a1050703010055018100104001c01039410802840e030340c0c0800410031a00c40070749a22800e40300900001007080f0130080043c4003410681d02400800c4010f0078156522249800c11a04070340e0304146410005000c00302641000c4c2650b008002c2c0c10045040a0a50f59400c1d0748154142000e0280f006102c0024200440b00302260060400064240f2a03a6581c0e095940d85081e001e101e22418060103030402c00f20952a031a04017103800580e00e101307048800340c03511410088050700109607240100280008182507000c0c13000105182c01001461407266040101080d1071900807030202f50130014100241c04189003a5025644207003495075442d4424400038058610b50b40c001041c894910f40000305000c003401100d00c0090810210341403950300e0240b0880701d2a54204400b280784d505110011080760804081d08030250010048454914003900040302d583d007051441460600a20001445591 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 142102580 1250 142101330 142101343
    0x7021215010e0402010927020d0204030c17030306010507060f052502010615030b0406120c0303140a080f090f060f07120b0f120304090c0903110102060f18010e0f01090302 75
    0x1002c41c0c0001c45041c503900003000001184190305030040c0350303610703aa02d0405d44e02c0240034212076001d0455076442c4080010300039410a200942c0d0040d6045000940c0c442080000210b500780d4a0243d4503542d240c1006640b00e410648050b43d010341c3c1c504c025201c040b0305104107409000c0c61190030700c00b41c0003600406003210f5140366400071641868410400c2c10000340b5400301c82e000c10b0401184402106001c200244865408001c480c070035511240c061249201050741a24040d681c1c0d0089404042d000f54158031841d288480003c1031000002c04001d4a02d0742d054000345000d00303070f0300c080c4600080c0034904071f0259070300504510054284608140c2104150301e451561a506028081d40c00c40028401e10040f107101d0300030000840c412080300070920848020700b046002c00c11600e06d140034010504209404100d0b24030741700680044a42d800051840d01c41e41022890741d81c10364070078a40108010010801d4001d543d00ca03441007859060510030300400703155010001400705030303d0130024600007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 142103830 1250 142102580 142102589
    0x901021918050f12030f040603110c120703030e060403030e2a1306030c0b03010312050702130f020c071d07080105090408030717130b0a02091c05030702121501 70
    0x2000c0c04000903000c200d09031410480b18216010701c905640e60010500c480000818400540400030306060354904050203003003134410b550342c10040c4a040413072129491003052900d000503405014400c0d0f01480071001000c4c042c0c82440c01107102405035a46903d403140c217440c100c1c042602c4041303c40401a0400c1501d1802140841d80c080900e00b403401c024003c840451254042c038061034144500d41100d401036002950300107444041141e6400711202e098100780002c40c1c40c0d401e09903031005014801d8068907081d6800030b040c0e481c85804102198000e0140740c0c0461806078003440305142d880018800c500007016110300c405d40500b908040181c000e50300502020510019600603c01922411003071030340721b540458020741c0d07515056000e0b10007081551442898141845c20440075a0066032200c464a1284848a210340c0340c01200070140d009100001c6d8121050307025600440d41c4a0000f94640703030007802038038034240031500400d041301c1286102c00103580c00042480c60304c0040948075070060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 142105080 1250 142103830 142103837
    0x40f09030e191d0c0c0307030f180b0d150503100f1d1c09051507052b050d090206040605120705070515220b150a030807020103020a120509010219 64
    0x190400400203c8038514803ca6600c9400200004010312000b0b030494040d4403a00080704d885aa15160040a03240740c0701da403e0001d4981c030100c4020110141c1d00506440748809050300b400c1c1795010141c000c12802110242c0d030915041c1c00100b548081c02140a000000d6801280c0d101c4a800c9580560320f2035182220003100070303030320701c80340d05000710311505444200042c5070135007504000d0855070040e080d0000b5074484020b054070a4a02c5035500117180291142040c0d4003c000e0b004801d01c00001c41c031300500000c001d000c0c0e001d000140700b40000c014000e0002400540000d00f600811000c2c3c1003508144045080042d10781c0d1060186135090f40e00107203500e0050b20709825580c9454850300072000c2e80f41d41100050124980e41d15100740a4810740003088109617441150800c10b41a00c001c0d556540c4d80b01d4010b00301540340c1021841e079010303239030441039040c0740c030410f035004500940c040300e64070040000d401c0999003800d0080c092680201041c01c00541c5442080c0e8050325089106403290040c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 142106330 1250 142105080 142105129
    0x23091b0609030d140d0608061801020a0e090c0d020c01020304030e2418031009020f0f090f09070e0907031203180609060f02070303090606170304090b040f09030e 71
    0x7141e90004481007507030420301e0510480e4405140c5104980039803445e5102c810304000c00419401000500b6603c180131014681200c000d00d004101c2c200c0c49a80310013000102011a00d600a04180c201c854000d4207545131a407030101c4074240700049802040c06950301380d400005210600d0f5119000111241044502510303203086007071440003042401c260141a0240810a05041404030000b90002070b03001e42500c004002c1a1426802440b9200040b403143d50000303214692401e10400d000d12040000d040c418a68590280c4900e030850000c0200345688640b41001c105240e000c40c4550086900f007000f0103150742146051420b442c4810201c008040c17a000a03020050444900c2d480b200d40c00182c0050444a2070400e00054000c100c91300e5400ea000203880c1c4101945940071305030780c80c09070030304006441d1207150350b400c10008880c541d00250300034041446a1016a4840b0912640090000072240e90b0040c1003001c1d134081d1501540442c0b13424249400c1800d00340c070201d0a017503c1d100c0c0c03c002c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 142107580 1250 142106330 142106347
    0x50103050d03140f040204112b0c0f0c05031b070f060e0114090a03050714030105010b030103030206270601090204170a03051909030602040807050a0b0a1223091b06 72
    0xb8404021320000388070581d036001c10306544440d4091002c600603140100e903507406102d914689114404039850103000d4401c084001c2402604c80c13135811042c241d03100388142c40380020450745504520400d407150b0004000d001c41a5000e10390140d004002c7e1000742001d40d00d0080c256005040340d500c40e005100b030040350211544e034442200c0c50902500030000d6142e41040c000726140101d250401020751241e12004607241000e0f44a04d11110811070003801142e0f00c4120722034550000384030046c05079204001145c684289c010070352290306c03031000408049240d110070a5207889001e902544240d0b9002805000c01c10503801003c1c01c414015008044105680d6801003440c0314100607100141100092000d40b284038020040003990441c07002d40d11503031610111a19403040d40300d03a61182038480307000110449aa025200701c00c1d01911801004650030150002a080c61084824100142058100ba030354103145124082d2422030010041c40515905c51444141401c00389441648207220001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 142108830 1250 142107580 142107611
    0x110604020f0603041506080708010e0703120e1503041a0f07140f0c031c0501080706090509060616030f0f090305030418060302060a1701050105040509041113090303050103050d03 78
    0x1910381d205607040782c3d89580f82c0c00c20b2807250f404040380908503400c220f00004c80075400180c480030707100c80100800003d08090201c0da500c5010f07200003803c408844050588490040320108400703070b000303800000c0c4582324a90440c5164811101202d1094807541c2070110f401801345c102c2d61040e0004a500005d0514220140c452460504098954400010010403213460b0505541003814207200300c80d110183d141200301d8000c45d02502c2c0c280c0381d14200002400d41c0c400902142103950603115541030b1400c101c01e0100400c4001c2007103800400401c28011071003c0e00c000910082e0003550380303280c4254046001080d803039640c0d60710000c1040b071240902c0855000b00c03c40e4120755915145040400054001101406e210391000e58480400f00d211100c0f02d410641111840d001d50810780c0260780c0340c0005454038000c9000381a00490f00c040010000b403c10f00b0794042c00c4030300502c0312000e00e0803071540206079030f80c803603007140000c0c1c98000400412504114000402c6424181408800805481315 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 142110080 1250 142108830 142108849
    0x13020310050703291f05180619050c0f03040b0d0504020a0317030403020706021b0103020c07030b010909032312070c0206041508070f080105061b1c11060402 69
    0x24940c99507901e000c207944034040d90002c5410104110740e0801800701c1c030038081a122648a030680a130760a40108a1524031400310a04010400c0e10b600b41800301022901c52484034002c02140c004030104540900754807056a64901081c1035070740e4680d21058240c519052204080c0101d05540c4240001d00c0014581c0d41943c10640c28035200045513940c90000415100196101400083d454801102d40003c0440290321441c082c1d021038288903a0340300d04980d245041080029072400c00e40540b40698484d030020a128400e083c00c841600d07440e9204c0e2030b10000c083e888034030b00b19035561240081542041385aa681580d9102c4040c0c4222076890341141445403508024207a2007210000e58058094180e80602a402510050b2280d460b05042c4a85115906000001c54031030700000e1481c5200e000c030300746600c0c420340d1008110303442c0c82e0900c1348a40200e2640455281d9084140810101c00c01411a100320340e1030310780c10b00c00c180341030140551100e8030003442e007a08000c0800c00580c4a88410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 142111330 1250 142110080 142110103
    0x606180b0d110d02070b090d020703020d060c030e16050307090b090f06010504030f03081b09030d052b0b040612051903050c101a060a09051302040e0403080a05130203 73
    0x22890030200e0006142d40c1c807510f550a91068400f00b2143c081c840080b80745403003041d44208403138401d111302100b40e13503c0359035110095000607003062040008207590801781a0340c2d081c2c10085042c8030950441420202c10707501500c003070b5001c088204803518042104200410115004118204040e0081501c2a600410348040c0204440c0400d01c03030391050040703030000c5401004d10205211139250041030040141c540d411021040c0c0c1c4000c0a45c90b108003242c50740314000b0010711252200301400d4540390480009040010840400207000d0b581940c8868040d002602c0e0009996010000b000122407540d00440d080b10001e904900000340300040e4401003c00c00120030380305d540286412504c52080c1300440400340100004d5480070182500100c0c0f00c45059000142445903520034000e0034080c000000c1d00041045100300458204680381c50130a50800b40094074107920f13102a518648002d460440004520314100040e10b4828802d00350004400c990303800c509003064000955440300b0844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 142112580 1250 142111330 142111357
    0x10f0e09040f030c0206030c07050105070f020d0c141204090c09060909020906070804080a05060f060105121302030f03130605120f072d030f05100e040609080d0606180b 74
    0x102c0000c0c9030181460340d2110f540100a103581c2d250422103000581c01c09001210b040d0300b4200443d030070500842614031100f8140e07000300362200341480d044032120382c88127084d00e043c0c154000c40c4840032418400c09084504030005903907903c1c40c00109400719034036601944100704401c10b0601c0704e980d0011440c070450315070040141c1c40e048440c0c000b903014480c07550020071020000400013120840490952a1280200d0541e05607980e00a640300c42207204580c01c50008000b00060340181c00220004ce401407049060907210b8440c5502180c42c100e402e002c1d1004551010941301401c00341074001ea00500024a0081d081a010f540660403284014082100c0ca8510400180215106140c40807050040c0b68040130b0110400720990803004e0b1441c40e1000190400c2004e180c0c412160040034000c9100492404001e803030110020414500035004543c4941c03030780c103031001141d1140c0107404036441e18580002d4151070030301e0180041c0005100d54544100520040100a6403a81620001c0b082c485 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 142113830 1250 142112580 142112603
    0xc0d030819180f0312061a070602040302030a0b2203210209040f06060210020306061608072001090617062403010b0d0b1507060c05040510020606010f0e0904 69
    0x1030460080c202c0d8a20801020110000e140e00b0700850741406510b241c082d07152085407010f500c040d10140c403018022814448006030341d00410315070081c01000c40501503a401030806d6200d900103820165246000d8450000c0003061141c082d0034800d000110015510710103103124115a40549a03001d070107015410071a100d030944158401a40482e1034040c0020f004008003800140300c44010807050103184014415060485e102544d03030301c200e0380222030041c806414071418140062010a0f1460104c0d94071206010302d00c0000d001d2440e5110340340880541001c0c418000c000140b40c0d50071355000c4020441d8494451045106030071005400c00c0082c0c89040c403c0b050380d45800e04001d580c0300c3c0001409400000000c5c58068000075060b040a01401400742c070700c4541c1007200201c80190f008100340f00401c00c002c0051010fa00c9072400c081d540c00c043d410305980750000b0b8107031442c02d00b01201517000441001019a0710480c5848401c0d0740d8100b01c4255214074011034040e12004200074103010000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 142115080 1250 142113830 142113871
    0xb09130f0c030807061e0c09030620070c0608160519020705100503061f05040909020a18020a08091626190302070902120606030613020d0e0c0d0308 65
    0x1c40c51502030350700691400d07620b040f249070100c010400d0f01c960003012508a14a0f4114120f103000f214454069036850249940c190384510000300780741c110303e0035a00481c40c1ca10f91164010b40113480781900a64113112140e1401d100034292903030003069600311580d4540760f1030160344c1207403e0f070b1001e8040c5842c800301510980703020fa1401406400860784010344201c240007407644030000b14811841070300d0180125a44803201451050170726100808600140310074084446c241d80002c640900041401c1407440c1da481150441840d0103540d0400c0d1600010b151a11981052002e40c021106070000c0c0300194100740201007104090041c20100f07224551501c503425031005000c41c00d2070488040c1c0d40320b2292050080d1041080030400c4000d80212030002440c0540d510941d00d8413018640c0355500c42c2d48100401c20294002401c413944900e280e00b98100d07658952014184040d45a0b40000380b1016100c0d44903c0c007c1103202c0d040c072441210b0011000030794000e0742c9582100c0301e0368611000d01c400713 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 142116330 1250 142115080 142115093
    0x100e0702070302130b240703050307030603060207060e010c140a14090a09060e010e0103050613060e0706050a090803090f060703091d01060305180a08160b0117010b09130f 75
    0x15031001e580002e0380311500b04c3c0c140701c580c000080740904696100301145c0d0202c00c02c410003440c415514484005014200c00b01c0d010704010340e800341c500c0c43c00040d044e40345c3c3d680300100d0700700207003c1ea0b085595030f0b0328030b003005006d1045d01000c2c5490f04100b00050800903c9215911400d9805d004219000501c856105109000d17900c20041c014940e02206031100c1009004101510901d008444008000602014001d00380d6041c1e03908031000c1c01d0590b035134109120641c6d031022022203080e50303a4400007844290912143c006080a41e4070650b072502002c1000f0700e90b000d0340e00700500d660010001402980d80c2e000142010440c1521076540ba4452410169000749290303000442810700c1210140345280c030701050034142c0f891621704000c3d035203440c07001064120385a14490101d911442c0c40c10045405100906044003042999812880055880e4406d1120a0b44450b004d16030a50071070380c80c2d12080c0110140c01c01c06031601862481c010035000d038844410320024012030030840c880c5092190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 142117580 1250 142116330 142116343
    0x219030606030506042102060708100521010c0518040c030b13060501030c0309052521150212150a05040519050603071401050c0102130b130e100e0702 66
    0x80006003004901c0d9603041054940504a5045a000d00d0103400300100c51b80b40410400c2d0384401d64018009965035503400c0d1401c05c006000606c0880000000003030701e696242c81c00c00b400700c05004440e80303038480c65034140c2035070031254140d000d100b000e0145202400443c40c1e02601200f0441e40400c0314010300506a00a0800e0b040d060340040c00c01d00200c8603030115070418021038000781c0c1d007001a2482008100c00300d890801006145421403110b4410b043c9500f803c82950b01a209406d011103503580b21041d04521050402d0010700302c41c860030340d0900010011082e48000801c00c10b51038012103c0704031803250300081c511400000d444a11003100c0d100d00c50340d48003800307014004200d582000044290f000700030030f15001c1d0490034030300000c4660902145d004c084070038100034102c200b8102d0005490035040300513581e2041d942802110340c81100340d40c582c070040007500c103003d40d11001c4540316000020140c0005a040d61400140502000c0d80c0040d08200c40c107088061409840d0848228203016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 142118830 1250 142117580 142117583
    0x20d030b0d0c0609080c01090e0a1e0203010609030302070f03030509060a0909050a02090f040c05090402090409060510180209090406020a0201090606030c0519030206120402010c050601030819030513021903 90
    0x182e02c50000700b1100d82001c0360b0300980340c1c40c01c11121489060720046401903020b005080c0901c8045001c1000b070300c0f0603040b03140021075846213800b0300c0c103011082000301c1c0c02c05d03031210b000200c2c0082d04005140e014050b490140c1a003562130340c2080d08645000d810f911030701202c40d028000014600300c1843c418280c460103061002c01c144558206004282c02a4014200b041d2066842c600d050105141c076104d44081032074540c503090301303011140e410440207400c10004190882c0d1a1841040010050f108891040121000d4417400506158296480300c1100c20110010707841003054424a030368101d103003a4081d600260140c0c0d0303010300e40000c9015000010004014504110380813040141071040078040c1c800c2075610186207034100ca03248000f81c0c031038030003c0c1d0007400400604d0b103c40510311610b07030300c24010304101002100b26a03d2a00d405026801034039100c80200321107120107038000420b07880f582c4910313041c006030401d90300c0c050035403241c2c02c0c00a1189000f4560b944400f210401c0e80b00c0250f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 142120080 1250 142118830 142118843
    0x40e10030b01060906080702011407031805030d0e0606060a08040f0312020313020f03010c051c14070e0906100e0103050403350112030801031b09020a0201020903060702030406020d030b0d 82
    0x40d40c0d16200607084038411700a810200d62880005410b66105100704018034001d80c0180c60148c490520550007410f12034001e481c0300d041c025510000c14410401080d09500c04140082c003a60004c603180d0074103202900c4288901c4d8208400c128581d88040d84980140c1c0020400c04d40d2269860169401000708a503225030b68004020003003e400054413122059000b0340d107440e003005d80e0800b01800c0711188408500407038403d00445000e1003450f9103600005001000001d00c540c03c03503401f00d5507114200c411000248003000100d0081c1040800c168018006850001241c078501401402d2040010006810155204005070a052150001000300440f1120f41c4a180340c90b000041d00c00219000b441040c0603440000252520384a541441c441c0d406540c0c0d1892079007075580300f000d403800481e01082000905030020403a82510701c01003103203070b003d03070001a0741c2c4003071780c05041c14403000510002c01d40d04280010451560003154410211600e4540007603a108498000781d00041000d0001c3c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 142121330 1250 142120080 142120103
    0x1005100e0d0f03020c0906030105101404090b0405070f090c05030109020304050109020a061215080d110120030103021e0907030209041d060403120204030507052704080306040c0311040e1003 83
    0x203140c3c005c01d0b8a03400070310a030ba4a40f15980c03018281404c1e50010348200700704c0c201703445040046100c0c0d40b150800089005001043c401c54a0322207503812481540c0544007074024850411940300010f0900006001d415070a01c10707018400f074045c0240c0414030601044035000000501081401e40c080b500290307000b450070209545480d0300a0001b861250380c10000b5180644524000680104010803949120004c0450040b034142c01c440150f5805050401ca6403134040c4840321500c1091084e1400d4200c1290540701e41c518010485180c01801411040341e050600d141d4490721580c024550041a900740541c1c4d90b0144c03c0801d0050281c4078120300342c04504203044104110104949015038001c0d680c040c0c00000041c40c4100303c2c030440c40020003540c0040380800c441d0500c0700900291b0444400060b00c0e9240c03001038010503040441d01294965400000c00540d0b18192081601d10800c0340380030000019001280344c03803441030b0302070300401c1408400050f1442c541030781c009020f503911400704040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 142122580 1250 142121330 142121333
    0x3210c150509010b06070c05060a11060c03060424290c011b170106140c030304060c080108011a060903190303091a070f08090111040605121005100e0d0f 67
    0x80c20300342ea50101950815480035840e00e0b000081e9101d080c1c002c260b200c1c0040c5010100003440d40b20361820030500003e104540c0c4e40780c800340300d1a44507140c4641095034030325007941004100c03000c00113090341c0c0c00803c41010910511412244069600d060760b03030f20b18182041075011070903041c61070070000d48030300148405080c007040d001942944054100b0492803005405c080da10016108404803144a000c8010400e031803060a111303402014a00d0a03500d0445800c11142c2160320032101600c4040d10b0b203822011881c2d001e0801401084040002c020307200c1c0841c140c0d040790400039036042c0302d03070760109a0600c281d070140304540c4280c841001039540c0c0e184a00d009000b0705001841030360070007001080c04805950444955115921641c0c9182c0f40d29001c10307081d2054031015246d0900707503603520201410307c04141c0041028002c0c50326030301d46171090107450240185006011800c1c90036005400c00107600c40d0b100070018600305051042c424001c08001c246e10a5920f107000d00700740100e454650 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 142123830 1250 142122580 142122623
    0x918020d0e07030f0b060a0e01060e1207060903030c170a09080105010902090f04020a090b132d03080307020309180906060d20061606150f03210c 64
    0x1040344500c61040c070000d07003605540c54680c40c4510001c2c19550982540d080001c908403440781d886000180358a01054640210341d40c00704090300000c000c03511090260780d06213841407110700700c01410301c001c241c0135040c09030007058214540300040034004599009030400c0146407800e02d6113480c062910f038a41c142040001d0001040703119038001540303450004240d51005008403150014040d00c40c80002003020240002035001d05001c00410400002c081410a80760008050360b045806005ea9101d0038481080256145c414504522403121840e18454011840c0c100742100d07001030f2200c0d1a6500d80310264150320607044070941c4804841040404002119412401101c0c00007c843c90f030303a1800c0c140481100050800f510404501d2911070300045000c1c400b1401c050003910980c20701c000341c40c0d8640c2a1910741e00888085407540d1034030701103400c8030443d8001001d11821051a8501e0754403030349400441c441c88590144461030032550014040c589010b107895201071840324580d080c0b810078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 142125080 1250 142123830 142123837
    0x140111010f02190f050a0c02060c010b13020a030b0301050f0a021e030108071403060402130507020102040504110403060506090103080f1b0f0714060705032706031003120c11040b01091802 82
    0xc9021412603a240e44d0a640300d1015070b26801c035943c41c3c48402c2c8500d50204402c80c0c101030b65101c440d64a541102d038154440e44007070161158031000146c4c481d802203078003a058401c5c82c400640030380c0c54481044821900b40f00140c2d00810107600040e81d80399910340c000310580030b941d03140c080442c00200000c0c3c0410006000c90444a17019800301001c6809001c154880700141c40180d400044090303440300010300c0d94001600159540001480c0507655400b00c1c1c1980c0d022000500c500201003020014803500e40161070740510100d80580035503041d81e403200300d00d004807400c000d072481005c0740480c00003d400000d0840d49441030129051021918880d42c0e5401c010f0040001e48003090880822504044003a00c10059005020310305180385a1803400e003100d01050318106521500c4140030040d15114000c1d030050407481e10218000d4210b061140c0d828105140d08400c100040f010310010601c0d18080e030140302411900854070015100c01210044030075000b4031901c0b13902c0c078070b551800350165000303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 142126330 1250 142125080 142125127
    0x9010f03170a0c1101030609060e0405010f1b0302090d0c030501022205011d211501060203090f010e120717060112020a06080c07080313051501140111010f02 69
    0x1200014109400203000d5020b03151003000807071803200c00701002581160445800241c11324001480702d43d251060310558109502c00384c06100d903481800140304080c090385010709030440050060b03401c48103030540310303840c0740102c8020168040703075280c07080c0d03980d0007400f40442d00244810469526030800500035070106100d41d844840c0721a81c90350041c1c0315403629085580503141c4000010050709640c240b03041000300b56a004210b41c1d1210305014015032941d034948148c80090070100c1c4079072105100482c041e08058190341c01401302d01c140b903903940d0306031401060030320301842c0076160300700031900c1c0e00445903c040031401098000308091140c803001d1620807805000302d0b1b400fa40e03200591440d1050785500a50841c0d01c084040c481c2d40c3c0184003103908071070500700d036a15048075515504003541003a9104051101000020020720008009030460980380110b078442c254541207100360003449910300725041c451080004c1c07030b5651342980001c03070717851a028043d565612480c82a9131121000c406c2e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 142127580 1250 142126330 142126343
    0x403080f0a1701050609100207090507020d18030206040506090301090b07021b010e031b031212060103060905091f0e0312011d04081812010c0206040c08161203030b09010f03 76
    0xb84480d684500450240c101e03034000c0c04091508504400703100e03036480310070151020351048840c0061481c1c0c040c841c1c2c1c3c3c841c01403a4042c0006d020714100041c86804c0b1400509901c24228000f800581d40325401c03a0119002100c02542e070742e846002190150805007400780a1001e504c04104446401041c991114050003644c0704007400e1350303801543c500030780003200303601540091032400308103075101c0c180d54101c0030003403c0721407905a20365000159400300c03240d401e03141d0b00d80080c0034540d42c16014000107429009001d21071490900e0400d541d410752001401d45485c0034520015100c00c6a07072010b540003180d142036a81c2c88080350100300308a5020720814620700100c02d14054030740ca55090080c002e50b4401c0c0180d1400c451524202c61030403072107036a2980322001c3c03071150744403550900ca0405402c450b50050201442c290501c085940c50591141210350402d8940b030540d90907204541c400d4541e80c1e0900303d0b03030103080e0508030b00034004900c445070411108400422031200080030103046a1281e0f1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 142128830 1250 142127580 142127597
    0x1204050c0a08060a020d09020901060302040602071401050a0c03122901020a3809010e0c0301020406050f1305030303130605090c010e0f030f060a091a07050901050d020403080f0a 78
    0x24184205001984940e02e42600014042801c20304260002c050750210a4400f00300606142c002411400007070b4030103070210354001010000705405000318401000b1400c04c140104051b080060040e1055111860400003100a010b003010b008804585403002c2e0020704000a51900d440000d80b500076058007002c1e03100400c140216036200261207403505600c4052103100007440c1c00120300803851080307229440e02c80390552142920040c0212840780c02010000301c1c104e91801c5550741030107004009a40a80d004100030300045070420210740b02086044001079a80308410220705c1c520249070002d41e41804008148801c40704809102c0700c0450041c00d040010f40c032401c01d502d0b036414810300402e0204141c00d42d010442d151503183d0391000c04000d0107640d030880b92180c2d210f061440072103130041c45aa49072034040c02c0c402104170f840310b00390302c0c2404510607050444014280380070b00601c0c1810010700040d544112505501541e00666008404030703103c1710b0503007a5402942280082c0300000e036450 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 142130080 1250 142128830 142128853
    0xc0509090903160b090a050616110c06030114060d0c030e060109060f0905040f02180106020c1e060304080409090503180301090308070e120a1109071404120611120405 73
    0x8400c0369840401c5910f0204102c100340e88401c03510b40003c0101d006406091044004104248080c81c403400d1b581e604c1c00180c4275621005400f4025203100792105034440904c400540e03c40000322419142c40c0e065440c01d000e4140c002510901c200020802c4050504c0001c0d840300c3d40503004400000003410540d607250784c03070b88012021640741d4841d1000c1d034190306804214403d0190f00060b0041c0c002d403c074031090a04c0da0041903031041024403950803c00440010004c055041c0068002030004440c4c14003101c640b0140f00f0800e0000d0544140310b0040003000c01c04101204080707a000703001400c030a01c0414014141b054580e00000110894410058013020003072406104541c01d042c0e0645610f00951107080341201c0e00b0420181085d04552041644498032004011041c803280c80350945100314031055051050252004c1c01020070b00c0390100022640a03945010744040d50b00100590701304023498140040500424124503010b800001810300c1007101510009204500800498110b0b0001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 142131330 1250 142130080 142130083
    0x12241e1505060f1918050d020103020f1308121611011b0602090112140f0709050310060503120915070515090604020a1a0412050c1804060605010305040317040311010c05090909 77
    0xf1402c805c81040d01c0e40d02400a840c0202280e00200d0041c5001410400301452040155004c55400c102500d000c070002c00603410304100000051020504560424200308105001c001c2e01007c001c2607440300c4030404043c2d07485203a02e0b0545a06c24610b0000480640c1440e00083d840f07120f40a0000d1070f002003800d40c07205075004102c4050a541c203104542c0d500d1800405c00040c1c050310010030843c2260001995540400c00882016103100000071071318900001c040c42d080c05000300400c0c00c0e1051240038030903a00c80c01529410110b09800c26511205440c0082c1011205174244024404503028091394000018440d0700c9507200341c2c0c3d03480f20309444415401011080701160065490200401d00a001c041140f451115204904403064001800d000414440508c48120f0500252074104170911442d40590b40081c07000307090421880c10b041e14014154140b10b00c44802041059003c00d04040c8602440e8020508010082016a084540041c996070003440032511401102c00031072541c980 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 142132580 1250 142131330 142131347
    0x1510060f210b0a030c060908010b09040c0b03071403040308011508091b0301060308070302010b18010b16020f030105010e0703060e15040e0712241e1505060f19 70
    0x2801c400903202848011061018022000b0055080755002c103002000076a00056003001d80702d182c035581142800e015004d402c582c1e224003038a100d08a05170910010829110f050000d403001004091394980d521141610900411172444900560000400082c1540901101c6c1640c0c00d00381840c0500790300c0481106d1880c020b0350508010b81082088201c1516040c4040c11602e4001e8000b00e03c10390750751510000c0d60010a01900940d444240e0181d5910b001e218500258001d14031071440c550406039008041d0289041d440200c401c8036080030290b548100e217a02ea501d400a0090011390303107400003c0d06105041d110f150109041540c0415001e0038084201d200d11a0f810b00c0c4c0201c10b40703900c1000058a00f4051703084482c0144507002c034001303428110710f0310b01c0c0c0d02030000f43c21420545086c42411400150082c18540e2400100b6201e41115901654103500ca100f400b00740c04031000070450300756919038840c980c40342002850504034001540508601009280798454001464806850904 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 142133830 1250 142132580 142132607
    0x2010e060a02071511011119020304120303020304031713050f01090b0c03180f0a11010306080c0d02061c14090601030201020d080408040b0a0c02120102090607060b031510060f 77
    0x200f083c0018000c10840300d2406034107401c40e19241c6140d41c0000666030844500e9900c2c0011108002842c80090954803803207500a1203904c01186401c1ca052a040003203800e8907401401c16400002003003d15200c0d800ca101094181605624103042c01e980c15401c480034080304603106d02036035140324451101841750748070f400d4111004455a6031550a80030f515031004100c0401c810003851040d01004c0d040040344140030301d000c0203294030189410101003209805001604150400d8010301044602051480a50178180c8041d2400c082d81c0c40000c005004072088011791422095900c0d00e4110f0503001110100700102c46040580c0305c510035540c0303500703090101a0141e40800c904800c2d65105000281d4041d0080b20b10340c0c00d160b00c4804410190b03119909610000e0f1420030040f0135458904658012001c404008615044502c0c021074040e0140f40805801da80d40c8010b5007030303952800d2120220014110200070700d10b2605010801e580042c81c080c9400140901a80e08610340c0200072080030403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 142135080 1250 142133830 142133833
    0x3060e0a12030b060f031306060e010f240c060b150d0b0a030f0b070210050403051c1514060f030a0e0601090209060f03360f010504080403060b15030408030402010e060a02 75
    0x5031144105e91421b41c0054400010b4219010228000c18400e1084802030030714000b00c82190351400410000310b86503500010604078940ca8109440254484250b003440c40b242000280803915081000007850324440d016000b90094520390041140c1c4030050440540e034440030400c42581b48103008681e40c1b41c0c00010891100e894044020074130f0b02142e40c2c0e001480c2d1040381d82104102d20040140c0d202603808501081000c10343d800d083d001120540e00f088903801e010405002c0c01e40851510120700d01c130b2880031070030702d08140b541ca460314002c031080d030381096154903980e007000c51041d4010810f0418909680c01881c002003040c94040c0211107500000401c1d00b401c00740320700300a1959034005400d88a01c145040d503840041c0110901303002044540035510f1a001e86101c2e10181400d80380080d4851907490304003000006084241568242c0780c006c40700048003135064001c50160785692403284602040402080100f10030000154480c03032007a41e031600020344038400d01100d0b0089000d0707000076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 142136330 1250 142135080 142135087
    0x20a080606010906051e031306110403151a090a020d051003020f01050c03030103020f0a0305100507180b040b1b0604060b18060603040209062b05120301030b0f070903060e0a12030b06 80
    0x2041d06401448c0c101d8600818185900c0c816516a0119680f030050055880d402080420620400d81662002d9004121043c0b2030340c184000e01194460280004620480c046004036510011580c1a01c0b140507404100b08480c2c01e01220442800c1002e100803882182e03403040403042540307c1e038143c1c2c00e80080308004509503400d680c20005001990510f40360000700400c0000b001c11010001c010390300742c0d0307843c000a1030708201d0001002502d9102207138241200f228010080035030080f049504450a01c020030f0740b00c07050380c01c0010200d07481d2902030490703100300428003060141f00e42c0401c140c22821200d1001c01c0060b40f0b4914141103040b00c129500403402d000042c054100030f0501380d40a0402444007000005000310840035070040305040701000c02c41901d03102004130410441c00e940180464050941d807565440d040356500c0107009045150320540407888032400390014002a5520030340c24004058101461070362804032450980d0480140059075610340d0184c0324090f80c685020346451314 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 142137580 1250 142136330 142136377
    0x30a05040501020f0d051b040b07030e030709091a0f0708041e080f120a0219181805070e120d050f040302190e1b1213020a08060601090605 61
    0x408004009607000c2d50200410301007095204014804008031030000030381e6040441003200d40000250804001e010100414888041c001050300ea800780d043c07600c01e41c02c52004c030100341070546030382c080b040c0681843c0345c10b070801c5040e4180d196010500d40810440d941d1f20311120740c0d401010341c0c285000c00c08040c041004580000e50b9030000c504008080140403a9507a1461440e90200754950800c40c40412072112220042c1340c15500459034400550905240000908400003210b0522081c0131203d151205040541030004009180c1102c0c0502c4c074000c0114040c020745001c8924000182c0c0c103010701d88451814403022984003425100915426110300c0b0b082c1c0f400d5104507094064075506200000041c0c0d940c8035000f07220860720160b2040c00e4a0214500510800500018096001c0891024900f801001034840c12400c290401e400c0740c8882e00c4a040c1c040d40008003030f4001c4800d20001c100c01c1b4001a825002e90400e0340c44c5211165528400c40b0980506511004000c1034010b1510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 142138830 1250 142137580 142137601
    0x20304020a12082803140f0a0b03070803030f040b0f0403020703080a020c040f0221042a030204020d050601110309060d0e0304080a050709110f0a0c0302010b0a06210c0503 75
    0x903045116100383e43c98000030364600c42140034044c2620018425140c14070702025854010040004058003442c4d515080ca4402c007030030050010101d0341b6160b6103038102803807507030100550b41c0204040c80031b0725501d00300003122108031481110705071072500140d40070a1800e812068002d01c240c0d05980070b0801035045940f10707441740d4007c0c500c2070f085109005010802c0c0c1d40d0743c0300741c41030804170000060fa1408450b506181007411120700c0046000a1800c00000c1029880d41050405117021064603003514404d00340005150b075000a03400ca4030100711110070764010b41c019800b4507402d803070f014a01620801e040e40d80c1d21441030142e400580c01c0c0020382180c3e103140c002950502000f07003a0b0f41860746500103a0320302041c88009445c0f40d4040a800c0200007954407403070000c800c5181d50140f0b41201e50701a0b0400744100800f8a08010084810109140c401c0d80032581da04070040c840180c2540d681001851075070884e0314244030724030822a4600210051003480c00d061055202e031030440d9505120076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 142140080 1250 142138830 142138859
    0x14060906030312100906180e010c02031c02040f06032408033f04060b011e0c030201060e0903090103050c07121b05060403050a02061e011401030e101e020304020a 71
    0xa090204d800325106a250062101501000354440c48184040510b0401e4504c40881c017811a45014500203080d540802290600d1801807039041000f01c036108860001c2c800d980c07190074a505c00c98004505030340d154001051000b410a80400d448180415010400c00c0310302c240b030031540c402c01101d5045041990685c940510491103001000f0f20840c84c11075400d030001490000900400802042089912905c3e001316801e2070840903041c14011803503074030300e81c40f1a01070500042d100d864080510035080300000e0501c50311156110f0400c2305580c1da40e904942d642901180c10030000039119061a0140e40704144c00255016090030500819207003800e46291590590704108400c0c408154104103e0340184d00c2030b45ea150b500d82050700000c0c00c08a0140442c0b41094101820044201b960311144d4190b580c40640e01ca038903607030b00c00140c0040c0a900c03040720480c003a00a0b107105011481d4000c0ca101c04020f90a000da5404008040c0c040344000c0f14001d42c004150b4030306000d0a0110b600303c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 142141330 1250 142140080 142140091
    0x50a0e160503280c1401091403210d110d0b0108060a0504050403050408120307031103090709180c0e0405280303020304030c0602130503070f030b06060711100314060906030312 77
    0x9070890f03803410f8544c0e245141c001d80011480700003220201d117035964088028401440490781421b248001803000988a032142c09420007030b04a0500b81e030040a80d00c004564941815680402444151210440c01504040d07502104240303400c9a058880d4003c00760a40b04250040c10720b62010308003801c00c4020480075100381d0402c2828040410707803040400068210b100d8804280c1d4881c039141c070f00282990b1a0f01d9a841070f00c1000d0083c014003850004026040d10311104000c2143e80d06014141004195010040e01900b1001700006032001408406401103002e07000b42c0b810090a030150362245450320f1004a0b280c046801080c001ca842030b0301030740d081442490180740d1580700c4c1e00d444060343c100182c1c0d200581180c11040005146c2000f0b100e00074040040025030403072650308c1d03441090400910f554010000002c001080042000e91510150001807210354604070114000b0001c0c603440d120820940280c1010a6152401501c1948600f900400951904150444c064a00c0901034403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 142142580 1250 142141330 142141393
    0x708090d03062d0b04061d310e0a030c060e030c03160609021203091e0d020d02120312010806090109150b01090512010c021005040209061c06050a0e160503 68
    0x120710340c1107400007400200102e90350380c0840c0d58681c501f5042c014441815601ca035000303c26101c040740381681198581c5180003101c50318100601e07001070107080310303c41411503030003240490400c1540144d0380e04001c40c09220100002c0900c800019960300c50040d40071004c0d842481162500c50181c3e01c50703441f0510070070020a081d80d0725400b00d0b86d0340d680303007185548036040403400341d845050400000150b80c0c2d91080104c0e150741c150020500d0148c560720040d0040d41001100d01c01e40d2514000d404103103d4a10440742d40b5208141d00c401460028040c2d034516000e00e2010a0780001e050003809149038006c0c06250282d00007404102c000d1560300301080c18000d840701c1c00203240e51145407803034645400900200c1c000b80c20450003820181c0c1c403400000c2162400040c800903807100b0025a07800042501c17802500741451551616100003041c00504041c1000304201580702c01d41c100e1400444440d0485000c469601c440b44540d28143c010303141c256002504696014a0070440b0002d01e006200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 142143830 1250 142142580 142142669
    0x8060d050c0d140d030204210201050301090207110904061508030a090b0d1b0810060c0b040b090325020a05010c030e060a0e0307080312010b1201060f030b090708090d0306 75
    0x210303090030000c4405130440400e45c00310b0104000c00550150200803c7c40ea01441c03001e0000340d0019081d40010f008516070168089108000c1000c0e000444900c02001048400c040ca454a01100500450780d40403281c0742e458500003400007000000d0300c0100c451500d0f84075401c0c0c1425008021038110711040105141c84182c0d2081024045000941011541c1e8600303001e4a0607112503220040b0301c0d4810010401429030740c2010031415074105800541c0316030b0004043d11000c003420315500401c80c017081c1c580803a9020501205606040203034461090f01c1e00300d8203d5998005413559079010300003502051000b14211031702d28003840100001d03030150801c03186100c45030000c20720300881a00850b5650b0300001d2180c03210240c1e4483d403030041112800c03a13854443e03d21040d000c2a81c0c188a00750520820710305801019000350030030420f4102c050081145403074400c00042c1000310a0721250582d0007802e03070a44002d4801d00032310040e10404055140f901c0c5c2d42040c000f200d040d0307a0010800100a04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 142145080 1250 142143830 142143863
    0x10314040609030e010e15071b08060603010b06030405061612021803100903020a08030c040506030702010c0807020607021203090f031308010f0506010c110a090e0a0308060d050c0d 79
    0x20000a40224000d80d00000c15010610b40602207005003042c1c58140a400f180340091607a811504d0060043e960001c56203504161501c06488000d60198040c403850b101d0700403412000000c1c01a11500c800c0b0000c2c00310b0a11003080c0300141c4001d580146c015001000000c810030603103000707024501080d1405120341d210a045400403a00100010a10341c4000440030030280f40402982c0101812428100010700ac0c1e0b560103503039107201e00b100801451004c4002880c044a4405460091074040e0040d6500c0c0307440b0704000d00821030a0b0004c4040f41510020600040c40000c04510903010b940040c0000903151800540030f0300700415220b03d910070940301c1c2c0c00041051010340300c0d552181000030082e608203950726080d21841061000034a00c0c00c0c00300140c0c2d80c2d00259085669401130804400b108040003c1040c1e000e1941141c180a428580d0700083ca01000030410321403402556051b1254464101304030741d04030f80c880044d24a5008110b000300781d20340b13080c10f00d413020305c1500700c2a0400e103035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 142146330 1250 142145080 142145111
    0x4140f12070b0f060a0e070302160303022208030904090f05160611030a020c040906090c2d0302130e0a05060c0310080309010207090f0e0318030d02030711010e0103 72
    0x40380c0114065400100c0c121041262100c2519080700780d680803a46985081800300d400d05007603105800c91403040d0303008584994044d41c112103620743d0078425070030001803500340540a0740c440c00d405c02083c80580031204c0c2440e4041c102d241035071500d401441c07801407280200405419881c1d400c0e600420081c00d5540058420000c00e149081e032480303124602490408050611003115001360483e80080100d1000c2c00c0c1c0c007107042100790004030f800280075000c5081c0400242409140200f26080c505800301b84186072224070f5440c40f000f4014100314048600e064040e09030b80788802500003111220044a21003c2e800620301120000c0441c0c80900450301c80d02d103041c60075584600621000420300000c0c0c02000d96100241c40b60030300035860000c2450000b0355802c0303503101d20880300742e0b100d1010b6005106500aa00342400b0042265100c1040619400e0400b000401c0181300348500c1111500b210300100a5403442908401006026140d1400545a16490080035410985e4500001d042e0340310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 142147580 1250 142146330 142146343
    0x22050a0f0216030917030405010c0c03061a0910030b0f130803010b04180b09280c0801150906021b0303040905070509130b240408010903020f1203070804140f 69
    0x7002c4061540d0a6450306001c3c1203905250084000c1c60401e17090100c400c0400800c5408581081c80d2100c12a90a4181610b1020381504000d0aa50404004031840c1c068070314a000d00d0301e421140c400c0980c54036284001c4200f03031071100400c0480c91100286041840e01c0260350300c42900940200d40d90401d80c6c4414241d4030036040f07030101c0500480d050105801080305402c000410320400c0151078000400901c0d14900100280c550b0501c41e200c460085c05c0f40c1c20300400e81a2145010701c0b400c45c85010240641000340152440c1c1800c20842d0091131380b2441e02d82c021282590051b02a0404a01602c140d681c0c0001c6120b0701440304000000d0400c070980314146c41049656103242e00d95841000b00035106642d078000f21000c90500b0740d25406a9100704c1c00c45d1405030321780c281e070000d41400e610503032060080d940803800651138000040145600418000200c0e000c2405580d20341074010704420b8140400e450b0a4001500d13280003900040d03404009514007403403c41182c100020909410f890103c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 142148830 1250 142147580 142147597
    0xa230a0305040305060703180f0f020627310209060301060c03081e070c0303060e0408130602011802010e0f04150819050a0303090f0c03051b22050a0f02 67
    0x101d0018040042c031105010903070700519940f8091004000710400320800f4001c1c180083c000d1841a0035840030002612445180690b000c0d10241e1141d0320203070800010b128030004d05200c640112642ca0440c03901e03807030f080302d0701c0d00b112184400540918660f00190482045002403103900308050103107070b91541c0182d0b000301115030781c51219a03e00c1c40e00800d0501d000e06500380710800701c2c1c41c240c140415500c0840e80104180380c000310012230740c2011409011140e020744c4060100505000600c24401c0c010304000c581140000324055607008100d0880c1d200901d10703446060001d031024010762050003400c0e0341c584020400c400c0d000c1000c0c001070840d8402e04040440f00b10045040120380c0042c410031100c41c500c60440c694480d825100c59880b41c50203000242050369619403a41084103c0c0f80d010407040d0040d4030081c8040d101c2c60f242c0e031b5400c0591082901024804c074229031514000c62003200354490745034207026119110041002501010b0305908456840da110f27011459110b1001d04000c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 142150080 1250 142148830 142148837
    0x6010803040f0605090109030b0a1d0604050f031206060a030204030b0f0406060807050603011e170c03060604050105180c040812040e010503010b0a15031103070c0b010602030a020a230a03 82
    0x1507180ca00c2ea1000c5800c0c550040080c0701060043c002d840c1c0c1c104024104803078000c440360741c650f5204a02500109450079051004899802d0420409800001c802d031142c0d02c1034040351121401400304036502d001d0551080c0715101e1040020f011801c182001e0040c5800c107040150030951281d0340c00714000802c40700301c1a020842402c020511402d07001d01c4006050b6807000d0000350703090070040b458034401401141100a52203042d10010480c80ca683c0000380006541025400d204800190f200c4034400b520038070920400c3c011075603d00e01445298100c840041030360307880380e0799660300b40000b0328020812800130505000004c0c90b5a010710110301aa1070748001c03a50707104e040a500001d18074041c0c0090b4081c1e0f00d001404101a1100020344064828201d51304240b8180c003030046003d012000300d0b80601c40c40100c1841001e41c7c01c000c510211b00d1152580a15170f81c1c0b07070001269640182680000143d00640004022a88504081e000ca05a514529407403401003103070700e8030740080350074202c002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 142151330 1250 142150080 142150087
    0x403030c0207270b120f0a0605090d050711010e040c05041805010501020d050f04050a0f0503010c0c02090a180515010e09060108030a0e0f04060e010807060509030303040b040c030506010803 83
    0xa15a05018207000f414040c42000c0305121010460620407920034001c0110b65502d0802d25039a58a040381e0440e000005c0e411906610b800302c0c075003625514800c0e02115200e040c003010440060300414511ba600c40c0581e1400c0c2801001d0303c3d040341c40010180001e062040209035034442d91114000c0e052190500d4484030303074035413800f6600094100940c8201010b03614003001404542e902045031044030400703241060b11180000026885442150b01c8030b5070100e00360600050745e041c031008500480350f08038000c1080500300d82e0162824071440c03200a50041028002401d001542d5000c0c21610300c0c0c0c1c1180080e62042a5a11407605520000074210b084030500100044038410b544168042c075100d01400076540351880f080d42d02c1c000c1c500c0701c0051244c6902c2c00700342034440001000d451b0b0380c020020b1000c2542c4e84a5140d03000c1080c01030180e140182d2101007041d41c024012681210b4000d001580ba640c0c8030348501d9a4030f41c02920448805030b0080d000004503500f001458041d14006000d9a603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 142152580 1250 142151330 142151351
    0x3050a0818041d0c0d020d111503160f0318080f070b0916050a0f0308031b030a0b0f011b0f030c0506040b010f170a060e0102041e1d063105040303 64
    0x43e04020f0313400c840c4221000d8400c0310058446202c482d03101d0b075102c12a52203941c891130004101c010b00302448512900b01108019030f40f502c4511060350301c80b4503115045201b81c140303421030503518400d1269007140800b9200c400010384800041425010041500341450003968608607044c4055a82c80c110707a100d003612070390b00c107080244080201003c450590842c0d1038140944400049481301911842c408400607881155400060f4003150242110640c0c81c50b01008010081c41e040e620107020f400724200400c015401104004462096911110306040540d52515418011590110200842c650102c000100e04000c002d0183d44036403070003545513043c0b8802c0007450760964020034924a85069149802002140450f1980d070044000f26940070195910350281c851580a6140644408845802d0540c0091098141e4141d115100c0c1a25018541b0118101003640d0707040e03124a84140c0204040074400070075680c41011076076003d0a0360070161072412510308941c1030303000c241c03103010720130303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 142153830 1250 142152580 142152583
    0x10f050f060a03050d03020a030f0509240c16060b0301020a0c0516030f020616120f0207050301020301050a050d050c0d0f0b060103050411190f03210903050a0818041d 73
    0x1c0d0721980c00d9400720b03592861616496681c41007a0805024580c1c00075110785075a02c00e800803c10015100010302c0181441c0304400e0307807a5a50443c80c0c07007000c000c0d0201642107110240d254091600d0748441810040140b09002024070005011156150b03111501c1d05251001c0c0040c0c016480d194480c1115074945041082c01e0824942c4212103007540702606100199401110600e910740554915444040c00c03021001d503580c050401601d003449840246802d6a07000d041029842d1417a030a0344c1c42c3c00e50314420b160a1b40020300559078441c0100320305116078108031110b0b950860242e011a42000700000205c0e6515000d80d106032810408510900c1c00d000600c402560865400c0c40c0800481c9026101e030b500000304650f030248100700c0401142d40000c0c20044140252403920b14506074a99a40b401d4012010315204c00300307440780c141003c1d42260b030040401a040fa6001400340035100c4459071b50000a500c1a48041d100303d40c1a0f40307101c008d40301c0e413041c185180c06501611140e42e44282c80700e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 142155080 1250 142153830 142153861
    0x50a2003030417040e0c03060d05010608010203090c0a0e0a020f0d020a050403030f05071502030606070204050c040302030f150106030b210105010810020f0d0b0607080c0606091006021b0a0503010f05 87
    0x141050008000411001c5c107101e148a6011481c81c01d0395440b40c841b580050060001007030040d2503582442808a00d084045d4000c50064049000700c2c1c1502842c0c4e028003995000030701c41c0380072403031041c17000a0b503410709a0000c04140c3d80454403607151015500320403080341c00c40c2c280c0b100003610200e010700806401422074140002c041c209030741041116a50b10a00f161b1080f6865406500480032401d69150303081912143e6038001c2c13043c845da1620003008000c3ea0010b21060f8402c0c8500c014103001000e022511444020010351040456800d10070b044c1c01402c102a1104d80000340000c05083c0882c1c0386c004103034560141e40011405505d01081c41c3d15005882012b181414810424840c1801c8008d080b40d14000140001042c03500b81c010009020b03000e60140503024140000c0e024169000208820f40b040c4c104940c2807010788c8512002000c0103a8900801d005607120018038181d0385511900301204c03510051417141e0507074136440801d003959034a007000c8982c0703a10358090214504909901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 142156330 1250 142155080 142155113
    0x30b040503030a0c050c0a111201060b070c0605070203030712200a050c030304051c1e0813060e060301090504050f0d0909060510050f0703091a0306010e090103030906050a20030304 79
    0x11b800c0044039481e86489065291000300096003219410960341c440c40139201041010354001c1128039a44c1540340c81e0740e4403030003044a03400d80c01c00012454070301031015a480250050019070400489650b06c40c083d100034400070b070601030508030196201c16a08100401020710501426038a000352030302ca4036040301e868030b8512030b4106201c20f0040341c5801d04d44409a0848140c038941d410340d076003001040c0480a81515100b401a0002031050121020081c03489400003008206015500e25085880120040c10b00e07500460820040100c14000d0b0086604140113001743c4501a200000143c502014030a0281c0440d500800400c05655907209003030050400307a6030001c15070240c0c7c1004002c0e01c10029210341503440031802c401403500c2204010050304881c0301017500244040510406a04212001c9000407019690b185050601c048041e040702da068507030306001390800c00b0589464009500724020440700c8110300d0480145100c8640309044124083d43d030301d00b01400c12042c8031404004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 142157580 1250 142156330 142156337
    0x1712070c020105030604090804050901080703151104260604051606020f37060f0b060c070506030a02160b1608040b060405100509090d1d0f12010204030b040503030a0c 73
    0x820001503604401205d034421802c450002e54008946000400c9000f940c000d9500701003d8400400c0c0380074001204002e883c0516101200c1c3c000e40c04854080d034040c82d800164019040c00208801130501d401ca03034400200d602240d01c04110940c05900d00300b070807102601d01d680012a95045c130401082d126010741030601c043d1012403c00292540d036103000009401420004a0400c480c0000d4240711b50b02030920b511300e45240304144c1c180309024041101c0702494091408203804800c0c60a4000c5445601e40070004d00712051a0074108001c58000401038044c01d5000c01c44820603104880c041610b95200e1900112a82480a200c00640450403511000c0c0403000b014071020440072440b4035440441110b020406580d10b40c0111a52002036100c83c0e0050803840034041b00318000700340005480e04e42d0352150320b002d00c4007207150b1031700110325400ca400c030403c81385031041810400340c007120305111507001602d46596641d0b03c04000d0801c840c280c2d4036070004410b20400c41a180140c03000c0c20154507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 142158830 1250 142157580 142157597
    0x2004050703090f0809040e03070614070504030312050705130e010e0903070816080d06030503030a050c0a0c020d020d0507060206180102070231020301090207030e040c02030406080a0207171207 84
    0x540344025200303d0180981041000300b108005952180c01044203003260740103803900c07603c00e890303c140a0044070303142040100000c800245040c0c032801c25a021242c1650390a034500607407040031030007410050100030400c402044521b2029032000e2103140200580b0b1520251585021002c0701c49600150012680b42c00c100110030104110800741d411408110805030406151450020b09500c550225980202d003081c01c00403c1c0040070001d10300c64814504140115540d4909400b09441003d007c040842e1020440e1805070030003000c6801001c2c809030410900e240381d5120285003404641c0001c00581c460030401c14030403940e050881e200d04d0844025801d00421b58006421007504600c2c44247c0641c1207240107030042d00d00c10703802c8800c1050f80115a656102e070079030300295200360000c0d80441d400d06121071990074030f4804c0100f045050b80c00317941064103054040b80c800754090401610140c0900c45e8101144c4506d1000c1c1c1800c2d030304000c1036650704115000719800078004000c3c4c3c0c00d016036036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 142160080 1250 142158830 142158833
    0x7030b120a0507051c12020a06090c1409070206010603020a0908031216050c070515090d060b0a08030408060708060d08130f140306010b0a0201060e01120b0108060c1c09200405070309 80
    0x17900450059005841188010813050200d1501c12003100c0544081d0422411109002c40b01d083c00040d182c444100c020640c181c3d90a00400380c505039501001a8000401009450300c40d90240c84801542d1a00d140120365900f2041e140d500480081d1100f21541410300c152441680429041c0c800c46040080c1000700800f5404e44070308003403085600030517074550066800402001259940107000b4120080c9000a08064000f000c00400d1280203458820b004180214004280d038110340c141001095640c1d00e01380210f0b194007010700641c0d00f01a08200020003d440e02019241401003844405a11032038250704200c000313185d90103c5003c05649029000c661030100d0510b054031050f1241070340d1081800c10484c0109041e500c0b00082264010000c80d9441280c002d12980074040c03041d4000d1662070b000403680742c04040d0f403c000c200c1c80811040c5001e0700c002a441c151080c60780400200742080c1d071074103040c1107040c0070009500840200000e01d20b00c0c0c107104a40d001031007480c0400c032540c40c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 142161330 1250 142160080 142160119
    0x6020c0a031a0a0f0e1522060b120f010212060d050d03090309260d080603060411040912030c021e0c040203060d0609140c090f06010807030b120a050705 67
    0x101c0c1d2441d80c01e0001c4002403540c18541c01200c0149503c80003040605021110107882c0e9421010100c04880d0071700200d0b00031a403450075804103d582910044030440e25075248c0000f006012241c541081c8412501149448280708540c0040c3c4240c2c00543e840c190080404ca803045c0041c0a81d10540c1e0030b25103031010500001d15001e000031207080000b488030319030a007640c4146842d48603007808803441c0007501e50034040100400d80f42340c00e40b040f2135406811003c00d441e44c0c40110f9943c1e070181d11450028000c00c001489140305034501600000c2d007950292103001d2070001c1c40c0c1c2004040b2784c8481c00032452075810001035050f110050310025500c4a8001855100e00398500710394030590f000310200d80c042c0c0e42c0e59000600d16501440c1000784440a2804400c2e400341c24000c1042c0c1c2c000e43d214042c1c581001c01102d40300f07589281c520012607a035200152506030000d0a007404140d030b1030107481c22039150f0301e0080350019440402458441810300c2c280b40b0303260246c5c2056000d40f000404009100c0d06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 142162580 1250 142161330 142161353
    0xb180103051207031d0a0b040b0408120c1f0b0301060f03140a1227030303090311030703080106030f090218010503010f02040e07050705030c010c120e03090904110a050a08010606020c0a03 82
    0x160f0061001d02005c00c0000c5001e070254100840b01c0c24005000603111111034002c1c4101e803140e000b90742e00c885907100300e054a8050300076001410b0700b01e0196080c6d030516441ca072900700c001e4010000341c18804080860f0841d91580c00450519500000504c00d0040d60203000803440d50345801410611042c1e074880d40b0100e0408595000c1c0154aa84900442e40c0c000288484550b0401c805803010303503070b0600034017034050313007a0a030040b80d042000c0340c900070000b10841d02e91540603102c03142141d2800304100d00030114500e1580301260385111840040e40e51000c01d1050310f20540141c445075040c03034101803c64200c0420107408520400041108018504d003140d403124141c1007264856800d418040c0c00c600c01c28020105651921840c0318115412101450000140040822504c0164508540d4922900402d03d82c000c4802c0002800901e801e12444c910350000303041c0e000d06680d00d07170118282e05034a0304114071594407441d0a0121940c10030005d0950301c022039044510502d5511442400030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 142163830 1250 142162580 142162607
    0x180601090e1008060405070f080a1709040e01020c012009030615030a05060702030301150c050c0411041d0406050703061a0a020c1f030506010305071d03010b18010305120703 76
    0x18240010402c880d0780200714020102d4509072a05890a0300c3d00702d4076000076000708000d894091002180310040001d00c1003103603501c0341e22101c2c13a086202c512011a0041e01041d580f0903211031110080da0420300241240000403400403400f825841d01c82090002c0004034403001010621845100d43c3e000101d403508104607980d03020580e1442d46c007007030a0404070040641248a1070051000704e550000c000c50480d100340300992400c4070150003c49040d100302c037020340154070100000c0d030f042c54a90301c012000c0c040c018025103000d40c0c0d02c4181000320060744520700251401c40400090003d03601880b5800040d40c42d0400038a800d10b113035100900c2003010242c03041840840ca08100c5c5000b00710103102c2e02c50041c11151a020300b407580031a90a00c400442000070305020114060f54080e019440c064800c42d190640c1401c0001c007042d44030071f2420005a450f41d02c40c88200c2950321800900310417507000b90711282807903045041840c0b0700080c4603019011a0000c0181401295106202020301e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 142165080 1250 142163830 142163849
    0xc030a0e0613030f1104140105010f0c0b0709050f0306040b04030807051e04090c0806060f0a03090c0b091002070b03040201080601230c0d09030c030b0c131418060109 73
    0x180900481d00900510080400c00385500c0404024807101003100380c0140e01ca010745800300d840b580c06000658000388003040b99159484014001036000b0f42116414040c9460302200429442e122540700c2181a0b40711008200c654100780403d041102c814845000181c0051800d420903903a02c880420b4010000f800308800c84002c10105407280c01206e59070702d49403041001c04048105071030082c0d4001c0c0f00d0a40b00078640015111854043c1d20541c0c41070301c1c0200503a042800a290845469002c034044000301176071070302d102c40081c504030b2103200034051909445440318810030505c00c04214005604040d5881190100081608942102d0b4401e9081c03030b01c910591905401a109d41400c03491a5440c800003ca1401b0501507840113850304c00c4650b022101182d00c460b40507101c40c0414000078100b00c0440300c00744080380c0e102d840304e604628070101d454540f45409066050718001a040400010700c0d00c586120b041c44c1c42c82a1807004504c0f0780c4180c5039030902e000042e085e58070030b11071000c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 142166330 1250 142165080 142165097
    0x120030112031b0501060509060306060a0b030604020d05151009080d0c020a080613050c270c09130b04060902030601081503011b030e0d020a1505090c151e0c030a 71
    0x405100300e0b840c07810503c42d8019400465031034a0598040e0219005803401000c030000011300070303d40052101e01414003d4049030390241404440c420347e51000b041c040d0001d40030081d000000f911031064511680c4aa5500c04c01c2e12000c4003004142210742d0b020008209801405101031038022845903010005030410b010ba0013103d1022076000000c56006030040d0007410101b08500c2c4120b440309500600c11816101c1c0c001552080000300d545a807244940100103030301d1191002c40d9007501607080015032415900701045040003401c0071071840e54901e0415220350b200081e80c00c00d07000315030140011a07000e50a6150000000f011003000921103034030008c0e0303032502200948003980028054041c1090442465060711030150240c941081c6034160361284c5041d95600510209540d080c00e68010907075402c0740500d062100c007814001d030004217203005a003007401303150361140c0340421001c0443c2c8916840740240c0303542c501030000c0700d90840d00031002005214603070302c000b00898841c52441d0401104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 142167580 1250 142166330 142166333
    0x70306091b2d0302060c100b040c1b0f050f1c050307080a020d09080313020a08030408030f0a0e0613080105100510030c020c06031e07030e07170c030d0f020120030112 73
    0xc030002c490788080c0d00724000003100f07103e03164007145604079001c407204140b244280702e4040c0000c650b4a5080140007900950407000f40e881100b1025048a0241818803400034054030740c9800c0c0618010301c00d1031a80550300409090118503020032a009060600c00c2c03d606d48600c0141850b10000c0101041c1a40040c100c1e01000143c1d100604054010001d55201d241441c0d00b0710480541e01030aa11541c03c0c0c0c503000800e118000102c80c10303241030401440c1002d00901c0c0c0e00c0800d4200c0d01000c010300141c840800c0b81502c441026001e207104003004aa58145010035460031110054841901800741080510460710b1340c3c0c05d2803805440d036140c001074044200c14100e040c211000340e455480017000080c041c500e91b4040f905840c0c000760025158030b60725141000e508517080c3e03020008480d08010000c010b0384100a4070800c045a0780c4050743c100e001c00c400000d0400102c000b801d0042041c80c841600e155909100e11563303409483c02c405100000e03900d80381e1040c001403058924405441c4103020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 142168830 1250 142167580 142167659
    0x6070807110d120f0603050703060506061c020702010905010f080c0f0d060b04050118030b01050d060905010e0a0c120c0b0307030905030d0b01080c03130b04050f070306091b 76
    0x200c26000e910640354010700c0e5400003064003c160422011070703070400c3c075a000303d228540b0501003181d40c001d008040161031030b61050b029101c01045168004414094840c000c10741061100440004010044c0c1c3d504084c400504400084d4000c3d03410130000c0001510700380e0700720555030f41041ca0100e02a4076800d0405000ca014803c0710518610241040c100140c1040318a001d402074450980351415200c220340c00804103000c10f0300c000340c001a00400100a10309111003105441402802b01145104081d220b050950381d119091100d290b000340500d0060001070007d85000d08981c414111030f02e542c51b100c00821f6002c070300410110b07140c000045000b05000c0e6024602d9180d01c001038a80702c4250130100c20007004440c0405011507d000c0c0003507100e14060048901c10358003000d040207031032900c0e20f541c2403202c00144115818810303e01c41c1007842d802001048011480b07840c01040203010743c50401500f8191081c0150b12010045040c1b00c0c0f1402034001344034950b461501c049507071114001d00d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 142170080 1250 142168830 142168847
    0x320030d1109040e0309130c0807050d06051e10020d051210241b02010f11150a061703030402010c031409060316030e0c100c1b0803030402090a0204060206070807 71
    0x20f074000c1c9400b511410400021018000c1a0000c55070003900305c0d00b520344407003941c51104c00c94001540500c0040c3c609402403024010b03802807190700042154940001c42c003480b0306803c0c0c4004951010300308403600e1900306035229000d24244050050300c6016000074006000e640303e000b1400300030000040102d5140200316005041d040c034100110130081914184070b5142c003800c0307000240b0200720000d544078464013002c5250345c10780d0351b40700489511004803016113518025007c68094280d52040080204504a001e04d01c41c16000842c2c92800410b0b031600c00003d051309407075800600c10000540c0c0c01503424100c20740c05041001d04907d0006641440e441900d100c0c5500003404002c0c040c80f83c5468042c4002e840954404101e50550f17920b10fa03a56149540039960f00c41340c1030a1220500303115181c81d001182c8202c912000075680d100d52084c941d0840d8200042a80c1f000c020402945050308a1640050604c201180780c0fa050240003512180d0042220080c00310040105681500c2080309 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 142171330 1250 142170080 142170097
    0x62705090106120e1504030207060e030705090a020c010608031b0106050609040225030503010f060c120f0509040612020405130c031e080a02011d07060503011403010b0306040308040320030d11 84
    0x94443d0503a95015940100703105030b5051f00140724a0001180040c0070725a41c0b0381d5a10010002e00b000f604d01010850001030041c20382008036024418a0840f2009002d243c01901e8041d0180d5101e080700d6000282c0c4101e214117040e07003681800010080b81e180ca90803030768007090954000d41c0d201c5405507003000003151601600b6038003400c1d1404006040d0b01102a505031000e81c2448001983c0d2020101e58030103420001401e1a00c9084a0100032405400781144c0d091442c1030072030034602402d000804468140d44030880d415807200ca9181185410b108842c2e01401c2c2008640c08129540c444502c4240c25000080915108500040300e1440c46000410840d600843e4541e80700b0f0507480007406441d87c003140059103140c10b040480008000b040c440c080e6500c40c1d44032030840c3c0ca0020303843c0040528111607500740d503948048541b0350300c080c03104620440c0661562400d5082c50f2800510340d140c04410701c104050302e80d41207072400c500401100c0c44031903089404100d56594401c1c000e00d81c41a120b2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 142172580 1250 142171330 142171333
    0xa0b070201020c1005030f13151512030309170a0219020301020702040603081b0c032e021b0c030a020a050d031806030603050616090e130b01062705090106120e 70
    0x10f50040217a01030300031481801280c82c5a80d180e110102d001d112010440d60003000c200707000034442007141e8103a200c1d070403005840158139030f210380d034440707002c0e83e0341c5160800d0700080e8407032515409001003805c1c20201c0e4089200d82c20701c6e101044c44001c0d1244040000344070085200b000c42c0083d542d00f50151014260014010802c3c1c603542d00e809015640842c280000722031120280d0a50b241001c6000100d4001c041e020308400ca08140c03446030b04030440040c00390300d1481101131003001c030058806461b100d0145424220650000803d641c5000d914420030fa110b54864810b40d0010f8a6185204c021500180c903001d0080c56030b440c1c1a2580c05088240007145c000700c940000360543c0c1078220400b164000c03070541c0c00d03030745540d00c108054003050b0703070320101140400004200d134081c81c5130354690103071180d8640a20b400c000c1e0750f4200d42e11001e078440e20000356840d01d0541113402d010070650140b004100183c003850b15100108141d01d405209001c14000038401c00c40b807070507842c3c009101b5620f0580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 142173830 1250 142172580 142172599
    0xb09120f0403030e0a03110409060609090303151a070303020309010e0d020c0a0b030f0103030e0d0803130b010909050717010f06290309060610050702120a03080a06050a0b070201020c 80
    0x41110300507070014481903000481341d5000d0342d034606203803000c9400d413034101004c21404420325040c800900721409003140d01560b1001c0c002046d0b002032003259002446a40d010450b0802003035121b9000b0380b1a048045204035105680312181e6060f0215030f82c0e50b0345800c0c0543c882d99280d41c0c41c0d005040382c522411443c007503e01403595060780443d4010000f041150010301c05601c0e0800030245000886540f0107000e0900014404203014100a0283c601c0082c002040240300d581d0703039042504265101000b50030040c010208000310482000d0140803503940c2049a4102074840360703550481480341d1402410110445800700d4801c0d001082d080200441c14000190380b07107207210401104041c031615003e050f003c079503465800802103d009802d02d1005022540307075901088a0442212401d90902000b0030422006031541803c045c45207440f10050702d9110900c0c01e01418503407000f00300f41126440e041c1c4c1402140d8410000c0c0050320140b45800d5119001440140c1c50044403032800b03540087c036003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 142175080 1250 142173830 142173847
    0x405040201110619060b090102031c2a020705040902010c1b15051306170703020f0702040513030e0301060510200f0304031106030c0301032405010801020a080108190b0912 75
    0x220b1300e4078004c0610800800c400c45e40c0c4d03104602e080c0205d05038140180c00400c41c8882054400c0450a40303100e8400d000281c600308002d8100c001000320391a2008681c14540105c1d00c00d8041c0031100c01400c0a41d01072150120a500003000c0840c400030040c0711840004010a00784007031070845e0050142d89001d01d187c0b0b92010f0005d80541c120505541d801303400c11101140b094411489006200206440002d0300c2e00c41c140d055000c1c1d0020a400c0c483d03000280304201c09030f56940a95401901c201440494401d90b9050003041011030f14885802a070400a041003584c41e5040520407032100703031a0020021400954805440c400441e8500c010310031064400158240800180201c86c4145c1c40305202c51060340a208941c00101c9040e80003000510040000c540c440304d401101c1c1500040e2500ba4401c0d500802c000c849080c2c100c0c0c003060b0350104c0e60101c0560000303502d07400f514500c001000369005410b6074000e010941d4a004180518003800f1a6040c002040020214600c2c82c001d15140d1505 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 142176330 1250 142175080 142175101
    0xa0c02011e0b1216060f02010b04060e04020910030c050f190806010e09010501060206010905040516060503010f0b07020325080f0a0c06180504180f0b0a0b0109120204050402011106 79
    0x24110101d2040040601d59801d0100c005240d03d5030802660140d00c3c000d140c003106031b411031852003e2606554072030b000c023000d541e42c6101d9840035050164400005003024018002e001000030148541c100911506002040c6259012002c80e542122040a402e44081c0441c030410142c0e0036140b280c565a8002040d907100106d03105040c1d85a100300300d0b4a5030744410500d0f013030300c81c20b11454025030000d1b4018006013080d500074550040c060303011600c058040104a040c41001c03640010005040400140711520f0b03d400c00400500c0465891070a05503039170002501c40030202c007086803210302d41e20002000001100300c900140b005109480701d4070581c1d42032075240d0040030800c0703c80300f41190340855180d005034000b0448480540741480400d04110a010041c034079000180c601440c000107404c001208082107948440c89549008054200429400d0a4420340c02010b0306000c02a0000e118010215501c007189940450300415180c45900050360401c40781c143c40d05150140204011003d000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 142177580 1250 142176330 142176341
    0x904060b0c060603060c040302013b0f01030b0f0405060406030816060f290325090f02071203050c0403020901030f030807020106050a090207061d15060102060f0a0c02011e 75
    0x40041940ca030b0390388003000c26031031342c00c1203454500d0280184024409075125403440b8109041480c0c81103c0c407160420151200b04c40514241c05000302c007181c21081d03041481d00d09100310000e00301444030240703840008070b43d03040504ca00b90065036144001203031503917281c00c040000d50304003500d903a0f01c02140010018080c00a582514491b080040c2090345a0b014416400450120058000c40000401c042c16644000103103c0b0380c140b0503807004518006c410304001488607000c040c10004149000c4c1d020702031355070710307000046080d1041c014480440d501c1900514200c45c146400510b82e4ac0e283c0c08550b26010b55007000e03411000c1e0100200420400c1d440d80302845000c1d0b1907032030311580c85410880c240c2e2214064150000780c2d00104209901050f0040d0120780c0c8510340c00b003200c4a00d12409215106404004142a803041c0c071040c202200b5498403940000081c4003511661608425598800760042c0440861540c0c50f2402046c66100791711000b1008203007111082c980613010342500c003501 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 142178830 1250 142177580 142177597
    0x20d03020f0601050d0c230910051207060206270307060c0e04050603030d0c030615020309010f02151b0d090305040504061212030903090e010810060501020a050c1002030904060b 78
    0x40740800225042c45c090a0020440342c0c42186103040f98101420806d081d6034403601907008505181e0200541c1c0c6c0c411240c2171040302050031440f002460301003000008c8983c803d14070300d9608440414000b40741d003c5481a07108801c079290030304242040c00045100700b40c11603005028003021959004000ea80d4022040e41c680640d00c12904801100410088860648203030f980b661082100d5611002a034020032404002c07420009500740c0d0718000b00c40c0794450411040010303040010a15141d60b00201c0ea4003850500f440144581220022007070306015018082000d40b40c1980c204408600a030012941101c100d20418810800d05285c080d0054005008291085061034008607545024071107a12859421404601505080f08070640040030210015410131075040780c04204010b603894568000c042901c01041c1c030030000700c1100101c13600798000a045400c120b00d00804a03000180b189068001120303013400c1c0456115040e8030b18450103000d03a8001e414203078005251740d140d43c0070b4030170706 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 142180080 1250 142178830 142178833
    0x50c0105010e01170c011707030e06131b0e0103030c020a03060c1e020d0206060d11030601030305070302011d03070212010b12010b190b0708030a020d020c06040c0f0609090f09020d03020f 82
    0x300540c0040e20b0300c40f640405c1190000e21004074000f01101100c040b00e80141486c1400a0155903142c2590700b0039000b141c22050b0030383c00340c8404081184850704e4509550001c240c0564441c106088160061010f11002e01044540002c060540d500e06801c5801540e0194081107441c8500c0d2019000401c0188072461071801e00c110b0411844c00810030744010415a405890319941d8002000b40e0070313480b05801c3e034100000109981240d142084014040d50003a15038603291101c515000303007590044504217a58032403c031002450900004140c6d51460740c1100c1c110705500e140001d00f80140b8400300325a500500280348003c00710f03c10750101c0800c0e02c0944002c0c8001001c44d4100751043c1a5115906030500708002117400709010740041c0d034000d850b0f14030141c64809040400c5003030b608049034030501500018107100411821109000090a1800302040b0803880d105000c2e06401d440e10641210580310f21030101255a00e6000e0703240d40341d00400202c2080031340c4c14000d640e41140395000809 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 142181330 1250 142180080 142180109
    0x12090b06010e0a15050d11030c12010b040308040905090a0203010c05040306050c0405060a0f03020c0a1103010b010905130c090815071106090a11130501140a05010302071a0403050c0105010e01 84
    0x40f41820340e0204152000305600c40148088400d046890764460550003070700903551030300c8414000c5000020f50043d01c50411480d2103030502908070651910680c8010581c0b0b4081100304002074220b0203640403941c510800142c02e58030243c0302030501d925904002e40c19440d08120307001c10303a007103800b40055a000381401c1069544188041c2014071890007419481881070003040141c52182050f00808038051401604102003c4220b6141443c002012221014050a0401642024030070949000b00c00d02c0c0034504c00389004040ba200e0610650412880b5840d03822407414207024541800040c00180202c4414590321040020102c800342d41c0340380040d42c00903100c180158000352007030042d0030072809040054007a9995480210b404941c0035040340c5801d08804108070395100709030007803002542c07241c50f24850f5000c105010840786c1055051601c14888400421912504d250007007141801c10a803945071810107841c14018144411700315820038002240c50212400d04074101c0d203c18200713180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 142182580 1250 142181330 142181357
    0x307030f111903051e060303130b040911160311010b03150906130b06091e040f0209070903030e06070f08030a0207031b0b19021908060a05010c080f0a12090b0601 71
    0x9503002500d901048041408500c44483c2e1011701803a0002001000c491808002c0c400d492805101d50b80214100c00707001c9020008680310b409212014000c8007003041c982880001084090041d001d0f01404129001080240030b213025440000c4224000b0221140d21140e40f81c41185444c0851301c080d80c500903034012402c40c3c04101000000c0950212002d802c60356103d0501c00d12407c010504040070383c035110540342110715401d83c58000c9000320b00c1010007646d0f90060001d0040c02070300704010071075501c80810210790b028001c03c2003820100c0e075440e03460120b42400700c1002e11000010740080030000c20b10280c01074990083c00e55511030b40351a0503218022400009503025803102500340c0340c0b5103000400b6140441a0311858140701d04005041c0348030300844105240750003071a400490150001c0c44140d1400726210380081c6402d1826400700804c995922696004030005041b1140c1d000c2411004a03004164045415526070400c00c07800c052400c0281028a00b0740d102404581c29401c80305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 142183830 1250 142182580 142182587
    0x1090f0509070315022a0105010b03090a020d05010b1914030303010b03040204200a0f14040f03120c0611030a1d1b0a03081201050109090b13020307030f1119 69
    0x340710300480c6024008640c80c41d115803104082044428030142e50811017901541c20302c111a1300009455200c001940c45510301d55401c40314181c00440c44040f05008200c850f0200107108440c0c0c59042d10410340100507480c2c1a80500440a88a0b5100302142c0f9084e0b08ac402c00d414450480c3d034008101150b8441000130305490f0310080c000c400e55030b4402c100240160038290400e07110740b900041c1406500305d183c1021000d542201c0011000541c42000b01114158003402c03602e4070321080d008503031806140c0000ca140a540e0383c032004121240c0b5017100d8800d68012210b141070a6008413050000f50100c108030b0b0081e034800c607580740d407252030070441d1400540b400078601c862000351340080540c0170034100d42100409510b810968850996030b400b20000f042d040140503411890158010103506090015040ca05190000142680b800311002105d6403648103080c403c000b1068016034981b00e0090032800343c180035144000c45424054183c0c804040d8100506000f501c0f10044615091004400c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 142185080 1250 142183830 142183841
    0x305071410031e0b030f010905010c0f0e03030316020f0718050106020309090f0c040305330f04030e210c010807030e07170c030a0501060302030d030c1d06090a090501090f 75
    0x22100440d4880710f11031003505610085840c400141141d1021144410803400c0d141e000030200c4159466904108101d508034607020341501c0e080c208a259940e003040420394a000041190b1101c070b441c6d458041d9024004e000c1d19800c01d0495080e245c0050301d54100103a82a101c40140880c640303800000a503041c1f010090b28110f2100419220f900d031610000d20340314400c00350444007000c404220020000700104205030382e40780d9a4240407901030951100308003010480500d9050040150200700c0300456018480341c0c016894105031003008620000304601060030000c9a81081020200d011a0700000580003032a180903a2411495070710b1503030440941d8040813103040aa031111000740203440b501603800c8405044003003250404011440040d1900c00520400c0da02650f42c1c0d0300600650030306000c1708a0420007814140804408540024601d4441d55034680c004d04448404a46c0f556905d0100da903408801880341e00b01e95158814140100002e104010b007072440c051200e4070b5440c403030041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 142186330 1250 142185080 142185101
    0x50a02090303120c090d26181003021606090b0f0c07080a140c0f060a0b0d0305070602070215030708010801090b1303020c03010509030d051609030b0406060801140105131401050118030507141003 85
    0x40b84d48c1d8441c1d000611104440c525601c10034183c092000e03a90220496402c01940c50144c080030030050018202400e294a000d0040355118000c04100b009400f1743d03604aa07035150b40100180d40c2c0e100d10460882da0900e0040c080d81c54150000b0b00e180002200098107682c00b00d051098420039190703d101007003161030b8008074070f40200d176052418001c280501c002c1c0200a001d004054540f400320b44c0021148040264480500b1402009000240354040c0d44540500700c0000200441d0000381c0b100807400358010500c081c4010fa00e0288000c240c8280f2070030700d558402500038411410207890140e01e075000038a294000078a480000380b900440209007000d045000c2c0c54003562141551610b0f150024010402c1d0380140d01c81e1800215140d09206508415040c842041c0007541030204012444e05180880c0e09090300f041421000c0c0c00c1050f00c0c0c103044030b1017400d0040d01140005004070131000d00e503201804501500c0030028032031100090300c3d00f03012812111035808050620050b0704480e00e2100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 142187580 1250 142186330 142186357
    0x3150f0b1f0c0503090301050a0603051612060b03010e1203071b02090a0b03030c03040305030a08010518010b0901030b0a0e010602070503070305150c04031e06050a02090303120c090d26 81
    0x2a100c0e1624002c00050201a0160341620303c1d0281070000719094480503145503517016903403801042448401c0c440c500740250544c00381e000c100e10700703005c070010f05182c0302001e031500340e55425400c8030b59025030008402030849030507100709400d492015030182d0812030790340780400c80e0701c5c2c1740c80c0340300000790321603d1001c1d4001c0c18a100c2d61101300a10000307200d1991070740e4052004120840740c01d03000300054401148640300071561680011001000114183d00050043c00c0c80d203403001b09405040d5031141911500c841321900d91700d11500480c0900414810035030004180702d00030440440d1006645d06807605502102c201c86c1e55032092680c2c071400e520002d05650000d05010748a00d1660000d03540006c9041201420035450303454002141d41103154200104e9450900b40040021a02a8a5000360644011424406050007081d101e224141c0314a401e44101d00004100250701d10580d41d1101d00680003d1145043d403070198001c0b03040303c04030802e846c40100c419542000d61801c403910b5a10412 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 142188830 1250 142187580 142187629
    0x30213231b03012304020f0703030c0302040b12040b070c020102190f02061b0c0102010e071208120c070b06030a0c0b0c0109140a110306060a06110703150f0b 69
    0x114081611000d000c150090303440100200c103280c04007014501a00c0300c240462005034500340140d005480c04405076000c0e60042c0000429203504800359103206806040c04181280a07150881c02440303140c00c0402c00782d4002c241285c0c040c28025460b4483c9200c0e41c0e20798401d880b40c0c441903464000851000b8016440000c011409074101c0001e05403032881a02074100c0f0984541c00142e00381c100950590b040040c0a2100040403820407014010030401c1c0000c0014540110000d0307101c00460088200607941707402c2010420603e070044500601204000c1c60f41c0f803c0284078030409a02c182e800f6900d21404c000454200d00d00800c84413841c03584842c09080c030f02e292071031130242c9803c155036010f070700e540c0c840c1440c0c041416100c4410480d60182c003e019200c00c02d140110208071120640c0340aa03100c4800c0081c162540f2407131074103903122800c0c030500008a0403a418600401900010504900840140500e112540000b0300b03410322444184040c000d001d040c045240000d880c00f1041e400c412 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 142190080 1250 142188830 142188881
    0x30f03040f060b09070804020405100308033106050906010603060b090409031206030302061b120a02030c070501090317010b07051e0a050703051014010803180f0d0c030213 75
    0xc000340c50100d8814000469640103c0700000d02144040382e1480228507548100b2046250030712070154412080754210711460700f90340300d01106000080020740614407860340207001103103001c03c0c5404540c5042d102e102000c107500e0301d2000b821090300d5000f524031420340046882c500a019000a481061541c24204050303e003c00000c1c01460f0416030a21001901d40030a01785c450084034050b500a400902003030a00c09603844002c041e207109204032101c01c0c0034820120905414190f00a004d0440141c0c60f40c540503460030051080c03c0f0020142c1d0711b0300c1e10840406401c2400e405541d000d46181e220207030780e50307101c1c1d0030702d88110038005265400c1491403084240015001480d4050041d080f601800b007140c1e141031400d43c890b04107071517a82c02050000c0360410540940303108030b20210034040f00782d4035005010341c0e2402580710040700d18480346000032060b10381150340c44401200918540071074032242049044003800740400c4c3d0241260210030100844140a01490548500c00f00d50180410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 142191330 1250 142190080 142190093
    0x9090d08040f0818100c020102060105041113030309050406050a0503100914010903090905090a0519020409150203150f0d03050315030a0308090c030601030b06061804180212030f0304 80
    0x800403141c2c0c1c20104000b00104110b40c0160030080d491541c03010302c41e1409000c100d19821400803c0041000200c1c0a50050741d0205441d03044810a0b100820143c0398100003220501402d040002c0850340400000141075101d41d01400b10f400560701040141d03210b00510509088501030281c0582c0022504113a80b69a82c1c0100e240a010b4031400c110085801c592500f59018407405800003020b4100c180300e00701c114840c0542048401000f030a03c0310295982c1034440c6500b115030024041c05c01080000e42d05c0300c1d003009401703544c03000102e03c0c44c06010405400941054072141d9815400e0204a002410865500c9220740c10041c108204030f4090f03501166940d0004042041400d9034003104d182580f4100000c0c06954070940341c680e114a40b5502080c540501c0d00711217407080c0c0c4402c0040010a41c90245660840010b03201d0b159508903165101483c1e450b4084c0c1250001d24121495110b6001c000707200160900c01c803242020050218a81c070781e01c3c000d0440f040c80080d005c00104000905 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 142192580 1250 142191330 142191347
    0x7120e030316110d02030f0102070201020c090105091317130e090106060503180c060301142418030c1011120f03070f02070e040c1409131104090c08071409090d 70
    0x900400c5504142c1245d8042401e0002c480c030301d5001c0d6900891020304542e0140f1007002076007000c1d5410260b642c94080080c00051020744609502290321000c10180f02d00e850840b0490182c007120a5514801400b01d400594214070401815a0302200407440c48001030080c20102c0b0195034403d8103540783e01c0341103414461000d844030020b1140754817518581d04c40902850080c07654040b20f00d1014a90000d201c1c0c401c4c20407581112003409455a8550182d0075820b8841881c5400304400d03940620340c010a24041c000b0f64115440007201c400c01814643c132203001c41c40b0aa001041d10b0205040b00301c0504280a19410a800d100c030034000110814401c480740550051684102e420b81d540d03e0041d07100182040d5019190a29520710a004c0400c51041810340554140d903803103202c0c13500000c0110744105040300180103000c60079401800d5551900f081a10079080004d42005031b40e81e04401d6941c0480c2d10560318000006400c0d04c000c0d01d4034500c4988952040c0d8040d010354102100d0440b640c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 142193830 1250 142192580 142192613
    0x31706030a020901090b01030b03120d18140607110714150403120503010f0e01031101030f15061106010e01050307090f021902010b0406090216020607050a0807120e030316 75
    0xc50000c07000c0150707448a0b2954024065908006020320101000400362510459403034040c0d1700544a08501d56041001c13100310320601074001074204450440ca64035407409500241460010114030380c0340b070b031000c04d8040c06460a915130359090300510801981341d107101e12406625104804034038810f420030700129602c0c80001131440d4945a100d9989502038095012600c002410101c01484001c0e006030104000c1e29808071080299851955090381021603000224105611506101c40d143c0c8a600308400b102c508000c0320080b517848680c014141c500c0070310151003a00c1003100004624403401081070503203034090040c04041c0e04020a690141014182807450941d00300442101c1c00d401480350380f5481900c2d0f00111320354061600300000d59080d500300420440c810010455040107111603c10700b030b54155410794a9411905001d42040ca8500c0058503480000800800b041080b10042003640320903291503c0081c1c45000741540c07405050303402142c080d03410003c0340c04075010148081c2602e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 142195080 1250 142193830 142193833
    0x1403070608041a041a06180a02070201020718140c090a03020603090a020301050c0a1107050307090c02030c01060308220302031207060b150315040510050d020604090e070306060e0403170603 83
    0x26106000540b4840d00304c9040d10502030300109690b10540880d525500044111803c000c40d031242c2e441400310100141c14043d11640c00514071045900034003000300100401e005900c0e10300c1031f020340403000d40241d4242043c8144480002038400c002001039507000d20003d0700c030820203800d507400c1c4180c42e400980320806510800320000d005a400b4050544500c1c202903400741c4582c10f01704040c01214054600e0b1050b0380011000780311540b4006030040c11030b0511f031000300302600c204100703908521800c00b0955580d424808044181700c254001042c0d5102c003000780902c1c000d085030040c2003005460000960581285a01c0d007000c4102c440640170785401040700283c0b090403880001c90a20741110503800f0310b40048101304031408110307041c7c540024117a030240014546000102d4400c0c40900440d40705100071072100080d91500000d48020b0003001004000c18031405241a070f480041d440116801400d00d0b80100359800e0080f000d501543d80754036009144003004982042054000744480d426 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 142196330 1250 142195080 142195103
    0x30703050310170d030e0d02150c13090515030d0f0521071e03180f080408030705150105010903021e1215100503030c0d0e040b04020d0510140307060804 67
    0xb003041d4005004204075980004c00a26a4581c0090143d841450050009411128034091307160380201f031002d03845030503441d802400d42d50780f41d845030980204038008148a407584404954129954000380c01034400e081e408188414500400d80c1d60304000203000c0000d001c15402c140498042e9000e46201c0d2045e5441c803d090950b031010305c500c0d50080b903040000400c12180290b40a4448960b019000d12a14007032000000504a40b0b014210841e8001c1000b442d03860020103000b520703402c0e103016210000940b90348060908000c2d689007151680300c180c01241e00300000300b560180d42820101c0c7d07800b034450111600501017a080300307145900030340c2d049030310f0302d03100040c81509004694040d4120b2844400905284100c1605e22806402c60f81c0079a1007040500e4440f54001900301d600340d00351401320300c00080c241c085005002c0ca030180e9a00180003290a11021849410161044840b0718503520004d0b522200307460a42e640b541c0c400d405800c0550180103039403081540300e61050255621000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 142197580 1250 142196330 142196339
    0x60a1212111009031d0901120f020f0a120b0a0203100302010309260c010f0209010e121c17070906090603150b0304062009030303010e090a051203070908010905030703050310 76
    0x1070f500fa4100c100e0000390b039003101100100d845918031540c07250540f005401c540c10100c200554881404010b00b144410703c44000456035907103400c05d481d0701c0203081880d210350b44901003000c000045004803644c3d080d140004001440d5031080d070303103d880466200d00c211032454005400410310804142e801191665080c0c08204070541c80035158a16805060b5803145410305090844504000c50310034180108142c120580e400b11b0480341020b0222900e9440307400b5035013840e00e048008881c5042040042410500c0c6640220040c0c40d403412201308009103a442040c12101024503000301c0002c56400720382070250701d1281c0c1c0281640e50002c4041c3d1019615080b100007550002c40d002c5134001e0312040070a112032075409602550f010040941400c0411100c00280c4a000c14000d0400d614006400150b1898003042640d011540150503151540a05e2034140300940c02100c00d4000300740d0360900019200310510661000b1504403001c0e5061414a40c0c00311510340c03000d070000c0d260030041080403e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 142198830 1250 142197580 142197613
    0x102190201020321060f010201050f0103030305060a08190c0801050f0406110408102711060901030f090606050102010b031f020d0b03030a111228020f010212060a121211 74
    0xc4c060380e50207008a0985403400803c000b0006d0340070b0301411a41414144800030070701401060540358141400700c0e040e65207001080c941c6042e0f9121040b140300b00c030b0b002c40c010542c124a003441180549081e0f00b03e551281c100d98241e590540d0603640b20004000007801140f00c42d8400360140340e0300d000307191503e941d903404d07540707044000c150400e03180780e8030840008030003010f20340002991000d903e0307620002419200e840459180c03031034441c0110400203520000ea80f003a4081c8282413910b850801c015a4203013081c1d001032020740207090144d0300e00124000c0c80d1500062074001c00d0050001d80180b00b00c4800040082d40100d0a1a0142601c4d10303d421f0301130341c003800030708440012070340d44d50195841001800d01d0221080e05128108404210b420381d50642c401140b007850784000c4001c62909061242246000150810b440d01d0b54404103050003400401d502c0381e4080c02c0200c81421220303484a40d40d100300c41c22283c0061900c0311126001417a0b038041e0076410080702800701584c0d038100e08052050b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 142200080 1250 142198830 142198867
    0xf04140d05030a201b0a0c0603050a0b010e03120d1401080a05160f060c031403010803040303020c060f03040f0c0306020f03190b0109061b1b0e130201021902010203 72
    0x40c03000c070340084108010780c151885200c3d0058000c1040d1007050101c04400c00b807911a001c000c881c05507a5900d210300c0340d00100039404441d58030504901340300b03a803550003d000304000d036164044070382000c0d01550650710510005200c50401000b6024020b03c002c075101a03903101c4070040038041e8540c2c07075509001d904000c4250003409124080c20b220b01d0149402410b01c9041c545074a800805c0e06028403d000c030100312402a02d02a08010045071481e00302941c41540c0102c24042c0312200000100ba210030100242045a1007a0200c5c0c0040c8074050401607180202e01881503425000d01c0080c000c1404502e245c59481e008020820702e058a0b07888020907680300a54100052000000340308400101c3c1455941c2180c441c0400c0024a861400003800070110b40300300307001c01c510305101045081441029080c2d0a0b40080b11102181054204c000d0700555885a0328601e020500020300715601403000041b840d505070b0180c40c0340316017008040480001000305030704504c402e10100c0708407180041c44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 142201330 1250 142200080 142200103
    0xb031006080109030215040803010303030905190804080c1e0f1309030305011a0a170a15030506070201151202040507050c0609060f01060f0203030a090203031c05040b060406030b0f0414 81
    0x46049003a500340a0310b085031b840384030742d42a440c00c020840400d440405880c10341383d251401148c6862503003061791400c0240b4178032407119900f90130701c0004c001c1128000c0c000c03244000f040d00c0c00500c54a0070806040541400040343c07540c00b048140da01e10780020643c0500b1760041030f82d07258403400c803001411100c0506003100840d680380010302c40000590b280421444440d0030b0300b4581054880000c2003810a028410300007903191002c00e52030f200302d40001840c00074182004140030f641c0d0800aa0300d8405555860255103403881d18000700386580041c90540b030310103030000401c154503401d12000702001400701080103018000200504003e00c0150301030340c0a1b50040c5101d00703208140c2d4241e098180d02ca101844103c0781c10a01c881e4000c0140d0f40d021100000010709018240040303429071013403c40c1c40300c8600e60b204075050213400c298401030146000368070245032340d6034520074482100c0303030380c0005454403031118000f42031545124507060703201c2e11070b421000340c40c0c1900e5000d602d0031983c2100c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 142202580 1250 142201330 142201333
    0x609050708030f1c020403050a1407120c090b0607020d080a030b0409060b04060602010b010f1d211212060913020901090b131a12070e0703090516030c090b03100608 72
    0x44008a0904d055088000c0c02c40b007003c1145464a15607a20f83d540c120324500418000f1a01921403603520140b18440c0102020243c0c8004010140342c24045c90840b8000c03440c00c0343c0f51800070120b07030610b01c0a41d100c583d4058a05225564691111101381d04042542c40800d504d074181203000fa20b490007401d0040740b10785004a5115400c00410058610030380003541160b1421751150910b0383d0198a07242e00a00380d0500a00310420103e5020019107100d074910f800600c1c9150500092104d2148074240c01c1030070707090b01c1f030060f81c5000c00701d0144211100b031031002c40c050340811410b290101d0081e40101d20310000440c0440190b0201d943c26400764007642155540c2c1d00001c140c1d00b045203c3d0702200c03003104010000b442c000780a00010108242d0a2405a10414502c02c1400d10400244004d08081c8c0c2c3d07510358910745424020044c1030301540403180c078003400c1040c401c0c0d400e003480a10180d03a80014410702c42070504481100410a45440590504c5030060007940c120742441190081d0100300c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 142203830 1250 142202580 142202587
    0x20706051b0703030e2d040c140a02030c1504230115080309010306050603010b0301030803060d0b040507150804030206010b0a0c0b0c03010905010e0705030402060f07051b04050a0c08040609050708030f 88
    0x101003200d1104050300710b040307080e098031b442e00e0224114800c04a000c031040303400003540e41c00c200080714550f0710b140b01c01c4c08840b800500039104540000203030450b4600390782100d00c007107100881501c448500f0707038000300000001e0b000754072540798811414909602282c000140000b03400d40c094041d10207644101174a03000082c8200c100d50f4140540e01c0613240c241c1d003551071540f43c001c000043e440148009032100901101144a654510503040b1a140c0c1021007001513081c20f0030301c50740b603084074441d40a29980384445648101c5c000c09149104903050340141095038a00380d0000700c1076210790910740401ca103940f1002e0000e2281c40041c4c1c00b401e208003c981d140d41c1040c48801c221001070704410160b0724020100010340b40e014080b01d600a605482554072000c0703003034800c0c5403405011001032003401900250310100b01a5000070038980360440f010302198a4041810080320030400540002600940000340814450b8008201040c494001c0b6464a0342e105541425a04204041d000550000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 142205080 1250 142203830 142203857
    0x3070309090b0102030a21021209030306040b270403050405030706090503060703090b04030f09050a15030f0506030c0f03070e090f1212070e0301060902040b070b09010b01020706051b070303 83
    0x20b20424008900038001140b8202c038051015140002d1502c0030061010803c040c074000d0080c3d85c05440350041341ba69460b0103414405081d640703a41089480c2c1b0302880c90051903048510f400300720500082da0b09928140d00d944800c5121143c014020019801d100081000040648003000403030700400381c3d03581d80304200e800c20041506049001d001c8200301070500000d42d02090181d80701300d40055041c14403520380040c0c3c030030680d00c004443e80802d521008950001a0040303100303c0c01072034410b9039502000001d0b80150408100c1341d040e80e0458142c0c1c0400f071b1201031401d0190b03c1d0040044020b04603105140d0f11980e06449140490b407100c0c17980c01000030340051902c00c000d28003482d0f000c400d002c0d003040b590b00c04039901c403880204050708200020394640200d03142940200e02604480070b042d036489407110038110841d0320002080f10f08016102c0010100403040c0b182d6071a02e42c0503806485640e250050488680d00481c0f10309002c4080b0f0f55203095000010440c0200640c0f0030f8880403d01c03400c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 142206330 1250 142205080 142205099
    0x90507030c14161b1e062106050a060801090518100b01050706091103071208161109090322150522060c06050109140703020c03070605041b0602120f03150303070309 72
    0x20b00c5c2e19524010007808007884043d4115030710307141e190010310303a2503101700555288501078035079603101c05e0700800e404901140159002c400b803416102a40d105211a4030340c030243c4102038030640700e8624550000340301a2000c00c515080240f815605140003814243c142e100c0804a034840d15080b01c8520f040c081d51100da00302800030764001d040344200c1e40e88000399a03d0b11b14103032240611140001280c03100756410044c0d014103032081298083c08071805460140307072190380c941c4490311b600100c0c0c80780c0550081c3e0080300d4a4403030503994240750010281071030a00c1a15517410007420809500d55a1091842c00c1403000c1507107008007816600c280d1100c41909080007141c0040e0011440f603418900c0c0d29481c81c441384030060b0030110600d4010390780c038589107486040d070244841c01803c1074101002d00c000c1c0240c2c444c0040e0f41c0340441e007580c04025a01c0c2c00681c4d58600c0c801400032000e8090210f030b00a058032501560340200d00c00c000c0103c9100240020341590b201850807000b084126209002e005407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 142207580 1250 142206330 142206359
    0xe010902122d070c0506090c15040506040902030402010c08191d0f0f040e0304170f030301060c06051306060303050a0e030c01090e150405040c090507030c14161b 71
    0x42c5049041c0348030300071081c0d4000758070200760150044249000814241840f40b03049809954105e402c3c1c0d0304c0d03401d0802e0f840d61988080b4056502c64910249050f4001803400200c2d011903800800c42890300d03140c40e004c80040c0d040180103a05012020fa4101c012070f528034000c05a42c00c40303403403414038200942d102508541920300d11404100803000d440c4999164815902c2d01d6007405c4401c4003c0411030000030303001d044050240d103100d01001c500021400700c00d5651584100b0f048042e10700c21305500384d120746d0302e000900c14100055088400030011885651016801032080c00b8620044411506c0355015550a584118005000091400081e036400022201c1910040707010f04055258100000c10f003100c58003c01d283c160a0401007010781c142000b86400c1108060018051450300d801c0c0480d2054880c480c140b0103038180f000051006200340708000000d00e0680300c1e10014520080c02051540041c2e4402030303602d1008400c40040b40e0340705d004140e070340802e100d401d40d15030800d401d140c0c00340c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 142208830 1250 142207580 142207591
    0x90608010b090a0611010b031c0206240904060e032a07031104023f010602030406050403031b0204060b0d0e0a1101270603091106070c0303050904060e01090212 70
    0x4105000344059555002c2c0f2181c01c8482e10318020f00480c3d58034200ba40100031501000b94103115500054401d0b5244203400100181039400396801c40d5944c52641016205006c45a4952410001e500503140380c0000c4498205000301800120a0b152500491071940150710b240a168040c842c800c008400d940361614446101c01c014001c200d1a698a00134082d0070507034150f100b203402086400581c0401e41d0b50880c1040000039082c040002041a841c01c1c40810100441e411005000840c0c203d000004803021180255942880c0603d140c40c110b5001c1008054045400802c4000c14056900ca0244402401c00c45071026610f004030840001110317550b51100445070001e1007080e001c00c002c540100343e2a00c0030300700720011803212840c07106404510481c03583c0360500000082000c03a4541e00501c034082c4282d2044401030103000400c0014024980002d2003480b2184003400060304c500081c001184002d4408903109843c0d850a1041c0e9000341c2001d501c00754041407281902501d0b1060a4100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 142210080 1250 142208830 142208849
    0x206160509010e0f01140310060f0504030b06060a03020409050f01090c0201060b0322210f090e0402010c0302030c030a030b030705061c1104170a020102010c1404030b060607020d0309060801 83
    0x5510001803d00200240714a01c0341d4a0607504c00010b034064144130034a100003001c01a600e15000f03d860040d0200f83c01a000042c1001d15a021514050812142600d40040b10120b05d40e44000070404d03e580119410380c01c042d000c3c040090f080000c1e0103001d01440800350544103e40c1003100c010100c50010f2145011681810001c01000c00e400040303c1c1c024460082610b41d41110040b4082d07031041c0044010085542100c80f90100100040318222001c4180d94003101c02e641d0000c101c0b0401518092008040d0701700c400b09005601a8009440941c400e0043d2403e010154130903900f50f4001d0300304000400c0c0c40d002c8505580c502404110042e01088400e5801c103d07107003080a12854100358600101903445054060895804007650018030001c45a40315285c840308183d40c6a07007030030204901541c01d00fa40b8068440c0101c0e408000d4042d640140741c10036141d0384541080c03031400b07040e80ba04030008000760005600c4103580c0d0340d0100c2c041d8a810080742e01d0000020b08543c030582c06180803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 142211330 1250 142210080 142210087
    0x50619270c0914030106170a0b0105040b01050901050a171003060f11040512070b07060e061e0610091206020705071202010903060b0f0a140307080109050606040c05041502061605 78
    0x702508001c0d10015100d400c050152142c1c00c001c007203030040000340c0091502c48007035000706140d1000010340398807061048804000c0d0f039a0310b80030700081e201046d041c0d034007051090002e660a54426405440110032520380080e070b1250000401210310780644a400c03004c407490a045c41844000c2c001c03414111002c5100f000361444032900414203010b03600910384101110024540c03d202d007000303840050501010907680e140ea8625089005122240822803e0701601d40082c07426200ca509241d11071038007110300c0e8007507a58a0304214060300841c00f00c00504c01031041c045202290384c1030100c02944180070050f41c803012400c1c8580340c03202c60350001c120b100e80300a000c030060764070171484c0080325401100401c00d059510002104480240c04d5503400032a0200006403072500d410740c584070201c041e0141c031081070700c406070300d400c0c0d481c40303080078295170b1010020850500309580080d403001110300d803039401c103511084648590b00b0026032850050380100140540c42c1c0300d5400d0060343c0f26803400c01900d07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 142212580 1250 142211330 142211351
    0x60315060a03030e06040b0a03090c170d030203060616080711030714100e0306070201060504060801090818030c100905010215040b040303050c0405101205100308030a05061927 77
    0xc0107103000c010104000b140c01c9040c0c94503100159400b0344000300020340c68140a0000800a1900340401e40307290302c05500018808064024441b242511103015100303284c0038030310030b83c080d40c070140c440c54010800304241c20203c030305241342c81100f80c07003041250b40d0303040c503410025049012841e400b03100e0380201c1c000f00510704010b9a8050948400d0356900101c82031014140d40c00310781d800ca080c5d010301900041100856040d4400c2d41035441c200c82c204900c6d61298202d908035807001d072009114041c1009034410f80100c00c5045010401c006007182c902140400115042c40c1d2a001001c020032007801003800290b0b01031242c00c48882c00b0824103490341c0ba00b62110320070b03200c028001409265940010500c880c0d01c02c0219400f402c00507040c1c0390515420031009101170195098070400501c0c01c07010036560100a4400d41c2102c0d0010b08542c2543c4a0082941c014130000c4c02d002c0d84451401132500d0440040400304000f005100c51400d06c04205000d801031009400c000d00e002075207440c0c807010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 142213830 1250 142212580 142212589
    0x1403030705120405191101090b0c1e01090c18050f040b04110f060301150207080105040201201f02180301140a18141e030406120f1b030506031506 64
    0x940741d02d0306440d40091929039051117070403d05201800041c00d4401592003090084012089200d650b080e81d5403110383d6901d02d05c040060050a040034030b95041a42c41c1c6250079103d0256040c01c00c1003400010741c007501c9a60340c0707441d10140d610030883c900d01e484e65903120100383d1065551005c0b08140c0c51520f464903594603d0016402000113220b01d01046500e403158440c0341402d11810000351640303950756103483d06041c40342c0c82c1d96416001803149507404a14180180515070082d94180c4918419401c040080303010002141c14070780740ba12504000d911201500212600591910000140d0b204148810f04a440e694810290f003c0c1e0f0400310160000451010400d500180e8458005140079a034460000c04280303505000d007200003402e80a80400384046403511403181032243c0450030b51840360b14161072340070f18481c540c007160f00342d8800c025072941900015554a01d540000030401c0b00c01e41c1c040f8540d407121180d180081d540c0d4040001a003010811034950380d808081212480c80c1050004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 142215080 1250 142213830 142213837
    0x2100504050a1712010803090f0a080a060c12020403121e080c03090c030a060203060f0d08180604030503190206151c051221010509040b1b090a06020303041403030705 73
    0x10485003c0011140110f101502516800a03820701c5880356940d41e00d05e5180e80e50040e0189a01c02c1c3c5000f03429007440e103407040148044580036000780403a0315417900c0d10300003400d079032441c00140046003241820081491000300051441070400c48151b00c1da001004000c1c0c00130801c040d44e0000300c0320016132002d40040d0000d070f1003181d1100142d40c1c0d03070f6210744403030603d0000c846e400d030588075187c104010402c507070300036501c591000c0c2c030680010340319582000300c600c1e42654050440903013040f2202c1040c804c544002d0408174041d148515280c0e90b50f4070f003072071503005100c1450001031021242081a40c10712201c2c0c2c110340c449901c25101c00d40c6000050703400e02c5c503190ba004080b08500c2c4c8481042410310610000003182000c684c4c513a1075048403000c0300c00200000445280b405c0001245520b4080b8545000340c2d0491b0720303100180c0d90640a00202e59180525030100c0c501408560803d903a5010600c001d842d050f4090340e00ca060514280412403115110702020342c1080c804c010a4a03808001c0d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 142216330 1250 142215080 142215083
    0x150c04060f0305010501020a12020106051305040605070c03051903060506030f0f010b03150f2107090e0d0c020409050c030304060207060810030201050a1b060204030818040c0206070f0210050a0c02100504050a 91
    0x1640e021089d0300c82300303900400032079006940003845180e5220501102e07600a92246020ba1002d020940d00c400045541d80314440000740440d100744080c0c41240c0c9006000b80b5041e54904000401d10f84610014040307400807160100e050220304104600340c500550028010298988000d0a41c1824446001c640c0d00c0207550b2409808504140310141e552090130f824102076100c084c1500c01d5011000ca62623902c91700416000c581400114100180001800400301e8482d0307480070a9010190b080001900c20380d10141c030148510400c580c0c0940d400d0009200a00740741e0020803115240c00320190030843c0092202c141c0d07e0f014101080540d0304101103403080c1806207400711008102c000f00030500c0e0b01f00b03c1c02401103440480c0110030802c01c0801816051203810100310b0b20411201048180c50224002c0401038021502284029006481001000401d4016101c1c0a0301d00040b80080f00c00885c1e14159454803500001c000a80600c1802550030028900b40038910f00768a030340b640d81500910 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 142217580 1250 142216330 142216343
    0x118030207050d150c021c08070503160c020316050a05090c0a081807030503091309020a0302040b1201020310060e01050301270207080c0604030306090905150702150c04060f0305010501020a 83
    0x2209800c104c09079201c50502410503904010301135595400070341c1c07500d0481060200419070400302c90064041d07102c035403103240c40b0740c0d070540f0f140e0300d844070790440d080c0304901203051105003108200103a50034440c0c1c1083c00c001c50305494100349014100300d608a4503900040c050018541409025001801211442140350800da0110344600c0800c29030b0011048061005005001021040160220007002c280808503040410200359034814030845d86905002944910031640800050130280c000034000c034001004000c21002e80c01c0f446099900480d0f00c0320994200100074443c10390050110740b1088002e203425810756042030203440080c0d280c0b04181d45030451140c5403000f00406a0102d6801d241d000c58000c0e200d008031100b65640e8001640c0c101e005c64100500410900040d00c50108850381060013070111000307908401c04000000b401d4071086001d10305500750580324940b5003500900c640b1507059030300c81c98100014948108a0b04441c10182001300401542e03a00241d107501260b041417 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 142218830 1250 142217580 142217599
    0xa0b04030915030c1e0e01080604060b0d06030c140a032d060506031c0509040f0f0510140916120e01051006120c0225080303011205011803020705 64
    0xc0aa5162aa551241c10b1282807814078144035070b455003010030340342c1194941c103545000d4996143c12600c08006214000f80c400304606110b07611440d60113800c8134003d480010380030740360340c0f400c0207990000001c42072164866400300100441500f03400001d02d86498154148aa8040014000b03845888082e1030405038840e1036544901743c2e1580301e88032210b00c04403070800392985844d00103013000301d94081c468001c074400d030022145280520344040b41c0315640e441c0b03088000010400248011a40d010180c2d82d5084145e0103c10320740f08460203622206a000c40e003e203440c0c4010f8084020210003170250400384144031518442104100c0b110031103090201d120150302da0440c005083c1e1001e1440e0540c2400140148520b65086002c180d950a5840780c01c117070700c91a60003082d20001c8a003035006034032009034034800031070654401441600102202e240039954842c580c0c6190001e820503800e0420640d1307000c0c01c20209114000c0a0402060f60552404081d01c2c0651141d03803601c0381034011303128071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 142220080 1250 142218830 142218833
    0x80f03040c05060a0e09060109080d030e03210402270105060c0c030607110f16050d17040b03060a05030c0102060a0b0d051906150f030201050f070503070f060f0204080a0b04 76
    0x202006010300000752150391100402d0130024030285241583c40d0041c0006000710360740794070401e00303c2c0a950416004104401070b88000b20002d0101d00c0724100c031f030b020600414a42500030f0003440ca031482c0c0c0820b00c40090900e4010404c1d41051080130f403400c40325071554020b1640200041e076044840480b203641e140c2c1201c15246044c170f6011001241d05029002c101302c2031301c0d0012250310742c003c0c2440c110780079070300e000c2e00140d0f80d424082c150806168825004001918045e10f104810310300c01c07a0000440c00c0c942c5203044094000c0d81000000c3c0c2000300c10083c01d418422206801014220014a1f813035103400c0001c1d440d48005011800400d40b41e0350764007615101e008810000030b5014007201c4604040b07044000710040045c07011983d0908004003008a007072907040c402c0940380442d107441b00e1149141c3c01903580c1d912071502c1c1c01d102541440000040351091014041d994081c2c2c403044101d4203070385812000c498103084001c0c00b031441070106200c0c0032000204040c40c039070300804215098480c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 142221330 1250 142220080 142220093
    0x8390904020d060e0a030f0201090302030403111503180c0a030209160e03070e0a0e07050907112a0a05060301180b0409050d1107050301050c090108280b030712080f0304 74
    0x1800b0003420040c241071840c0b00704500020a103e04502036528151600c072400c3c0202e0a9075031200380500140d009120600200c0d00088400326808401000d2843c1c403500085030118540007100c40e600e11000c0c80b41d80440c003403814851108002d00c21120001003030304680c001001c00c507000d40340001c0c2c03d030109a4000d0709802900c980c204a80d00508603207895070349508441081000315040c030001428001d00d10200b0b000000d2280654400802d919400c1d9101e42040350380c00c0d00400a886139110b00103901c509400110b5581050071802c065214502c020270b000e001001d145940700303900400b81000100000341c500441100c6092415202081c2d803c0000001400742c000350001525500a6a8881941030f0304a90003034101c92001c415113402c00c0d9180b04250883c1c070100c6128001c0e25080240d0f45140d8400c3d140075074042031b00703542016805000500198410041800d41d034001d640c2d00407007a001c2c81c04103d05001050b001c031101d056484180c1e140c60f0b840c01401c01010301c203080400403c040092 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 142222580 1250 142221330 142221349
    0x905030102040909020f0d0f080a0203090a030b01030b0f0f0a020702040f020d09020909030c060601050a03150f050a17030703050f0d0f020421021f020a020a0839090402 74
    0x400400075901c0356200e14600c4018212441d00301e20074a100c600705206420003039019214035410910308407415100d6180e62505074080d076200401c60104200954099450f41d180f00b020b036001d205104150f60541c9029141000041c100c000a0b82800c02005840030762140103903480744050b400543c0faa4880e1000c20050040b031300c4035030784150001c00c0c401d6030601540d2115900c01e000320380c0901291194a002900c0344038092103654160415400076040d035004078000d14005108c0e18001a007070680c1c0c01d420041c01313025008640c002d01180341c00c00452414100e14809401c0c031651001e0101a154004ca0360780c0300d41c0d0001400c1c04000304000e6051807980381510321000e40000188103986202011034020340c40f90140d440120114601c4030b65294003941c005450b280d001c0c1603020b5a01c100e0800e0380c0e0740d2a1000d0803200b14031070040c1010058549010a0b001480c003000141030180c2500b581c4e800100d105001c000b40343c03150030321000310105541c0310030603500c0701560304032101e4031640040742c0c4208 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 142223830 1250 142222580 142222589
    0x4090507061b02040e06220b0c07020a03050609010905011b021507110303070e04060e09030a031e09030509041802060403030f020120070308010510091703070f0507080f03030618060109 81
    0x1454066456504400400d030980301f607000c08005072036091020302030f5000012008010b8900d0714800c0010704810004c600820030180014031032100d03d503481c1d46031441d0084c22145d900440e5180e522400810000340154208881c08031262080810701000080da9241c2504d0442c5840c0e8100010070031041c040d5800007000c1e00c200081c0c0796640b500c544041c200d269a084124025031801c40006298004040702d00e00800c0050051840e140d09a00104c010b0700c1d901300b4081c0c1d2910410b040034030340d030344620138480300d5807007610340907145c101510800007140c0c0d0b511105d485007900e0030150030040c3c1d00c800840c5c06a903131504150340c081c950345100300d0051482128802c0080304035104030304006250005041a5442a40d88220031388e01c07a000c1c050384880384616400800d0709418148180d800c044091940e64400b80101d030305040c400d0b2142a4418020324007a5100d4100072014000150140306180600b80083c00a610310309145011800311150f1181c40410440341c803011580c0b90b840f60300084000d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 142225080 1250 142223830 142223839
    0x70f060501080f0607030908040501120b0405160e15090d0602190519020f03040b0715020f030f0109050f06060c1905100617030417030f161104090507061b02 69
    0x1907840e450b075265980860340b1904518030840c00050402446401021701035584100154285842c09005450014840341001c4542c0c2d214811000300f51100c0c8030b0940704007400310301d507000c0c01c400c0320300582003c0d505c0c990207005000007080c40780c3d40e100c03580481c1c600e403c0640d0b440b0000881810001c00a0081110f082401c5100c8032404050301d40c09006040103884030003000300c14441180c42660760319803c68440905420600040084160250240888030f0080314041c000c1540c900305002240e00c20b000c200b9507082c010040c0140c0c09002e0302c040c2c3c09406000400c01c1f040c108810f038400b0314400101900d2041e038000484008650701440540501c10009100c2140c0007194900940c840d0340700c0d0300315908e9519120000800d2000d07500c00208440c0c00d940a11b16080c00c24090180400400c9840c62081c80100803900464040b0710052604440d40940380e44c50340d9003842c0c5038a50301c88000209105078144000b21000c10404140e0710102d0b407880c10101c01111840038845030340f240d200e8020394407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 142226330 1250 142225080 142225091
    0x10050a080a0f320a030e0303121f0b04090903030c021908090d02030a0f0210030902090f0a14130b0a021809071101091a01051909020c01020403120c020a0506040b0f070f06 75
    0x1200c0000d8419101340c4261501c0d000e00501d0f00500d0303a01d00403950b80380c0030900d140c0c011036100fa40d01c515498101d0300450b0310440b034607110701022040b0390082e8804041039171b451100005150740341c411103010380303207a2015041d4600701c28000417441103020030160102c400029102000d58030030220701601903014060700d04020303446c149007615800e0b0303c8003030740201415000301c9041846485500e000d00d6000388118429280c0003110204079100500c4c2d03840c40d95841e00c040c4021240490240c0c8100d220040e00f0341510218501881507910281824403003600600ac2c0306140070343c240c5469003061050328410b415031b882c044212002043d4030402405940380000b8682406010306040e848240d00c0c0c00103408a0b640c40080c1b210740c004200d2840e4005019020500214000741c00400c0401104400582015100c0d125100c0400c140365400e8045000c00c1e40440441c144904000300500003114590704181c03905a6002c258415101401d5044200080010400c807040000011091b0429020041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 142227580 1250 142226330 142226423
    0x2040501060f0305090319180503060405031b0712080d060302040c050c0601140603070807020715120c020606010e0f04060b070803090709020a0e090402011710050a080a0f 75
    0x1a4100040302e480001e0400000031141c040000807611503021071000c0c5aa11348425604071070b621826040000c00f0312030950000744a545c07c00150740a140a10081d540d00d81c418a0328510700808480502d2150f04046410400343d5009080b805a0b0354124652950310041d50042d04001c122a800080d4030600d040941d40300b00d54444080e150419900c01100c68a980b6109002034a020600d10785038442000c00001300d000740304240141c0c004074075004072000b06482e1203226000203d517141c1c0074005071554104480c0403c480c05038100703044690010b082d840c02c01c140000d10301e1904d035103c54080d010b1010500300a482da030b8014002080804049070b11586645410301c200c2d44203032808240d92096080200b40364200f8402c980513500240c41705a0b910340324005201c50440000d00c01d03414004809100414480001c0b5030512998030444043d00c1107091500b0401d103605144c014220301d600002420b40081e00c0400c1180080e40c010070710462800c404c40c01da0180001015601118070520440d621 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142228830 1250 142227580 142227587
    0x4060212010807050a090e062a0c0606010818060106081005120312010e0c070f030c0807050105040311031e0d060314070302030c010309051c050903240703140114030102070204050106 80
    0x6058450071517180c443c0966900c038120940d480703504884440c4d00300c240070075501c0e041301c612100351850a00000c0c004640030fa02414003500407540386d044680002c0d04004c229030780880103641c0084060029510740091000c0140d81c1d4505001d07950030b10108001040c0c90080001c02440140b000500186040006103c103d80726002008101641e015040c0041540013040c04c0c882c0c41360b801c0921013400e002050700d600d4440c3d10310700c1c030039028800091140c0b0003103480c120040c0306190180700042818100b41c9002401008404105c03034098105200301c0707aa020581213020642a0a00c510340e031680c90291046006080c00d900041c405441e00c000c0403090b141c0800c0190440b802202030383d40d0380070988015400d40703070145001005900030704800c0d00c01d099010000b003030b640410300e000c43c00d200d145d0010a06c4c0680c11030b441143c0070740c03014581544003800440280d00c207256250a00c240350141c1140d0154031810b0040c0740c036284500c998004142c0302581900c540c0f035001081404035581d00e40029 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 142230080 1250 142228830 142228843
    0x118050304032321090a060804150506010f0305040606050a030507060201060501031e02031f120b0a0209101413030c0501020d0c02030601050f0a030b160f0c0309030308040602120108 80
    0x110740100c407140a41d081840800f807048002100750740600404051580c090701101603500f100510218180312444039900d031083c0341006004191580340c1d043c18142024020407652a000c0d01c031071400c1c40c081103141d9a03c1801da00c07800c803240c11301140c0c0c0d80f1146060400341c111030b082f403a00080d50a4001060100c00200c09044030016002004619240c10046040d00c078031031203c042442e0b03050716584050210380d005650000c5c0d40c01c48050b01d00c039411000c141c541ca046e8031a0303802100048942c0103010821940381d4110408140c01c42c0341c12401008200c0e000090020b00c0103003c80d4080949903c44210102c400107814954004451504c9107090f00400e4100d000f0180148281002c1900c640d029050308502079070002d00a0903603a1801c0200182255902c1e030058210382d00000000c0020215100e09000e45003002d40024420000d480c002d0020112078046c41c100035100c032400b030110f0340040754442501e0f01494901c000e6912810301c4ac0107441040d0580c0102e401c0c410001800341c00c0854013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 142231330 1250 142230080 142230083
    0x7082211040905030c060c07021002010608030306221e0c05031003020904140f0601060305011202090117031b0706080705040f06120209100908100c02030d0504110a090203010906051c06090203011805030403 90
    0x1034041003940c170ad41c03c900b01c03403090284029952081010a03c2c501d40410301040e128441060f80c0700d0b00c0d1003203280805940d005501c0030110a66224154181305050085140c0c000440ca811420351400b880a41d546140a2001038007520002010030140840c254034425045441d00c1282d4007542840b0801c0e80e038070424890303040080e141600102c0c501c2e01050020117440e40043c1917020726420040802c0c07000d226102d501d0054401080f07100c43c0d1407070903241d0228002c0c1c3c10000d01002c034074280018140c103000504000c20403104110602015a0920300e80c8296003180ca0301c81c54084440200e403000744580c491055104006110384000141c2c030403812000d07240004103032040303007407000c0c0c0c45404d480104613007001580041c4500b038060100b0b5032110390300c24000c2420545841084020812400098110041c0140c00000502c04c00e00310340510001440141c42d151840c0e010040490768050540b00c2c0244516154088070081d0766007508616401c1003484510b001400203440e0280c0c0d203600c40d100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 142232580 1250 142231330 142231339
    0x905060f0f070b012907150b1003050103060f06080330010e0a0e0d020d180b120a0b0a23011806090612020403020f060a0c05010507082211040905030c060c0702 70
    0x9120700f1030810441c040c481183c0413411b05042e179803000a00304402d105c0b1041c00d951502960380c580d5030a1900101c0c000c442d00e00240c0c1e541541409020b58044000805089040030410840c05c0000002c50704081e000b100c082d18045182648ca40c14070841140150160070000300202c0c03050100e20029015460825040040b00454040251200c640101c1c00300940c001042c0803200c14040c080d10b103000c1d54012021a40b041e1900c0c0842110740040c25881900d031400010442d20010a11444544000480301c4c8042c151401d0a0345640c440600c0c2442c040c44400d6210a506900400101180034050511120300c1c0391a0702008022849501c41c00c400a01e0210403071030440200c0c800c51b004e603500030f824208124600018010355038014880b4800300b1040e80d0b210300101d0320070320030580540901c4d910160b031810644050004420f0180228000700104009100001c49602c2d03210800b10b0b060300c0202700400075041c0981036020302e000c2c4941601501c03003005841c054120091440c0c81c070858 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 142233830 1250 142232580 142232609
    0x90204090515061c02120a090311030403020a0b1c0c030203071206030b010303030903140d050711030a021b03030c010e1e0d09030f020402090d03020601240905060f0f070b01 76
    0x80803042603141c1102030302d80001d03041240e03150540c0000d40b9200030001489015140c0100760646c10710901044800401150380c800c1d002003016481231904400c185804015400c20b801c41d0006040ca1501d846041003017130002a05041c00002400325000c4240138042c01c0000080c072980c098040e41c4210344440024026008802e0740710314031f00c16001644d41010344122241e08654044d4020301d400c110a905001801a0a03148030250400806c0e01d100e03500000700e00c6003021140034041d1895050a40f0140c1c005001401c4002d500290100d01910079400d03d682d14035108011900b14401e030005410503508018042c2041440020909000b15030b00b2110784001c041c62140030b464001052400000507510070f000c201240a00c081980d200b030009200500d0410843d0000d240000c00c0d1004601580198004110000c00d118040461100016405182c880c0740d550040c2148904c2c0a0b840c03140c070b00800c0c01925204400250b40c0c612800c03c044580e08c280600b0300080b061401d100c0e541f4085441c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 142235080 1250 142233830 142233841
    0xe07080c09040c05121b012c04060f080c150306030307060c0509030312010f060e0a140103020426010b060c07030f1a090a050f0d080703091a01060e1c0c05010c06060b040902040905 79
    0x141000c548c2c2a41140c2c064582d0140d420340c218040000000c05a4070549505004c03d021846881500c01010044000c101c2c6030f1000e42800340a8120400c03040b8201400e200700300c4992030100486000542c00a00000c81c2e5911000642c2c40780200862540c15200120359a115110801c802606817840700015500b450b40d500c0c0300b114440d80703514040f40c1084651400300720070900d030a010100c54905050240c1072a8442c006840c00041034680191960210304030011190000e00c183c100109e4207464491810104600e05960703100300b448020206142c40f030185c01445001c0c240b05816188400482d895410080d5460750b8030345680c24103440c00e0103038180014600718000f41c80000354812b526801202c1d943c0e0502031b8024400c0a400769004c1c10303500880088440c90041580c064081e580f82c01d64840c1201c0d0034040780d950070002d0345000f80e003040014004500b0103c6000c048410034a046a14070596161500162000e07900c80001e40c1d00104004c1952406500034005440c0310030801c01c41e640e101c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 142236330 1250 142235080 142235087
    0x4110a050c010b1c0318031e0210090f0b09030a080403032102031504110c01090b07030f230717010e0703050c090904110109030206160203010e07080c09040c05121b01 73
    0x580c0c1060313098448010420300000c0c09552188500c40080c214241c65680c0c03a00c0b070803c0d42c4400400f84c4443c41e05a2a0642180f4007866442501740d828501848014280b01800303006e440140a4905903440c04111540caa9404201ca00c00307807948001e00a448554900c2c6c0a03218480c0c00400035034000c400c1554a88491039482500d2055284900c1c1c071142e100aa400d21009003449454250511410020030984031024000c44820f00c1c41060210a5468500750003000c894030020900711a038149241d05070080d0b0740d05600308a0100300f220503185503c3c0c42c40252036280e04003036401c45041101c000061140506911107203e8940703500c0a002a699440000d403051150b10507a0b5032201c0c80e80045004a1251801030303200e0441814142e01c096100d4001131629000304400c0290b9040c2c1024034002c5040c00c0c0101104032007850001c1c1099424000c2d0203031508003071138406000d1059440040d0038445909011401404040d01701c0c1013140c0402c034810b440d015820f00700010454038000c1c80d40503511 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 142237580 1250 142236330 142236349
    0x6070c0503010b060f22080105070f0e0a230103021b0303070810060219050f010e0304050f0301050c0d051f06050a030507080709030303022a0a060e0601030206090f04110a050c010b 79
    0x45c0310000c61a19280d4001900c1c01c0904031040c40c0240001e17400070030011030911a0500440700c0781ca9000410108240040421b0b10380c0104a010742480041041010b1040d0341c44501512480040000c085c0c540004a0003402107500505103031071440040c00690201000450180c1c4059480b58815600c800078800c041005209040051f4000c035001502016010104400b1034454401d50368298000341c051030a40d038000802c8569a04001010081b074600240170010540d8154028401d40c41c0001008240c2e000c2c0c0c0c52280090740e140c20010388200040004006155810f2074586002511568003c1c1690045c0030a07001003468503010a00c110702884d0311038070a60b01c2e59115050780d42955070880180d000400c4448044c26065406c2992200703941c2003110443c400d90040c40d002c0e41d1400c1060581ea451a844801500400c0042c005a1a98412510180c0c020b4680d0002c13920b040000c03038010100110041a2000003185c038140003130b4400020003601e180800207000c1d851010b0200701c6030301c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 142238830 1250 142237580 142237597
    0x10c0918050a090c14030c040e0d050a0207180b01110f0304120f020918060c0406050307030b120a03030209210c040b0a03050a0804030b07080603070314070506070c0503010b06 77
    0x14401400c029200403035401540d0701c28400e4030301180300000c0d81d552040310400c80d00b0900d4050b50a1700e0061181c01c00304170700305110b030b012035084c854003801c02082500c44489280d00e01c00c12000045a00005008002d2240141f003283c201ca4081d400a030307810402400407145080c00140010f044072580c40001405a00400d960406180341c00e15160386444001c000203c2150400400700c07020025985103408036101e11402202d4109801d04015900d0a103100240680001039042c08248511540007003030340d90003000c60600040701440310000a88100074051000f1151040542903010140d040d000742181c50820f0b40c040c2d6068062650b008170f5005241001851507200c3c40c5c4c408000d06d02904042d01c3c104c0042c2031400e0741902ea84626050003111001650702183c001410400c014140381403d1307206045240c2821a41003c0d000244c0b1281c2511000d8200e42108034204e80845060201c800103200062100b42e66001518181144861601c500c620951030810b4411503030400310308a4443d072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 142240080 1250 142238830 142238849
    0x705040e090a200f1302030a0b01110d0503190509011b0f050304150204050307060216060c03020a0609110607030909060801060b040b0703020a020409140105280f0e010c0f02010c09 79
    0x148080c20a008400d024504969440a202e40741341d0f9803511001e01c0494415200d84002d03a03246030048000058458411106040000940d01040080380201d90340043c04424a001f55482e00c4006034680d80304111013032060307190710700424000d05040c15400b580d080c6500380255105004c400c1c03c1a100038400d5400040890f00400014002562660000c00048201900141059103d07000300f881c00d0041d800c5240560b01c00d10305444080249802900200003510703201e89500515600203441d21138916005004589601e2a0303010055560421070110700058003040d200c0e103681c20005d200c100701d80704288140c0e00d001d4020802445c180101c0003a140b03000c004900e13203454001d00081b15070003c001a01103025a544190050b542ca0041414250007469030960118013044100d086400c060404400b21000c049101501d01140d401a8101425281e00180e5810500d2401c409061030030f40780c01055282c903020070300c5542c021000f03650010301503000f0811091110410303980905140070b0203012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 142241330 1250 142240080 142240103
    0x80105010f0e10030503070f030908010b010f031505090c0909100f05010f03021c05160e030c0607030c02030a0803071d130902010c020a15020120090409020d0b0705040e090a 76
    0x2980707100c41c040b80c0c014030841c2504402d10f40c0c1e034840c1421030700000c81c101d07814501d00064006040d03004403c0c8026091080003084030340346000c0040c00000d55014128245512101585001d034002c0c0482c0c0b0051401510524151400180c280f0131a44003422091188240801080e09544080c8444081d01d1840038403a000e2402e110040d605404c0c440e82c4034041540030846142c02680020707640d0004283c01c0707004035090070300709508103144480c4c503120000c100325000115901e60740080e480ae4010001d45206544441c503060849661021520194042c03003451104c41c100480700c00210303ca010700c2d6607203500b50310150000480c0031301d002e000c00b60301200002d8000340d2000d4942c005d40496105040c017010040d11507010500d0b03204142c0c0000040702002c000d04545907028000c3c54101540010301251003100010859500d0140c0700f000c50282e43d45110030000c644401d5035000a0030b0b04804000d81d90f02e04200b004000f41e10900075140c1d0900c1003804107007020b000040c5c07481070591040101c0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 142242580 1250 142241330 142241339
    0xc030203040c0b16080406030b040e1c051c060e06181302100e091f05011b08090604051f090b07050604120905061305100c05100504081b0d0801080105010f 68
    0xc0c0e40260030b0181c200b07041ca00c84140056170f814002c0004019645001c95003058900c1000111100b211505000f80c0100ea4401c5902c034041607008244185400c09984504074801c005a03589501e080e21025540f0f00023010035460b982920b1503105c0c503012100320340e0004541241141002e41503030710f502d40c9070103120904018580240341000014040ca0507039131092040d0005044017009991200180000c02101c05400014603128000f0305006c0c20043c00e4281c040c2050200c105c0444000b520b101808a40784041c0e540d41000c58000b000e0081c0259220001489001d80e0384040c954660040b5000001c0080c40f4500141541c84064000010300860b41e1140c651020121020091400b041140030020400e556050007a061a0006201524056043c081800100d540c102051414002c018080e030001801c0001d0017140640b580c40082030588a9241001d554000d102c0d02040103110303000c44028021000504030038a104aa403a40e06607643c45002c1070072100c007801074030700300d0844441c28030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 142243830 1250 142242580 142242599
    0x4020a0f1203081f032108092e020a050d0501060219030810080708030a020c120a030f030f050c120a0506010933020606090a0b03060f04021f020d02010c030203040c 72
    0x180d110f210100c07020a41d030130b0b0000c40c880f06034042d0011280c100030407802012030120140640046121803c000285003040b8540700d584c2c4204d940001800b00e000c1040340b010381d14166406501c00d603074220654407040d10003000390a58211030700300f08895262100000c2d9441c80042c0e490075200d089121150b2445594500710703652003000f8481c2040c65a800c1c0002000b141c1008100000c20185003d95164003a40c41c009040904c68812144100c2c40180d00d151440c902045046907140d1509100c0c40c00141c010081e4064901641c2e050300341442e01040000c00700859009080c8214000c103103c403903503503160f0706004a034029150540000d000790b80074081c0c1004540b811001a03500006500141c501e074001000c030f80c03010200d010040c0c00c10f000b80034260a01c1904190001c01c07440c0140700c00c184040111b070307a0700c0c4002e0240d4a4000403d01240039922880043c0c030070b061440011002216038080c0280d6104044411880158604200401e08500c648240d90149510003044d10f209450802e000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 142245080 1250 142243830 142243847
    0x150f0f03060f030a0602180a1d1e0406060f0501020a03170a200904060608011224021801020d09030213020306060f0403060e10021206120309060403030804020a0f1203 73
    0x2900b00c030a0480360005a9000c2114000b200c0c030410015948621500c400c0145048001800c0c0c001c18404500f8030a8507154600d00000320a44000f8281c607070355a080c82840c69005202d41c0200c10803610134031047c0009500180162044415020030340750382c804c0126914080b03c1c80c040c0009800800d0802009407650036140c011084032004142150600c858541101c14241c000c2c00400000030000b0180c200390054800070711440c1042401e80d07240000101680490b90f1004003034400d462404401e0040710040d9000d0402c06400441d10360452001e450240d500c41c250700c502500c9108008050244989d0700032055960203445181420f0740806580c01039003000d00055408241400303072840605c40b850103000190b006801c04180000b040540c1fa0074205007816005581d4010021051010792820283e50411419981d034403400c4080e410300c80c1107004101c4420b900a4001400105141d40122818003d03030085628148403503403045a24141c010070701c204405c4410050b08100824040d10b0f16 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 142246330 1250 142245080 142245091
    0x622030b07021c1d030f0714030609030a080406091a0a050405010b04020c0721020d08070303050a020a0e010c03022a09130201080c07080c060a0504051b1f120c02060105150f0f03 78
    0x12503d446c820400d03c40d00740001a049114641c0700c40200d00c1d01403904110b150f41008510300554903050401c08020600c5100600281071241c03504060000c1101d41c0240030444040705c0c003481c00a080500c00c1402400003a01e041e0348541c2880030740c4215180074401c07608100480320041001c00d141024007580050901d000324903c065850360701c0090b8980100140a00d441900041d0342e94900b480c001e0304485024000251040c130500400d103646400c40c020445e960001d0900d07407100025441c0881c5802c04c480c00d40c500b11202001c03100710f66403031600c200b031200000b15482c0d80d8941c3c9100ea100e034030500c002c8001e4001010600424a000e66200060040e20301070a6502d140100d5503c00360714041e0140c805114042e640d004120901005101c2c440003440500c800148070001e110014211408a86011400d951000354515900d405403414042083c0380300c17014081d00207c03000c0a51a44c00074864503002d0017403502c20090700041441110059542e0031186818820044014035150700020035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 142247580 1250 142246330 142246333
    0x2010b03010c320f0403050706050a0e04050903090312181503010308161a10060c052d06040f0b06030a0503030a050c04080a060f060b04050306060622030b07021c1d03 73
    0x43c01d40c82c098030030000c0c000c0320762031901300b603035240341d8030f8a14a48009548a5010024248a21003c00b0f5011410a0603d00100d8005c100e546400310032604521a0814055142c07203207e1480b120519400007600303244100e01c1c00901920201c0c4240315401d040d0280002c2c0c0803408000600004203072501508013009400144010710305c43c0e607030301c00bc072130910a40399241424203010000c00c8039128203200007401d840d2904c12000d12141d5501d9070347c0c80f512600c022510200d16540c14507118406074400309140d00b40c00301c0d96a401c190801300c000354580c1d10290b451000f01c1c00051600c1c01c000540d10403555000d00103501e075560340d0300400010300b0003138041516000700300700006103500d041290040447c020340b000103101d040c0c40715a0303046417030a80c00082200020b000800043e81c0115801d030b8084003d80305140d5404462441e1900140b000c514110300c0800540c0201c280036521001c144540c40c65000c5815218041c41c5142c801410242c25078002064413030980403070301860400300d070362400180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 142248830 1250 142247580 142247657
    0xa0306090b03032a1e030d15050609040c020c0a18060504020f0304111503010602010c09050f030a06050c04050607030906020d09140d06110a051e0a0c02090c07020d0f0302010b03010c 80
    0x1640e001000c0000c0c1781422443d4800b02e075688403501e65103e03408400440f100501503d6280002180840c0079484c1003610841d910203119000c18000e124203046894001d08415a6076140e0280d03811146500161040c15464a1404515410280b086030306250f4040d0001c0d01f15541d81d0b4030104c11420101d4580d401c00268440b0302118103a0302c025502030134260300007107007540307024130000e0468086520082c414000115a5a180e031808074039140705540100c000318682e50341d4240344007184610350100750010350000b0084c0900d607205100e1003d0316043e9082c1c0701c04010b8004d00325101c03401c50044210411075207070505601c1c603040c080b50100c244200c101082d0002c2041d2564129000340c2d44020200d240012021102e8045100e00d0b400354020280803801c0c55401d81c0b00030000064060003d00500c3c0480206039440b035020141c9a0aa5008003800c0c11203c0030714105401640c0c8490440240d03080805481540c5418050021090f039140d8500489007128001410090108500c0d103052104a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 142250080 1250 142248830 142248853
    0x30305030c1b030a030c03050708060a0b0a0903050d03090221070b090d05010f06080d020f0c01050f0c070b0a0305060f0d11010512010b070b0f090a02040f110a0306090b03032a 77
    0x74000b420301c003130054a0015001d00811000760030764000401c06001c12420108102840e625680c2401c19a80720040791611745c00036100c1610707061500e0300041c000f0302c111244070700156816003000c20711910039102503144100c00c40624010b00181502c06001d908504000c1c0950111600601a6404000c0c03103540510b41d50703183c03035003100c6116184458590301c0380700c10711084104200100b0202c110b8070052804401c407510098440b000400024100000003484003075483c1004145c5001603101c3c400c0d1100705031341d241040c3d8141d020092220200341004002080f515000b01c0300c08240320050034040c100d4102c1c1d900d0709c45c400805e0f030301d8a0500906108842c01030020382041400780c10541807003941c3c0d07051070520801d191402041481110016410420306402c003184040700030764181d4000c584001100104400b81501640006d080400801d0010101b41c1c0340c0c000c401203e00c038034000c000d12a03011043c1502c9100c1c1c051042d892580340c030301d000d02e610354500c103980c4038040400c00e031191100301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 142251330 1250 142250080 142250083
    0x100b040216140f030a0504090b01020703050d0e0a12050c0f01120e0c040f060302030a0f0204020f0c030901141905031f030f0b130c030807031e0c0c0906030305030c1b 73
    0x2030800c01c2d034010a42e81540800a44100300c800030280c250402542003000e21100203081d4800c034011300640c10b0302d42c1a42081039000300803460103140c2c40702c191005500c9088000701084842d0700e4051143c6d0215600060000c04112041c8040741c114001e4101c9049000520044080c4c40b01c0035070400c644058100e2001c482e038450403980c0c50002c40600a1074441c02c0800060300d5500c10040c840d80c1c81d010b401c1006070b400103048580140d020000c0082d82e4500c0c00010003e0007400102459030a0009540b440404003200404011100740c82e03400940403402c00d0b4013203a000360040c414401e14000d42d00070b440303400b0f640a10362258000200c0a012065601c0d2260341d409181d204441c03444169041c0c00801080f0b0a60715485a030032840c481e668001d94079071060b284800d10002d00624030008040c41403603c41e82640c01483d072000000100d24034600c1c0d00411071003080e041030700c070502c10b104040707040d0707845000f01400c89070140c0d501810748d1035a10440110340c4c070401c116111543c1d02c2d80a4004100e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 142252580 1250 142251330 142251367
    0x50a090204081b031906020c010f05160c080904090f060c03151505040b0c030c07030c080f01020c0c041d071202090601030203070c0b0a0b09130302010e030408100b0402 74
    0x1511601588030391404071440e10b00300e41c5400801c846941e075826462244c90000e04810074400a000410200b01c1a05060000317219141a411055091420345001900586c00a0303000c1c80c00764605000d40c82583d01e040320040080d500091202c8400c22140659160581100e103d1500501c0c50844c1b088603030303403402e0844030306c0c00b070784000310b030326402205072880d01c0020200060482800e00f144801a02000901030b00c12030180c82561000800e180e07411800400c26140080300031011139039a29101d0502505440c801d100f461102d01c40c484520008144c10b0080d5150400100020b01681251800300b0011b488060303e1410b0b041031286403d14014410881c0310000c002c100011600c0900b24010b203c04c072100284850705040c01001402441a0710000c1d041c2029000203504181d9101c6c0c4a9003400b814010b504d095203d10305009001241800c4a12445e100c3e00c2500200a0a070f50075106a807030380103034403035004244c02c1541969400c42c0c681e0040e020380c02c00100300607e440d6401083e40b14070301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 142253830 1250 142252580 142252589
    0xc010509060705040602030d0908090409050f120408071403012003100b030408160c08030d0e0f0d050406050c0328020606010306051c0f05011112150603160207050a 72
    0x29111000c0c4108640180301203034020000b4070b45140380c58180385020355680325240c1814441c0d6138981d180410307c00c5d2101541c1c11504018402c1c40480700c4c1d0b040c242e95925072003400d400207009400c00c0240203061b40c42100e08a984003405811418070b40341004a112401407200e503015500c400380c000202c81d140d03500039071600c03034004070944a04160350340c6070303032890385802070140d419080050001248080090301c45a1440f0458010002c506140444001c0d280d81d000060a00c000f144081c8e03020683d42080303140b44404000c485014240e6900961780343c1005482c1c0c80810f0302000300f0301c1528171600091003c0c0b20050100da1409400280303106940407224445074001c41d1540c3c0d583c808079418080c06810010910b004d02c081c0e401d100004140d00c06141c0100d1201e03040c0d2029000700310052100e004070b0382d01304000300b0110840001d1150303244c1c00315a000c220801600b002420001e25005c081c0c100c0003001d809141141d44540b040c1595100c200c89003002c1d032007005400a86541c8181190002c1e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 142255080 1250 142253830 142253833
    0x2060721020a0c05100806040b040f020307021e030909060d0302070f0b030106030c0f090b0c0c0915150406020a080c0a0f1401110412082101090504110d0b010e19020c 73
    0x7225541410b044070000703504010321a24416030b5810a146e4088000c2c1d0b004081103070009a00002400003030000d110000030681200d001004112200e500844d8807500c40207612100e038140f407426141192640300c0e1a0055521040134008a800780c1000400710505034400c4c0100c48d08240c64001c0c1c542950110350101c07030000f038004014072041d5814091a00c010401d424003130700000d6801805404450309000302c010401001c030f5035600a040411028610080c094040c00084c245a203811650749403841400707006440211005c0300d0701125004980417241c690340070f41a100103503a107408880e40005e62080e610304c2903030944004a2418194652410300c54003401c0440030035009441c0c252000007121000401c4188000c0280060202c1e500d510300d640003030110380c3d8884151032203111034100d8001d900d0a8003001e00200d1a48031551000d030041d801b44078251550b4800c20204003c0317201e104001001c40040d10010809007600f440196005518030a0500342d2031a444822400c0341c20003101103845 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 142256330 1250 142255080 142255093
    0x3010909020f010e0d1203060905090a0515010320270a05010501020123090f0f0a05060a060b0706090326040b06030609150c0d0c0302130608090a0206072102 69
    0x8520700b50090018103007003030a20790f007001d02c2840007498043c0d41841c003401c0840002d5800101c940301398030100c00307041c0c10300d004c0029040c80727100a90b54885110b001c41e000e200b00e40440465a0050525504036503010240a00e000e0342c002d40088002c140c20b036242d80049200c80040c0b01101207404022070b8400c1091900030070710740801c02d0001d0700c0043c0e000c02d065924110400e40304100090501d80c504941580c850f07999110100e0040c6400e602c8000171402d806410700d540345007040880d241104500a60480701b042d20303803290040803249180321701e202901c0f00f0030103203000845c15048044940e00030b04058a030040c0088401420015004480840780100b03820002002a42c2459581220058000340828a003840c0301d1980e603402001d40504200e10704e00080d21072120b0000312a02285207100030700c400412240080c0203034021183c7c082c1001514640421403611488000d40b08840100c000d0210080c95002e118096122040030340d5200c8004c0d901c03000c000745888408201d0070296004092 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 142257580 1250 142256330 142256333
    0x3022a010b0118061d06040504050915010b04210201123e0901081308190f0c050c130908030c0406110109050709050702031603020309030d020102071505041703010909 73
    0x10807084454001d0403014200f4007480400d0348000e50021901c20b0400610142442d240041e0305405280d0005501500705802c001c1d000801203112850303c2060103280e6110b0b41c03140a03030b03001030049000346e090385804011201004105581c1b60042c42d4010f0500d6454881a58444010380c0c1c0d010180105172051a4045041c03030b082c40302450503010700b10300d41815017500a100780415200d0b08800a04210000c0040b505480150340e4032142a54044081c0381c0d5000548802e2141409405004010400301a881003100703003e440b890701e070a44c4c4000038241c020728240070809012500c00c1c0072a045035035865101e000078015001140190740c243d503603075111840c1131b4004140c1c5100b1022900707164141841032001450004135803046e500d200303c0214440c4d035050001ca00d140240c032896000340600c03a881c0320501d0340200c0104401202502034900d100c1802406a082c1d101d1440020160b0400449500c0ea01c001d5901041d0000c2c860009004d81c540401541006c5030001c0c1c218000f581c1c4ea9161000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 142258830 1250 142257580 142257587
    0x31e02070b1b1e04140126060a0f06030507030608060405070605180301021303020307080307030804080912030a030f0e07080a06022505010e0624150d060303030501050a08160603022a010b01 83
    0x140c5c90303d00f40f903d40e640810850400c00300d140142581118811404040343d8030b0740d1401c0321400540b115004240d04a540d41e600140a01403d880d41000b1914011010071008408210b00340306d607400900509299150000407500e5034403038055000002410131010b02140d80c00e0000301107102d4504c01422809040d40101030130311400ba031007008590b0042041e80006078221340416131103500148983d03220403110001c24245a1000804d150902002510980c1140c040d480011b10208910041050440c02846595243c07034600440304190303c00444e000000d525500100800702c490390110820540300f540065100b82110000c031fa013a51501850280c8000030000c0581c4481c40980403000c0c280c2c05941820218100c0641c1401400c51089100b0785020500c226000c0180e00c420820090b940c0e07040c007c008107400c0c05403900c02c451424001829203400902c840c0420100000880003a04e4180c0c240e00a5100241c41d5a504031402c103010b9036000c1803403140d5142188640041051a240390006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 142260080 1250 142258830 142258859
    0x90503031006230f09060d0f0608010e2805150901050603060103020f0409020307030219060e0d0b010e190204141002011116020103060b0a031e02070b1b1e04 69
    0x200304000c40d848203c64140e045241da5009021103070402c2d079680138981e00d00b81c8144100d200700c03a080003001901c1324040c500c5a025109821040b00200000c54446144138240d034072890243c4400d40c003460401100e9031340c02015030207807115402c0b00040f8008170395410b0f0078131070040702840440b2400c4042008c030032000e010346507000d001140507200660541d40003c40c4d07406d07440c240c6402103564107502821501c0400220000d5600240440c842c3c0009408c02600f2445034002d19000402c00c0030084000d04003081d20100080d44000303c080c2d00d80c00c201410103081e9000b0315a004044141d86c66007001c02c1c6a100500161220140701c44c4080c140c44180000890541800c4045a1400551004160400003a16410900610081c46559003400100c01410507a00041182180051000c0d0501d03019880071016081c0042040001708010702900124052104090420503000002810603072080c00c0030032009401c1130710103040450b07802c0f000c8507500d001008807128420014044c402d14840c520744 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 142261330 1250 142260080 142260089
    0xb0319020105030a051f23030601140d020a09051e011403061605070510020a03060b0f03070f1b0b0f180c0423070503010603061202030613030306090905030310 70
    0x8021015600080c500d1000a000c002915611404a0104800c001c4010182820f8140c0042c10544561105c668065201084c4482d0300c0440d1945c0454100424620304907800108640100d0345604103200001c902000b040307900400d15200840c07040040e106450064002c003c01001088100d000042c1000042c2c006200c020b03440c4005550540c2c00007016903022408400720001e00781011401e42e81070042401c01030440c0588100303000c9140c207a034064440c20b0301c1540c01b072044694881004901d803203a194400d4042d4010000600400d01034a0b041d1041001854044540f00302d1502c4100f5036800703075504403040c04080041c06070504441c1c80381c47e0040ca0311001942c05940940086030398000c0300d003483d1f01a03034031500007807410a414040d22404000502110680303240503500105643d00902070040400c2c035164002c11841100c2440c85070465001d4000c10311038940443e42c1d54840701c032010403000c040d11800c0200721418940038005100380700c0c100654a0381040c91011300c0d84540c6410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 142262580 1250 142261330 142261363
    0x606030219030f150b0d0f0902060d0504050c06070605071d030d0e27010906082e1e02040303080c0a02060f07051324020c0604051203040906030302010b03 68
    0x40c0540016980002032450322075081c0003ca8110034507000c0d010300749140201000803021800012210707103940080034004210300d01040b900c010000010b044844806000c0d402220510601d403030301c09240c6c000d94006016808450402031100d0010b685a4403076942120400e032960148a4200d4100c846035085800c0602c01640c0b000008000c65a40c01c00814401c0c20050700606961454a513044101d000d281031102d4603403450002042140500420700c200a10345141140010b0030a4003c10b0701d00031200c031700064404c2030103c03949828000041005040038240d4442c003130f9010700c03a8081c0303c00704035150080160302c40d8594100a070a10000a18080b00aa001c012032024590301044181d441407004c7e5070b0901c1038441c29000c85103401030904640349a201c048010840d14181220306c048003e116991884100c84030307034100d8a884210b4070458206009101c00d11040c075050340d04401c05010881100d00340f80c0d59242903403e58640350300030382c00341c3d41d541040400d50070300380141414000e0520 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 142263830 1250 142262580 142262587
    0x140105010e040f0212130b0c0a02060f09010e2a0a030b180a0b07031b110c01030506030c0603040c03030e190b0d090f030215090106080613060e0a031206060302 70
    0x180080c00c1550400400d5205607512200c105000c402c59041e02c0020802e07107124840f525103001000d011403034075002544c0f18281c040009541c0c40c6000300b01c8244c00115405000543c58400220f115900d000d000e00c0220b5403141a20406428104184100a2032110910000c1140e650100c100350042035000d40c060300040b0360a2011426140d01140c019080480c03800700f503401c890059041c035808180003050000700105021a0980c10f0b00200200c480b050b005206211200f102078031000d001010000710390f00080c014024541c080c5e406075070b0000b00074050387d42d50011000003801c20307031080f0340071611044c130310130103000345035012414019044040d03c803094024403950080710444035500ca4000e00c03d2001450300002c0900c0e4004a032200e0344401e80d20701c18006451b0107500c40d6040c603c000d11032105000004c400800500075101100e00c000058403c81c2c40d84d001a01e81c040240781c09031340c0301e80c07282a8103c80e400104840080c85029942d52000d1007107412015080d580184d006008260050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 142265080 1250 142263830 142263839
    0x1201060e070e010c1103012703030b060703020606040506030f030708130609050604031b030206120415180f08040b031f06140a052b020d0e0111030103081b0613061401 73
    0x400c1c926464120f0054481c101260380020301402c0344648d003400c580d4911050941c1d4900f03222422611511030344041c8000c004101c140400740c011404042c0041e8071001c003080d081d040c2a48081e81004000e41540e0402d909401424999804500110344000001079443d07450101007026401400c810324115542d540390200192050049001c017a001c0b00c0032144c50003074061b030b0090b5000259405007245442d01c1c070b000320904241a0480f0140c41d072070518036810300b0b145898410741e60286040c0b02e017100c164243e511a1041031020100450b8100020000402c5003400d031000b5510070086044020352540b0f4100390090441280e50158041c00760040e4480e055120340e0040e191181c10528180c2d48412242d508142d2188001e04800f0100843c0c01100c0c0d00038606030000c11b0050500d02040c85403140c0d01c0d00207401c031848420100c65404040c0014000916404001c20507448880071000d82103030044800c1e820260b060300c20b00e056883c514110004c10085028603512610543c41c000c4071585030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 142266187 1107 142265080 142265087
    0x71205011a060406030b01030b04060e04021002010c17071709061008060603060601030b010c05120307110c1f02030403351e03040c051201060e070e01 66
    0x914081e506189054144000000380c060b0042c0e00d41841c01c0e034101e0041c5000d008007410580caa0300115a180d880307000f204003519101c44811054100352040041184401c5010400d40e41403010409403e42c100c59056000200a8200b00403541e52001c02c031286040c504500076028030a41c00d10080a81c00a90340c0c1c4242c0142585000d2140c0300c44806d07030f031001e00305d41440d4158001d00004031194820b81000d0180c0b0fa0604150039001000c1d40e44a08200007104420a211b0009c070400c100740351f000808843c0750f4015006441010a048041251204406030880c0c9482129100300b41c03440c404c008503001190411141002e0b02802d206a03c0d0404440011f2280301c0c2d00c0302c0b4000184c601d10011205085818652082141e0300c1c00488485034200920685040d05207180002c0c1c15190f58000d005070035204400010000d003002d000b89050540034010700304001e410000b8500a980 = true := by decide +kernel

theorem cover : BRFrame.Cov 142086330 142266187 := by
  have h0 := BRFrame.cov_init 142086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 142086330 ≤ n) (h2 : n < 142266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
