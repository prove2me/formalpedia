-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4297
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:09:48.11779+00:00
-- url     : https://prove2.me/submissions/539017fa-1e4d-4c21-a256-4299c2ba4a39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 772661870 ≤ n < 772841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 772663120 1250 772661870 772661899
    0x6070c0305130b1b0c06251a011503051e01090e03130b030709060c44031e0603120310150903110d050c0f0a08100e070806072c 56
    0xd2002c40c0070740b00c010481e05c40e07500507410f01c0303000d01170411641b894400e40468000202c0c40c818940c10801e116a5601c0070035140d040c3c07180c06ca00000c0c1c00ca0404500c104044600040d0140b081603080403014007885924040c52601c600c654805000c1c1e6145140c8a14550300484400c005869040e0540c4450318600340c0c6510860465400c100c03468800240200400a40c80c1e000b906d111685a42041a04076581800000d410684418030f840500c110a41c00d01401248500440e440745134000258140d030300e041401c682205242412552030030720a107541409250307900010b01c100c20a0f08800d6403516907a800385020704082c030b07917800791b03801c2c01d050350000520680c84401c82098920400d55200d10101201c1800316044858400415030740c0329080e40746452602c855040c09542c1c0007060004011f40f10128107090404165001103010b440b050642407400042c06480003a100c1c6c0c9008180601d0f0100c80201150b800c21004218030302c80c0f0810640d0488a03640300310300e032180075004441d4410078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 772664370 1250 772663120 772663147
    0x150f031303080601111213030615031523070302090a12020a350c03030d0506040e06040812270609010e0303070207050418020d0b0907050306070c0305130b 68
    0x4990490000b0080c034006106980aa4092109030203820010049101800c0f45c1d4480ca901c0050036881600c218000000020b181c2d00426550600f15410041350901d1481c2004001040350501c01440341001c0d140c40c0305483e007448642c0121000c60002e8910b0711030003000c2d8003c0c0304209045400c0301000c0800b02e0900d011030301010340988280c2d0651003060366042102c0001c1030020041c0c002400c04088050084c1400038000c00041048040d00d074440303001000285507600c40090801141e803914108000f620701845a070303440500800140c520392600da034800019206980b0404044107003280410f0180c8031013020300304800681d4400000d034144050040e6907a2608a8000e0019820540f6031003150201005980c0100007079001041e407541000304100c0549590140000e00c00d07480401e40c009070791103000455109000d581c0c82041421300040e540d042402e10b81050740030b03600450900c20700c0b03a4042454000c068062805a8030303011046040b600d0340c00707103a04c0422100e201058010340c2601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 772665620 1250 772664370 772664401
    0x80702180108060c0a0905010c02190612060902130b070606050319050c0102010e07061209060501170f06040812191a04060801050c04051011060a060303030b030c0a0302150f03 77
    0x288402c5501d65507844e1001c810a110b038106050009000d00401c001550080044120703252008101e02008a4609542492030360035a2001d07002130342c240010414050144102e134040c0200141c00e600e04a2502c003222000c800a105030034461600140b22801c6c80080c4d4004005441c1c020300383c451229410034000e862030301840c002c0c0c0c1c51f8050140400c20340d41c01481404e400b0041c09002d040590314000c0c09484400b4114825141962034017101c43c00200d4a1090747d018181c99103010034107808a003400e03898900010341207903d5512003c140004120a8400d032030500c08c803460308a405603124145000350510390030103003442c103041c442903400c41d1a00940c1551007000c240d80400099984152250a071178040c0c5004c0001101008103010600340005289104840c9040c18901c00d101030041d186480300407600f4480f055601c6030280205641400f429103071141c110700515502400b800058001c45a921000780700c0c1750f0110050000e11440c42c00c1e1a02c80c07210910707054803807800144c2c0301d003200d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 772666870 1250 772665620 772665629
    0x50912120a080f24060d0204031406010501171302121f15050a0b0f04030f0f02040515010e0120030a03051504050405030304260f1306030506010507030c0807021801 72
    0x11181030008094025000d080d0f44584a1462003944c204030715401c0200310700c0110119900701d0410400003811884c0b60006100540c032030221441294807130382e107079401c0401c1a04141c1c10440c92130707a60203803c02c40240c081d400c4001c00f1134500c110f007654070011745c5c3c4000070f41c135200c5203024440000b954110050b4102d0301c02115104184010468501003c15026480c0551648002800c1c0c0070b2040d01110740c01350000350207043c00180b50549a4aa01040e2402c000e41210764441c10081101141002d0240740d81041011210003070f007040e10350000e45441e044541e45030410601107040e009803002c00d1070100c0c045180005032941e4080d080d4004025103c00c4409030030707104641030079290b142007502c40c041c031540c0c011000d98259140d550b141441049048800845014442c0b00c1d400c10748a100014001d80b0041644940c1c1c0e03d0705000b0340c7c400c116907940010145842c0130100066a60880d003140d5440b903151800901c81940743c81e00403014011604043e41050111140c0f240a9200f950124181c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 772668120 1250 772666870 772666877
    0x603060a0c090e190e030c070e19141504060f18110a030605030c0307051005030405070302060d0c27180e03040605040f0b180909010b03010911041a030607050912120a 73
    0x180001c050745d41d484c0f044030181c0d005544001d50401031200d1100301c6075005903040081c24514540000800c080d100d40081003000e0401a1091001c0181d10518414643d1070a5174280040c52030030f0380f6141c1525180c81420425140038940051312205503220340f02e13940c03c0c24046a00d401c0480c1e030003402003003280103031030080c841c4402d183d40b00e00d40024410111003000b00100101401403504903001d401c081c0085501c0d00c946035001c0010ba0719503001e0454440c0b90700c8001501c01310300c1402041200145641d00400d4622006801c503072b0800503803801500d0071124681a1a041500b0031002024019804646804045804075415070722400501c100c61210301e1075044162154123800152092401015620102045007041401c144102c0395008031003800014a0b092402d0110b400d481c15034808a4604200c03044130301d000c1c50b0601c100080701680046c104690b007502c40c0460707a6264040d0050040c01400310749421166503148446401c151003c09444500c840c040951a00d6000000310f100031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 772669370 1250 772668120 772668131
    0xd020c0a0603150b2a01020306090c130e130c0305030903010c0203040803180402070506040b0417090603130609120503010312080606090103091b0b071104050603060a0c090e19 77
    0x40340c843c1c0900e00100d011640d80000d211300c0c0040d5020181e0040207400c0c90a07001c02400380302c540c00c40064040115400c40056078a00e049410004400e5004002c40400e6409101220548980d41f00c4401034650500c02503100b0345468500074911081d03040001d00ca803040d4030010080040200c040d196281c0240c0080c80813030b40009042e030312030041d40281c41c51540203210f0101040c0c8940720000399020041d00c01132402c005070700c0c0c180c148041107400f40d6400e0310700001d22041002c00c2040308900070a000e40d0394101007200340040e1040c4806040d00390900894400ca070140900c6611041c0107a0f805400d09102e00c002d21000344c0300d030b0000d22064070401e00d0900e01200c9940507041d5140716500c000c1040f450901d006005600600382810f00b5039145075910069168003140744200c1d0085e100030740c0c1c0e0765103a0400c0e280104103d130b080003000d0700481c10706081c004103440001d01030b50000d5011402044218985d00d00301c07440c0a0a501004a400c048420712410308400303076401c4c407400c0301d00505121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 772670620 1250 772669370 772669379
    0x19020c04180b04080a0507170915090a030f0206040521010e010501030b0c22060e03280b040624050316030201120c02030c15010807140a09020306040902030d020c0a 72
    0x9816030500e001800d00c10b402c00000e00080c01d260020681e43c080c0e410028201061612004200184440c88018070000020709610511300502d24460100e0041e1507203181c0f038410b40110307108501501c00105201c038014900b004542d20361064602600d40542180c005480c036a9007c0d40d13070007480c203400385154a45483d8008000040c002c16041e03a411444120030b9407a030310340c40c10403980001440c59041100301c0c401099004410141c500030042d40d500e110010810000300360800b0021214400c0040c8641d00005840c902e50107d000c070f07183c0001088013140e035203090040281541412a164518031008031100e0045050001004d5460540844180755a03401000a44100380d02000c2c0c04210f052816500c2e60680c1d8100c5100c1100900c1664207000d40ca620750791511540c08504400c01ea0328100600041008201c10b00081a41c0c200314444442a01c000c2401c0402e44d0041030320b09600000007407050303140c9070040c40c00c680e800750481d80d2900385140001e4842118060b62441084030050004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 772671870 1250 772670620 772670651
    0xd060b12060403090510020c04060e1f0e070e12010504080301090c0806090402040203070c140304080f030f0d0504030306180e07150509040506120303070e090109090515060619020c04 80
    0x42c4140d034162150302125040070f040080300031030303004070104500c00d08246040586460040d1001003810040d0001a0304040c45d0380800c03106d001c01c00c11201c0341a444104900c0c81e0b403080c207a03041145428140388a400b0100070410961024005029640c240b60a00c000c110080000b14100c5103005001c01040065a10840e0544000c3d0303421684106030501040c05071038640d00030b41d044811405d1203540501969114412000c65800d6a08550000b007000c1101080511141140043c00d8014500d0b0014250401d1014000c445040c10220759072000201094001d5006801500b0a03142040f680c0100d20040d10150100311491840c030702a00a00091034113905202c01340311155511524108001c2409110080c40000d101c1a0702c2855455100006231003400218001c510310f644d8101c0324174494040c060030345010313440000d24609d80140d01010600100ba4400c4003001400740d614103407102000103581c1e00400b00f00c3c40000704080d50080d2126000520208414001d0710b00b400401d150b0040b04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 772673120 1250 772671870 772671883
    0xf13090903050304110a170a1104090f0609030e042d02030c04050613120b04060b060301031a10031202030a1214060108191506020c09012103020c0d060b12 68
    0x70003081050001c2070014044101c141d882a01c09080014500c0e965040c0825100040449400540100310002e0034402c48007003003a0800b400760303400e00445106503a05c1403c03512040000d86002c1d52038117500101403280c035010348a524014030601000200740c180498050701080d07541e0006c0c1e025544070108504034000c0c0da00c00d8a150b03940606151070801401680e5010040c400104003842030045914840000444200d45c001e11351100380d8030b01441d05600322002d0300400d5100e19014001000020301e00d04d01c100340781c0e101552506541c1c0707456038460000031554000a11000b07c003034a003603050b40c4c0003010380340e12071565983c80d07a501c280c030840000b10790400508a400d004044001031455004030701d042e401c60380800d11900c9403034800c10046d00302c50744905040383d04604040100509541007021640c80c042c01c4440c2d4040f54034145004a00045494841d1008012200c8a205140c001c0c80060004180641449141026403501c000280b8412002510903074514107012407005000451 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 772674370 1250 772673120 772673123
    0x1602161a071401020f090a240c030e130c120908040b0304020607060e01050103030915080a0c05040807081e070b0a050d0f0c030c08090c0a0e13080f130909 68
    0x48001000d0300e0209142540708580645402901071541482c80c1e10901c000c2a4003031026040c00d485200c5441080702d0301010764849640e81c420385210100d856000030483c0c07a159041d0070310740c2075446ca51909850203c20080b0040e03004502c404081c000800c00d0300051104401039540e55000380c20800468120756035840040e04000050100b44041e642400c011034006000030001c5007003400580d0307104c00707071a40c682e00c0e5000307a51260010170826411407045405002c440b0040307107420441c210002e102c00f100a1401000b207880301e8018041900560480c0c014065680581d08081e407100c0b240340d0750b41c1089175420040d204002c45641d004002061410036242d00743e603d6441e11400c4801220281c00140c482c00321956150f060003050707001c80c454140440c44645020400030030810019080400042070a0712503002803550700d07015a100001740040d54400038414484c1d440e104020602202202002040e0002c006059044141600c000c0c104103015030b50013410701c0b91541014401d880c28101c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 772675620 1250 772674370 772674389
    0xf27031e080406050a0e07181505010509130b130203090c010509061219020a0807030b0604050a121a1f0504020f0d1a1e0a0e090703080a0207080105160216 68
    0x401c0015032a0b4004c2c50300042c5180010803000300c2c022003d41481810b6010701d00000c0c803d07995080702c1350280140e61245080e8103808155900d0000060244d11134001814441d40b12684540804601039122140241015003000c00e11445000542c0095109a80c43d02daa0301c1360794183c0140358810403c641c11110041e2a00d8200b9041e00c0c0010340000002d03181d8102d2204d2040190030342c900c03920241c00030060543d01c0c00742d03d061414015040703518006c22180621000c0100303101644518041d1002c4420020032400c140c0510305019545400c1c80e41c0555101660000b848080070600501c4900c0d82103603113400050540d03590400049104112820340000d40c03d000c50340d0b1a01d51540000c160000348032041d03046681000c009680104007642100441d10380866035030686c00d2078440000036006027540e5021a00700590410303540c000703c0c03100805034600000d00e804001c2c070911010380101003e000a0044c0c0c14a041c03c005814ac04480b01001841880e000e00200310002c8044812900c0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 772676870 1250 772675620 772675637
    0x60302180a03120f0324031b0501051902011503141002070b01090902030a0c0e01080106080a020d021009030812070e090403081f0315060815090705040f27031e 70
    0x40d401e0f100000c4c1000042c0c10303d41d0702c1d04403030485400ca90590038084080c0c103400070b900c0c1c154540090069441100000807a41c3c240003800181d030130a003100e00702038803094141400c480d1100c04038007402500300102c0d411010710a0000c00c205043c842060810482000c0d0f5840b0115000030b10224081c0c00b0300a440e900e0910010071034480503070300100e8030728000b506844503581942c4804052400903130000c20f03641582c0b00100074002c1c0078400c0e03402600c0f0b0035019008136800340e000208074040d03002002c0d100321406042c184626015000c010000c50f48102e04c59100c0c5a032098018010a088810101050050807402400e2400c01c2d0850b00c99503041e150501c0c00e031200c260341c800240c0d14504c1001400d45621000c000300d4a00c0d20b6441070201803400200c0d400e07081041e018208074180e0741c81142940c6140920021000200e80402500e00a4500182d951520b440102c050306081d0111380480c6031104200c4044400607411310702840c003980fa109048105441000e6088245001a03800103a811 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 772678120 1250 772676870 772676903
    0xe06090c0403240236181005030a0506040b070507050a0b0414030d05062e03090305070f0b060109080303070e010e0a0302180f0c0a0804020d051204060302180a03 71
    0x500c00c46a110301106a00c0385403c400320043e4040707078415078034650040300d00e049146204038405d024044484492201d0381032060301c0804100d8101180c4881244280d1031000151a541100f403801c2c010030004044882220301d40c10410744a540c240c40503142900c0c60340025640d2406042101c0d40541d010780103019400081c1c8525041d5030014004484e0031075050031291041e10200060b011464001ea400181410903004011410322054440d150003024913020715500d01070710005c030320f00e9920340c00c0c0811900e4131803908580740e1090203002401c1c2190101c224003400039000d6100c0c4665020f88640c0401da4a844036550740307000854164000420305200300d40343d94402d00d90301d0101d400c0942148126600ca40c00180f105050600038410303900c14004100c0c0a20980d04060340100b803900729581303420b0030403000034007a14005101901a9400e2001c3c14100170301080791800003c09811807940355511030300001d002c0c0d80000c0800c4130701c5c81703001e011481c1071401038044011294002222010310340d05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 772679370 1250 772678120 772678133
    0x60b0a180c0503070f0c030c060e07050102010b030f060610230901030f1a060714070b0307170f01030210111213050103020313020111120304060f060602010c23090a0f0e06090c0403 79
    0x2c6c9400c070304200d0500e081000180701c90041c10300302800e40010b00021f2b4109400242101c0050690758402d52152410503c0d402020643d140c1240013940d1f8000d0301c0c051504165200c0c1a14a0050b800f14000c60014080c107010350301610f42c00c002660705002c00107128151109072502c0390030101c801410241540f0301858402d00502d1010703c5010b103078800c2d0a03c01d440a0a01003180d1007100c120100100700103e4907803042d103038020400204022819030a0554002c0510601400000d018444041c901981c241c0201403040a403035041003215105950300c1c400c0401c07500566460744403c0701c02c02d004249507019000f500e201b0808400654103030403d940044030340d508000068921402172941d07642d0200781c001c00942c0700d5400703803001148500c5120700410488500da0302c070034116450030392000c6a156010381e4000d0303811a00390750280c00d11854030700140140704000e07200c1d510900c02c080c00a4959152034a80080780e43c1c400c3c0642a07035480c4014806402c2003101d07904040072040005100140a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 772680620 1250 772679370 772679387
    0x108070e090c130f0905070e0a0b0316120c032a1202030406060e1e1b0a0c051c02060613050702030f0a020715080411010306060203070f060b0a180c0503070f 69
    0x21100040000d06644070a0400213031043e401c074000c003d03158010407450302c0d000761a2500300c0c0c0081e10054001884e1000700c40040c08050815101421403404840082380301c2c000040c0c501126902c02c10600b50010b0000e4020301c00a061608000607519100304002e40d40c4900c0c4c0d50842c02c0c0d841c0e205040070b0381020f417402948020801c50b0780654588000ca41500080001c91180c100400c90805120110750701c0a03222000401c0c070f01981309075480d9103119030640000d03100550018106100a900c0c07a00d40720381401001146042c0600301f050101c58030716030001f01d00d401040c050b145544503107420302c41c0d041941c00485100015074000c101c0c1c140b10061900041c1102d00483c8103a40c019910f07a11519803181032602c0c0400040c0b18041400184411100c01c0034240000742000c00155142c030b8806034503402495400350210341c0d00d007001c4003489403640002d44443c02c0204041d10b61501d50f0002c000341e4103c5858a85981d151002d650802030080b0116406801d050300c030400340c0844084d00300c50703020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 772681870 1250 772680620 772680637
    0x35031501030b010230190908121603080a09060513110a05030706141e071208040c060c05010b0a030501050702160f0b0d15080c03010e01021309050c19030603020108070e090c 76
    0x108005080302c4000c86c42528a03149107170381d108860701d40380a004d00d1800c29500850358581030f04210829042d08500c80303401d00e060f85818040066699442108000c00101c480a414030341088108590008480703e130b02c0300300f032150f0000006040740f0b00c20312011185074090607070103a1002d00180801401112803c10a04001c0c81541c505040c1003140300301c003081120b102005000c00f261480800c820000300074000f100d140340403c1c6601e0f1680325000c1c0c240f42e502c5003a0500205003000350620100303400000003140d001d451603d00da039036031402074001c01044480e00c0c014010403001da680c42c0105082c4208450111416070486424250501400e0780040c840c0c050203a6100000f40c01c2803000403150004000328400b40407443c04100c1410b080d030356000c0c89650319034410400100b4030400e270880c040903100941000103055031441c1e9414064400c5880102502d000c0f0f00e180d103d1954560040010faa02c00ea03580346454591000c181e400c0204403a403650300c100128000303a80a0361000140c01f8a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 772683120 1250 772681870 772681963
    0x130902130207030e100c05070608130512030a0b101403151207050108090d08011802120f100f03050d082502160f0335031501030b0102 59
    0x540c018540d081264040b54088022442001c00c2c140c80d031030160f240b2001d03441d80e800c1405201030b040c0c1c0c80310b03110350030340c020230090103150004542d1035130502c1c00b1032a806a03c00101c90107801c1005090b0310710307002190380d0000603042c11402c40b42c5040c0790000a05c0c1e5841d41c1c4a1600d1040c0041036501c880e00000e1111130003500108100915030b4038010001001c44402e0090070038103050000041480f40c00411462041c2d1000e5220380d05650f00015043c111000001100c6000c0c22180003000a4031480c40c017140e114106034140460000558035150040129188010340107a5583c0d9100c80045284400303011900511400780340f41d801003460b01d5010804804d242c0c4183c5248900980381d02c40400c9a800592040481a290714481860341001c0d01c3d648000d07200980c41c6984145030911010340d01c1e01d04104030910340c41c0300e43c0108640c0900140040003e9120f1511408000c20341c1203104540b4006420113003004080d5001003030a403034041c0310804c0c00c40e2120701003151001c3c0c10501510f0a091 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 772684370 1250 772683120 772683139
    0x203060105070b130302062202010e1302030708070f0c170d11040b120a0b0a030311070e07270f050d080d0207032715120905010606030b040c0e130902 66
    0xa4030050600348200e03108000201c0702004c90070700915188008000440c00c1d07100ca0050113200341c0d5901c10004299091070b08603900050312012480102000c800c00b00c110740084148503040390000c80c047c1c4034048990b18038504004101007142e1013441402c001d4084010380640b5120000b03081c008040b01d03e182213010550b000c403000c9070092030f070055002529a20001c500001e0440c64000c0d00c5402207000c02d0b007030040203c40d00000e52022100d01c00101031050380c5021038a000300c1400b450005102e0300a0032a41880e16060103040411506034044880f001d501800d1071104560b420300c0c0031b45405460380e0115500300801e0240010410006542040d810300114094a420340001d103c2c0903c03954030b124518050030201e0b0b4100800898100e00240c02d00401d000c48002c0040551400b400f034075220400c4419132009000030124880c02030615401c5c04004034207190941c0007020704080540b4100880940e000702211003a000b048141d621000449041000041e030f508490013560009081444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 772685620 1250 772684370 772684373
    0x8040b0109020f222d090506030a120221131712031e0f07020c090a1404031d0607021c05030f0c0a1703190c050c03070b01090b0d0510020306010507 65
    0x50600c8040d0f03841c001519880404d00810800c80c44000000ba44000b00701200c5c18034040c0f04100d84001d0007501066039480d0001803a5035001c002050441da0003074181c809010340c0340402500ea404034202c030380061030821030002d034054584040754004001c9220040401c4d0501068500810104450000300e200301c0090300400003c141c021030151985200d218030721400507010782c0007e03000400480f0182c48000401070401d801041d40010000c00b00d41c00821035030f0780e9070504010300d101400327405005408001c010826400c07040f102075007142b6a0582401e603031940100102449a0300000f90040e015a0013140448692403949003014415001c1d02d0038240ea66801030060703000012146401c0d07016075401ca0910200b00c440310040c102c0d08181514602c0c1c8010050502d101c03054488105913500c4c1114648030f03110720140c0d03c2821082c0150303035a030350580c00c0a101c40d03130080c0207243d087c0f49450401052458041080d11440d82c3c0800035203814403201030600c00942000f810b46042c444100300400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 772686870 1250 772685620 772685647
    0x20d1115040618080a02092e09050601030b040605010e060d020c030a0c0303050109020f070f0f0b09030901270b0d1e0501080d030504020a140d050609071508040b0109020f 75
    0x40e001c540d4401c80074000e0304520080d24403c0d54820f04a9070008124030025886014481c4d41c802c001003c0c0c020003c02823400d00b0003040000280c0c1102e15500200810021490740243d40145803d0303805100038584c0a0400085031024071031035002c81c05009110751a410100f01400b40051090030040c24007248a03100c0782140c0c03121100c40002903e11011104054051041d1809048801030840c10306030900040405803044081c0688039400b01e0a9800402045410440241c2c2d070000e50344400d811311113420781d680d407c071446c130383c2c013083c0700300444180c002100c0c455052805840007050080740c5041d00da50002d40c443c6032400c03440b54440000c2d030051082c01072a08004400030304006150740c90301500a040401e0312a40c207040500700341c2800b02590318280d4410994070f4215001e81e5421000001400c1c10501610092803402000708105040701c0104808085584e075040c151411902c80d401107030b44460481d4010320590116006001c9028160702800d60b00410250f0799103030a103d41000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 772688120 1250 772686870 772686877
    0x41403151306240509010806090c010c15140105030d030e15060a0e01230102010e330109060f0509040b070305150303030415111e0304030903080c060919020d1115 71
    0x20050225403041013003281005030041d401400808007402060a01210054640030700030041410820917141c04c006000c030030540b0901002c40580200300300c01c0c4488400000c62001d02c1201e01c24054501389001e198040d0140001242100b806007200c8505030b400700e417410101511254001c60501e101085800c803014001d4060618172601d0054802c03070401940a80c42c140943d94110b90400b05244c10303411b40003800d00f81c48000d040f0403128106004015001c0e140820810740000e901c4007000040030440b56000e00143c596640026108a03121401d21813040d5090320014001d6440134000b0320705170300c290b10140c0c10254166200201008580003e0b01d141c2094805803039800c00c4511070014041c203442008400d42c0c4160f1070b681031144000b0b00b02c41500100d07044e90710354500000040c0806100da0641d0010396030117846030392100c00c00d031665aa03460044034220454031492032084030740e880c00310b030510542d58010700300d031285681665812080b0b034081e0300c071070307004060040c82d000c0306007800028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 772689370 1250 772688120 772688171
    0x5011803020606190b0313051f1b0f0c08130e15030705010e031005091009081905070210030c11190506010b210c0702090a02041403151306 61
    0x3403915040440812002d00c2c1c0e44d40140c100200b902104102c0568031509907580000321001c039584480380303400c01604000304001c4000052140368404030b0400b007941d01206441c4160b01e1010a0b0050715281600c440c840317464002d0100e20221144400210784100401500d0381021405264955a1170301c96207814060702c21030900e01d02c0041450183c182004100f0041000b440c110305003041ca6001320343c803500c480d00344d01c1c40d040c1c40f4000178005140030032114405800c0e0400404c51a8154103154106400075521901e43c0c141c4980e0401c0b1940c03040701590400c40e0002c004008040c0c24490640042025481aa05000f10101250040c3c0c0040c0014003035102c040c0249003c0c1142c1b407400600b4010305070460b00c030429052002d600c001a1103520542080f003c10501c1d07800d9110092041450701413200000c0d44184048100581c805654010f042120301145450751001014410191124505c070410a18040d000c000900650580210109007a006e80000108540d0240038001c069003400b21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 772690620 1250 772689370 772689373
    0x12050a060503071e030f1514240f130903020601060203070c0905151806010210110426010e150901090f060b0414040b012c07050a200105070f020307030e0d0501180302 73
    0x2c100c01515582d0041001c0324908c1c0e80c00190038909052030020110000c04010000c1d81c10200c540c80944a041d141444902c5c01881ca80d0094104030100e0040c200058080700107009500c000030310940000156061240d00001c0e000c02107003015071030300013080c006000d8500540d00205c8058a0340307030003120014810301080180c0381e620700140003a00e4290740802255819241c005108903a5140342c0940c1e060780e500fa44501000c01c201c0c6180c42800c24451f5100d48a940780011516102c5000901041c0e1103030322035800030312682c0c1d00304541c1c2203604024003c0c0ca1509000340200005095a0001c1a00c1c0c500030b1002a981544240208840c0821241201d5a140346001884004c03000c1540c01e02c0781c0c2010788a001c80004140341270b80c8040340580705034280302d00840e18042d003a00400440d84a032804540b065541600882014007030310702a01c0501c0410000300304141c1052000c005c5800050f01516a50a50745501080c004400422001901c1956840c000b44010b0141e4544800d02c160080e030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 772691870 1250 772690620 772690643
    0x5070302060706022b060b0901202a011b05030a08091e07080c12030d0207062310170c19030b13110901140105030402040f0c12050a060503071e030f 65
    0x2209500f101d000d87c0100e8032075a4280801c46107a80c0c81072404020a42c1c041e0111500901a02d4851a1048020003030b084064000210202410328840110082c502661604440b41c1d100d640c1c034a81c49844100900180c204020340810075001d54001034001e410002101d81603105c82e0340e5442c02d8007003c001e1a00540101c6401c10204400b00300744440784604545c01982d08040d56201e960f41d1040902c82c29030300d9008240c04044c066203038003050000b4580942c070b02103a4022504110016011030710485510700662010606011017009000c1c0a0318a4008200c0f480c030b44010071003120110302c21408a89441d550110000d00c80e42107140c01075441c1e10740c0304c1200720145040f090a8031507842c10b40c01b0391180b400400090f1440c41904136005000e0806540da501c1d240081000740c000e4540d01359400741440380f0308058270380c8103079a1140b0600c4254104502d40f1307413808010031390711544585503141c4e011400c14409140510010f580d480c5014100d44041aa40d907506000707007454000c1a03801c2c04190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 772693120 1250 772691870 772691947
    0x9010816140105120405010f110705061f062a082d0d09061503150b04050f010512280201030b120d0503060402090405010e0901180507030206070602 65
    0x405100140901103104071070300c03803000c0000300907006618028040b85011008142401000c5d8010414044500070a0100a031070060105160780040c1085406100701000140300140302464a003080d50095080d05800d803500c1003c030384003000c4040210700b251725a6890700904442100b1480d1092003070800e07540714562a0f11b00701c0c0104580c0b0710350088035460300318001070480c2c0130116155004501c50000702d182c5182000d8004029032625802d54183c0ca11000c400d014030f05440304201c18040c101400842890310038002034550580c0d03580101c410a600601052418a10004000341a58100d40c2110003040c03801c038082030a4842d800720419060301034829540e260050040104050303500c000c800b26140070341a07032004101503501c00c129010012502c0c955a0ba0121402008000e006000ca940c4503070b40c12809020617a5180515860000d44220a10f08605000b11058000d009440c0c990f00e55002c0c032009501070780048400c44d42c204900500400c4042c05464080045408a035101c10207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 772694370 1250 772693120 772693153
    0x7270e1807050907080121060e0c040f1104030210210509120a120902011107030312060f0b040b130e090a0302010c09150c110913110f0607020d0c05090108 68
    0x40c0e0304100d002c3c0f00c20b04208403055811201c8903045402c020b8051381c8082c0d5020700b6481c009014a0001d1000d410510000c2c400c03200065502e65010044500f00b040552011790a011150209600b5030010410720040005d0b181145101ca1040203500b408400c5075540415841c42c500100d100301c6441e60750354248656203004101c082c0959100c40180c0380341040d130060140070001000c08144280e900c4031611411a48108090f03a0700712848421103c0703181e202d01d0041d09120100c1c2c2c0d0820214941240000d0942c406142641240d5415200d00d06c0c2070f0034081701c00300359400072170381418a40201c1070000f0741c0e42241c01e04511615000010301170207503103403900030f0071b603a21602140d08000560f039040c401032501001c0180f10814605200440e4522494000303035180d2881c1000740e00c480e0704802c200030664050300c0c465180c0d03c41c0320060311841441c42081940c800c5151403941100c4240701150050508207100346a103801584245086540e0b50001048454240c1203900d6a801940546588548 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 772695620 1250 772694370 772694383
    0xb0c0c1f0e01020c09010e151306090b030313060c03030605030304030f060b0102010c02061611010f24030b070323091018260c160501080f07270e18 65
    0x900740f0240c12840703a5807000074000e900c10300441104291040c04103101c030101140706104480c002d4480c1130442da55803000c8005042c0c511891b0b203c1030501906222500e408001c86e8043e140441543c07000700d040c488120391080c840c103000c5040c16500c550109507980c08101038802140b05d082c14840590b840d10f450000d46884802c018156814640c1000c5c6150300854055444000354803111410f00c03001e40102c0d090a00280d03903070303425482c04041d85854846508a4903412023006004181911207415880505440e880301402e501d5600740444c10440c840d0300300d1400c801d8106076000d00c2c0306040d040010044000d80b00840b003075100580da1881c0d140107024120f045200d0340c2d40e600303042500740c9580300c0098060131580c007405451010445000c0c6004280d805803040d00048030902441a041310741450003038000d80d80032503032030030009200791014030300f082c8210495a00c100b041c603207141c1c0e002d0714140200d01d04112043e181e00d0125454044000c028032a0b800c480c11005103801240c2d08034103104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 772696870 1250 772695620 772695647
    0x190807061d0904030f030209090a05070807080702100f0b10030501050406080a080306281418070f030b030c1305010302090a0c020d0806042315030102130b0c0c1f 71
    0x100381c0c51000c41641c1c1d002200c1c2e90298140c1071850844051308401c8009118041d00c0781c2d8080c00745030a00500c0c201591041c0d100d2501a12100134503192000c0503074404108480c0300e00145d1000a6200100000ba00b248a00e0700d084100451070802c0b440010350442201d0210030006a507403001003003036140500600b4000c0c11203002038080e00f815a11071350468400282002c0c040c0c000101840d4400720800040b400408103020135121958980080900f14280381c203400b407080200d484035007a01500840400d0048034192115403aa1020102c25405081040d13049a4103000b0060060910380380c0004901c1d00d01540c10300004e03c1e41c154410007281200c05090018036500c0c18844500e55900042d0810742c905060400340481c1d41c43c20009805840450002269101032000c101c0c0002003585166000321080c0010104070f1009505060803806040c2030002c424905c40010025500030000800c604d50042c1c040d0b0700740030075240101e9a100c0c06012440c00c2a003901c0070031000154031190346890300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 772698120 1250 772696870 772696907
    0x32a08030a081008190c1e300f0c180c0314010614030405071a030402130b0609131404081e0406080615090306070509030d0801050d1119080706 63
    0x128204130b00c05546154026911010100a9103c00203019820001c40010140d103202070081c541c4c440c0036200481941c0c400d220b2002c40254000b5004c1c10445115640e2044070380c03081491040e2600d420881d40380803a8181c031a0140c600d000714120275000c10b0303920741030342d0300700e0125a580c040b9500030100c0d03d00010385d445504400e4018014141d01c2295401c00c0019400210b88a03112801d0103400d100851f4068001414242100c50b10864200c01071449503008983c4810000c9003c010b80094603071780c1681c103609c1142040f407008240380c90400b0030303004200c603d0001029150500c0381180301c14161000e403240c50000c41e201c00f000d40c81c001c030340030000016941c1c1c82c24a07143c190087c140b1382024101903c103000c1040911504c26440043c1ca2001400030300701c65041c117142001520a0340aa01c5040c028024010800401805204501c2c1220000352038824814919129229101182ea02c0568440125000c8141448902c4100d801414640f0003a11000c1d02e0404d000d41408100960000700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 772699370 1250 772698120 772698151
    0xf0b0711030c0c01080c131509080f0a030518040e070e011d060609060d0c080108060a06060210020702190e090d030507020c010c05070b0d14060d0c032a08030a08 71
    0xc01000f050700d10b0700b00800c0c2000c0b0b103d07456030320300800140154014406042d02191000446150030700e04450498429101c9244554541188540756456100b0800312a071180c1582e200082c03051009007003c40071954041085984400080d003560514010404c2d41d0780000e40901854141c00d158500429013000041040141c070303c0700c0c0711a41d80c000c2489110700c0012400440ca0b8030784000311480e40b81e14110800401e5116800a8103c203020301900003503200e06000148210410720401c41650540e400500c02184070401450281d402058201c0c0c100c0385401d1401c1030a0b8800481034003030518900c0058583c40c00c00c0d00c0c170b450402e044403108101803c0405120100b0740100c0c4540310703494280785c400005d420500780b19203010201c0c2d1024105120001d24030301c04280303e900c04202078414611012940d00d45404001e1480d221200140440410f51010070001d00c2540d03260030301500140d081c210185c0400c850455040c02648000901d40002460980c86036000181c0761b840521041c20101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 772700620 1250 772699370 772699387
    0x130303170c2508070812150306061302070c030203010c12050f13030827010b0102160b0405090403020a02030a0f0203011523011b05010e0607050f1905070f0b071103 72
    0x2840701c41000030000d00c00610a00d442404020004c0710300880d0801d050a903242d40c1d003544841000e40807600b001104c0160400c4034032500c0d0200e03095018203001400b04603d01c0718400400020b500c174500484001841400010041e202802200100d055545484204583e038502c60300940741c0042030403650841e0f540c100012201c200d41005005a01448c092030141d03a880758005034004080440741c0b128400e601c0c01c0e25005030541200804403420b03800c0e00c540c10007410100004800364003644d0700c1c1c0e910a0100f07002d41d0600e66207140e4424000d00c100e4500e6605c680110781014000c0b64140c940c3c0c881441c000d8150f080034000e0305a00c80e901440c6601c1030b072801240f2030140801814003051406030111800080e8424440e00a0300710365030003ca4416030385482d00500071300700180d445041d1702419000a4042d4041c5090704c40c070301030a480ea24079100703030302641902407089150b0b802c0074090180300b09004113883e28070300011903104043c841c7c014100050301401c40e0840107004d51055108000d10310 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 772701870 1250 772700620 772700647
    0x1204050f1f0c03120b150f0c0106030b0619050a0306020901020a08070614070c1101050c0c03060109050f010602120406051c140411030a0507411c1101080a02130303170c 74
    0x40095442010203840340c800c21f00e0724815100d003604a5203039600b0204040b080c02a022413603030040f00101c8a0341206140119107000120143c85441c1e07000c801141d0800c0031805540080c80074460501c1604e08070300050b659660990041c900c2031701d6003980c5400c01406100245202c5400510b03e05100608802d680c0d9100c8000d022100d115042040216102c00ca0420800c03072042004001410350b0740342d40c1c5604004002f08000c80d555841d1112500000803c2400800c003504031926940d00c603031405003000302c00d03695a0320005000d40070740c4010091060800707161142e03841074540e11404000504140c1044400e060078034a0b15846030f00060000f00000d01c00040c06401c481c840ca050180700c0c1240ca815016812032201d0040705000740090305d20450240d601239245405040303d0000c031a00c88541e500e10941003014004040303e0b1401100092176018900050744a620201c0c00b40c604500c0701400c1203100f260394000c402003101c3c1840782007000d10180049034800942c801c1503040417500e16009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 772703120 1250 772701870 772701889
    0x20706170a0f3206090105100302030714030702100c091805060609300c0108010e06030705040f0605030712080f0a020c09040b0106111204050f1f0c03120b 68
    0x803040556a020b4821440c2480c1c1054160f0f9030b10f00c00301c0143c15460340e890b0302008520b0000e41c080449800004280b8503244818605a41c0080e09503c0d4509242500f40c2c000e51002d0100c0c030500003030318121340d41c814500000310b1003404260f015003d001c02100b44c2c18107441c500b14030300051041d0b1042c00d11424444040d41c1c1b80a07a001d00004c241501c88102003081742c4142406940c001000e442d4110505542140d8a031041002d18107009036074016a2603103480c1c901a104143c0098040300040200160013504a60000e40c01404d458140d9941ca00040c1282e002d0900c41001030b0302c80204201c03a25040c4001d50007004034003410800b8102a94590040b44101e000c0030040301c402040030001c19100700499101202c01078020600b5003400d0415560050091190320009040b911104820010225544419044060105051a043c80c081004200703c0b00c00d0140c00000300d01c04040405c580840508000704661100401c41d90700b030800414000108214100307460800b161000c10313490341500c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 772704370 1250 772703120 772703131
    0x1030e0f1f110a0e10020105010e040b06010201140109150b180d0f060203010b041401050c0c1002100f0b0301051b07030509181e0702160b1303081204020102070617 72
    0x1c1c400c41210349003038000140500300d0080e002003008909420303a140c00c4640d8581d00c010403134103040f81c203031600401c90a0355024029420300d902404d0120700015920106640c200b1414000400d0031a0350200031410700400364031a1a24586800c0e5000c1c240d0010130503e00a8600222028504522400000380807640ba08005008800500c0341078244500041d850a00035404582950b9035607440700c421307041760003500a00d40c107440454903191403580500b0845602503d42c40180111210344801c00000854410700e81003075014614030811360a520340304441e615460310100041d803180e12400d01d400c4400081a0885800c445a13521805055600079210702503070502d00365649080c4100826007041903205100412440e01c4103010301214101c02071403001030b21100c001110740c0c030b4081c101c1c1e0741d22040e40c2403842c2d581d042c0d5080c844411b00000800c80b01e21880708485070b09a4030750301c0d11150b90014413a0340041d803a0005101c00c560b41071040a0044c240380c60103211704800e01c4c03100c0c40b203c0e82c041c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 772705620 1250 772704370 772704403
    0x7030b040614090c01020616080610110a060e0706020a08071b0f060804050c01050f070605180607090e10030803060d0f060501090c03110a0c1217040c0501030e0f 71
    0xd08012031500607041040700207404062600f000c9194a40d2a101503da1a025014007000500c0100c2603039085950008140ea400302a500d6070000e1001c054000e5088101300406100030b1310603914104140e2107854420000080c14022070482c45040c40020b4002c1c00c119040f05130600d02181e000000c0c0d07200e041d0010101d42c0400e20f81802400c1c84145548400030f144104c40b03002500c560003401c00c52040d4090340544120784482c4004654a11035804005081c290030300008010546d1640701980c04400e480480804a910300c4078203242c984200c503800001440f01c8c4092040581a107080c0384c00503082c00c0d50f0f924a9042d41c1d1448002d0100500c21405130a10303102e40018001c0c031102c0307180c2c8203400440030000c5584610351540a8034003180c480c008030b41458205040380b0415011145404000e0b40c51f0242c54400f41d4407660313a282ea0004c9601000b440900010002d00010a84c9000390321442c4038011711440c1c50005410f1714505241840c0e0358006480f0107202c010f01080f60020384078400c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 772706870 1250 772705620 772705643
    0x3030703082d04051009031d060d110405011d01120c0513090c030b010215070f1205150f060909010302060903030f0d0504020109051914131802100c050703 68
    0x40048040100440c0d071074a078049001049200c0c0e2650440f40114001d8041c1e43d1a00d0752010000700b07503a0481030003000294000320090b0f80f8003c000e141621040018285440c2620034052841034030006a100351280c0c8001600700515a00014860f50b050140c1c420020a000c800d8006402030050704981280740d40c588000b0320100303105400312903150003442800310155403980450002805071a000601081c501981a0304541c00090303080c40300a1341482c83c0b0b074155076480d4110f03500300740d0344124420b11a070300000c040d0b151010f01540f442254261804150074240f0700410911800c144240c901805040100b0950754541c02907071415660107403005951020350034040b81c518400e104102081940100f181b5282c146650840360245000b640c540b12402e844208002080f21440000043c8056131390381048440342900180034403c40c024600f8008844500c010002d461440300c2c5005281c0c03c020300802145800f0300114440c2e14941b81c800c0108009560702d0350745101a0001421040444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 772708120 1250 772706870 772706881
    0x50c280509090709150306080c060408031b01111611010305090a110102190b011a0c03030711030d111b03040b04091109100804150209060703030f090203011d1501050303070308 77
    0x1119001e0007017150780342101c0d03a00307000007004008011901981c4070f240075410408809180c41019201604d00b410301852900001200b40c00049240e41c8086006540300c84240c0141c4042c88044c040400e081116044002103601d8150701904c008103640381850314010500206a50018003001d095520051003d2910031620043c1d19014903100c41d004503040d4050750000308030510340142d04958241c5219041c80d00340c51600b01c554010200f452007254824000200ca4034840c494404040d0b450f00c080d24604240c0382028425244e40c83c3d46608030343c03000101c800d41c1100703807400c40482c2c60f8040c000c0e60610b410098035071001d1186100d07061031151189540c445e032048680480c1c000440040000c11605115036016100400c125401c1c1e820510004416190754a54000c0708e00180e4014400c1e85000003035a41034000701501004103040340d40c2c1c0ca00840041c0c13424440c8015514814070016500c681215140c0e00c0c0108001c80c4271070900ca510010010b0b901c001044da8441d60741404c040745140c0c1d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 772709370 1250 772708120 772708127
    0x21905090d02090108100f0203070c021e060708040e060a0f06120608010203160815010206070c0303020d05011e0603060b04120503070b15011b02090c0d0f050c2805090907 75
    0x207264010390f0101d6408000102c050000601a01c084540c080c01c0c4030350103682c0000401c03400210f9a40022583c005082401031400401c040b072001442540300fa0000c3c40781c804110f0581000700100c032100000a010701414004008041d80414119120b071401414007064501d4034a00748905000d00164110361007920301c85130019009003200c100215128074101072460800e0104168a002040d11760004c0b0740c1440c46c46050450202040c0c004012507100c440046488180842e4180d081680c24804280b4066150156500a14034008040c02d554920340b541d1f500103c1c503901000c1410320700341041221a007550142c404035840d0201007804070b002030925030700390300c242200208091480c07000c006a10810800f21644080281c0e614800d88400050b60000f600d000100a03510071000d1000030303084654500144154000701e80085094100c4102040a845050340d00c0394000c0c41c04034445400c40502c15140070045810a501c1d080e8030007034040070380b01d0300c1070b034070514040c0c2100700025120500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 772710620 1250 772709370 772709389
    0x5010e060a0b090a031502120705041a0a0c0b07080103050c01030c1b020105090a120303050f010303020c04271103010507181a120a0504060f020f160f141507020102190509 75
    0xc2044a81601d420305460020003980854020181d648080c404a07606030310540135100cd03a540c8413401c010b042000103110b0080d030482c0c0b400c036040102000364107001038441c02e040390040005450302c040e2541986016814013101c518910304051602240982c1640d0180700042580100d03034018212082c01c0c001280c40d032150380c041d6070b00041d00b00400120309075004005460b0341d000c0c1d42c040103507488003980a10807640c28440640140d019082c01501c071725145e80038500c0d01c600c40e20b0500d0542c00420805001d6220f0307003410b4a410041103d038401504080c01140d0f448580c40c90311780034076034028004084003400c41c040d00e218400c01800030b0030322b2020f5008039000c100c504008070700c0a140c402c1d00311000e404200e41c200c40c017904110b000803500f8018001d84103c0f50540d01c0260810740780715240800d0b140b8600098491000c41e40c01000400d00301201d00007140c8110026000d01c0030200c1c0c10300100c90018201404580c0f041190f0824581603411102200c0079074500140e0b41c12498000881a51 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 772711870 1250 772710620 772710623
    0x219140a08030405030c070b090a031203060e07091806210501110f0d18032c06030a020712020c030a0f1529011b0609020105120f060405010e060a0b090a03 68
    0x9070000902041c45000005031144488035021a034440c1d072500d582600130b0082009403600000e00400c2840003611614400301e0f01005440c0004000b542c4401c0807c00d118150340c108081801041d05018180c016000034140c0c442e8030b0780a11000e440e0000e1901c00c610040c00d40c546202c0c0d000001c0782004070070f410265822507202c90442d01c41801e100f40b42403940c41415040c00076481c000e9203800e00081c101200f05155050346407041c0c1e6500c4024085442118058540880c0000c0281441940c0d180d902450203803040c0b2400507100c0c181c1e0300c0c0174001c074401094850259070001030528115640000c5840950741d0014007914080c0945c98016443c0c04410354215490b8105441c90612602c041c09034400c001444d200001110f500c400190340003400c500c60252700081c25503008020401c40c0d000070009900c1854902d2070500303400151010014165031001488000000b8080720385032600485014200004c0944a00e0030308200047c5401d00718410001000d5000c590714445650354000040250b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 772713120 1250 772711870 772711883
    0x303140d06030c0f080f0c0405060f0d06020414030a08092b0302060a050a0c0203030a180503030a02040806100e060108040c0518010f060309080706020306041e0b0306070219140a 78
    0x4070380b01c0ca40f80c0a4a0340c0c1e4010714007a1400300d100051031710400034000d98056019000b4102c0c0c1240503050001422000b4000713034001291500d04030598850504103008036014100c01a12a4240100214202601102c035407195104440c4040030401c000126130100000720391001c404807100000c0c21140c29540f8418540111801003001815004549e46100d071524031401c224950f500c500541c103c47e515040c3e2801a1710500c0060301520103503000ca45038107811220300031205a941d40d068038560084809101c92070b0081010044010200240c1f0342046010107649034260501d000030300c0840000f08624100004000030a06129450590300007400000e03044d140b1207078040d01540c942c1c406c00e1051272004461b1020025005200c1d202d210b0080f50b10400917440c0030741544465000e50405840315500640d43c44105c842c540306259400c901400740307680031035441025000c041c140000106100155080540c9a840b12000c9102c1560801e51000764084040c02400429103011000c401c02086c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 772714370 1250 772713120 772713131
    0xf060f0a180b090f0f0703020309071703041509080f070b07030e0a0f09151202010e061803010911240418020d11070203060732070c15020106050402130303140d 70
    0x8140c616091841146034205c1d0303611984070b001d021012444125983c03803180c1c203c0401880303010800c1881c0c0c100e41240c00c3c100c3c3d081644803400c0d03602c0c03030144886000c00304600480030010b500342800f0301c16400703d2400140c54017a14100c0340010b54816402c0c010108407600f41c2c0c400b1660345515414019024003120b02324059250402d54004085480c000d01841e41c40020000c1c82c51071902042c0c2c1d01c554182d4500044181e60400d02030903401003441d0600780815440707c0d0750140c03401d2140d0b048480c002c0480001060300d510030701a04c000381074020034809002c0f40f0443c003c0000101141c04695881d00710034500c484400c03140000380518180380548a007401d04107080c0c00e40800141903200d00031010340e0700b1070b03e81c0c62058810b1900c014000c00e041c80255131401d501c4009140c1d000303041c06604083c81c640100e60390b400e2664041e079040224481400041c000c1c1407603091040c44090b240c180c40441c0707001104038400b91021802d00c00102000048009100100031070310540d81e01c1e41030000c0c00d002d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 772715620 1250 772714370 772714381
    0x509010c12080a0e160510020708060702060a1b0e060d020d0204090f0b12060f070c05030a08010e0c0c100b0411180f010e0f190b040902030f060f0a180b09 68
    0x101c0d60003542c2c01104507082c10840303800f20902007443c0c541143c2c1c41800c01901458907052044419001f1400800c0d800360a070006000201071090ba031080c0c000d9405028940b0b054800c000407201e01000302d050700b008085103c070645401408203001c00c1011910107031144402044007010703114840e0f60180c004c2c0045000108207046401c22000441c0410092041161803018000140041c0603282501c0d4001400f140f01c0442507484a504000d030741c47c04a1698540e07131210380c515440b11503020001180b010040002441881115070007114444040d40381240c0c220b54a903407010502c141103150707950303907080c0f07003440c3d0325079000f0050340405140d569222103d00340c10755a141d000c8403c6a001d01031410364011158425442511140c0300100308610a898400034410841d0529041070f0112606501c00b140c3d00076188054001820103400241e60380c6000c0344140c4a40fa0046e00070f0b40100800075201c0c00b13507940c000c450320540740040240c1e9003070150080880080c018132800305801c068443d0a101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 772716870 1250 772715620 772715627
    0x20c0703021f08070c021302070506042d06110909010b12060406030803041103010b120304030303061a0f0d0603060606030b010f0c0c060e120f010603050715050a0509010c12 76
    0x460707008941e4051207019a0702d00c102c010284002501c0003401880006070b4040c003421800482e98006000f06034102c4003c812802207900c900310541b01540480200020001c2e41740b104201d00408600c442d10060903500d49030010b01000d40c008100302e44484c2e000004c0090a02511400306000302440d0855075115440c00465000f0509404540f110a001a58a007042e0140c40110381e07001c05154a555950749411074180a0030304015419502ca9103600302940c1d40c0c11800e001c4c1019080510b9480340785190107003c545c603540c02240e60030507103854808280d41c0301065a04445045804643e109941e4280c200100101e80005101514150000c00d0244d4180d11076603042d6400e03250510079500e10701d0190b0748190062401400d44000d458180019403103400e85803030b0401d018061108038100c0b038050904007540b5200d59460340e9500e4004001703000e020850180103090300c00c10340d04507030356a280c0206a4401c01152030180300000524980c0c5074030901070700340d45035000f41405c550b01206c3c90004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 772718120 1250 772716870 772716883
    0xd030c1116260c0d02060d0504030323040210270902040e0702061003060b0402091f091d07180518061002190f1b0b0322030c0222020c 59
    0x4000c040c1402c0341c01d02c40da411840d244044100007600812501d560755040000c440c0b08450200c0e049402480f514800402c64000c10340528440c0d100030031b08044680201400100845280c008004217006110144e00d9002e000201c08460b0b1900d8003040810000000c030188200000c02e0380908507240001c0c0380c503490350180c01641c0100480c140300791690300d0204d0f90340300e0540c1e8a61440229620401c0040c807540d00c81128604090805401c00400000003003030b81c01c54102407003004040c90f40c81d07401c465008003103901074884101d082024101800180d01c048030002e144c082844500821060071600c210704840003450020010722850700c4207014258440015030710076008244403610100d403640041095a48401081e0300680c0f40c00312920b400007048540f210550740010f0a4840010592013207014a024103100040c0d50f80e2400c0180d6900c0c1140c1c01e503100b81110316420f40c0c00b400041c0d84454a5007409404803800c2c0841040b00021b50303030b00e581002e90019450f1000860307102c51003000c1641c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 772719370 1250 772718120 772718129
    0xf150a1d0a03030e120c10030f0e0111030c090307050d12090e06031203130c0e041106030621010b040c020f190506070c0302010225150605030d030c1116 67
    0x1140d200380a4105100d012a5103000041c045101d1040e1111a07091829900032500b402e0000c980b40d10407020003090700030f00c08840c140c00280c1c175105800e4100b1281c0c0600340742d01b0080380c0200001c0103041c3c02d044580c00044c025446036400080da01c1041d0b038040001f034020307040c020038501c5c20200e00d1600c072400228000440000c140e2100001901110441c902c41c4910f00c081c02a0140c44c40c210007291090380000e00c91038941e0f800800c1440810088101e00c000b412503080590b04c1070400741401050a9418440ca91051604204200c00d9031a400e1421004c08401e1407603008500c640a08140504050200281c03c149401801d884140d400100d0b00300c02d425032400c1d14141340a1010400c0e501c03500540190403036101c140401c260502c02d40109085500a03c0010300f0041c2745182c00b01c0d0000c5185041e0000c0c0c3c4441610400d003c514450306485420f14102000045d18140100780c4034802c2540100506664804100c02c1501039038041d41010f20100944032030310302100100c0b140782c000307004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 772720620 1250 772719370 772719407
    0x2006010609051807122c060103050609070b04090b01052b142a270f010c0f11040603020409050f060907060c020f010522081603110f150a 60
    0xa84200f0b07400406589000b01e070f00e50350300e803507030214071001602410f200d40030200c409410900394586031050900110b02003042a0161426514604007a4603000014000d10815007040004000f0002a60101d60449003410000700e00d440f001801a60203001d4064000203200c2801c40e500720f101c1da455601c010180707121008000c800709681c824440c88800325016400743e01319002c25003900340d1500200c0102d80c00405214076140c00b18082c07250b04619060250500b01881c0300c81d0503a4503060307142c420840c4080c60b00c805040c04a8031240031701e00c0405006080d00210991600d501c0d215030b08070a0185402900501c109044d2f442c0c100c0e036451404020241d1402400046010400080b6603581101c100307a591203121442c41d0208501071006c00c6019040c003104011b00f50540000051104c086a10031a00003030941c648694a030501d40c0d41200180c00c54040e00040c8001490003a00b03071510300c0159405030690403264045040c00304070040d4502e070790002258a00c0c030315a0010b034100040781070340e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 772721870 1250 772720620 772720639
    0x20d15090c1d060f0702061909060516032003070b091204030b071214070c05102c0a050303040b1008010527010609180b0907050a0501200601060905 65
    0x4204460000b00c4542840d009200700b0a00742d41c41c0b4103200a003407544840721000789403080c640d00103005503001c00e242d904030080030030340254206e4016806000420301414910710780400c82e0410400340d00e00842c000c1c1030102600f682c0c2c803103a03221003105101c0303d0303201c003100d03039640c25414030101c8450300b10b90202c1c0501c81c7e0030b04110a600c1c4d600545040b654098203000f65070b22901000d56407101c08020030000c0d5035468030030340412061684164002d1001e0b0b00d8105a4080c4c07030926070304258055410300309840c105030344680d40300e003e944110320503020000740034802c80c00603030901c1c146440102b0142a071f00c004001d020500224501440c00340d03a0318620690100e41d81e80e105400da4404a681d6501c00106030910a02c0940343c2c0c80d1403131002c56030b2000144880e00d482400088807000500042d1421900c0d0b000820004440140d0390058020001003280500d40000104265818000d0504020201c94400342c0c0320342c01d4010f80012043c89081d0b40f0170307685071080100404098800c5510030031001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 772723120 1250 772721870 772721891
    0x3020d1b03231c0507020d1e081801080702060a0b0a031220010905191b0b0913052509030b011514030402100810030507030f0203060906150d06020d1509 67
    0x1803c42e01402c00941e140d0328140b6800c1d40070401c8002d40014103440c010314220b80c041e01031002c4005020703005c0c81403e1541e1a1880344034182180d50b200b40321241800381070800d01800c56000240243d01c024600c0d00030905e03101d050086011141154030081c40150300003072900c016500300a100411807801c1204c012000c001c045803a003070f204034400162041d084241d01d48008510030380329808140c001e140b202848147c012003c000507802d940461422040840c958400d0328101d4040088000030010034005402c250920701694607244580110450f10081c010040500900b408002550060580b090660752a08407036a84d000d452480030005010911608105a42030252030085030094030300315250300560030a8a03c19405400302100030403082c0d001000450801c898000f4502c035003440389a00302c0610516285c44405031003100d80760448030400080151000c01c1d4031008600b00c80040b440d40850034820024801e84001400359410103c010008400780ca200204481e41c0480410111b60034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 772724370 1250 772723120 772723153
    0xa0515010503010f140f031b0a1d0f042a0608010504050f0f0403120c0302180a150302090d0b01080a120e060a0315090606110c010903020d1b0323 64
    0xb4018240c40d68a40e8105129440c2417005900e80c00c0c1c4084d1107400306020304030001b40742c00041c00300700c007001152a83c01341d260b0a019104800400525298010300c9089140034296881c0c01000b9003126107100c40010700f4011010b4ad0a404681d65140040b0414110704440c40c0d04920b5000f40c1c2d01007138400300006002d080c248078461207090880c001c0003c40c6c03070f120100344032048003800660400c51080422081003045205102041d125a01c006940b00c0286580401000000c18400c1c450b40c886041002690405424185400c24034540180c1d0303441480d002448050b1600c0e0f014200240103030011400d4100091300c003030024090b48110303904c544451411624034401030411600001d051180328544d602a4201d0764220707800c0d0018240154940d100e400880380207610080014071100b078140803102050244120010007071a2601295040d600855002e00b401000101001000c02d0034100500f900e08004001d158001d241c5000400c40c02c12107040000a6000403090f8029a00354a07040c00030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 772725620 1250 772724370 772724377
    0x11030f0103060e0d0c030e180114090610020303012d1203021603031b020d17030414011404170912010c1101180b07140415030b010f0c0803090309090a05150105 70
    0x4050b80c0300d1117501040d9608480070404c0080c03d1f03801080440080440d904050009070207403d0320700c5076000c1400c0280070401031a401802150085c4084565464043d501004403815122204a403a41d014000303854aa07001c024402c406111103242940410f8400c506004485040e010340d0884100c084001400c0d101c2c0e04441c8030040114140d40041101c42d070280c404d2664150004003070608090458640460220701c004041801190000c10801080081458211380da68804003c00c00a0000c0d10401122807000d800604401110f0360440d00d00350081c4100c84868001800e900c503070348990a1101e0207001d4045419011450800b48484940030510070484541d00d484003080c01c0080c66201e207105140d02828078000c101040500300813021504000740020718000c02d40742985802d40070020110381034116114100f10706810039815061340710103103032240f64101c00d206550362640c0d001286544100131303000ba008011081081039803140780d0700c418803d81460b4510541085e4217401101c0c0ea10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 772726870 1250 772725620 772725643
    0x1c050d0501090e0a0b1902040e040c2907060b030f07260a06051509070807030f021215010210110304060509060103080d0903170108010c021b010e1311030f0103060e 72
    0x3404440403c0200e002e280495400ca600c6c103001002c8140303100485416a4400e8006900e502c203400203100030010030242c1c1c00001c0a01c0e40b80d5564044854607010a50b14100603a059080070205112007407009940c84031401e514000c0c00ca90301d000030b48a00380d0f00c403009881140901503101c000050b12402008848020001c000090301c5000c03401d0341c0b558010900039056120807120140114110340b00c0303181c01802440c1544a01c070143c6450103004082d900d000103810141d900501103983c00c0881551440d070171282400c0d4842194a060b40103e20b00b0846044090b013041c07d02120380000e40903000118003c1b80290010300c00c0399038021005a650f403081c40001d10007201000908001c071030690000c110180309103084480340401161080d1604002c2c2c01800c1c050f50340b10083c03600141c04000d10b4030502c2d4060380305110b0f9004c02c00060407145040604e2030040e20903000c001030041c0c1c02d80c8061082e40c20220415141e04124542c11400502400120340c81443d101e1a400b41084c00070f00c082c8000f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 772728120 1250 772726870 772726873
    0x170c010e0d021b0d08040506041701180c0b1b01060b0c120403050a0b150307030308061804080406030c0504050303040b1902370210051905030610111c050d0501090e 72
    0x8698030818000b07040b090348005c0d2842d0505002c081a903686020090005042100300685c282d171244425074211400701204203070011003c1903400001c3c0c1c0742c0000c0d00881d089484c52548030308650340a140719010310600304c2c0d11546481e10100c0c0300b0400d9400341010500c9a400c440b892030f002c8a502019101d2408080c5c207551000e0f0030640020b141101c0f20713622044004002c07101c0c0c4102008a4070307218458100300c000c40e40003005c0001c2c40c1400c22503e1040c42c450340385002d850400792942c40c0c441c81580500300c01c15840f0a00d0307291a40c0200211401008050101d913526907450740303150007641140941c41c035a10712060040307098510024043d8000709180e030f064100500131340b0403021103261740b805041207080d008502d032001d0389d03a88440c80341441294035002da8031540242c22003203040405a010f414000c040c001c0c0405174480e40401030840c5400d040641c4407149000b145841c2450380000c6c1011211401a110710313090344200a0031603031182e00303420300041c2d0f01c4900f00c0341078503039a1451503005e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 772729370 1250 772728120 772728163
    0x1503060308040911040f0b0a1115060909010608120304020a080706021b0406260105090307150b03120a020307031209050c090403030b0a1d010602030f0301030b04170c010e0d02 77
    0x10315801e507200d40b0410b240c84081e45d140030f660b0090703541401e000384e06c90085d4800201d0740302c1c0c00a800071010103420303640c507000d001249548807500740456009030200d405100c41c00005888200c09500403405007095000729090b0f1031031000340c22007036031084900303d005030300300c1c800050700303040003c2c240c3c064403c60703006004800411034188840d21100a91380341c0c06034942e400000c900d1740b40348440404c4000d001558441011010f81903095540c0034101d405540d000704191400f00300c0000300154984e1078408003041022151000a14160f0b411a100c40d524000146040340c044c6c0000003001800d100b41c54100820319040412001c030b40e070b013003000342103030b044881e400100349486042c00344d010b442070900203404462400402c04400c070581008940080084501d111b030310141620a00402c9a0f10045103408200c00343d00341c1c2d0b0300040c07000411260080c0003080c1007040c44002c803110000b5110704a9140e2142c00d102c58040d003502d04100e05580075851084005a2011075428420081003e85801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 772730620 1250 772729370 772729379
    0x40c08010e040f08040315020903120c070e0c190f1101140c130b030901060f050906280b03041a150901060e010905060409050405070603060302030c1c05070e01150306030804 76
    0x43d038180500c040364514403c00001c0002002c01618110024030443d0041e202d52501c000e0514084100c40b900816020034014a00d01381400140581031300e0448064000c292500800311025009081c901c800100e88011900001d650180d02e640350b10043c0d5680420003d003da660034200c44000614451040c103400c0064000d41d0000010b00c451282c1001600da1284d456010072601d0f04142c4c0c003250f050b5140d610400c00303203003000342071006807408407860450b03810b0400008003604044015080b450101c4000200940414000d08000707040084060f592031030b01c0d1404506d00542040c50340100d029140200300615910b1725002c42c01c200160050740e2a9080400c00c0e11038646c0e2400c4981000451034001c5400e44400d0081d100508204c0c002048906017803426900704141a0840300815160600c10000350380e000607294140c10090324104c15510100800c51000c2c4407949000d0311034420b08000245002010782414100c3c3d10302c1c013403000c0e007445280e821001c3d0b03026440f0240401005010500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 772731870 1250 772730620 772730633
    0x120f05092b14210103050610060534050105010e0f09030703120b15130e07020d0c0303020702040f1802040b060f2205030a0507084b07080c040c08010e04 67
    0x1000070041c1d00550b000d0110f01c140300003402e098000702e07120f810440912401c10701203c0000003601c81420803904107103001c0c052420302800740034401d0f480b0348840540070006011010211025400070000d120319a1100c2c1c140402007416a80144500142da0000700718600100c00c1d5070910b64035684042c4002e8481d0009405000000185944a246400c0002140c00e00300024a60002090505c03400285040032107040d07080c004080b00c0954002442ea05c0219500840300284554142801a1a0b00702800401d0080c812008040482850a404154058950301c4004c01e02407089409002800300c40007409140c2c0205011007401e1041800b0302e2418074a00510f00c0801007000340949207499aa80000f450b203100c00109960329001316030300380715202050210b407189000d030340031086600d030109800180030710806007440200c00e40304e151500400c99041000c4060902141205c0540707840d03081030354a50080c8000c4511075860904088004d5000b02030b01c604070313090903840507020782d519201c00c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 772733120 1250 772731870 772731877
    0x5040908030402040f0f0204080a110102010501060504120c0e090c150421050c03030f0a0f08060d061a100f0219021f0201020c1606020c0a15120f05092b14 68
    0x2c05c2c08a48403071500c0d80f42066403020b000140301000007010328100d1030400f0456030b10841c0c1030a0440e4188001841a240c000c42164211102c01c0748100c961659410900807010168100303131610b000785000e0042c0b103500082c0e6a0500041140c0d078001c0a03182c0600450300d1300c56881340b00d0b1072a07401070b0352035100300704601c0390a14240118141d54080d901c0c03a0019086620001ca84000480082030488100f070740480c0c82944c0700e85d01c0c14514507030305002c000500d0b0b149030580010a00c81d11580000d003491000c1c00070300d01540e0041c10190314a064817402402554800080d003006110314104140440c0c081100c03000219005003000d01007442c00740c0411075050706050b811080d03640030824118030800030001c5507045440d40058030000307070030550000d0814240a002a102e642250000c0c411a441980c0c1d82d2091400d600388a195000d0408008010342162040c00756a9454031042140031100800e4501d040c03014103203010301c038004644115090420b40e5a14200251588500c1650184000000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 772734370 1250 772733120 772733141
    0x21052a040509040f05062a03151801090b0f0f010e1c0602070b0a1e0b13110309190b24090901140703020c061f0e0106030b0a0504090803040204 63
    0x1840c909601c60010942440e0280c50494414255000843c28014140000344c3c000901c410380044290701d4411001e00c4101d61400302c91035140010110b026000b450110321050540030b814818050241d502088010000b40310759881c050410a1496003450030b58024040c10340c004201d4140600d29100440e0181901d0318a690468119546c40e0100b641e8018084400c0303106490250307840b041e900d40008010005008420810b040c0355500c1003040101a4040d400980031000080781c180c07800020703c1d40e044480c000c2009a1920400010b0041c5040085115800510869540141d10340104017980d0000344054030284440d0b000c911206002004030001d1051003000c140d84107100790001d13441c04030a4402c0246030b176490100d04040307984108075641c84805800c0171410582914481611450020302c0068034481c2da4078405015220a1841405000c240640152a684880c00640280307070a003803a502c90501030000041510740fa001c2c00012903840b4040c9425512150f0030f100c0500454807e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 772735620 1250 772734370 772734451
    0x303190509060304050705040b090c07060c0905181b09030307170403060c03020a02120418051923130c0902160615090b0d080f03090a0f032105 63
    0x80840950314000034501a50049014000c6e1034a080c04010480b0901c0801d180590003102c02c10510b0140c80050719047c90308440086403140c041941250301c2d803100c0e0401d0b07030700ca00c0e10320141824440e10b00c1c0982c810f219402c0513808640b18645a100c072402540e1100f9807652041002ca030014050301c140d85030150f003440806003055101d5840f071054a45210283c40069404180004040d0703040140940c21141c46044629050524418529004110b44084040c0b5100d0004c00c030002c9411514810181013400100802800e03551120204034290301c41c02201560080400e203048425600c140e0b01a5000340d00307100040c41c00c442d04010350844404000c06803100c2190f100451180c4c0600c610620034403041c040080c1c03c0c03034600c50464079020700f031b54005c0c0b00d200104030020361807a040783c8410105590494403a038900c0e51507032502d52408802460034034032031055030403da0854040c610b4000078501000080030140140b0b400c4550031904c03448400007981d100d1444100f8031203611020503100c00d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 772736870 1250 772735620 772735627
    0x260604151814010c0305090309040b15030901150e091c050c0a030807020d0507020f092d270d11120c03030702010b030319120612060905061503031905 66
    0x15100041c10454007054440910725003180030a4102803080e030a110509003020015400c0480d07034a50342e40070f852105400713942e0b51603082080fa41c400c990054090700c01401d0300d60b60314050300900d001c0c0050307035910700880c4040840030a55070031100d0003600c00c1c1144030042003183c1c03010450b03800314204903011209201c41005020240c0304c1c10700c641c03104103010b41c48140c000d0030300f07000c000e1a18154030301d13101c2004414806e50b001070384c07008024611000110307000803040c0c079500d04c08020f081090f0265020f6664100d090101d004820707140900c2800c032130032303581003042c110040310340502d4100d20110b105800121052586030f000341503069401e03d0082c1115503141c0400b11142040d40301d1041d01e030042d4008420441c0c0680d09015003155000141c024509120105100e80b4441c0078602040051084189151500c0071480c1d001e00c004003046502007952440074100500101280b690035152409180002440360960031803002c0601342c050003c0d46000780c445840444616880174071303004c005082 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 772738120 1250 772736870 772736891
    0x803150d050d0c1b081b06090316030519080307032d09050d0201230a090c0902090901051e011d0409030203031e010e06040b0d05100626060415 63
    0x308094007241c1c0040e202c10700c0e00ca0440c1090445115400006400411044e6040c0581c004c0450601002480d800a00c1c20714000c1000040302802403070b0503190103200c0d4840c034410f266401c0e44510112405074040d141030444c24a02041d00300a20003028000c41c00400200307031042d100368030000805201000144c17800f4507411140341070441c0507041f081c0d0527450742c0c041f00600000348014503080c10300780000c0080b40400a00180604003104e059000d9000301070001e1961001904000c030069845078000381015107a5140000a40040000c14003c0c0c00480002c21a8200300703100f240c146000460101e10003448200455158800f1349220240da40402c400700340701d84070f42c000c841000340300f80c009d10740360328103c040401c00c8402c0450010140a0100041280b50640c1040075001a0140c801103001d8444001081352142440c00090491007102c80c010f41c0c114965000c802611b800755292001000710002040321120030f14100400c0b500a070b004140000c45221f2280d41c0300540c1600842c0c80707082e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 772739370 1250 772738120 772738123
    0xc062027090c1b03032e050a06111605011b060e0604050705100f0807050c03120f07090f0f09020304050f01061401030506030a0b07360806090a0803150d05 68
    0x10b4454010102c404100816400c0d207405001030740841d07000c0114114509144031b109012011281e030084029007090045801d035111145002805000d010440021f640e13020041042c1140301c400344030b5009103a904d000304500741010401f00e420595a83d080703d4021607034a030403201d101404580b002c3d80c0d05c50705003e480b01401114403580c0190302618800e8905004c0c07000d51030309202e4030020003014a40c02d100c129000381201c0c1c0c0050032403500540f41d8401d028071b43d1030b61144e902d03400789080c006820861001a01c4101d1441416181e40310b01034143d54851103809050b80380100040d08441d00c1003803201ca0007560280d40d00038000e0040b6001d641020b52002c3c21580c0e190000d48800044d1080380d0102d58160050a8002400341c3c0140030320425500c900c2401310b0050024410455041c031040c5802c5544081c80f5050760740c108164042940000c001d14000e41c1d14402d07060385001d100c0000b0710384c0e5408a000c6580681004081d0315540d182c51504040300c1405002e0b076407140c90030b80c1c0107012410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 772740620 1250 772739370 772739389
    0x23030a050105010501092c1825080a05030d020a03020418060609050f03060a0f0213060e030105010b0a0206041205070602030c13170a031214070c062027 67
    0x36000000d55541004001842d0454070780026000b240c0c0c0d0382c1000f1503603982400c0700301030841400c16620140c444821889000c603501a8035480e5105205002d003c03a5042000d080640c003640d40209585643e0f19052901d605180c83c000d046a00184250f481e58015900100000070301883c0042c545070703c0d1404640070310401c120322249c0640d954401d000454005200b40041d12085510880c5400c4000c00259130b04801814421b00d2900c400ca0241d072144590181d904406040303410a01540d1181c400a15140c10115050310035801c0100008080d07078103404650076401c00354060300c210341c0c070317511814030840070150721104000c010010b4001040c203620246d1b0040342e4400a850341c038910415108240718641d004503001000c81000081c04080024580803c41da0600381105401542000c1c0b5004040310103995510840481c108149140c0c00244481003a01c91542040080d8000b110504a600300300481c044c3d0072410002d5604007561040c1010041652015001d400c40003075012508546 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 772741870 1250 772740620 772740623
    0x10c1505011d0603010902090103060914030a261510050c10050a0b030d0e0411130803070c06030c0c0b0c1303051b01231b0105041a01051923030a 64
    0x6800b40c03250700c0403410504064120708124020b0080d0000c6e0b80004030a49010310000307000580d2507e00310200000034004500400383c030300a90361079900444002d40401441042c80440b020125801c020030803040403c039001d050780c00000742d0444d036a01e081c480140c81107907010041c06400e02140c00700100c2081401200121250013040d941003031744444064a0442c040070740b10b40c008030456400e13294007002d0f01c1c4c52003e0407100441c1c000042e86d03015444d8402e0030035010a00102003008241141d000005040301ca02c280d089990b155600d0710120216010881000700240450440300b000c41c03e042111900804e04140051070700d54482c000b03e10313130845644202e6180e0801c3c0903c9510f80b101e1400b4030807280080c01d1800c0c00e11400408402004107054903044044c401041c030b50300c06107807181c0980c0059000c6000300002e040c1802d00201042d08542110602002e01c8004200d40c104441081c08480c00c5481c650300f85401d00045007100d40d0140302d0002030340c00c2502e1102c5159400c000164859 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 772743120 1250 772741870 772741889
    0xd050f011d06160e010909021207090f0308070b040c171c020d020a08070f0f0c230d02101404090e0d080c0d0c020c0604090f0614010e010c150501 64
    0x640308250300c014814000700c141d020326045001000031110080c00a180400503500d010307202d1140800050350580299001498414404a4180761804807401c1c2d0318040c0344103456501526607980349466592696000007000d0030801d208407000581c1c821403054109100381b400b1203000d92540a01440201103c90403209a4040c8120381c0006403400c07660701200c251880038055640c5801e6001c2c1da513440d01d9100810500000030100d0074840c11410018000e40d201508841d5009d05040c03040942d4920300235001c00c2c0001000780346c00c4110301d460a0324100d10207020710855506980801c100b40070714025040900907681188a04a1400b400810140450000010720307083d40f0102d00346000c2e0000d82106c144038444003403101c591101c1c010313035088802030540031074682080301049017070216040465800600124002c00c0310070310f5400206c20110850001c10940359109000c5407138840710701c10303580807940044076500c1551160407007002d0309014419180c8142c4100071004c08890342644450050f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 772744370 1250 772743120 772743131
    0x3020105040b0a05093c07080d081b03060f060a030e0105010e0403020604080d060506030a060305100506220b06160308090c090c0318100c0e010801030b0606090d050f01 74
    0x20004880754180e045180d0003c2040545004151030350340d0000050071480900c4400c0c0107a4162289241d41c0c8864014038107242035040c070a204242c0c1c0c031030a07401101d146c3e028440110b20031a01c070705032040c892074860300341420301e10440c00c030b801c01580054042074002c500c00758801916111100100f8a0514507a40060300340440950542102c6041c3c104414016840c0140004241c0c0000d1090f0040d8000505555840c5040801c5005007002c1d1b01064104802008002c500701007540300204490150040d10f4004e102c50407503000f00c42080b61150341c040c2c20900c40c0d241c042c18030f5040040c00b0041003030005040d80e0f0300380040c0b001d801118a4200d442c078403006103800c140c0d104800030780001d60079000304200c203002800200d58800061003c070314007602200061030341c08400f2170307542c01c0c1d005030041e10501315a54450740094000c420411020030380704000c5c1c035495481802064101c07500581c1c110740c0740e1038886c10002141c3c0010040c5510a92400c00280410f8042c03108685001c101d0000260 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 772745620 1250 772744370 772744373
    0x1109041b031218050307060e120f06010302041b120c02070305011802030d0801120308041e2a0302010914060426120a020a030806030f03040303030b0906041b0f03180302010504 77
    0x107060204102220b18180d0720f40b08111607100018540c05071400d60905101d60034403075000c51580103203007191613098884d5951a000c00c1c08007040c0d1905882c0292000e00c410620041b07804604d508115a100008030840303450b224061040e404018040b04510603034465542d25181c031070039102d4031301d00150f005076034a24510031840d04214580c201007603030405500310741c91b240385040703250307011400079040c0402c0c000010100000140100307280d0004040b024100341a50602c14409035800740d101c006c42c104821040c420350100126101140d134160345044600741403c4101c6040e05451040680001041c0304c080381034060b1501010510950f4840480d066074058109490304071603050001c0c0f0180d041203000e10107640858011142174060404400340e40341d010100780780040442107a0024040880d01104250b419040003001c01402c40f201806519034100700700455200810006d48801c1e414407841500f4090b89110440701c466050014400030034908042100340a50f1040b00142d540d00304010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 772746870 1250 772745620 772745627
    0xf110310060c0506190204031712070905130905012a03060501030204050f0405061210020a03060b030f04031107031b0e250e06090402041203080c03041109041b0312 72
    0x401405940303004980c410403a224203441d094003909000c01c07000502c0176809450b016804940080d5170050800d550380d5103d5407008003580001c4012101c030b40a040100310f98911a00388242a24001001314000207480443d00001b008040d108854070354070b41d403503c049100142040e00359484842000001805101002412280543c10140c18144107000501880e11a10100803840780203540002d03484c0c65240000385008010007512005200d0062550603048464019001185454406200d041e031103500c41c20190000700c800d018403504a40006001c0f03481060a203400c1d4650805548107203440752104a1140941501e254200c0300014040060316061781c820755002915044100c0429041d4202003c01d80311100340204201000c0d9100019585000464514190082c4110b50384e03507940e43d011104010b900713826004110040c0009904411207012248102c0d070000781c161101e0601d408100e18018003400aa8458110030850074040192088a4003d1405a98259006003043e00c1c0103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 772748120 1250 772746870 772746901
    0x210a060e0d08180d0e180711301312051e01051623030f040204050c1810090902120115021f1a0d15110c0d0804060f1103 53
    0xfa415105800784031000710700e001c0303001c4c10780241d00d18201d60140d64540c00561703125018001d4011200086003070255003a04031030311210b0080890141c403003515604000300e80400f281c1641e0b058030341981c0b031a041c06804500040c2121942e543e0030502468490701389041a004146c01120301c1d0b071100e443c0310001c50035070904400c01d1f164039000303100c1c3e4130f802c60040403c1e4449000c0c400511441c1e0001401e40044035102542103005e1031021604d1f0b02c0c20f01110104100c041c2c600760300551402c0b0106040f650240221030403140701555009290002000380196000d0841200c0b0800c03001400204e00d03590940000d00704070701c090030100b00e154100420b451041801c181510290342c059800304110a03003c54001c3c000a03980e40300060f2000340c2410784640d034075001c600c4941c0319804503810703010402d5041142c0b003807a40940040240101180042c0c10900c82d42c42d80503070586c408440380000610038000640c1c0b00d0721540000c14110708803625074040c7d80000c003d10160000100030007003580c144641c030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 772749370 1250 772748120 772748131
    0x2106012706060e010c080408010e0a0204060f030c0e0408070f050f0708030301050a03030e0301020c01020a02030c07060903080423030706030b01080f070807051e03070f1b02210a060e0d08 82
    0x1000707841d240901c09048a04918805418004c0c02503c0708140581c6000307032001081f2101c000e000d08003800404546910406104900c01d5240c031030081680305a0305606030580703501c5a141d4004908241105e468000018001c49800390204030050006090707001c2e104400d48168000c00d001229a0107031400c004203508091130795402800100322030755480107c1070440e83c150408003c0d18107400701182c0a0300c103101d10170684e0340c00018880402a8000010724014241c50103036004ca43d200c0308112941e04131440007402d80a0b0521050000450320b040310348081122030000500f509020010a0402040303500100111355205115241560490310305136210440e401070b0107043c901100c0c013030145100903100c0c0e0308000300400c1060800450081c3d0744840c15110325a03270786030318024100502600c9641c004000198100b020103242c0b80e15074540c0103056074002c3c0503138050020702c0a44030005c2000090301025104042484000c18141c0c481e05c401110080c02a007240064004040d0200a01820 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 772750620 1250 772749370 772749449
    0x2030c030d0e060d0902060c0303071805010c0201050d0932120a1808032712120a140d09050c10080f131401060f080c06040302210601 59
    0x8088407075208000302c0c400e10044452070b84071005100d01d4801007003003090013034000900149a0380d41030b0b4000301a521924556449025070f41d0010072813008282c451150501180850003240015070241002d0017090740203040c0020390404544841c0d201e86580480060340c01881c02c1d20481c0030461b002c0c000c1d844011900103040c00402800303100d1440c030480407a8070401c51031510040d00c25102c104040700814007201101c1e1182650b07075084801c5030f1614400303030404040e800002c3c2d1a0801e41a0040c6403281c40c4054101503003a04648001e65010740c80010401c03100c80c03100050784455001a1a415001420010720160140750075072501d4210650706115044c4410600030195102e07240303990100030100403210b070381c4414070040c010094950004003803111400302c0c0341c82041c0550040c0226480800454140d07a52004615220000340da07100760411820802880903040206030a40010082d8440d1031011100c4802c1a00f414405c0c1c211f244814001078031800b03400c004028005800c1584403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 772751870 1250 772750620 772750633
    0x80c1804054b0c0403080a03140105090601020d03050c0c0307050109020918030a03020904090206040312020724081012050a150510090c0306081b0102011a011b0602130f0302030c03 79
    0x5081031003000baa010b08440038040d14001502c000780b503000f5070b401150310600560b2141d03040c000181c0645513100360994600210030000a0900c0c081c00968041c072810707000340000381130460003180a00001012520801c90421420320200f80800c0104002d60280d400010652080e10422400001c043c081042d0b03034640301218500003d0103c00c4400d038504a003001070350340c080840410042e0120720f40c080e62020f00414000b080c05421683d1010f090110fa00395084aa2100003541c15000f0304c82c0c03440641040c0003401d045440c0140d001c2500031100c0706284602c542e0381c18a42d0380700700181508646540110010104000404800588107980d480d8140a2458400c091200c1240c0b54850070482c0d07900c0746070407135556009911147c0230b8103d6400f40c070310149000032911007180880c00c00a0041d840c0185282014038450290001072405070368034001f15401003011080404041000e65100e1743c02c00c0220410031414010328001c020007101c00c08642d00d98010142002c0c40040403602a40184 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 772753120 1250 772751870 772751971
    0x307180e06100b0a210603050c3c0603150a0b0c0a06050c07140120040302090708180708010f060605030f06041e06140f01020a03080c180405 62
    0x1e400c084140c0f4a5049195224440c100d800c0b41e00401d182000c01c040f0011445201014269802c2801941c0c0950101e841d202d100805000180e0301101f454482c0c0f0001c400071000490700c07000101c0c0340d40740302440d0130103c4900e000003176203542c001e0381c3c0c07181a6030400d01803101504229100c40000e080d0241224200b013146114a038580554041c01422282d0307032400100a18a01001d0350b10142c0c01c505405a15280b80b0038640c020900007184d4203e0303001c100401c0c601581614205e90a40303502820380b200c952210b150544d0240006820341c10148a442c140c222220380c01c0040d2001424004004106031514020320b800715400c0340c00a0040090070803c06c442c1061200c2c05036003051003030703400207100f0320b80851140034410500103015480d81400800a10300e00800c80070115400c04886103015aa88172005903a9200100306c000d0100d901000011030500c1704001a00f16403007902c40c40103514855200040031904100c9801c21a01c0a511032104080c3e0b80386080030721030820955240700907a05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 772754370 1250 772753120 772753141
    0x70305060106030c0c050118020406090605060d201204112e03060801140a050105040c0c0b06011704030c0b0702030c031c090b04150f1122050307180e06 67
    0x140070b0041403644542c800340040d0310074040b4100c010b800000030012400801640f100c1403800400c10707403041e0709240000c510115540b2640f4215107000f4003a500e84a080000d05c0c0181c4003955958550640040e0b01c8103441807420700910742c0302c864041c001440e290601c0c0410060341c2c4e4001aa00402c1d0038001c00402d8140e800041c4092805001d4400c44018203090880c09003800360009065942403400410881890f030031198020360f00304000307028136070321001488101e500348440a070000d007164070500086a4040d1129800c02018549510f95142c0d5207603000c003212056404a0002d0751041d101c1090013000640c03660000c5481c0b015600d00550301845503542d00074000a0306030081c405424105095040d0700901c3d100764008128507141c030b000d0421250368155540421505030400d0140b501c44840c0388203904c0c03c103110700503080c06d003000c0d019512003001650825829404000d28007096031303075082203500001d0070000c0c041081c1540d0224480191825542e58842552203c0c041c060031890b07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 772755620 1250 772754370 772754383
    0x605010206130f02031e0a05010f020702181510031a1915050717040305060f0105031e030714030301150305010e190e0a0605061305040503040302100207090c1707021902090a0f0e100e070305 83
    0x201094203507680c0721079400000301d15909044fd80c0c00600d81d824055102d41540200304540a542c0c05c0d0f4244100440a010f445209007425903000345071400e00340003201c021400d6401d20b0034036140079030401e41540d490486c101034076510004029001308040080150420a0503444500380214811035450517020a0f038402040000f0200080b241c80c1070340384040c0c208240c42c02d00da0803007404040d546030b1b00c000700d40b13990082c0191820100303e50030803c0380030302a001c0c5504a030040d03c640c0c0d200e0b0b5106000095000300506851100d50348a040104040c401040480380e89030003544001001c1c10031100b0018001d801c80000360842d42048104800700f1008416101260b8050301c400403180081c040480c10070b8aa50041c0c1c04c002c1c94051001450366114442d4100640a803a015155445100d01070382d9610303105090740401034040c03445100600b001c00c03859400400303030100410719481c0078042c04d064a50114100c080740c0c2c800014051485403500a150103607501d500a00221800c6071160340c1c8402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 772756870 1250 772755620 772755649
    0x9140f0a0209030a0c15080403020d0e010e031f0615120507110f1c05090f12030d060608060a0f030b0f071e050705010605010206130f02031e0a05010f020702 69
    0x15404005240340d05190112001200e00406440d020710380b524008030000c15501407022001e258021440056006500c900c1c000c0f1b0b0590000d1040500c0e004003216218646c054850400c00741d06200307401c0340c404001c140b1011035241074a28805000c5003283c030032a0095404280d40e1000c4041000ea07042d048a2001e518940d00d400c04112595140c60075a09204003291380f00041c443c83c81c9070207011070301003200c0503058901828039400c484013203404c882502170507004907030059247c4c852007140e251010b41c1c145000c403c0e505590800e03113203807001421100307103034001404200c18104010b168034050300d00d280607003042030310400002d0954540c0704110000400c40e020054001002c1140e03280100404044091070f1101c59503003030100c0c10000d00b25080761200300c40641c02e184000c00c0c00c0d800890258411014040c0c02d620400c0c02e500c400710702c600030060698140c0541c1a1140c180000418050888c01047c070090105d01101e1030814211600c1c40901564036105100402c0181e035a61108491302 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 772758120 1250 772756870 772756891
    0x9020d1b0e0d0b0408090a0609030303240b07210c051c0507030503150925020609030a050d1d01021306031416032a1103041203180906080102090a0914 66
    0x15139640c5066401d41c030030160255403090b400c080008626600004100c00d032807083d1b0381071010050855141c022900c003000e4100c0f80c540e4000092154010000140643c03034000c4684421028800200803c260005514076000858144c2d0007402d100301006491405c542e542ca44140ea11045d0300018107501030640f0046c2002000800b04883d4a900f01800b100004010014255401d01040c98811009465039000c1f0640c0c5181010880c0c07400450013034030809403203014503d400810a82220240e022240a07024103076541801c1d510225803482e8104460261000103907500b0b80391844510b48900c0e07078040e900309418990020041600100070769040021180250500c5a0f01ca000760094840403640d5195020f07810221403411040c1d00740fa444030380460b25145030429124104503142c1c8039074090803010781c0102c04035500003445807124004e60441d8558582c0101e81f60700c900d800380c03001640820b00c1603401003407080c05032070040c90040091100d4030007000b58840560030b80024010041120000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 772759370 1250 772758120 772758143
    0x7080c04090212100f0b1f0e0301060e010e07030e12220b07030305061003060e04020904050f0d1d010e01020c09070302090a0b13080c0d12020709020d1b0e0d 69
    0x110344520780d0361407481c021601511a0140b2100b0100c000342030118041702c1e582c0c2088403100550070f10880400c403c0c0018800040d0100c01e07048262000144503492035015940c801c00003a680d010300c000d00e406001e01840f0703154541045000141640c44d034800d0a06641c00011858100c07182d800e00700d0300032040c00342c864204a0380d5400c04007886c0c030055102d4500c1d210002440702c109981a400b86120700b804549204c1c40c0300300c41c542102110300c13a0198150134114000803c0c0549440c1643d603610510030000c46462084842c001810902503151600116150810780c032030300d021100079000d005a003840d194108211000000355610040c1c84428001c2c903007100405c5181c0e00c250100c880030800503000e190b0301650b49070401c10740e611120003d140b0710410170000c110300b00301140c0303d4880700c0020994960715040b51036082c2c1810707a4034502e40a51064403400200460580050f141c2c5507451080002c41c1c1b10041c2020804030010b201d6a41000b50b6012000c0c420381e6411041c040c516001903c5408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 772760620 1250 772759370 772759373
    0x1020c031902150d0c030606090f03030309050115060819090c17070503060115021606170c04120602070b09210c120409050912070812071b140f07080c0409 68
    0x300d89007500003440100c900042540a860700313174020484603042503608000303169a0340c0b022104c100507400340c0c5641e0180a0700810200341321307030058002e103805540001140e1008042c00082035000b80d119001080c400300c01c01000c071800c8e844603004034180a0f0700380f00b503a800d651503a1aa03081c5009198401803c00c6a401310041e041140e00050034018003101d12558481c0d42030b08a00405225010040c407a40c440c0901c01d218400302c4108072034a40c3c85948041d0340442c2100c4451000a124010440040c0000640c100796244504441d40c014180182d031a4018100300b428008000c1000007036601000803031503940a411150541d1042d1030403901c1d00e40c05142c028a0800e0b4102034448031003000031074003144a00b000d03440103005011076400c80b80029042403000d6050f0081c1c40026010303907020f0041070f0091825103d8680e201841d450074586040e2210f0403044030b09035001d02615407000f110115440a04100400680c000744000103029240c503244007242e5442c8402d03003041c012911441c01c1030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 772761870 1250 772760620 772760629
    0x1150b030106050a21050c0c010c051c09080d11090a0801050603061f0e1009200a0e010302090d120e040b2b080a0203030907060302190309080c16030b0601020c031902 73
    0x414005c00150500450921107040801030300680b0500c61075510300a503d17200e2074001d0301150080168400c910390034299160703207403005100481041e25100d03420086202c1c0f00c6064892821903481e550f0500f501c84070a1402d20103224002c5d08481c40c142c1c0b5060038851250790016015600841211a40714a00210100040c1604003640030201c080c2d410414042c0c2c880c4041250825901c0450081003c0440d4100940c0840350303840031110103000c200981044c0c58800d111044c5400010704025140201c1034001c1044413810000907600b00c8841b100a5411171344c0036096898240782203600f030100f0546000015107807401c40c1160425129030744610519415420a0206c90a030040e4406032140c00c003a0000c2d45070380c82101c856816006044010603914040c0c070a81c0d4240c9044e00c40f4943e030207200f21040e402812469810723140100d06008410207400108460403000a0000c2007102541c41d41c548031444a01c05001e0300e0541d00110a9116103440010700003608540360900205008224000b14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 772763120 1250 772761870 772761917
    0x20904020c010921090303031a0909030909100609050906151b0c03190b071103130f0e010302030c100c0b010906030b06010309081803030904060801150b030106050a 72
    0x11500240003041d8003901e20010360050340d41c20b000b48100e218a80900a40d4511071001401003800b090703e4400900100c0e02ca54842601001d0081641e40c00b0310200c80040c0c0c0219089801004690002171241c0070760074590100340c2c0101001070010100c1d410003001501812031409964006c50300c0100046a6684861026919a1038480303015540c0040ca08482e02003021401075184034481c10f248c010301403c0c001900c0e0012072101c03c180c1050340143ea50803500103005007400d001c201904a041090050907c010f24040c0000788118640528098450426215039484403000c404440f00400150301c000c680078440910451300b100c1c40780d01c40001569000c084000180c01070a00310004103840b07403182d211800f920700a0702e140c00144c0d181001141615903202008002407014404c240030244200da805001c8c6000806990904d9081c0d0041000c40d01154040d062036911840d0171079008024000071406024035080861540d8182100075085108a03148582001803405020865a4004015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 772764370 1250 772763120 772763137
    0xc05040b030c09030f0a0218090c091008150105060f070c1e0e0a0513140c0301050406060f050d050c060310050603190c050a0c14030c030c0a26160602 66
    0x141c0301c1c200050b00000542012210343e0003031180c40145000e83c5400921541429402000b140300b01160130968080c002c0b0203441c02a44e48100d400219965aa048402e84a2115440c540a010707142007243ca10b09010f6030b150240c013460351001842550bd481d4112506102200c0400c2c1e6130311001d20f0001003041076a40310b80105041c03008248020300101c49054201c660143ca010481c0e102e151005084400c20342e072510125031709111500c001251204628194206901070320030548152010034207407501101c046034203544d105401d1200c0800c80d2190405440700740c80c4168414242e0b551175685403062141c4038400d0b0404030008440481240380355025060281c20310ba03d80c2841d01d02031119404171071600e0495401c0c8440f0500c910303c5801950b141044503903e20180070b125440304118a0860100c90241e03000403c41580c0f0711400301b005206a04a80c1e0060541c011682000b181d80b13049880d00c4600000c50341005031001c6079440603a40803484100c0e01084518061a2401c000d10a0450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 772765620 1250 772764370 772764389
    0xa17030313032c04050c280219050f160605040e10050d0f0303060501031e11120f1602150f061201060f0f0905010819110a0e07031d0c01030c0504 64
    0x40200002c0300341001e42a80100c15a01800140c071122403900107030054a45132001c440c0b42c0392110205880c83c200e00340050100f07005a072740f202d29010004c065588014000c1c1c0d030aa2105205107a6008208100e4038005a2243e0358003a071818100020894415403066031030340c3c0c105a02040108094504040c01410000c0c01c80030285810f240c000c8100ba1040c8055001ca860141c001a032035020340100090000c0040c0f41481038009903809030002c1850500c1080300d46002e110f1121003002e0b01901b02e011342150a915803d500d48051420445155100828219004692401a1b01d54441c00315138020943c1011100705903142801700c4c402045844003128a5803c140000500c5d5000c56405016108603a00b181c0d00e041d00c44d0401400d40f6000e110715680f96001d803c0c41112080e1000d140c2803107901c04c01706222030b9441d010000b40100381c02c0d085038102072010300c28040201d0305403148110354030101d0041107240900045a640710703813240301014189074680051100d07180c070520884028210403407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 772766870 1250 772765620 772765667
    0x601060e010f02010b06210a11040b0c100905060402030f01091a04140114010602010e010605030c06070c0b0f091e0d12090e1620030d11040909110a1703031303 70
    0x820f1001e80047c000c1c00d104044080300840d189060501900c0052184144440d2a0500d46407800702540d200040104d1940901c40031401d08920340c0c054980000d01480040c542c1e0b040c03d004044c1802d10804580380320340e2400104100042d104030b13140940803800c410b0203a081ea5142001100701254a01d086a03a510701a41d070403250f060684228103031000d039802001400c0c44824420b0803901a4024070354550b00150504010b4074150004000091007005580c00140d660704025203150050704094040c00d90100d2582e400e400d24030340101e0a43c0400f0f03061610325607200c02141e1b02d0035030a2000f40098000b90b9543c0705050050039200000c221001d0021034500c1c02d041a801c440d2a0b0f003000b1000540001c1c45544442e441c0c1c0c0e603800d00401e551000d540b402c82220411402004800c1849000740020b003c00610080d4520400341c049015030290390501e0300701c0c0200440003489800074011040040a4171044072070000551754440140941d02030001200d080c1030320409540b07980e542c00d101280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 772768120 1250 772766870 772766887
    0x9170a03140106090b07060b1c0609120302070b070e0103020c161406041508070e0904030e040b040509030d020d09050a080a08010e0115050711030d0e030f0601060e010f02010b06 78
    0x168001d0301011104520406140d8840600f2241214144112805a4403e210034000302d045540186072440b0014081e00114020b250007001e100c40c03030300c0180e8400d5500c4800f0014000d098221902d1a60f55180c11440c0150300e58500c04440c0c2c0150400342044640c40d032102ca541d00960484d4144115801156110425030f1015003040d180b501a00e100400c1c4051141c034182005400c1d2002c1d941e4140344a0161001c4070000c6505400c000c101c6020090684a004a11b40714074a00d1400b507802580e8a56181d00c1d41002d01080d02c42d14001140503178684020040e1001c004070688900034401007000d07a40e4072060491001030302034244007030104d0107001010803c02060b02d0007014030690036111007000d81e90340e020b4080c0c82d001c24490042841415884803200310300c100c0007800c0c031b02d00c68401c0c1003040d0410700102e407a25078480303500350108105d503071880a54078040210b1681035008000901540d81800d40050021500000701c40c1170151421019549038000c0d001000305003c080c7c146038445044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 772769370 1250 772768120 772768127
    0xc0206030a0917071e0515151212030c070c05030304060503071206030c0e0a02070c08011a041b11100c0e040c0c1a070201060f0308040518011809170a 66
    0x9002c400c032a80107062468046104000c801d58841981207000702c0d040c038810308a611000c500f620002c407050b008800180ca11449038040141c010420000c0c00b0114640d18014003103220840c148401d8168800060a01c180d0284000c80b58804c0080300312a03107a603118900014240100d41000764513000215010035034650003000740d80b20711110759540c07070b003200c1c040041c000300e80042c0030240c00c140d40c0380c00910004c00280766003600040d40300030040c580061900c83c10080c1003945c0050101d651544402c1c8141c880c180711210b8210000c0702c04000c00221400c10700911400e40b4481c0c401e00941c425800c401c803038180441074080317003d000c0511a03800011002400076221031010f43c4120324142140042c45d00c06c04514200c960b000301c2d419601c1180c510fa081001c1c5005110388219034940b200030030b058280702c41000041d23204504541d01c441c2000c00300142405014581e07600d156000b0010004030f02ca0540790040346e56240d4000903100700506040383c5c80340c921a0452000c25000035182101a032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 772770620 1250 772769370 772769381
    0x3060b04080d0305010506030f0115050f07030314010803040e0a0504061803080103021906080403030b0307170f1b0a031104060f0e040501050c0901021209121603031e09060c02010c0206030a 83
    0x540e0fa034100010fa8940042002c2400191140f010341a031000040c00580c10301128405c1c0e480e02030620500f492010030400030280d008840c01c44c000b98440d0084007841e0b00d101c0450740900140c0d030140d403c050a000c500004190002d0280c65036540341c0e070202c3c052001076444124050061680d00d100c101c400e003800781c60021b01b840207c1c0500c034403112001c14440c501c1111000c1d50015624141c05484a450807030162600b0400385038507004011000403200152120a070140ca80030000d001805092140b03103081290711441060810071810407c0c03031554540040c581920780c0800c180842840c002d0104000300400c0c1c000c03004210341d039280031540840000d0401d202e640314200a015541c0e41140c2020342d4090916041d02581c40820b038514403c4083c40034024118020344442c651f4650360300414a0700c06016824884081040014414140d1068011050004400c1d4204a4220f0f1100c0200480b981703100e14410044000000000c40e1720076070307005c000c0315001441c0b08e4880c1000c0441d10010034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 772771870 1250 772770620 772770643
    0x2090f010e0a060e0610200106030b0f060f1003020f0d09021e030c0f1203070614010806090307060f021b0123060a05042f030103120809071503060b0408 67
    0x248030a0002e545501540120015111201c2c400c03000c07521114140515540d1618005e010b101d00031081011100c281c858051240c03401070000301d101441d5092600c0c5650707000e015210002840b100300406034407400a082e0b1409000e81e42c4490344442281c00704e00034021003c0ca1400031400240300400c04072290010004140200c654804544001c0c0c1501603200d142d6103601c1e05a0040d009948041c501980901c1000e8406400c03e041d0904d110900e50540e0300211003203038290f03514084c044100d42482c240c180034065150081c00c0504046a0480c1c1d41d0142c03000c01890a6203a100300c00801820fa015101a4130400071125000f04201007000d000e4840342005200403000f41c6000008565103098103801840e015004601d00307400c2c101404082c0c080c0590708420303084100c4070072514140340103040c0c0650444511041d140d50661402e41e100004584050702009280300c1403192008001c5841c0e8200c2c1c03c102c05040071404800000d070003030440c9a20082050360040760008945202042541445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 772773120 1250 772771870 772771889
    0x3020f072f0d0804140102032134050d0608030309280f020d11101e0504050f0d11031002091504080303061e030d05070c080a12081003140a14010c05070b1302090f01 72
    0x4010558ac2003452000c0b0380d0250340c1c82c0da44a42d0004620300581c01040d80c119005400310710161151490303072030f55005a510f82c40303d6100a051421001d001a2070b1801c2400310440e0032880756803610f42c03800a01c205140640705cac14006401c1c0c0c0030001031504001050401600f241c8401d1100d00e405440300c9802d03030302e0030311088018102d184141d100307404840a40310300804006807644c020090000d003041d81c402c101d40300c030340d41d040a5031542e4040166581005040c4805652818041c00b0300000c4606d50581108520302404148a02c0601106913a07000c2c0c000c6c5c540c035860410483d41c95420300352403c004c81e0140107a00380c0c0d040d00d03503012000b040718902490340e00b455990341c2c150175580c03190301cec01c00607186a4010910342000740c89103240c03d40180300c2030050030001d516601c807070b125000400091251a40032905a01c00c01507460b50722031440350b220000300f01010004034041e100340b24070240188603001500c000342e169400e14094040302038026084043c070703142440d410041c0c2c05081c081c20040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 772774370 1250 772773120 772773151
    0x30b040507080702071e080102040e0702240408030603150a0b090108060402090103120210060b0c150420010507120228020a030303020f072f0d08041401020321 70
    0xe000b0061240561036960081190501d0002401c5050444440c803c406403808640018100002d001810240150040300120b41c1030800c0083e1030009800c04050180384c40d44078071445510030028469100f030f04103041980d2540c41e4000681006040c4055440b1604100c2c10b0000102e020b501a403181038003507a4100260b602c8a00d007036135540080310002d5102a0000042c400588188481e00420410f401100d2414042d05010350984a154110420080021440c82c072901c0341044900113100c1c107290007140504150700c88041025941f00360780484c44814034000460313442003040390409a080f000f8034200010559000b03446196000321316442c0110901e95064004210b807444840301d600800c000302d01c62070355400360080d400220020340c0700340090044d40301085034141d4050b90302070401d0200c1c90051007902e5140c3d568103114802130003510400340c0900020100030403542503410111002501511200040b4954403031448501c0100c608102600b43c040f46448a4a001d1070003607011012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 772775620 1250 772774370 772774381
    0xa0b0c031504020f0d230f040227070e150409050f090f030d0507030b0306040c0611010b0607021e120a02010f03050702031603270e07020d05071205070f03030b0405 72
    0x10f900800c81100c8507003130b0400101c0801c01d90f95200300f8048106588030a0f030f940311810308200f84001240c000c04903616507800c1004516040c04180c00d0032061400c4002c44e05014a000310400e0801040701040c8211011000304669800044d008403000480c1003ea80d1500d403000c05014000503106141800760b0340c00412001d90380800c201c0075011280b0f0046042203501c0c11114080d02010f480350013031541c6c41d5048004d50314244202445140a05082010b40e45000001401390348400828141c5900d80418482d19654080403504181c2e011140110b400e00f9403150264407000380390701581c0c0241d13852001000e01c4030208584280034003d03282c0c80d1094610358815030503500f04440e098016001040603072441e2008122018409000385810030001c404c4c1c0511442103200200c00340c040b020000b1040024414015411f58000743d948080e00c032321420500090001c0c059117200401c114408100007516034400d005503030026030401e00c500c4645890b400d01400a02c10510348500860900c0c000a2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 772776870 1250 772775620 772775629
    0xf0301060b0d020915030717010e100501110118030924210603080f040f0b04050603070503091c0c06140402030c040b0114030403020c03070f060e01110a0b0c0315 71
    0x42180c452407030321440c0110b004000002503021500295104000d8814440410302c0280610701c07031035503038170365600300107c4001c46184000145e2144003c0794118007005a070284051551013114020f02306100c00c117855850b583e000d0402004012a007a5581c8202070506601c04100003c44900340c05e0003c05c0e011b40720b07550f0940003503030a424010030682000c41220303c01c0080481600710a6040002d81f140e1242e0b108459584a1810001c0c025070101d0184820005540813500800c0800e01a525091820000c50300b1800010701d0101400340200c000781c00e6050600a0301040c9d442c550440c20181d060020240080030300000c151119841d11040581013218103400e07030b0040350024000c00030030621408200280103140d0080e41044801008a01416610760255002c0c511a80203070028000b0340e000c0c189803c5080e0b00c9400600342c0c40c5010400c6079000850001840c5003849c1c412100751800300e102d486c0c12001c0d400201106040030410100518541c0658041c075820625021038000910412 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 772778120 1250 772776870 772776881
    0x2100f0807030b01080c0c0c031605041503050a020d02120609060a0606020c010c060f1d0309041b090905060621010e01050d08090603040c0f06030c080a05280f0c09050f0301 76
    0xf980402d1a40c0040f6061801d1003014211a40c41d036400c442000c45004042030a25064a48924034194040303010300039860b141c02040d14416101c0e2030701c607005255450351a980d01c0407060290003800d400e4008000c1d510f03044c006c101c4615048080314000d05148002c159218001c407a01d2041515140011602c20320215550000d5201695240000d000d42d031035002c014041080344030035a99031000e0303a520003014107034003203e030303c804001541d01e40c036115041c0002d4907031840810702d10b01d440900303400310309400a1844080d038501d0900002d90756030310350200d240f0344100f00d400410651a0351070151030480f12111181602c080c6121a1400c2e6a207209006e455561640014140e8800780041c0740d141c1400310246130700c540280307a1400f0059541d4402c0c02d11203110341011002949405012402c25048007003e60050040d010070441d901d400c040300c081c0000303444110800c1740800f001860800e6416004540303507540000d4108074020b0340ca800a810030b06a40700b5a4040d20070613941c81c54a25040c4142c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 772779370 1250 772778120 772778141
    0x30f09080d0e0f01090c0f14060f0a2109020406050102060603070b090310020a0c060b060711130906020309070806010b0708031609091b120b100e0d02100f080703 71
    0x6607050030700e5a85140042d0548030071040a0b84200b1445480c0c0c1c14090085e020b5081c0106624808903040007440c050003460781d00f0a81d0740400134070341c408107500d5003c202d400e4070031355401481d281d10400c0c20440e0b031185c0106400e041d8403c1005c060a000c1c1d10b59002603400c5200320b40410100d9529001640c8a40c81181c0c0c0ca64990840081044141d01301c40007800a40e40040c00e68800990302180f00c0d049030071001d105d01c00904050350b410100169031041c1d02380c80200312202810714a840c0d58400f4a4811156220b010311a071006041902c0aa83c0001c0013607940f100d42503403a49881070045a496a151061207520301c60030000142008909046840654001d4103852a542d150140441d51646034040b40003080064600003d06010728032610015001003400c410744080311480003440c6084403410820a945086103203411b540e9215020340380780249040c00f8031509402c200144e0308034001d08019400440d411080f1503081d9005102c0340001c00b05842c0d6001d2070300c4600044044032000d820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 772780620 1250 772779370 772779383
    0x905041a01120f140f010e1311100302070b01080d17040b0406091b0b12071d0f040207020a0f060206181b040603060e0c03070506130b130b07030f030f09 67
    0x11018141081d6400c11040028891000b040c40081850748a200e000d084038100100742e054401800b03801949487e10b904880c1071440350b005292151504900c80303403104200e5204651450b41c1071042e84c06030f01a81c0d00c090b0071480e55030300b0b0f69580d40340949a4111010780340c0001c91004c0803030034040c090344405004d070340c10010b42032055440d41c0d540d0340102000c110a0b609014040c0700c1590142c0c1141e0300301c020301741d44040e40340c81e5110202e103204081c0300505074606200c1c0d100307141c401042905248860070f64007102c540340500c0520000c075000348210000070350071009180000c114034a00084010486d01c03140d08071042c59498030500c0030416281d41c020181d54000c2d00210010041c0450307a60600c540c01040003802a649075954811190b501084c410141c001c0c41070101945024441b40c0014041510039610304403100000030110030842c060528403800200e86c5088580e08270300300d800600b028090266130340d41c582c1409080d20044461090000e4140001c088500310b050094100c0d05d0340c00301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 772781870 1250 772780620 772780637
    0xf02040e041221140105150a0305062d090a0902060403080c1e06070207272708030f01080304030312020d1b170108120304020105160f030905041a01 65
    0x585040650054101e20b404010143e104002c0d0159010501c10180d20f100c40005840b0124954820200205900c814855015242201007040290045600051003807030001816681d40700001c03080350700050894a06c4000480c41020744014609102c840c000032280304082d6070755400d920060b00d0001400030340145050000300001824200540507690f91350056444031002d111780040705100f8180200e1007a40301c0c00078001c4041d018040f500c003400340c110b1031203030049000d10007040481d801c00c3c090072801c0d81c40c208010030140c002000c481c00e007100c1c10303005082205410900015041034414034070040800d800010102c5000003218100d03541070300c0340801c031f90700004000000e401c0300d5400348029885d644d4a441500c00c0e07406680751200103858801c0b0300411521691046001600412030f02c1d0302501c0078548031044042079a900580c2441c00e81e50342c0c0c0440e10b0b0024803000c0401c00400c0c08084510070000c0580181d0301101352041543c08009050891803080209100c8610f86400f0a001d00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 772783120 1250 772781870 772781873
    0x90f0f03130f0f0b030a020409050a1a0f0f1c0803090609071502100b010309051f0c1d0f010504030c08030a14030f01030312060b030a05090601050901030b01090203221101030f02040e04 81
    0x18006543d001c41b80910050400d81d8541280c815140c04803406080d02c2d0344e0704a41c2c540310030003c0c2d6050b5401c80070780d4200c0e41c58440402140d8224203000c0d03410b20480280300151014a0800502504940c2c4581d010b6181d092850106a690780c0507644081d50b80104d1501254003c1054071400245540d07a00078285100340803074220040c8130121400341015140d0b580e103030104404101c0101c8448030108103e103072802303810a2008940d40348d01c1c11010411040c5101003c082d0b00b90b40700894000071200c2d00760700c4071070360700595a41c851603000829418640c000016240008030160050203416103841e130400d1000d21555800d807008449804004c1704d101c0042c13002c20b104914485201480c410001003c81d220750201c007054000f158070702c00c07042d02c2c1d4080152081040c8030781130040400b41d031125401c0d411581e504100b10414020314440c140d011000903100092200c10300d492281050340c103000f0b0300460030042507264440000361301180c2041c2004501c10f50078800c503801c849021544114a031a103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 772784370 1250 772783120 772783139
    0x3030f0d0510081c0206060109080304170c13150f06021b0406090603050724090b0703030b090c0d1104230d0501021b0d020712020108090f0f03130f0f 66
    0x140140101000c140c0010640d0303031040013062111041032a01400440300c00b88001e00d400002041c090400c0700e602020490782da4000141c8090750201807014680d0412030b01010714044508200580c0311142e40103800060741141d00c04860b000c0841d44510381c0685170105120130b0788891141c01d0051f13200c00b00fa429403110841c00f44840d0f1034000c2c8040380c02039840e10b0900548255400641d800d0304000320410040030140003020041e00400d100c103040d1101d080c0060265000307803191030304020001075031000305440303540311184017080248504128107003500c0200c1c954001d04100354810717182840d45808043d0307103801d4130103d42c6080c0e001203030143c0c115401083c90480c09940d80e000f92507104120f00240080c0007030035110803a200f4030482640c691003920718101480316160155000208244000410411007036080754080c00e082103140c48800616240298840c002c1d075142c040e401441000c43c901100900c0d0115120151204d150344525040c00c03c08020b1154150000a100040002006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 772785620 1250 772784370 772784381
    0xc0509100e0712110c0106090b0306041b031a09010b010e1c02010507060515011e0f050c03090a0905241003051b04030c0302091e010e0a1e0f0b03030f0d 67
    0x40791414800c0b52480b01d82d0030054419011041603412008103030174403c1c8909201d40030080000c0a4103002940000300401d07182c00000e44054041d40c001603d03540c1c0c00c24070b4010740c8000c60748038024066142c1c03001020003003802d003541c0c0588203500340003c82c1003e61045000303040242d001025150080384002e40d0001440003c7e004906100061101d000411800d1107030754856510302d0701121101d0390039070005266000741400c804031010f800304c7d02d5090552041403020148002d013002c41e5288081c4045910314015507101a03444030000e0004204200e20b07410160040e00d101c1800d940405000700e81d20703840107000761100e421180303204040960070b120750469604051200c551944d0700d810400b004c1c100350300c20381060700d440b60104820821428070b02801507109003412480b40c1d190101f05032083e140f40f010710604c10b0f41c0780b0038004245400345a501010510030721080a2400b18100c084003001703003020154421400f0326000b00c1c03003124240882100c2c0584a6840d245103402ea400c10394800510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 772786870 1250 772785620 772785631
    0x150907020109050312040201080708010609090c2c19060206060907050912031201140d02041a031f050a02040810090c050a0603140c0c030a0e2701030c0509100e 70
    0x64035001c619020410030b01c01080b51030041a00a0174900d014000503100f008041d010004101c04c0d2401004030741d5000c119102502c0c04003001142a007042d0314125005400d0b40e00701001c06480148a0000c44145020301c070413034005551003190980c03805c00075802080c0c00e101d01d01c05070b000b0b18001401c030700c2e00003040342d848059810500d0512001c0000700c1c4803a100014040c68a50000410b007010b90780550f20f1500508660303859440d055030b0480400c5410300071a500a01958a90b000b40d103200142d07035209a203900010b800c940d00350070170b40000e000282003082c210030700354500004139000170380354000c42e41034803103140091400501000c090002402c0c6881c041e502c007a9440c601103101d544058040008010700d55000c1030400d4108449140144094a41704485c0310801503403820035808000d07103000080a04145003e0300080002c80c1c24003642485040502c00c907901c00020003180c1800e001e040e2030043c1c0003882920b85800500c0b0580b401500c69040049500b8010005400c4104c0c1e11503000c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 772788120 1250 772786870 772786873
    0x3120904110c15071803030c0b1e07030c03140408041a270f0d0c052b0c1d0f010909080913020309010c0819021e0a0504090f020315090702 61
    0x6102849481c01d10380c42446a0f4803850340e603c00d108a02d41d000d0f4641d040c00381681c00b030f94501c0b03242d540c1c050055040d0070300040160327844800254406036145240d841c2c690640c04412a0303840e05401c001d00400006451802003450440341c0d09080000e0005940300340e078030040142c90b00741490703066440d0484c250240c811004003045028000e8210482001900003040e401ca0401148074040015460364402500d026071038444041000c076040f5a42e420031184291581c1081c2050f01c84100c0e10110f03843e4521074404e00100f40681000078101c419012204040b00c0c00010400c03103025581003050595909000310b42403030043c41ba88109030b0002d002c05200d185954500113480e404681b152001c10080d10169501004001103680203028200b01c4141503e012140c40c641000b00004c03068210700340484041d270216003680181c500d00701d100c1809070294201074803981a020000e00b280d00078011841a40c0c2011040000d80034a802070320f000e50500e40050841c1d01d010011310110314001800f00046 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 772789370 1250 772788120 772788127
    0x30a08090717060402040f02070b07030509100e03070c0e07050a050906071a0402130b0108130204090c030f1b080d0f0e040e06010f0e04030206181203010902180312090411 75
    0x100501040d910b00401c403290060010b51411380104421601181c0c0c550411070b004020520005a6401c01c20781d003d001401c00140c03075100c50444174540719050b8411104c4d50b0ae00034644840080c0040500070151003120700c40d000b0350b10744441c94102442646d0010110b07005101460203a80668064001241d000d8076282c180801c5443c0d43c0c03c0b20b201a4001800e01d4032031000d01056060a01681c0200803240d4820b01940c8281c1c40002c0c5042c10051451140034212441c1c4821980d0301e0300075245668006003000342c11600c2e401c007800a61001c6000300ea6100c001d01c907034101460007101038000c807441d10016044921152409407280104195030301d08005051b6032808490303456208a004104110008000e60341c103004c070203449244150800800a00f181e810400083c0c1c0c00608150f011502154183c40000c4401640789890310304402c0d8014544040008907001d580d80e80580702440040742680d000000103414540c0311f042000c10303080d80220130002c0b000e142c14290030207401c514041c0c10751880c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 772790620 1250 772789370 772789379
    0x60e01021204140a170c0f0a0b0c061e060a23030316030201060b0304020a2903070804110a05061812030d0516031b12020d0606091d09030a080907 64
    0x10741e540260407070a0700d10180c5042581a041820541010384042194842d8059440c4103e81c3e5030290441803a204800c3c020400d0540d440b00f10404004001c203104031504c070000c00314040d4550000301c581070101d44100d000e41044241074419036000c0d01d4054000d120340c50030501e20201205d81005101d182003040b03500c08110303440420003404c0100101c1541d480c01c01d41031030001d082d26a03d43c0a019825428418880507a50312041c039011612820045d0b1500d4401e074580400c020807556411200c400040100000700d500510800d202c0c600c04c2d0380c83c0940e80800020402c00060034080c0e19049001444907103104800321039240c2100c480145002021072f181d0070841d1443d40920a00801a0380b10381c140124418414181c1b00d05042d0740c101407103148221860440030220000043d010410b03a095000080743c8554122091074550850500c111511900702030480700701071142c804c40c02e98800300c8015401503028054010f05211004e5483e000c8540300031106010050190403213401b0340c200009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 772791870 1250 772790620 772790653
    0x32112090f020928020f041202010903060609050a0b0d050d05181306060f05071104111b1606020d090e060a0e010303030605131b0810091514010f0207060e0102 70
    0x503c00c0e26054050354050900448958050344c030940c0d0510390300d0061042c0a1000d4600c400d440688650041581c8000c3c2d081c00120740c0c1030f21580c0090a40c92802c8004501002140c2101d40b182460300b005100000080e800d1000d28100d261018005810030780d160960107110300014242e03645d0b0b00b004062010200d80c0003a40c141516007214206599030b00081002c540c00048070580780c1c0290401c80d040141a480324030f0500120044c503440365079140485000b039549407080d61003680044e90745580d284110300103141c0d07449002c0140d0340303000855000041c0079440019005040f0b0546e584100500d442c1c01205c2d0355882019203c2c0740c8c4010210000f0075160200e03007c2d030b402580240d901003585850201406041542241890702d001c1c2400d8010900d008817603030781d070134521591414072600c0e41d64008070828054280c01c103070203041c24500c1d00071507090740440400c00d41e0802c42107000f4503c6a4001580c065248106000260300980e02c20460380d0701601c0100c1c000541801a50f07211503450040a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 772793120 1250 772791870 772791889
    0x20402092205060108060901090507090e0a0e0705031f0203040206090607150c08160f0e060a020a1e120c080f1b0c090907050607020102010608060c04032112090f02 72
    0x51541c1d01c1101c40d80d011001035409030300c3d0002070030b00341004141000720200e010704c0d005010f0001015250760100d4101486610003078024994001c2c98595030514035000f8014000280c541045d40c4100d00c4081100d10f13020030004846070080040401d0380101c4a4080e0103508001e00c01d0303a210304140100e030075903181c60004088152040d2460400c2c0700100c803a40f0b045603e280c0c1c203002006003010801a0003445460121848505420020084108a501150078941d008001904010080b43d42c40c540e81d000620f03100303201c0c404c1e5503a0440500c1075080349051a03581d680507184120104100300c0d9207002e10a441c40c03050080d0b01492420420315402d00250b401301d03100548a000030070303102c0c0d03828800b4040c511500b0411181c8a1807070528182d81d03a524400d40c01000e208540011b98541160f000f5401000240101001c1d200503190504402034990040d1100750750102041d0183c1507400550f1a0000400c0c0040e141c1951003580c03807a0110080c201c0407400c44540074103207108400350741c50f440306 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 772794370 1250 772793120 772793149
    0x22d030a05041d06210f070609060306060201020702030316020a0906140f060702010804170c010935030a0c03022205041503050606090405070b12041e0305031302040209 74
    0x4482c2c2d5186007009900807092031480c3c3e14800c004207810302038250303954100130084100300e041064101c24840a11401d09242115001c2e4611444200040352608502d040d01140c0054908020590f034031002a401d0f8072035000000d51580080000400b8403044103d40700c03000e030024040030384540d100c02c0300404654a9130805210709041180121035803a00c661140460b140980e01c030381c01e045069001a02d4210050401407034081021040545080c0d62004d0720040903101c0003d010000e01802d00f901c0e4602800900381103811200850307035584400341c1d07031341c403221320a6034041c0d15560310205200001c01c000c1d000d080405808010407250160b011640001072100d001607080d2031440c14080208030380e10250000d543c07002c0304204002040e80465026800a0159600429607581d854058100242a0051a1552000300d1000600d0540c1451144034503c02d0b010006030000300d01c0c41d0354070800b02a20080000e98100009842820001c1600c0d18291015002600300210302e40000e2000c0402c008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 772795620 1250 772794370 772794377
    0x2040503100f06060c020d140102160f0204200708130f03150b1203040e041406070804050d1707110a0b07021005100302030d1b0c030c050112060501022d030a 69
    0x220b0b0354400c15203118500007071030607040c5903400d500c50b5408140c0d851640c2101500082c0070312801074280380203404940710005981c1d40e1070b4082d030071468024444480c110042e40135034980503d810030804854000d81030007910915040c1040d44c665100c40b0285d100001202401014040028126444107010b40c042c44c45556480005203600314541d040f074600c039058610400500102c41715001d80402100c0540e003180300000c40c259244d0500700200c07581c180b039044c12840745208200c141c55000c0c10302401980314100352180a055018111030b00240d1140c081c10802e506008a103805016005142c405c844450680d09801000d0710f5444091408a80038409a00804207403d4a64154402c5503805032171100985001c0742150046030740e8601f115222002d02004481c40381c035030480c1c5e081d4140d1959216a002c040543c0300e00d028148000103110b56800708109004240d40004031f4083c1101707541c010b81c000c0200c034074400aa40e517007514442c040e03024401406d04001d0004814030042c00100c81549 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 772796870 1250 772795620 772795631
    0x3090804091e0c0504060e0a050604300b01050409050f100b210606042315011202120415020c06090a020a0e0f0408070206120403030c0f09080a080a030204050310 71
    0x745010031221814030815030b114584101d81007903d40110546041d0f55070792904162019113800440c481030401d40180b58020303404140015004650761522800b81d50407400c501d4400f29a0900c030081c030b003524200401e138007554401400907081c107a00004080e030242003211103958054030642d00b01410314400d9401180c40d06030f20302e03450610f42620003411501080c800c101d030310002489074941360040c10340c0340709507101d0322206038500e14802c10140d402c0070003c205103642001ca140c070b006c0d10405c000284c013203102010445940480e6200b0f880c52074550318121251540d0325a1542c5114101c0c1d110045842e509010b4409005803c0040501c01c0c425a0020892110240100402441e0700e601103640941c103c1b04209011800d01002c0313802c1548105040c1d1203488a05c0024094020f61152002c20f00b005000c1005040e415007014010204039150b0100e00841d44804440030074030340c0580c410030392009203004005103440340105030452030303484c00500b803580759070000381400610200d2488003501e88 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 772798120 1250 772796870 772796891
    0xf060f0f1d07140d06020a0507050f010b03010f022d0f0705060105030f06070f050a0909050403021e06091b19240207240903020a1206050a050f0c03070309080409 71
    0x401450340075080510f5044102140200003980011074400c00816064000c966041c0e507074042c03000d0700d0b0501e0303009094464207000890010700806804260030300c00d44c20035945042140d803600c02c4400c07052a024001e0000c1d40c0075070f50103101c9000d6805203403000c10104144500070540e40c018080c010b00c43d0300988002e5140c030341010715100300c62007200481d8100c2c905211741250003028000420100c0d081c00c0b61112380702c04064540b800154003500c0c4541c1031000300000c05034081101c2c80302007903c1c444c0041484c0a14080d69442e5012180314045500000f89003092008026091148000040a02d1105030346910b000c6c00d8000380f40e2124503000400c020710525101c4000003801905131610003030003503920349603401140c071070318000002001c0c0084002d40080b511600840700619000b404a01341966518480700106140003026942149454041440c209460040d240213038032001c440201900c4e0b010301c02510b580080c00c03c0c070070700d940c81a1380d0300010b605030040c000500e4044000140c21701c15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 772799370 1250 772798120 772798123
    0x72c0910020d09052104030b071206061106090a03080105010302160501021201082406010c052a030c09090a030e1305010e0604050601030b0901180b0d050f0106060504030f060f0f1d 79
    0x200c000d020869001750032080d0754083e00c29a170849400c01c4c1d1000c03440c0c40f6000d0941300b65103882201c0005504101002c520150401d02c1002a076002801715100740d0b07100386080e5110000d01c000100050034007401001198841e80143c8280410410520b00012440e602c41d422a405040a4038080c03035000c004200c28401032002006008045001e050080d10b940840124120000c250506100d05000c5000c00d0100401189980b80e00e4448038003000120902c003540c4505c1d00b07c00c41481303845400d40280700c50512040c25030140344880001c1c074440045030b4042d9207ca0220805079000080712600b07145080181c003515000308a0b01c000b02c945828001d081c4016107400400043c141810306c0c1c080061a06c07400c480318110b9092070424078025075441c4205001d00740102d10a0b5016100d164400140b01c008116070f003010600400030420107994440030b403840d0003144009858440300d0020030021523400e0308610710306100ba4400217004d40c0418451801c07074540651140010504403200903840c0e00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 772800620 1250 772799370 772799383
    0x10052205060a03051c0c0204022101090c140c0307051903030f18030e061e04080d0311030a0f02040905012303061b0c0f030c0f072c0910020d0905 64
    0xd407a950b000a0650b00da40c0d586005081071500b82d13210005071240a01d100d01140c03101207074020030035907880c0060307074941161380100000717058003035403010000901c0d0b15648641080341c80d2540360038904c0349400d1100601d40d0000035541e41c0d1800704210b800c0001e007061002580e402001c01c500d41501d4150304000342201c2440032a602d61500e440c04072458140040c01c46003015034586000c02d42e02160001044c0b550017013040700c03e811a9244564080f14070840c02501c103641e000011510500e400f204120300740ea50b41008a071402c88200081052030758241c11035080c0c0c42241601604d016035807403c0c0f4080307860917408803500c3c40900ca960301c0280b080d0565181008011002400c641c2400c0324107103010410000021180e541c00110a200c8840a0011180603401034003961b45030308207050380940b0b50003040005007450044060200c6d10100512103c01c80300c5401010140c9203115100b038008035140649004c41781e00c20502d11440c5281240020b040c15a2001c03404280400320f864150301d49503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 772801870 1250 772800620 772800631
    0x41109090f010e07050d062f090f0d0f02060318030315130501050a120501090606090506030f01060f12050f06071121071209120b0106090e041a10052205 67
    0x4c012107010405070799a204060f0b040ca420210001d80e80004600d45c2103090802c241040c6030144c80c4410b4184071401070054141e1031401c2c2ca0003201003904408011144105540052070b28000d0301500c000f50904c90003642e4041c070611080c0304040021480f140c6550800c80e0320402c1d41d48001f07070301d402c6400c00d1400168441030480d42880036504002c00100341c1c090b580100d0f0090134840d42000c0511409400c0140b4141d00650708200340ca490b1102e0070082c06d0211072184c003e100d500c110840c4584148100d070101c0b08031941843e00036007011451890408040421b0b107044c4203450502d80b0041e01404854000d9081d62240c0c038200007541c044500384a140c030440c421540c0702201c541200d840b4a800c13202c055038803030b0b0f807818200c600315002d50358201940c014050707512002c2002ca08001100314007134181da2050312039004941c1d40704040954482c0c11a00102408000c01c100c050700350101c43c40136080b01c1c400180c0084603840e82d011580b81030b5519956000110305074240b101c1044280318154001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 772803120 1250 772801870 772801873
    0x60f0504121e0c0f030c0512100f020904020d05010306060b0a0906030504150c0210050c1303081e070b0a0501050406060e090601020c030307080415050412080306030709060b0a02010506030d09060305041109090f010e 94
    0xc98030390552701c3e42a01402022a90385440b030044510720568126111400c00400454803041e442000307500602007400203c81851400030042414800c01d81500e0340c1410a590714210142450400c401600001d08100c8110070105006400c6c0ca05501841e00d101c4100d038000c0910346122041502a01c40140c01c0401d800f204001d440c00700d91600c40c2c00030943e500040200d83d540c00e0141c44d00c540e280d040c0c6088c5640c000108003141000a07801d000c2e401a81000020700041c0d8071082008100d0f0b14602c100700118003600c48061960400b1444a0392115050041c0c40e0b0000c2c603040441d00f560700040c03080b41c42000011f02030250350700820298992003590b00d030807070601c1c0c00e045d43c40c00c0601400c07001900d60040800010300c00d9030200000300180000c04001d00415584103a407510b960031206801d4059402c00d40083c0a80c1000608504c3c6d081969440948003403914509800824025205452042c804a00801c072516000c1d1420b02403410040280f18000c1010701090071100d050710410800d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 772804370 1250 772803120 772803139
    0x30d15051c0f0b070f0f080c07021306180902041413201f030c031a0d02010210020f0403140a1a0702010f090606060f0504121e0c0f030c05 61
    0x140d2102200040340d049000711500251070300d0308080514100703100006026080d40001c0050b025480000c24101c2c605c50384804595002510080d1040c0b00c0c00c90f400401d05000f40032101c0907280c80f503521f0b58240c04040c4006680d40c3c441c0641600010f41b607000202a9487d5102c4e04110306051181104040484444042074242820f41101e8108400c0c40640440703841207208803881c54440e0306101000c00108488031f00080010440d001107886144640883c0c0742031000303010b090090042626000311040220300184102e0b040205100031510264110311504541c690054001d01c001c26450401581c12030b1900d180d4031700350ba100510294003a03003680054a030100013410840412240e9403440b0840400c0341d0310b0304030803030040500d111441c0c0514107008064050080175031124003606d0759640d5903030305011310345000d550a10603442410102112001400040351011010b0000c5595004004000881980340e0410b114042e4000404103088444100304012403131a2010051805030b4003a41d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 772805620 1250 772804370 772804379
    0x20705030306090c130303080708012403020c0f03072d0b07030b0103180b0f070e0a0902070501060e04050c090a0533120c0a0504060305071202040b060c030d15 70
    0x3264040540403078002d00c00c3c00082440618504140c424000d80c881c0140a6030f0790301e08001346015001d40e0b1800c0458811000492510040d101c1082d50480c0c040154205240e00b1404400a5003e00310108280c00740c48c6850285d84028001002c10600801c0702c10f10a00300c015003131056101481010b8501441000600000b41c5c5881e421076100c01076007000203400012000603005402032051008111803600071507820080c41c4903c180c0185100d00090040c0d548040381952150303101085c142d8001c01d0200100404050340d001040154465000414865555070f00324044420551f0100d076945c1110704210403604200d8002c1d540b0070400c01c414841e50400320004d4900080401e000c0300203881560310000070503c04401101c01c49005000640c690701409100b41c0c550300303030861940c0f28541d5004001030034582070049009490f04280540038035407400800c038604840c0105c0480e0002d03260850705406554950140c0348018044014540d20703400154940300700c0342c070b0000030301d41a19040380910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 772806870 1250 772805620 772805623
    0xa050306040605061c03020d03200702060706020408070f15020a031202030a060519090e0a02090f090a08070c140901240c060c020c13060e06270405010501050112020705 74
    0x6070010b800c03038400182c5403101c13030202d10540f01e4802a40e4101101444000826900041d070b4540c0a00b20303601004803910310114000e0454045100d0380b5011014440e0801514010700240206481100c0040c81d041da104c041e1403c05c2c580d980030340800040c0b50010001d50f040444501503983c0c41c0c0c8080c020103c590340e0060078a00d860314020201560101c005028102641e1015020749801040c44840c0c0c03458a0746040000a94018035108905081e12985117500000e071074000254020407502c2c0942d00e410300c01903400c400828168062048456000c0499500802412500d00402140c1e80150820403107014102c028003941d030056001000402000124051010b810900b10009490003032070040b080312002400540684851b1420b15032501072600040c11900600d800d0b22081c005003616419407044030803503c5200900100400040e181c2e261188031000c0b464821000d010350720044903c031558174242150100c505079902d100501c915a000101552034082810302035103407100c660781c1e55 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 772808120 1250 772806870 772806883
    0x2007050607170103060b0117010f090f0e250308030403020715020a031409010e190504050f310b070f030e010207081c1b02011a0f030c0f01050409020408070f050a0503 73
    0x542a669500c00703203003490b84103402d02c3c0e6008e504190b06901550311803481502d0b5007810f220b0188294035003d00c2244644441c02105480b028800180104ec2401c2e6204800c1000410280408480414004c00000c4100b409940100d0107980109004c0c0c1c1481902e22030440200344902c1554400400c3c3c03400682c0c841040d01c000c2606c42d40c1507031100300100069a012000e050207a0b030003000c5000b6044d2288048803030404884007141d00b441203449000d042001540e080d01d1a070720410103002d504844043c44c41e60103008031407030002d05a40c04240c0d250794001141c141e800c00000b41d9140701e10714130181d02d405221001c50401000310b252042d2aa0317000201d110309081c00c0000245400c1c14003031040968007007522810081c0c0031100903519280001c1c020850701c4c160340e985102c014450340040c103200750101d06402d40600100300300350740c100030001781c0d41000400504001342040080351003e028000352005005500060103034a05002e0038103170703005443e000540200041c200c204000e80c0c002454 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 772809370 1250 772808120 772808123
    0x303060611031603090f120203250e0c1603020309030d050a050a110a1a090d0c0b06010c14010c020a050616080f1e011d092d012007050607170103 64
    0x210f40c1c6101040c5019201c03421240e00445e803c40d01e081c0c00040d200316207090001103904c00c40946103c0c04011150100351408a000403000d0a22440b0a105049205201c00d8100e543d010032282450501d050b41a076211840c002240142c01c082001e0481d402c0030820a90a07003003600380b042c01c29240400007482801915603500401540c2c00b400030542c44144211200d26030040100c1401c0c2c1c02802c0301000d07012056808562510030241d0441c1c3c69407042a4005000e640300015259580b10440115008000c0400a4641c1e0300c03180c5442c00c000d58244108556070700d594010344608005420a9401c107c0000d2a0721004110004005441d580c031942c0d260b40100c042d4640b261a0b12542210005014450045048804401c001141e0210003085036001416500002205507484055446d1a0040e8407410782070024100c8500d80401000f0001891500107000001105110380c0036410721680e8140d1007608040000600300c080c07000500c40c443e440380080c1003811550302091180d40b40101d05210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 772810620 1250 772809370 772809397
    0x1e14010c023007030c03050d0516060203070516140c0609100810030b07051806070c091122260606211c09051008040602180d0b04030306061103 63
    0x803520340c100030800c01c000b02011102118120707600da291010040c5414001620184540070681c00d625104408450800640594800c03256206545000180d00041c18a009000051006000c10300802c40d005101a0043d42c0c0e1030b0004101c00d801d681440c1c1550f4030203010301003c0060004945840340301c0c2c84400254900075915942c0c040000c0b090071034541006001c3d901450620031404d40c45009031858481c00000d803502d00d203881e4100411403140200090407103091b0801002440c94542c04001d1071210219078500d890b80c070181d04a8802c5000c440d8a0311650409001d114003103103200c407120113026080d420250040400c3c0002e5454400504040c420340803000030103150070720720303c0403040c414007402140c455148070107015a07910400d1050900244d41a4030000f842d1406030300030280349180d503d400d440c945690320750601940c003144000c1280c0700350320f20003403030ba484e5000d44d50380c460300980002210703081c03c0c60018191078240e03102c90100030520160781e0b0036580110032202e000c14000b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 772811870 1250 772810620 772810669
    0x1b1204020d020904060507020111030103030c15061805190e1e100603030c11012a0c03050312010e090304051f1107082b0906181e14010c02 61
    0x200007149150300d408025002092042800100401e43d0801406075240f03070001d00802040c2c0110600c54002440b0107030001d14652400c10105003440280080f000003d400400e0130303030700c07011021082c0030314a00743c0d40150380c0e41d0700304180a04014019401c1c908c81d8507007032041040185c461036581101240c8512010155840e04a5281c02044005c40c01c1c1d4100e5800d000295480c00c0c068885048a0b03400c0d101c24015510901c10783d1f00c078000107101e505070a007041080302c10001e0000d25010b1042e5003100c000071a41d0002c004514200041c0580004504440c1c08943c10070841000115001c0c050030029070040c4030900441e500c61b1400a009900160700041207500c0300c0b01264580101d014061041c0a400c101051f02c0c2408100000c040440000c682001031101c204400e03025100c10401c0c0010346024020f002c0303030b4842d0300000300401c180b42040b030030a512460050b00c1d81840101204800c441e0003001c0000031409a1000c0d41d0103c00d00b000c012800058000c1212801003000544040c00100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 772813120 1250 772811870 772811873
    0x80d03200415030b1807020d0c0b011211040905030307020d1806121d100b06040503060411060705010f020901091203020d180314010207020a120c1e080f01060e1b1204 73
    0x3540116070303c400040505d05c0710801d00300b0041e5011000d41d07030340006015a200d00245940114030940e002d540c0300481010316807030301410b0204603044034000ca030403074140044445e0540c1c8601078005101d000c2c0c0c1c041e40e0b40b424403120291030204a21412400d04c148852241541c0d036010a484048801900b0200071903003580606a004188501d06c46180036241400201d100600290000146800c03001c100310640f000070400c00d1602680c440d99070315a220300300040008409450100002102420060501031503654050035140029000308506501103610300956912244030401085880440380c1000c04079100252620b41c001018018007540001c2d0301d1001c0030006a40000310380150108217040490080c4c0c60103036002d400c3c1a485003003a0603003c10741262030000035000d02d030700c035981c0701c101444c00e05503400349a0188200c44050b22604d00020300003d080c01101039054041e0000168907052910074001d012000c1c05109035801075244009070b50303001500316041091043c1c2a02030725500c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 772814370 1250 772813120 772813127
    0x12060a080102070606090b06040f0302040b03010e030d0c0f1110150b12012d090c02072705150102121308250b0703080a051b04080d03200415 62
    0x226030081805620000348441070244960003401650700f60b66041c803850740b441c41004890700560007001c2d40d48118a104000600d001e51195090710005000490058400600c0c1402d5420000b0718040b07164907064000410b641c045000c454041245c2484000e9850540100359600c0002201c44056640d804903c0c250701065161034004104180740d5170340d42c3c0219442c08080403000e116000c0c04c81c00c41326598010315250200802601007503241096424601000304c0c010349000c0120a082d03010f540070110754010f8481400f1046801a000e51b000700c0304c500c0c1108111800105080c92066030384552480903a0701145800414020b0764909480c0d03025001c1046030483c1c00d43c0401410f124591a10744103041c1c400011440d21202c1c0310f0030303004070b40d074000401e05441108401400140100c1c00140014010348c841034005c200303000b0602c0f070391001e6901c1a41660042d00300c82800d90122885109240e894054100f1000c1450800c3e5000310446030654200d0255024102c0307202646103803103682510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 772815620 1250 772814370 772814389
    0x70813020a0801140a0603171c060e0f0f0103211e021e0a08040b0c0c030f03090415051003020a1202030c04180c09050411210f06030609031206 63
    0x10014001c0c99102d65400c4454024101800340303020f209100300c009004076659100710340440f034000040700101c0e1480c040c4200b8650110840d00c0f10a070b14407810000d5050f183c03003500041c008081114a9030704001c2041ea143e0480101103001c036110b4080140700054400600201090840c41c403000403502d0311106680d0030000028403031300380042c503c8085540d680000d44085642c8105500c000030021180125126502803c000d440d4810810042003c01d600070001d21845480c1e80c16100a403000f480000e08207142e621080b0515403000c5498661460540b044c0c01045414a4079040d0703291404010800111044002006255000c164003c40c14002e0901100f0f103900045e00710350320300c0c0408504801c4c3c2c00c18087c4020aa603280380c440c0740d0b5034083c410b00001a005458a038007075403a00f8200005003c9605454103122400c5c04107090110b95007040900300c5982e04400495444c100c15920300c130b0500105507c2c46a1b20400074400419004411102d9200815040c1c001c41d54408010904811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 772816870 1250 772815620 772815623
    0x7050c01050a0921090509181c0e0a0e040b1f030b1609060e0d060b0a03030509190513020c1507050309060114060909060a0b070c03060f0212070813 65
    0x50a10701000100351640c3d006005280c0301d480e103203031a601c3c0d010b07141e60500b501083c00300100384030b84400c0c40186480002142d000850b240f6403801c0154408400b03052100704090925212102829074521f5a0010803402c40600c068803e060954a001005100c00d240a00050041e1030094041741d03070f014042082075081100460a00581992072800b50502503049548201d05204041c0c2c001103584180707592012a849517440400700000c001c1002060300d2407135021102075a45e964002d101e03840341806d0000950090725010b803200840c00a005c940c050400b8054002041010207000c5a0384078080c80d8442ea100c0200141c076103015040b1070b494246504108030080d02603a081088495122000b54414180341c400d452059a82c0c4a1038860600c0c000f0002d40e10050600ca4070070241070200c41c103a88200e004000243c1c1d2540d070034012807154042001540c11548071142803042c049280070f03c0f580600c10310310840c0303031440f4003840301400c0750f01500d10003c112040300480d040350b440018101d01d05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 772818120 1250 772816870 772816873
    0x1603020114130b0304050f01020403020d1407180f1406030d180b0301090b030d0206091f110a0f08241e041a0a0501210b01050c0f014107050c 62
    0x82c0e807105245603240c0c1044800700e406203d182c0144001c4801802610201d980c040c00c15804102c4903030f105500003041c1c881d01c01161051940004040091045649055440030000a900d28001600c4402d84a1031202d03502c2044001007800708a0310006018402040c080ca051580038030304c04400400302e00a50300401ca50f01c0040004100010755074820b200c05036040341280d1020381c109100f81d0319800104c544c500c80390010b103d1a204808540700c094450303405d0390381c009040e96030550b080c000d0b5003050481030005041c4881c51001180c000d825290001c490b04d4204100009074981c0510861030280707243d000b500c2e65051489074200e6000c1113035150a00802c24840d1003a19140b4540840351794182e188650320034003002070b00c2c0d4025043d00c0c803d1030740c4248581e0b032441d505894202800041c550981000b00400c801c11401100344011109001e040c00041800041000c4014200da01c00751000c02c0100d0604510b00400401c5071802c4844e58091344000742c9541e80c2c181074581d07011f40c807245c140a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 772819370 1250 772818120 772818157
    0x11d0907090e0f0f0a0c0c060e21030a0617071203090902161704350604060509010b100e090901110c06040c090509032502040204030b07111603020114 66
    0x10742c0d0b003502241c0b1640e520b0824000c560341d28203080c001d403180030b20b01401156a4082103400714040f50030040d01c003402714044807039030407001b0703482c1c40744c1c10703400c541c0c40e0f01000c0c08018003200710322034003d403c024004d00c0e036510940d2000f40f0b01c4944850b41440341d26800c04507014040205401010054020b004d03420013192640c9040340c03550f40804000404440301c0c02c18511900c1090401d00940302030b03880c00c0711854240b04400001f00c2c07400350880700f16980c1198000038900030703950400c0f45902c11803181d500886c50b800c101410f1403d50300b0072101c07a481045032042040010ba0711070485030b00c1c18802c407582d9807241c5404160900407d4a0108400020380024941150541c0000c0c01d50055118091407101207944100c050115101a600500f49420070465810442d01034105403030040b05601d2400a0307804d840e400581280d0040d8011620007010200b080321384c0ba0481c24040d140401c480141006192600b417101c400495400000e040c031400c91840001403c4800a844412800c007014001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 772820620 1250 772819370 772819381
    0x20c0d2c03151609080607020c040f1b170906012d050a080c0117010f05060708040e0708010303030e0a05030f0c03130636031e150501050f011d0907090e 67
    0x80504000303c00e0004a0003000001400c01000108607104403800c3c0d0203001a032090380200000303002d13a6102c07075440586a55008848030320303646049c2d009801c503031128684405001e4500e101e0810042c490102504400c0041041c0e031640e0f80180c3c0d03001c0d480c6154003d1495000b16610f4403590380d03000507800c034007100380214044400240480000c00241c84410070003811001507c80c80c0c3c001d015161400700100820480303414084082c2c201c041c4a0420707242840e4440310303003002c000400c541e08000602d850004005042d010300c12410741c1c4000b032025000d050129140d1031359900c2503849240703401100103094039a145060060303461221640000c0d0310440d83e0340c0801844103204450418803142c164a522481001d0b41c0c0d001c5401540500403809a1451600c40301c10100203008400050010305e0101d03000034801078400b220103c91604000781c0b0354101000d210000c069000000e040c0041d41040740c0790b8101c1e408080882d141c1c02caa20b1100ca81c3c03040e004940703461080d80820b0340700801e80144072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 772821870 1250 772820620 772820641
    0x1e14180601120516111207020f03070b0a0c0c0506120f07140f04170f12070c030605040609140102090108010e04030507050604200103090b04030c140a06020c0d2c0315 73
    0x940c0003040c1d6600403c13801707440c21031505c45c2c40900750752890000070440d00d0f00505040202074003104005041e1303400c2c29507916202c44158880d60200c000030788003540031801c02410307203e0003018181c01c0c0c90b058205030500d1001140c00d0302c00340038843d1515075030000400091142b8181a0910081040c0035110191001802c84030307040760080c6482d43c104466074a13400030000512210820f0000c0090020071031700303107152249500050003954104401203000c00400c9642c01802c6c011440703032800080c000c4c1c1c1ca04040b51a5000707455040420b0b4010094012240c0c1d02c0035079141500da074040b003000540c48601e4240d0703481c4640e02009045010381c2d41000300b8403000340d01494412401c10805c02017101c001004500301e580d813840007041c4100303038000700c0d000c80e1160356150001031041e544c403040d5412034220289803002e0300004549550300010380c1d032402082480815036145580c10080401e001004104e880ca02c50341907615400f80107020002c02d02c1e5010001507140440e00441c0515070b081604190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 772823120 1250 772821870 772821901
    0x5090a0e011e0231060804030216060c1109060f120a0b090d02010c05040302010903080a2d1202040503030301050915060a03060501260c0d02070203010203011e141806011205 76
    0x20001950351410f9a04d0211443c100e950203400050580100c0d81c1080310507511080302606c1901103100715101d04400c04130480807480900910388811050064a250480d0044040304640c0e0040f54040d00380b00c142c0c0ca4084032441019030440e40105140f030b00c84406464000070342800780c405081001403082d1840d01164110004500d41e0080c4282c2040304000d99140c03145100090004402c02d20810200c2c41e40ca000c0d1180e4a030030b1612000808480045620000e1105a04401d800080b0181104c07543c024242d44e156810044040d0308184c5050b0009450b070005204c2c50380121511000140e88940404036105620b10040986481c0c0c2958000180144424014680450100c4415070940341c040c08400e4168115501065185c1e80d4545551030f0303d402c03620b031201c81c01d60203000c4400103a0f001c0c000385020701300344180708160070f075000d03007000c0c40e80c6c0964450202c0c1c4840e140c0c00309081e01c961084905072590558161f1140c0c80f91030048490701ea0303003180e02182c2d27441c12051001e0200150f425 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 772824370 1250 772823120 772823137
    0xc02011e090c090506100305070e03120a0e0307051c080d050907030c270b03190809010206070c080f16050d031a0105041202090603070b1315050405090a0e011e02 71
    0x80200368030f5202010031510260703100c6074070400342c40185000a21a030003141d402011864481d40a92085010a241200c036214003044d1351f0b800701e403150010394480c0700c20104100c12001008881d2429012035001244204050b07540c441030020744041c0200030044544020218404008074034043d0262030b00d500960104403400e4900020016415890054419450485c45c2c0707203003c0c00440004020050088030b000c143c260107030614020040400c0791030502d04a01504040e59282c142c50002818510000d01c05801c1c00070100601010a844100f510145080b00c01d0a6a85d07030501581488042e40014000b00035120b0300d02c03241da0307142d03054008000440c0184121281080c0c43d000540c1ca40c061805844803c1c0c0310b12200300090300e8000001a0001d0014099565045e08c0e0002c03015640d00c1074121080441041c007040054480f991960315848046151041c01c05040070300240c040900039100100c0740c0c0d26aa1000d900c01d40a500011440c2c2210410030400c01144007840c0194210108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 772825620 1250 772824370 772824383
    0x30903050601050906222019020a12030f11040801091101050408190602070b070c030f033c050a0c080f01050a0b030c09030d0c050d030c050d0c02011e09 67
    0xf4542081d100883c0a0500100307804421846000e8010b5030180090b150726980b6120360a020505400032150720003a0103204c2c20f031360780341101000709002903001d222141c11540092500b90216040c81c48a043c0703c10746250120f0046841c6080e48040d04800d1000c0c008403100290008007910705520030034070a4400c02c8130110072001880190b40301c0c0190303c00d401c1d054204290f500701450342c84240141d214030801005040c10065211020108400c54800020031401407450f42030540085024044108501e028025401010303141d40d13100c0700180020404210b2044401040000c41101c2c60302010440820403186ca402030401c7d01910150341c41d100420702c1c107404902c0d401c0f4103e10240c16100c0141c5910110391400b041d0814aa2008000b040c001c2d1007400a490241e40c140010a042802561a1b1040206034101641032200440d00307602410310300410010300b95040026241d81a00c000c000051000b0300c180e082e405030034081d0300d4040342d007486110942c248156038484d524082c010035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 772826870 1250 772825620 772825633
    0x603010905040302011d0309040b01171f12150b06071b140a1409070c060906050115050a02070605090a26012016140f0c1309080913061203090305 64
    0x240031a00c01d0104c0a1b403000d507400030094002a410301e5001a1280c90040c0342151421005d00f01412203100f0503203400001044041807070301844203000300301c4040c0400c1c605140309001d1980c2c0d000c5c40107854800c03003a41c10b5180c4203040029030b606426100081c0d00524211000109103190010848441c000ca0358030106200041c0f4007403c0482c03c400070303500070400a10b2002d01c01070070002d00400050982007048645106140001c117940502036502d84902400719455040aa2034010a104403e130503007040300602140307645503800241c034411034009007441e0b0fa9959019010030761103030041e080301e0040220244d00383c110410481d8840c8480c03080034000c000561440900f03640d1311400c44292001ca007410b20188030000c04840b818400d40d84244030300b50840c4203101400742420781007140c0d80d002d071700b014070313904c80c42c0c00c00c01414082520764030360404c46030640780d4810360f260140b0103503180240503000400d2201c669651140b400740c044007030402c22101481c54010003482c03180c0801c407958042e04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 772828120 1250 772826870 772826891
    0xa0c0206070e060708090d08130807090b061204080d060e0402030d09030b190b0901031a1f031518050703060c050414040911090106051e0903030702061602060301090504030201 77
    0x4040d00ca0003020001d0002d850800185c607841150f40208005c164040b90300284900000c02c03500040403078038840c24a0451192421040900f4048264001448103007410404130791550b5200890716441010001c244287c2c03510f08181d6801d01900701c490040f03d1030f00501107403050880b461944114400c80c111114071111407803c40d036060803444002c1441c00c958001c00d55030f0304807210001c040c0d1803031400082e4410030fa1001480040c4280c0c0140c5401c0c402480400040c1030300d80716142d00242c14240e045005c801d03013080083c042c005100142c100c290620368800e03c0d43d22030304005848002600c2e030b459200b40c9400c103207440b291340d8403049802a2506c0d1904400500550a0b1400c4440c0e181100120380410000e1101918008100b02ca8a0200342101c44050343d9814080d8082d19807a600c143d25082d46a00c0004441604d800111050304140400400e40c2d40002c12159460b905071050745c4c8a900e00f0044600b00110014025031044004c0300224204041f607004600c079901a900a03c40003550 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 772829370 1250 772828120 772828127
    0x702120c060301121106070c14040c1e030f11032d131b0b180102030708040501031e050a0f0c080f07080c09030316020a0b0406080a0911090a0c020607 66
    0x254200395085002030004010201c0010460340a00d402840c6403403012099000044130b07a48026812160707007181c06000c0c004910b040000810243c001e4604014400108002810b000c40210070000c1e2203450003002c2c80744034460742280141d030402240900411442c118030702200c0e001264040c070207403d000c5d0308490980300030782c0c0b103e1461210304020401d80c031152241078141581040a49004040c0011100301d00c0300c11a2010003807a83c0c44515840700c3c5280e41a00700303035400460f5141154401c5c41107101213003100c0203c500711007007402c3c00100001160390520200100b0303480200303014a0801041000801504100c001e10025501003003031558840d410b403085242600c2103003045822500140c1420300460340142c1007005800c1c0700f418140a9070000f0301d075a02001c3c13444500604040b501c4218103000900308003403c4071a501c181030034105000140f80c14402031006542688518005040c400e0140342d40444010143c43d400a030318103540804060600b20060f000140729050000d09060321 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 772830620 1250 772829370 772829383
    0xa0311031311040212090a020306070c2a030804080106060801092304050c0a0b0c01060608162a030503060a080c100e0a1d040c080a15050411120102070212 68
    0x18200d421501c81d4035502c42c03072416500e684940703800c65403c100b02002c41da014850144540c3e2144020000008144145410050041d1080061004604402d00012608842c114440f4400200404030000c001e00c400e600c10000d500142903041e00090225421006411603401e543d0641c40d01101341e6a11480301b411110387d0940c1c1c2000016070044ca520b400302c2c0001d400d0300513009000300d1b181362010200081c01141d040c0e0014106c281d0004565007141400c0c062100101100c5c1805100b61400d407208800545000498030104840c145820071001c82c2e141c554a0b40f0440400d500810070390528014107140d000350381480c443c4c480c0b0480090000310004507100c0b0701201400151040240140998501c5207240d54580c1c8400d228401040c01c061001d0109810140d0031190700580c101401c007a4018040ca821551454118000000c0400d900042030008090305150002d041d540d07070304200101640f41410310350700c445d0000c03c40808120540141218600864801c4481e43e80050840d07a07400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 772831870 1250 772830620 772830631
    0xf08160507032d030e010e210307020a0c09020c0c0904050c04020c0c100309030809150103080703020c03010c0f090b0304020d0b09030f0f030a0c0f1709071a0a031103 73
    0x510800108000a00c41c400880001c402040300044600b40103003e992042400d050200000303a540c004403072050380034007139901000c0c2d0b00c0e03001e002c0c0107034003010000c941c45c8000e400c1c445546000012414140c03080000311a0190000c0c403a10880342c454a1202c0a5401500c420f0b1061080103911926841d0000005010f554868010190041104184030180d04142020301250203641c6812000392650100c164150442c1c1d90001618902460f001e4941980501810381540c0300b40d21030321002c04c9011044d07056a4100c4001d40d116011490103d15040000d280c1d683c0550a186044540a0b00403c0541801e452520f500050641b9443e80300c403180130840703010798032003004290707900445c030006c0191340c0290100081e01d1508103911a002020f600140800e0344280d00013081100c00c40d01c5115041e050b40040c582044540d912400003031103452003100c0003005002610204000085c10000d210042404924500400504205c050740035000080080042803e0222848081c01d0880860f8840d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 772833120 1250 772831870 772831877
    0xd05070e0601120e151513090201030e071422090f031101141f12150b0901080319030b0a08030d0e03030103080406080709121103070806160c0c0e070f0816 68
    0x5641c00c4003007100b51720094180360300f00c1081030503c400e6440d014000d04d02c40c041c41e030000c5102900c43c4001001c542c045030840b20b003030308078190510451444d1400400c0400d801c4840d195440600c01c92140070044ca4031840020341e04c1d004c1c6203810441221719502025000303131600c02903d55a1010703d8241c40107081001900c402c03480025403001c03204048100c8101d20010b2021907161202a00c01140204801c140d800c8034215040f28501d034020701420b000315009842608403035141030581a0380380104040d03540d850310b01d200a518070071710a41c0302c0181018004d040d0300542d0354809400392281d0185a0f9000c8450902c0c01c20403101e4000421641281d5110300329074034081c50101e08981c0e01c100a0490300400c00c03907080018000c03001610300c4000e0340c00380041c469044111003c040c90710500343c0c001c13540d070380102040200c13004284904c4e013101500c0742491442584e092901e06049001ca0b0044c549156860041c440c0c1c0c10752095407490f000040d600c3d030150507290010b0f1814075800403010792002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 772834370 1250 772833120 772833133
    0x90302251d1812030a0c211a04180203010e0d0906080c04151d04200a030f050f04050d082a070f031101150308030408090d05070e0601120e 61
    0x1e8aa08428954006005401c02456030b401580c6141001c01c0880f140c0300c002008401c2c0540e4482921903840c000082d410b01c240c100740351a0b143d611209205040070710080c0d890f54001d12481d03607001e201901c164001c00820851700824207141e01005840c0e4240d01139880c0c280d0300c80c4c07010320004940ca920030b642e80f10206068680a800c07a1080002000c102c1c0d120024000041d80d214600c0e510004411a500d40309401080340803900305980e00c0c0040d140c400d0b13080070000c500140c09100340010f0400710712601d56982da6602025030107462450000303822523180c0750402004209113200540039078410340554200041c50b03142210101802e58980d0404030940c405912003110b140e20314411104290001410109107855511182142501c1a000f2071034942e100300c08607000380329107480c0401c1103122030415400c40d03c2d440e0641c040100010503451001071101c0c21580d644807081140381c3d01c181168080c9803501d400c00941201a107465002c602d00059140140109005503c0c1519145006109 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 772835620 1250 772834370 772834409
    0xf030807020f030f0105150915010c1502040f0906050f15090409061418010c09031a040503090a080304060905060c430f1a040b030705040909030225 65
    0x104103080b11001d41c9841405402e4600e44001c2c020325126040081a0000300d10780034040c0300710850700801c1e11001c804044003982c02c5a80080c00d9564464114914150424001c0c030045c00a20580c0c1040018100e005000200502d03141c00c0003068803002d861011582003802e0500c1300c00182c14502c401c03003540c103004d560b41c0e5041c40d5004002c4030380681c0780803503c4000018050f42440701900c01c160400d0403a42d0161741910240501c00900380b41d49050014145142c8900c000300e0000200c1c1030600700408042010f002080050303802c000c0d8000d160001c69035660b00d113182d480e070180c400c141c04a03070354140c00141440e0502c295154403070004040d00e0189855031150f200510f04951601f01140403103840c0b20504180b019151100d4261030203014880c1c2003101d080382c2c0d903640b0392100c0d40605514408504a81c01401500c08542c900010f040d00c80e00d0340141900c2a010351740207003034802d107015950414194002800c80020a280d8241c0d41d400c410a61503c801046601564203c801840f41240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 772836870 1250 772835620 772835629
    0x907091103070e150c030901020d110a0b04060204082b0302070b0f091005090312090c060712210b090f040c05010f0e04020c01061e140f0d120906090f03080702 70
    0x40c007000c008005021340c040040d201c40c6150130402c42c3d800f142d4404946144203580400c00f07079094000f1810040151a03030210025a50920311400070721400c00700012030100580d0740c06440c042c10308402074403079a103220403981c010b10350300420311005038000300203646040d8024821280015001000d19159035941c1d034500d42803500180c40c00074a031150040141100069209050080058801441e6200740c50b42141c9140c2d0b01c007500408041c0c200c0b9412003016521401101c180b40c0c3d00009000f001c0c1c5a545042d2000e00300101d48910410b11410070f40ca1807695503201a030707802e10485250515890307800102c511010110303002000b03003041880a02c074940c0906051000540541340ca245015100404078007070303800c28100c4200607912648180304da0b00041050301003407164a1804c0402d40e04c0c11000e2401181d20558642c05000d084cc1c40074075131b88500442010b02c0b600080e51041c00540035034002d2000c0c8491196000084016001154000248e9450021207800800e210b052410640811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 772838120 1250 772836870 772836887
    0xb090106030e0a0213050109060f0b030708040c0f0603060e09030310090218040603050105040309050d03020a030e0a080a0b0f090c0d06020a030204030c0807030203010c0507050d0e0406080114090709110307 90
    0x41c0302e24401c03d60514011307519034941c01c03103010360740343c0200380ca500d8451403505a54142d0441d04c0c40750100c1c031041c051003904400b601e5114031a803500c40c200e0340320b504000e0350600f010380082d500220240004168560960001002ca40700e19064582070b41c0c50540c00c54582c0402d8440051001c0f1140c0d040203012000e4020304580182c00594416803901c132000241117800d164802c075610b9460700100710030f040d0442d000c080200300664408c1c18140095500075158880300000038281301000016440d40e846130075407003020b41078150440c0c560480314100080e49060440e10342c1e02407062140002c1060101140c03007041d0780405410803181c10103d9403004042d4000b01c440d08100341c0e082c003000001c960036002000c01485040003030002a8203500505003903450b4000c0c0d00b0284002002500e0000e000007440303000c0c00c2c007289440d004601040002a01610555211410035820240f1007401c1e200c05013800381c0241610030403507a907190340c0c800000035504c5062001c0707003080d8280000390b805805480341c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 772839370 1250 772838120 772838141
    0x15200304090234020a03120507060519060f0803041703090315040c0605030c030a050901090b0a0c02070e100509040c0e04030503010e090f120c030c0708060f0a0b09010603 75
    0x252820251a208080c080341c0108181c809201c03400d005601e003459000c0880c140b5074203000364035480e4030b40396008102e10709403030712008142104001d20013071700d05e2159090300c00780b0f507012506001d91300f4141044448141c0e0b0035030300421680b40250004805020440e8101181c0c2910061070805280030174482c0c18810312220a04580070812164560365800d01c41c4c00700361059451580341c60704160038540c0c44222243c010001340802041808412031640003940d91040360f12802203040d9480320721107805480c1c2c001c00140340c05441c50a11101d41c100d60004800f003282a82100c580c1a540d13944041c1d83d000603200200b0050030800140241d0404a944076842402110041c6155641320080c41c00281d00300c401703500107080170005104403214079004a81100d15800100b801040786030915481d04085084564099800165611503640c140140d50001c4440782c00d658141d40d5400b100e40c4c80300e07000c4990007039944080c0300041140307605214020348070f5030191841c100e41e0300744481900240343e1072030f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 772840620 1250 772839370 772839373
    0x50f0409140d020304060206090a0f0b041e060c0e0f0d0b0c0f0703030f0b010509090c0d240306151d0c12091605011d240a181520 57
    0x40407001c0701001400300308645640119903c92400c4c20085c101400038004617020782084440d0b00c00303d001418440c08041d0440d901c018162914a804070030b04000f0380640007107248800c00d0310184942c5503c001d2008031140c9a21048441c014208104a000180c0f6160b01900c500358000210340402c507030644c0b000800e0602c51500220601c40282900b01490843c0042e4079040c0e0018080d0080c0202502c0c04800e0038102d06110070000080c074a00130050003818807450110f110382c600442d541003400302204040f4035240c804441c243c4107030a005a808180ea41030704000b039000c2c2c8401000325044c1102d040f640601c911007600603c5403017080703000c0c01580004000b0311806101d00c01206d442401441d03000010160b8142030000d4005100b00790b486181403221141900c0540003c0e4804500d074880200c60a2120020010030034001182003080304e10f004001144614542e42c0158000f0984003001e10300b00c020300d139201c04520015048418040010b190030440c841e40c170f840b1102c1012443c10307240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 772841726 1106 772840620 772840643
    0x2040f0e0c0304140c10030209030706081e0402010513060309170a0512040512040b0d06051035160915051b010e011401050910050f0409 60
    0x410181048080000c3c14221070703024800700c28001700041240c107104400301c01c018029002103104038001d12034a003002c2981070040d05554440c0782400200f680d0000b10540c4400d09040190049040c0103061241004110316281403002400349581c0001c0c41c218542819468410b003d01c50309402c21040014141d07859200046501e0300d2214840c0308040c1d00c03146400e030714003420910341d485446070120740840d96902c09001000b103020701c000240a00d507203803410000e148407280c0c2080302003000c07040708140122403000c00301146107201c0304002d03424142c08880458a08100d406403000480001d10990f10742e00300707001001512004000d17090000e495040075040d403081200c0817400807801030800c40d0700790094010480c40d28600000b80803c02c041700c0758185e12082070050318841e07a5141c0000c0c07183d9083c003c07104111203004040311310480b0380328107010082050100540b802030421 = true := by decide +kernel

theorem cover : BRFrame.Cov 772661870 772841726 := by
  have h0 := BRFrame.cov_init 772661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 772661870 ≤ n) (h2 : n < 772841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
