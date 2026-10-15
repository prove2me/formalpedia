-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4259
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:02:11.943568+00:00
-- url     : https://prove2.me/submissions/b7e01407-0b36-4a6c-adca-808d3cad3c9d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 765827338 ≤ n < 766007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 765828588 1250 765827338 765827383
    0xc030e061f0f03080d0c0203310b0903031b120c0c1e0a05010c060e0d08071b0305220312051b06010e0414010216080403210906050a090b0d0509 63
    0x40e126054000c1820b503140160b06ca40d20510042e100f8021036081d00e84046070041490340c01c020210b10421031500c2085d900c400c510010602e48030040036241849801401180380110710601d151429507100305c4110148100003464500d80007002c0902074020780c0c50000e08054a1500400541011544800f40707040c2e0048144400740d1520060032041d1002802d00c0840e1550700d180410091415503825100ca000d48041007640d00e910510050046080b603a480142cbc800c010500e02010705000801004204100b06508040c0c040509ca5107460f9004422100349035902d4840e00344894060400e00000b4100082c1448402c0415010645030b400c128010308042d81004007400302c1460150028000703800d0780d0305d81c040304602501250407400c1c0d0790194000c1070f555407524140780e400a0108450358811a603a0009a108444852074a40415030b946204180f81c01c80c15201540511003030030400c00243c3c00030943c8542d003030080442c0450070800060514040da5200d00349245074a000d40540d1800c103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 765829838 1250 765828588 765828593
    0x904031d010e0333010803120a020903030a030b01021011190903020d06021606150504050a051311030a0501020301170f070f2c09100b03010903050d0c030e061f0f03 72
    0x2e01103403132880261204100e03500e00d0b000700c41c1102c2d801000300702041107200128040c04040054803501024407400051521a14000700076070048404d905e0b0154000e00032240164860782051259040600588401d4155202c440c003e85032041020f004000d400100c02e80848a464490b011105592501d030b10b40a045a001542064034040c015108980108118421103a110740300d07515150300040c01c222054410703825100e404001d12442d8415898070001541d00695070103078134410131040c0e106104030700403551018945c118285d070300c641500c542050000050001d200940c081c0000074400b841c5890303402c40d114500710907941c0000c11508080c4040110040080301001902d03520089445c1d0103030700405020a6099010815072900300c01828052081008075006040543c0740000b0b00c540d50b80f0409041c00d0350088600180040c5041100002700209a030008005851600e808100414540501c51401d8800c0e0b0715445540b200b95814031070141c0184500004100748007906c0340861558 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 765831088 1250 765829838 765829843
    0x1091211120306011e0201090b0c090913080c1b031903020d030e0c04090f030e061611030307050a12080a0b09150307050a060c02030106080109051e0c0904031d010e03 73
    0x802490001c01c40800443c20303583c040c02140014054000d258044050300c0e940003806441c41101c00e1740c4180d10301c000708000f40454801c45003580d030047e01144054071031140340c5208041400c0c0581c0c1c114000d02c10a41111024052060100b9038401201404200c2c0002c260a00e0b2000900742800c42e5620071010006e038001c50752210701201ca0400090b03d0050214141c109400600801ea100745407035012010800402548400b0347d0003a50381c24103945005050001038071034007820401009050420400146951607103000034040642664203000c140ea40d45441c10b1008042260300340c1c0030703114141255a020071003d9009080c50000e112081c8030101103035000174042c2000c47c00784400b070032400c150f4408104200c000d00000c1c3c00185520790354a0000c003070b080171100803442942007041c001405d04050007171220041d00300c0041c103100030482c1081a0640020f4518603e00e0151202401c0385650b083d042d107219038083c0e120034941102600d01301c1800001202c0090612a2882100c040368400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 765832338 1250 765831088 765831103
    0x708010c0c0f0c03170307030c0e090604090f0c0f0e1e040f03110f1605040203090c01030e0a05100212010501031401090c1b1a06060403152c01091211 66
    0xb805411142035642005640c260a075080500200c02d180310101d01c080003400254818581c6540c104058502c1c80b80465034001503026155101c045d01d03010604625040e480740001c01d10038580703111036000603a10880101c8555000c13031280c01c0380141c100210030301480890341c44800c80c0e401c01031610a038000c1c0940c03820003070000f502c040d51194507682018058034404020009000403281c5040c40c88000700d03034035447c425100304100329500000419007080e00a40703000310056000381c00d0352140c0c140114001c28004070b00501e24440c10404001203401800001852003a550016035580b190b02034040355078406034003940c10140f5114074220019601079120b070644d01858408100200e403d58200c4c0e103640d5112400c0b92a41d2141c001c00d0801c407000d0700d501c1d003e03004109090855990300c400c100c141d0140d8440130307001808485110450b04010b50240303094031105245c82084440171a0144518640040c2d070500036075569002c40c080c0044c2c500c00c0c078000300551a0080b52004400d4a480d210440f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 765833588 1250 765832338 765832343
    0x40308070605071106180c0d030806040f18050703060b18060909070f0f1d190c0302130e061e0607020915031c090b031314120f0c0708010c0c 62
    0x1070b54404503e03103e110380b4042d40405015412221181172210301c009000d0f5008039180614403a9400d050618102054200310454054403000074a554200511000c0c016090111303c0c655503c10091071030401c0c1640700c0c043c590003140248141420b40c5000b404442103140e5152040d1100c0030130300c248030b40c4145d07040d034072581c2507610304919144c270801e07a49007118540041411a10180c0041444440a60304000b201d04149421080d1034a549059038034407010b8031414242070015103880c6030100f04c0c1d00b088400b40000e185c01450958a6a1488030322090380d0840d000c92452402800403625012201c001d11025000303000107009001400a1400d114600f4024091420711001802a65404092441c4600b000d015901030315035109080d4248001c1101c11008030344c1240001c160b011407103080d81e10400d07100103040d001070529102e155403415862105915071080c0d510403200104c900000c0c08100c1c0080044545030410110002c0c209030280d000341c90035a240481c2200031648c40300d0104030700d0380c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 765834838 1250 765833588 765833591
    0x1e0c0c152a192d0206060a0501020d050f2107110c090703090c0906030b0610020105010312031a1201150e06090615072109152109050a050d090b0403080706 68
    0xb680d45206594011080d001d0490016074070380f01d907801d0003901e00b035050f521240f98203560b069a9400200258280c05005040c016409401e42c078503864001c40080101d61100c811660030140440b0b05031141500449070000d03081e4901050052a9820122410080030040040c3c141e030a10b100104100d59801410a0105502c4810b20010302061428070b40143c2007220050088a4032820324845204040c0c4d400b5010b9621183c40d248800d01c11303c9401d0507241d0040980c2040a2412012406069002d612040d004200110720441d80d85d05418205501c244600125144c6401c0b031034074504105903403044068844000030841d031aa034224041d5032002e000c9610312521202016031401701d01441000401c2c3c80c0b55a0011010400301d50038000c0380041b01c1c0d642810180c0c070b811180b45004041840c89001c218402c009041607800bd11100c03161031703030701100003440b0040c54483c070b071510708003038026101e45d0000c030130030300f040b603401a40302c2c01900e4000030903480e01e481d59803654030a02c5511000350103503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 765836088 1250 765834838 765834877
    0x210b060112060b041412070806040204020708040909120f03020405031c09030c1404050c0403020303070f0201110a0c0f050402030405100c050f0309030a030c02061e0c0c152a 76
    0x809580c002005003d440101c82d4485440b20360068401c3c41640c0081e02c00c04029210384450100010345200303a40c40e241c0504040c0c0c41d00d03400c6c40301a401ca05001c03241c10609000120b4424103606ca8034120318050315601100200c0414041c11b0076903800c05000400d4010441480143c800250042e1080e0b080681900b01d84c05000045901c100e55410003803800c00e88000c0024030355400b0102d141412002ca50400040d16403403100300d2544201e2200940542041c884880803445032507100340501d0060600700320740140903400300d0a040380b15804452200700040240b1042501c1000040600b4003598114610f003000d8880c51b555400040d070380c1040917143c41d0f07082d10251055090b18090706920f41125224146281019280d070000507208000a00d00400c2c000070501c0065901c7c0920080420740c22440102d0740352003401c3c0c4c00140400b41210701001941d0b070304c400c108190014050003612098007810710b0303140d03018003940c100713002101c10703202400104240040200325031100d18480c800009a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 765837338 1250 765836088 765836117
    0xa0509041a1e030717030304060f06060903030503190501090905060a0603050307150213171b1f051207031b1106070e040e0a030e03010605040e060103030806031002030a06210b0601 79
    0x2031503801d8004414102079090340c801000b10010147d400303a0710690051040103d40c0b0301e59030440b206849440300240b800c050400100f40114021034111050005024035110403068a0040c0c2d01c00ba0700201d004c0f03550704541c5003881000c1c4152038010b031010005200651460b16010f03580e018005001e0818800c0030510300c20740e5042d41c1280c107041c0c21020020311565844004113050707030300100d00102500030000001c010360383e014030300002244000c28401540001c1c3c200c01d031040e1505104d071410b020080003c0e807611071440086511904403654080340c400510041c1d42203900c031404810061101034500a02c1d107030b2001c11542c0e80702c80c46140c02d100003440c0e1400038001d44181e1001042d180540700c0a43d0605500141500c00c0e80405c0c1c000f0f01840c0c4d52501844102d0b0094452290240c100500620000740305210654002d0401801c0310201217444450340c08903482556440d4043e59603000820418504850070008444040b40840b85030b107854690303043c48030005002d24100155500d50145 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 765838588 1250 765837338 765837343
    0xe061002031608030610170109020a0302250c05010203040b070f11130e250302040b0609060d060e181507090b270307150507030c06020a0509041a1e03 66
    0x249821031120b803031045040e410b260b841540180c3c1c801303009074500c6140112542c0107403a0340ba210a118003818009a00c0c00070348000a401500080302019001c0001c045c0a000300c4031914820813601c80c8181c1100c01514002007540e145901c04c3d41076401c148400c00c240c0d290042a03d0300c0c9504482a1141000d03145441d540803808221072030340c84503507a04003904200c5182d000320322020759042240d058590030800b40d1080d85440384000da031507408910a100506041e00405010a00504000d052103000d03000208136030040e44841d44080e82d070300f404202459600090940001d9900d0703000700810001c0a0103034656026812000004024401040d2120710904580005061141803261240505403980c030300d210154076000100445d21b44100124900803c020041340e141142c81804868540c50a54442c0c103c0d078000c0c0c0c14815056181c00100300103000a106590850795020b55885070354040208035065141000e01c1d00247c80d40c008000c3d2651170b002000041816407010140760131600084c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 765839838 1250 765838588 765838597
    0x4030204020a0203031e010819060f0603031206060c0b04080a09051002010e120a081f08070b0d0f0b090a11090a0906030308010b0f0a030b0303070b010b030a150e06100203 75
    0x203412a200060b10710100d41d01201071360107041e2000454207140c0b454080e100c42c5100a0041080e2908020080c0440700e0341c035604c44020702d100340c0003c0b484041c426080c00468000782d10544c007240c0850500c1743e8208240c401c41c005850b6034140a205140b5a0f05d8030044200005c0004201a0000542c80c68142c091440c100091500619074010051186d4000340a811140000056803054404400450f0007040a84030281d0b2191740b041c2c07150750b41c0300c44401d6919040048641c05502c401007c94114000e008407006070000305d00090359503206060050032503078541c1d0700c0360007180703440740304400d603a01c048405401030044500421942d92085443cad08910034a00c4c0564403150304000000c0c414900d4010070111303402900c9200e5141e0365803100c01e00300e01c01d010341500b260381c042002c68943c50103588294055100502128100a103543e2025100c504c280c00595101c0808410005691600d000c3c6e5880c9030aa5140303482d880785415520a5055006450030f071091144220610547d4030030010345 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 765841088 1250 765839838 765839843
    0x207080c1e0a0303030b03100209060924070308010e071d040221090601090b15040302010327051609140a0f090803040606080c1206060f030102041e1e1a0306060403 72
    0x44908643c0e80c030340640100342c0c5101d0a030180c0540051140301551038421b5a0710705130b0207400e151600f5024070402c903072a003030940444200f11640b43c10b101c0a01c3c040e405401094402d460f10500c5d5410b104005461380001040c550800040d420444150701c840401d40807448400e43e009a11000030002d074180a00c40004907482101414040150941d80000c039141210346102c0100100da203d0b81c18000c0c082e000d80b0701c944001d40708100030001940f09a201594080c42c03000b1950390103020741c080b90ba0311401414141c035181e110014601c1c2c910100c044078801403515041c01c028150703002c0f9201c0c5040d48014242e03003106507601b01e50b0003c00c50ba0b0b0000304401d0b602c1881e05540c0e141518082c2c000300642d0081c0e0185219008204003681450750341601c0008200c7c0007442c569950f9020401e140e5860030481d50195024030002038075107142807980e41c01c100f009012508041c10403140100864540c200c0012182400c0c1042110712001005022111a149240d0341d803070351000c0100f1040d01c502d5000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 765842338 1250 765841088 765841099
    0xb0915101d10200106120b0c09041a01090b0412060f0902032a150f0a0c020901171005150d0f0507060909050a0b06160204140708010e01060207080c1e 66
    0x99920140c1c40300007a540f0180000419800c1c041d507001c401d0032a5a03a02603410152461107200001c60003004845600900c0c00c28614640302d0000701107401c2c0d070740904190040401004e18403101d50f8128002750040c00440c2d140e9800c1624000b00944281391840307014048903030b41e0000404c0c2c0c1002c1c1e040b02c003a00b44c000c0e0803108108818001004620305034100c210000314902c0e8100300030729103000040080d40060854078100001080750b58016440004a0014802d100300104c00503262149014020001605098081c03048405520704003201c40e100440350901c3c1c0020404850301107141c041403d10305891502d0002444c0c54507040088500070003900f03502c030f00230000400c950301c40600c0080d05d056240500440d1a100c421074141e03440d490141e0f920841c02c0c0030071044d003203030354114a030020300007080841e48642002d015007601e40182d0b2050f002079a01c2c8014007044030760028141c0100102e10040026034500801035840d840030307030300c05440340409900d120707040f6042c1e07004030320b480000820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 765843588 1250 765842338 765842359
    0x604020705160b13060507031706180103060c0207170d180e01031226041e02040614041b0f081003051b010207050d0203190606030b04060b0915101d 65
    0x4014540200c0044404c0e0704074110080381452080c019070b103d1030340c50f4644502014580031035907c800e100900c62508420303510502e0105810582c402c9000314028140002c030300a16400007401c1144035000101c0241c1d030507640e4004110000b0b48407400800314580842008840c0414503c0e20040350300814504066800210030700080c1045c0a0044041e41c0b5034a10b0741c5042c1000200c0516841182c0d03004446800002c0c0c081406252480900118000e07010422103a543c0001c00321400c54000c4265414501e02142c5d040c2000d1003414600c20661185070407202400c080102080c116010207002c02c0041c4002c06c41c0600f0a03034402c00910347c4030042d01c080d41c00406440c50180901030049005128140c4005000d060400d140d00720160042d014115510004042107461845200101e800075582c0c40b000000c541c2c18403500303005512841010a1802131182046a4040e0140200c00c0c41d20b0010244996075031000c80c840c0c1c40c0c03034940c20301c0b031038200207100e0118081244070030942e0420035209 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 765844838 1250 765843588 765843599
    0xa05010605010f0f0f0807050f0f03040b010b0301050a03030e0f0a0312020c0405190510170a03080f15010c05071e17070605030103080c030d020d060512060708060402070516 76
    0x40184040c0e40c0c081c0d80f2000304403503043c021520000a07a1100300032174010050440703171500c245009644031019013402841c0054040882a80f0361120100607000800403003403204000b120314026004001a20b142800c0d07505100020b9002040c600c8000c007445480030a00d21103840703030240d807a0742080040c1988419a52402c24180c80b104410480c0d00600500d0004e4402d403525106440c0120781514150000401f120485030007440040c001c425a800c0e80d03d0b0014003401400403000c440071001026044d24001031070080c0c104500603004410703002a180401108280701e1060340c0c500a424a45000b440d0001d08080317041510b03075084146100000003501103c46400202901181e060f52102c0d4207491641040a0f103030325941c064030780019000c1004201064400000d0b0044a203c030f0305581c07815071011091070481c4e01800c149198a0340301c0c0010011132074040072852842224001901a51424410080021400802c1644516804540001400740c03c11070b513800210480c1c0104843d82d100c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 765846088 1250 765844838 765844841
    0xe033a09020103050708091903050d11040f0f060e040507030b030a08180613062d0201060302130e0d050d140112022701121509060902030609012f0c0a0501 68
    0x10038180d02090a11001c1104039220710741c910b02c10f102e0307007001d40344d1540c8045a8030000c9a20120a408200060040b041040058480d8102a40c0b176a500345580380c1c40c3c022100c80c8014668001c140c1303c110f1a800300440c07900b20340c140501003c2254002019070740c4603400d03030081c404803104035094490700054504010008000703025080d03900304101801d8400d117027082014800c08241002c0160b03003002c1088120b0140c0c00c2460141049031029191504030350320080000d02d10510784006070344070780080041d82003041c144012020982010303c4880d03105241d41e80d8410400c00c1c2241000400244000c1c126034a500000c1a04214180504d880d69030b940b13074040301d0f401c3c808241e10482e88030601300191b080c418400c00b824807040042001e16840d1244101c48250103002c250340741081c480b40f00080424511884410a110349000981c11220780141450315500804000705680741c02651424410350304049002d49034003003d00d098206441c2c1481e03041c2c0c02010783d25503452040400324000c00406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 765847338 1250 765846088 765846101
    0x901051908150a050f060c03160c05100507050309151c14090604020108010303050903010b0d051006060311040915031208162d030603020a0f0602100e033a 68
    0x400000802d070440160802c0186034030303445016072002d0b051906441a041101c041e04454800341c0940341020351140204001624409007100c2924230514184503078904034040e5203215400e40340060a04981d640c1e183c1e82e91103041c0481340320360f41d0340c402295000c449004035100781c2064240e25070f15a0030644008040e10b110f1b1258070301d4080300301c0000d200344000100d1911640e0141c1d00c200a503469610b0a07912a40125a0242c05540703503110380105490303a0580e81c690521840081681c00c40408114085840b15003041040504144421820340840c60070340b000d031800510001807801c4d640300300a0503030b400c9030320060150440ca419010b440b030700503071128851200b01c5050602c065040004407030240207003140728110414084001d0040010020030720311184a070800182c0d045e101c2c0c00080321060a64008100540c01f40c406001155041c082d44060314030003003041c0a030800700b410450f12402180341200c85c1c000301d6801e400d00b6251550902d071006030503074110036440c1240310310707200603000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 765848588 1250 765847338 765847351
    0x280f0b181f0501080c010903020d031e050705150907061b1205030712140f09010213030803071808151f151409090114132a21020901051908 61
    0x605400015903140c042101c1d071107464169507451708941540e00b0000c06400c4640241d04101c0c03110020753380703150035060495408410352a065100c05203071030300300e19007511009641c40c1e2458200a000f56814001079403c15200242400d5096002c0c8008040e0541c680506c06425002082294210145c100b0003c0d8041e40041d92890012405c12031f10070103480040501c4450f0044240009030700050241206800c060088000b524180313403441800502c04180c2c205131b0300c40d500013003171105c02c0e5046070904c41c42138a171030704000341c65140a81858581c14100d00418070600c40764000344104916903401c0008145e40c81e02e5101d56a107802200d42000d022019402c08604081660014080203901755031108030f00406038400d1341e01b0245814014000c1c001c000360840c84001e070b000f42585860180e08115299480d80c0307074204145418180c03601c03410f02e103540c00707200501e60b5840c0b05442081ca649194245030b2000341c1c0c5d903a4900d00407a403520442410399050300ccc0c1c1c14007003244580e01c4a0320310700548 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 765849838 1250 765848588 765848591
    0xe0a0209130201090b0c030a050708070803090706031d0318010e1f02011a0d110f060703171b0a0c0c180f0c0e010203040e15060705280f0b181f 63
    0x11788a1807044400e00c1400d04041e1725a00074059041440d1040f0028050702d403185d5003407810300000340d485403416041900e43c81140d410961050080d1303607141c442c2c00620a2003440c1c80341f42d141c00101c11074481c410740029030880440c0c44a0050180d01618003480307007080251009518045028000c9500c1010701040001542403500d4550000b01141400e101c402c402000d0400c4080195240150001c031200c40d55007040c1c880820721100c0d40c809000c1c08443d80241c41e40162480c441c05110061100101640b08008002d5100454206c00d5030540b0929141410940002081401e01c0d10108100c0c1c1e014050f01c4542d80c00003860703109282c0169064180e5180180300d10501c0c808191442c2c8450301c20035006078020b00041024090750300c11140c00007100c2c00c07180340a00d040c6010540d9035101e058203940d070364414030440320b421001100040018408416001080c003203a80c41c00d0403034007060b0025000303040080104080c248100450b0016281000455454004044d440b40b40454800503042c0703001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 765851088 1250 765849838 765849857
    0x50a03030504141009050f0a031403090a15050304170f0304060207050d090303050d243003090302061b01050708090c030304030b010b0f0c030a0e04110c0705040e0a0209130201 77
    0x5080038007404613610102d1311107142e194200028461040800e08040b68007100c0030348004041620a03502500e011407080c0038681c2d03a4521814480808501d0303124803508200555000c00079640401a26001544011240415503040740031300c03080d004804911800c08000001d000170840140d00500341d02c4e104005071402800002004ea6030b25110f4031000d00850420031004039041207036403001c24444061504201c3c0d611180c41c03284004e0006402c509400a8041030100c0e20150110940542c4190247c1c1c0d021380d40019a40100b0555542c40028080c18010600c6034410901100360410025490300801c52890b011000805003a001ea036480c0340c03400741c1d0700d018080d41404400c64040d83d410241501032070b440d011495429900841d80340b06800028803a5081c03113841031009066551a6503a85c100800500c0104002c5074950210307410710b102c04001c0b0740c5140c980414036908070360f400c650000380d81c3c0f013103406a42070186401000358030010002c20072805620a042807041a03000381e035008440f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 765852338 1250 765851088 765851129
    0x16050a090b03060106030b03070e2d01060c12030e03030712050105010c051203180f0105011809021f0203040f03060f051308031f1503021c110a18050a03030504 70
    0x480d0901c0ca907060701a00000010300c000e81c040d41200780840030140844503115611071601c1681c01c4291006410700ca440035182d21040803580448102480c414040d00c902c1d49811800f820500c40084024400a2500d000c4c09200f8003d40c04101c04d03001e60400d0f00da9034502401e0040000282e80d44595400340781500104540d48208007020080358043d008050400038030301040c926400042201c04030400c7c5056400036282d0512a80c507540010f1030010403994105507201c0310a00c80c0c1440c842d0701d9851f10b0b0004016a0740e184840140c242c64001c1c6080b41f0441403001ca0a5102d1600180c41f0907008000020421215900c054881c01200904105c56100c0020340e074880300102002610000b001c1c808924004200b81c040c42c80070302c1401218103419510078000c13041500c243c101c0d00120f40d01242c00030f00440840303444004010308020411406113071002c0b140440c020131141108101000070251070118040c0c9444024100c02006111360940c0ca05d8000c2166010b80070b040e900994205200c2813 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 765853588 1250 765852338 765852341
    0x180408040e1f0f08190807170c0105070e0907080411040203100302190f0515040e100e060f10030f0b0628090b0304030309060b090115090602060c0f0705030c16050a09 73
    0x25500503030085d00700d8414843c8642d0410000b103030140c43c1801c00b0018040002c0c910001c0899044401c0543e50710340012156603800c442e801850740b418003c6c00c0c020301241d43d40e401801d0380c0c02889414a500d00751501e00700080ba010201c1680c5d600140b001043c003c059600460400413203200f00c0e80302031000750b1310b2105803a01c480b0703200d403405020700c803001403019242003080140c1100100c18804c0c205541c03000c4079415180b043d150f40c42e041200301e005000d2101485111903018009442c02d02c00c190600010844203a01c1103500c0d000c044c0c0e40d00021040c40c209400103807012100818844d113070124041e8100303130195107031408420b681d00c01040c804079500811084084401b03261001d0308640d00c1d83c505402a004441c4100c7e912036a407132a107800c9903030f03480e401406400e1800810344001010341c40903200c0f843e142c1085e03040d50311a5080084440c010002c4036906400c04446c207440d4912442c0c02c03071440c01100b0b403800280c014401c019169070610b4000300c04a910844175904116030b2880c4100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 765854838 1250 765853588 765853619
    0x12040812090f1216030609060501060201020c1b041806020307090602060103080702310b030c06070f02040b150403140118080313020f0a092405180408040e1f 69
    0x1500b1428040d160000741c9032410043d024040d43c0801e0390b500740314030303464107144000d80c0d0400c0310000d0b581e206c40d0050000764070070700f805410f45000840c54014264411a81c401400b00d0544105405040382c183c10388864012040d5004c4401c0c2d0f0700d40e0490549400006074108455502c000340000f80001802c601c0001d2150403642c02071051882c14545e0340034411901081303030341c03540039400c0d1040303146100062108500301c0000365240080d00204e440e04160030851603c0d100da00c244024031011000c29240b20800d10866411070380080c41d912090040381c2064020b4201c0280e80401190000500c5480400080d903130500500800200710581900030052040c003001400c5103905000003400041111380e2442450300061030000e0f504035000c00030f50540800c3d00106074840e2111081001c01d41b9222548180c1200c070988035440d2820b000108050314460105003090720498000708090141003c125405410703d100d15101900c0c01040c501e28608402d0f900c2d030f004840e020340c0080c1c0c182c080111f10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 765856088 1250 765854838 765854857
    0x91c06110f1804051e040c0b16150c051b0a02041d010b030d0903060e0f010c050d05010e0f0403080705070506070806030610240504050604140a17070e13020312040812 73
    0xc8082e0010103d840785e110000800444012501035404101d20f50380c3c1c40603044400030034a9041481b40d00b480d01c400c04400580c045180070f814070710700c03645127034011059502c501240490102c08440e9120100d16140b400e130310194000b841e00740c2d081421400c50038840d00080b1400000c0c4580300400381410b1303503001c0600c1103c0000711225024000250301c0d8007c282d0002c00b4104840c500c840c09180c19007100d803d11450004208001070b0044918003602489004002e4a5103880c2945009180440049030041005040161103c009000c213030185049c3c03041160804200c9002c0c3c5403006015140360f40544d0050312030720805d40001c40f180b810101030002c1c1d4400c1c1c14005404d03126103040116001d114401d50003400402d00012801d916402e010b0030082030b003240041c04880480082c40030742e8031650490000002078294140c0d82220006000c82180c030b070441180480e40c0c0f0488041e141c42c910900080d4140542d80d8200c03a0124441e026009650049042d58004810380007451058452081e10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 765857338 1250 765856088 765856111
    0x140a080c010e0405070c020909030c070b040b041e0e010b04091a031b060405030f15060a03120e060d020a0c03030b03030c190c030503030a050405070b091c06110f180405 74
    0x4030b011410903070880d03070b0040c5031400e1419405000f0b80c0090308682003210f014003140d0001c224250f01d42401c002e40e01c010b002250b60340b4034103410588201c01c5071186014815188405640e1062003c2c0d09e88038200050001d001f00e501c00c0c0d40c580c40d001c00340b42e005110300e249040c1051510756803002080f001c4540c60b440100200781070405030070780c041049206a00d41d40c3c4040c0034003000946840c00c1c41102d41100c0e40c1000380011808100c0ea40001d203202400c800d0050b81c400400f803000030035080c40f0f520801a54105003a01480390b03c002251840340350304403e0b14030b00220302c15121075003000503c80c10070311a4501303014002080e02410303541d004454a40040b94003008038641d03800400c1080c032102500400000021985a450706c61550b0b0060350001552942d9004000500005010101c0030b08030140840345455155400a5a4280703010041c0111003c4400d100003005035981c04000410305c1e10704030702d403911a0b4a801c02c0c115041120780e41180030500300301e81500d01d01441070350312400d02000c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 765858588 1250 765857338 765857357
    0xb07090e06040b0a1a07050f0a0305030411040902120307170910050906220609050907091401171306150503060f07030204050d0b19050609130309030c140a080c01 71
    0x4102c06007104480c040d400141007603002c00c032159400050078000e401e4002c010341e1007140780790003441c2c201d00703050300035140e009504000002640201100e400c190422400c5e10380d03d14441c005001440540002036004a190311251210780307011000d0f0015500540e07154010103580345400e0600e200d4034940c160300185520f05602203500510141803550805071510382000402c0c120500710101c8088031143c00c5030703000d00402c26154820410b00240c0010b40f480256420b08440140607840035001e44200720700f01d4460f10509911030b007814510084243d14207242c1d03060407250403207442c0343c81000340d95660900c0401329a1601d41d080b8102115005001003550381d035035182c101c2081d80701401510800d42c08020020700380e5100c81290080301e000d14200c0ea42400d1014110a00c078030803410901090b41080100700d25030340c0d540c071281c6c3d000e6800350390310490003210b28086030740c0c400d1504000d18004d042038000c66070003071510314502c05510a45503003044a4803039400c1591604180d01075400503400c2a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 765859838 1250 765858588 765858601
    0xa0f030e161505070f061e0e0a0605090f06070801060909020f0307210501180e0a05120a11060a0605010207060804120c020d140622020603010515090307120b07090e 72
    0x41c2c600c0030000041c60710300c0c180340c060382d10340107070301c0d800481078580c02c0d11000880110480c040c01400e5548004e08104080e0380309003081a220101c84601a1110b83d841300040c58407d030601c403841800c058803082d1140d502c1d00d05c50140c0000c000303004160004159100c00305200e0b101d842202c4800700e0b40781c2007a080d0f50380c1c1c081c01c98000250940202c0c4000c1030001d9501c05900e0790040e54080c2c0804840b00740c030701e02b01a940b40116002d40e40404130560004500d240801c1000c10207824070301031004199074400c0032110070703140002030001c038110600c518030421000000f2030b4403031000c0d50301c00d0782951020f40d52001d040301c800e0410f5501520000d59403d5035074125004d01c00d010001c0384007400e0f121b0740310540e0300d0300c45111010b9007030138003241c000d0820020401250b084059203e0f60103d541803403800c194010038800d00050040c5800b030b40e84510500b1000010ba81658464400242109e90103070f185c0c141110100c00c83c1d01d08503145401c080200712120700942e0200d013916820f0b5180070465a80301d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 765861088 1250 765859838 765859859
    0x6110708071e05120102031b0301140f060c0a030c020f01050f160f080403080a1404140616061104330f0c0204180b0604020901020c1011030a0f030e16 66
    0x640d482100300c490b400102901c0c4c0104191280140900050720703481c2442c1d40a9080680c041d240c0441d800070401032002c051144508802d40c1e40c02d03201d0108003412400030a56503c20b10403403000510030000c00e2020558080b03e140100b9100362480c5448403903503001920f5500aa501c1964030a8042c052604444561000065164015040840c0060b0a9203400c0c02c00d501c1034006403503020f000500c010500c0e07040010300160310f08506059281070f180501d01450080c0e0703050020700c1020000340040e02605640041890144c06c000c040180300c0013610221820b510521500c0024410726040c240300800991000411034050000105803070b802c7e101c2110002495000e41080c400391000d10000f503250340c41001005000c15800d40f00c07520b094181504201c80003009d0030701c103600401c900c10300f90340e0200c0d088030b50b01c201f911035441e60440329201381d071001c0b50040203081902c0302240c0c030311020b41c0c4a803516100001685003042004104c0f160251141c0002c184001035108181040000a020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 765862338 1250 765861088 765861119
    0x20910050409031e0f0e04020f041724040209040f150614120c0a0317070b0406020702010801050d02030a02060a180906080606091902032d010611070807 67
    0x14944504410352180001011108012400ea00094111900100b5055103104d403084440090410280030314034031500500003104011040c0c040c0d500800c81c420000b912a0544029100c904109a44100001d00440c0d44030302a202c4c8114820015a20720000e90002c034955000750b4000e005820956159284c081c8500382002d82141e4400c3c000d200380340340c8110f5200703550140c081c4140113103407065120304010850740100d4287d101c91300904100c03403003955140d0f00002225401040500b41c8603440070040540d0241a401400d90102a4104400c00c0352070707030080507141d200340c0b030f4405180d81f5101480503102c15180d00940560041100070094a050406400104c3d00b0b407408030390320070100362506d02602c010741c40100e2040d20b8500520400342c0602c00c1390760041007620b1290092400d0017145200303100e9a1142140c0303650001c0420091840120f0300b500d81d1082034095010624200d19840054030709201d003000044001103a14207135400880d02400701c3d800c120062540904000d2860303100000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 765863588 1250 765862338 765862351
    0x70f0b060f03032a011401150c17090a0b030727080a1a220809040f0518060c0a0215090118050303010e06030a03140705011d03070c12030c0209 63
    0x6035041c0d6614a60350420042c605900b42c4400c214015083d210300100c001d284c1e2005640b50303410851400c9070303000d0244e0740c01c0c11964000c602c5203a2003c1040c05940000401c0c0b0b000e04413106070300045812407044002400300d4841030300d1541503a41d80d00000c002c2c80c0400e40d82000050400c0c088a0310545030484a0795043c8680410004007541d1202064070304411903008880000c690070020301c000c0a41c68040d60710040c40c5a40c080d200b1921401c00b80c03220461000182851404500300140f0b40f210b601041448206a400f00103604000501400c104c50b10781000009100b03080000b00700e03008540c1561a0000140c0042ca480380099100c1c0c540e0400042c1014502c0d0350b00c560796562400103c01080c040c81c01540556078a50410001c0c40c2c14075802801c950282d4003203908000020780c000146104643c542e50b40a844841f58509580074200e00303130710042da003614050003610824000c0001c14200e44615800b41d4a036070781c2c1a82c04040c40035860042c1c04a08826650030141c1000084e40e03a100c035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 765864838 1250 765863588 765863599
    0xd0b331320030907060212070b070507210809010e0c0603150d020402031302031b030c100e0916091418070c050102030903070c0e1b09010c0c230105070f0b06 69
    0x216544000c0c001d0380084500d03820350350204108100d0a6018032069a0304040140d81d2881c009940c2c40741484404054909410054001500014031680d01d8081c44000302252240c1c1043c040502c006003880d100b51400c980380e500e03201c0540d80c034034030000c0d010000d05800382c051811a5544045800d21404074114503810449000e03103400103940d144004c5222301c00c03060900000c4020347c01131500e4420110380c160b00140f04031510f00c0c80c9941c00106180040400c88055007884040d0f5400c56210b1146041103030004940002c0c40407086400380c0c012244982c503a40d01d003d2550f104c403690302c020b50030321420360002c940e500c0b01d83c212301030301d030410754442401d003402c58030504540d98503422a44202c407542c9440e000402ca42080110b200c00038001030239141c0026501e8240f03030314001c01c46d240340c65900d0340304080042c000b601640107002c2c00420302d4010399440c1030941d4515541c404000b4220080f401e0300d610070f001003100d40c010b10907901815003100c1d04640302c2d10759588010035040041e040c05e41c004e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 765866088 1250 765864838 765864881
    0x150612060f1807030602041e0f0e040305071a04171309020a0507050a0c081b0f04241205010c0306060f030b03070f080318011d0f0d0b3313 61
    0x20303441040303d01c00a51007050700603691490800d044104402c44000c28071201641c4104000c0341c01040d00c51000d5607030024041c01661940d241c2540c007441405030007030507031001070224070408036520800c500c954001c284000c1e000e0707a01d00b00d404440c4600000b101040100010a000d03035003855000e040b20503028200350349800084e0700e405140045600b13040354107040e11003060110403000c0c07020191042007c05035500019480c000200890b01141c041801345a44041e482da40b100c0000180c0003030b0807540e04414041c0d44a01c00d803410300025600c2034980e0340c20403e0041d401e900c02d101c0c400440e10903640d46000010851b0b01103003e40405d00455605200c3c001c030100f9a0a040103040f002400342600071035031801c9680d001b4503c2250680c2d098140404140d00c85000d106c445400c1025010441c0c400061040310b000050302030041d03907005041c81c50040b0400850000c0c0b129029250f82000d100310403182c685090304652110964141ca030041903018910714000059080001020321a5481d010030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 765867338 1250 765866088 765866131
    0x5031b0d060219120c0e0f0a1a0703030b09060d121e0e03010c0306210c030f05010b150f0d0e0a1a150a03021f0203120405150612060f 59
    0x50ba0807010b860f042c0c0760b40340e12821002c99000880d051006000000921001c0c440800140c600c201a0503454000c5224050610b01540c3d41e00c03614001e0503c1c017142c02d8001c08041c6815500c1d07002010100d010a1a011103040603280c030740c0b011131090000a0941d0420407059413056040d59440400d030062000c09182ea61001031341d105c02c450003544039500d0701002070201c0101402d46080c90900c806062034401d05014506180074400c4402144142e80192607086160244038601c10758005022a0890000700c03080100c10b42001003403c2d000c9640d1031003021380408000040c419400005020748003089204a0814203400028242c203510742510700c41590f9807a5202c3e03100c0d04810490b025000e0714100400c012440301c00703a8000e0f1083e210084403504650118640c030307250b080c581c0c080b0407032035a050403401e00c200f04070f40480d0049211003145041500d04180e5038000982e081c003c414002c0300188480c281203a030728540682040007062030340c480001240a001028000720b001d0040c5800f80c015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 765868588 1250 765867338 765867341
    0xc021f05060d120c060c02030d050c03060306010302011b050303150a0b120f310b011502030708070816080903010b06090120070503010c0206100602150c090a0509040f020112020405031b0d06 83
    0x207140c0035640123141d0710350342c0480074011501c0060050708014418000c1c48015100043c0950641c1d6082c00d06c02e8850001d41110300c0001d400110040152000100304540d0f11045203951012030710544402c8880d6803520f40703840407405402000e00400d450980003c90200f149460503400500c8000f004144054070820b803a5049140707694880003c2d5071007652410054281a4240100011b00c010035100d044c84000039181e204514000d0b100030320102c0e54000b48001b90085070042c00405109807403c1a80b498401c100740c2080070614480c0d441d00b048802d044c10202c0486010080c140c1d00c1c410041a003a001180741100361044880c140300e09100442c99072800d1284c0d00203074480382c008048518246101040140c0d840d00180c04640003104040c01d009440808641c2040008000c40e032699541404900c2c44c8103035034446603001015005110610400001c4810401c0c002c2c0d035070510072042482e03c082030b440365100b81ca8141e4092480000040042d0f40c424546040007000c1c41440741c15510b8980 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 765869838 1250 765868588 765868601
    0x120b0904080a0e03060105030a0611090928090b13060618020405270c0c0a060609020418060308160219081507020d140309010f0c021f05060d120c06 65
    0x5511074400998014559040b0a05036600b01044000300f0040d8144000b2a4075210001d00c010310140e160401c880002c0c0310101500d0000e20081c1804d11149028000d0440100c8003000d55141c00150f05411254226140070311030420340c100109540716104d046011404911008060392007a50310100070032740002c3c0701b80c110b0b003000c224100982c5860501040010f18014290301004440c881c1100403504c808440949038007072a0f05804507102c0c1c105610031828400843d00040400d4981a008903000b01c4070f81c00360080e0f81c1045001200c03100750090110444840c0e0001034140c220a110582d0005c4202d480d03003034039501c003070071160380c2d00080c001c07a030a001c01a40010704d0940100070b003804460f40c2911400e50240c0e00c3e20081c001c0010812014102ca40303580c0507081503a20000006082d00c1007500b0840550888140800c1001d8010f83d0094984000c0c102aa00400c1d10300d800b5180300c622401480d009410082c2000c00b070755102e664444240403409035490a000e10071100d44e012441604c500d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 765871088 1250 765869838 765869843
    0xc07020f180f01050f0d02030a0602070212030a020601410109030f140c030318011b150f050108071802031e0702070806070f17180706030f0b0a0303020d120b0904 71
    0x7140c2e07541840e0402484224a45089008100101c80c40000d6030780040c040502c51340001005039102c40b40d002191200705001070316925448005035114282d03500081203412a00c1d480290610111010f022017060342c0c003c00305106501100b04521031010a000043c0040c61050410000303c81e0f0f01c0d034442c001c8072200d05003a00c0050f0454242c180003074060010903050403040b009145490018284680d0340e10030481e0307582c10800511110102d036026151441411608115484100b02001714480054000c0c40c101445e07480c2004000903444900085030070075031f90b44000302e03000850744d490484000e420040c1109100201e0042c0019414200680c540c007540281c1c2c09080c0d41030500071002c2c074209018211504000074000074014581d80001000d00c1e40e090380d41c0a040649460380c2102d03003001078002d0000325004000d000a00700c1e070168402c1b5144014480280206003c0c0000c0100f44580c6200140258004a01030500c0c28401d401c150640c5282540c00500120f0f04004a51801001caa04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 765872338 1250 765871088 765871111
    0xf020f010e1b22021309050c07020f090c1803160b0a0201150b0301052815090504050108121c020414041a0619020a02030109030e0a08060c07020f18 65
    0x31900b080c04140b070580c1960b001650981409041003140d45421059001d0880d411607000c038003103401c6000e0f128004003c0a4101c8280920708201075126600e510401d4100d1149201135101c01440c105021910710880440c1e4070203080c4801000d4040550301072800c1c850f03040c01346525501c0ba1030804810b440203481c00b2200e1a4075180d9000010b400c40744039400204000961140c200580c2000303408490640b0019161204165049503000c5040c0d00707030095901d0f004511030740110300040d0718200e580d00e0315403070f585014041e541d84c0c0511044410a015610035900300103080ca81310746a2030014195103604032080e00e14084c00c42c150790100e0b001900000340300c0c0031501d0400824502030240c4120305003c1521300c1001000c042c00299540b040d40c030509404190b542500014034024400345200700d40140080c400b0780200d140051050301c621884902c5801400c0d0081380720304000488900c40c0300d840f84410324200f019000c2150080182c0d01c45584400e803d030340c2e092524410022203010f4a404403030f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 765873588 1250 765872338 765872353
    0xf030e070306140c2706090a081c0819050c1e04052706010e0d050f0606150a0e310911030a081204080405060304050a300f020f010e 58
    0x200302480060281c41092000130034404a01418030031031940e07180d00c0300e030041c15001d401803001040a07800b954955a50044070030100258145010a10702c00078020117010f03840004000070f00b41c5504030140c410b0b46101004009805100049034001504451038a04440c100401c071020850b241042d5078032008005c2005c2000c2040c2c0c140f4610301e200014140d00803000991a01000d500d00c44c0c00117010ba410000201092910341d207645144e0300c43c41d03800030240d85041d00b41a42c107507918039007902d00d1401003400910107102da101e240e05894122089942d56201c1548620400c4903c81080e9051000200c0715080303858045484910340907180040c44011030000300c14140180c601031089600350007500a4206c210000710103104481140204580c1c160068550303003805150b50082c0c3c0c21498010300000144000d0100028400b00001d03c40c3c0c00f045904440200c00401c00511002d400c070042030089024640ca84c0a1901618042c50603c1119168418440340e03d082d55030348004807159800066 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 765874838 1250 765873588 765873611
    0x30c0601061e0f03061706061c0519060b090a050907060201050709090509030405120a0b01080c0a090f15060903170c030304031d0a030b0609060405040b070f030e070306 74
    0x11280140315a042540d072200012003500b02c000c00400052041040b007400107803001303001e9404200602070303400d04030141c0b155081c42d1070350342c000540e41e042c441c3d841c0d01d0b182d000c03c49a2154034841c50780c0c000080c15205101204100d0f00d904400c00456240c0d4403248255020b0310f5141046c6d2180d90300e51808501c0c0d0800320100c50420040c2c1c2c00c074604590416040000141d00301c13000c94121450380b000080c042c3c0d601040d0368218042c0741c1010b40d02a8038441112240000001c10b00c041d50b0090901e0b40c0180d80c0c900180e996905034103a02c0e500030703000190130010601c00b544500301241c540e041c007003028691301c01100d00080103500000041242440240248031240c4510484841c2c10400946030100c12100a9030303d01000340b00a080021001d82608100440070700b0528100000e444901d80b1901c0785454081400c0840e401c3d402889544000380b5245894001d25002c3c0d50000c03803030103141e1a1404101c03602c120075000c00e01855103880c0082c00109080003040000d50080c03400244602414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 765876088 1250 765874838 765874843
    0x6020403060b1917070f3308060906060c01060602011b0801050a0e0601270611010b0a03080c0a05030f090307080601061e120c0309050d02030708031f05030a05030c 72
    0x1081483c0140750500345910300301c080403c003800f07a5010480008034801d564100074507041e4a0b4100010b4032030111000100e403000e9011440754000c0d004101484040c2d0041c0c45c009000402c05442c1c006409580800c1d041d080c07644620b41c002e030025145a00d0b1110f885480e80c01d4810960056005079034136030040340c1b0640c2c201d6280120134043c1c50807000307951405000450fa05541e004113041c5036550000701304a81c0c060260b01d0308190171050595010b4401d908101c850401501c1a080480c807400306030711000c9018440c884400000401c0c2c520468150b0700e9038041a080700d104c140c002c0c4141500100400e0081014204c02c41032280d24503a100078040515080c01c0c0c4980c0082d41a500950040c0032007a0032140c09052440810540c404609401c0b4048801c1c0d486950500e103164902042d00c1c01c0c0d0741d41900003030f071840e01500880b4807494040740c0880e43c0748108031020b07008101c18404210b0384400d80c509142c00c0c1c41003002c500c0c40d40c1d8813a80000d041802c20041290a44e02c0014050304400c004d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 765877338 1250 765876088 765876101
    0xd080105010909090206120a090c0306060612060819080405040e0303040611070309060503060d12020604052a12010908120906070f0806010c02010926150c1204150203040602040306 79
    0x3d0002842008815400702d039090140c40c0000505e645501c0c006460740d4529409004076a0708801d9902c0742d643d82c6c2c14440001c040070701404000800703034078109200c030040c1e004a000b00c9841100408141c0980301561040c070789241000c64001c10208400a9695502d00a220780215110055546e900302881c24038110b036603211106054003c2070007540003085d04603401008543e018100356549546082c0050480310110b40001d242002481c4660b42d056400512503100f40c3c480e0301100c58607400314240304124248100c0e154110041e0580640860a0201f02c0945404040002180c04150380d41c1d0040b468011220714a84500504104003420380c040090740c0c2c00814070300300080c100301c0391a40203000e6040113001c41e05101c0344901e0601164414641900140504440d600540e880406141c07115508406500d10038400c4032200403c0148000c243c41c040c2c2404044035241c03c11260549000001c020702c150b40c800402007007500d540000d030006502c01c52080e400107a40e14110310b08041142c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 765878588 1250 765877338 765877349
    0x908011d161401050a050c070b0318011a061c020f07020a0b07080d1805100e0705030c030601030b07051e04030312330816050405180a03030c09080d0801050109 70
    0x1a03840c10040c48900309a0070b00000e0080c079090b03a0b00c5485c040281c84603c01c6d41d100031094405e0b1900003d503005c540001c0d60062040003006d0549549560004d82a90302120400d480500c880343d208143d45411401001c0d00c0045642450078008401031110480c0c21110709895100f4000036008110f1910b028030b14050718203480090b0410056072201d044500403180d002c0c80240c2d03141c00d0300c0749411062070f007103440d958000215080d00c0e40c12039401c40900541c6c450200a0302c20b150300410740d4038001c00c4220011602400500c0c942c0e10703540350181d540d0009013907071050010401000c0e444156034250b009241004010090b501c80ca1494004c03c454020103142c2a114500100000800043da440b00d0660340c0c40d1250791000c07402600d113103101084560081c0c4140c4134081480f504080c0c1c3d0a2190100e80d800c0314100800da8801317003203c0710203070522040281c40e000b1b01503810001e4049c0c2d000c203c010001c2d2a01d682c0307003170f16503004504e485c001e00d60040c08181c040004100940e03100f0800d102402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 765879838 1250 765878588 765878623
    0x6060105070b0109092a050a0803070b04080a031401030305130609050d06150b07030809160803030c21090115090c020706120921030c0203070c05100908011d 69
    0x115282e0300420075060240401541e140d400340300c00d1028540054400d1582d504075466064284108440402454820540100810540024085404401d8800840d04004210b80d595260f80c1c48603160b078001c0ca50030702072568988030301800110800d407a5020314420f444039581c424001560b0310000f0900d5008000b0094820f901744a0b54035602d0021035003075403048001c500d1030754040d28038094021542100c05484000700d4540285640054280d0285c4401401d896881c2c003801a020741c455824000c08001e0f0348100081868880201d00501c0145508020010007030b0810101d0f1922400c01d0342c0030001d81c0c1d154031a45003c140341000010003096414010044000703c403038060740f41c1c42107100d07040510090a0700d540403101c080d0844080c3c0c40c0c0c410144400072181c000c0b41c094580519040c0e1000038600701004800900000c210f450407a00705841e10000307440c020030440680f4402c01810108084818001100c0009024841d05d41880c00042d00d01146800c050700d1425507008003070350100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 765881088 1250 765879838 765879847
    0x40f0212161823150c011d030703020d0809010609051314070305100e0c0301050a1b0203040617060111060a0b01032007063801030f090507060509030a050105010806070206060105 78
    0x890000743c40a0b11055800c02a030301d1005100020300d03030300500d49448800c11000617044403401410741c40b108001080740c240800c030702c4480e16065a01e000d01c58004001d80d10107001e011002d130264500c19403241e400d13000824510f407110145000c1e42d030140e542e40c598814042d896000c100032031b10412074000c2c490b00201081c80c80c640715241e803a030400050f0061266a0408144848818080c00c0c2e07036141c0203030003170095003030501d0010000c00701440010b40c4002d50450b07140d0762910110032502111041d580d080e170321000c00a000e000400c1d02904440c18440da0b00040c941d988400e100103442403900d0031000950098150014040d910003100001c000c000169448240200704000d9038556134002c2d5001448003041442d40005400400c0e802da070074101e80083c0a054044418821a604020b90b004d201c0400b02d12070030b0085d18030030f401c01083c0341c002c444140001c5101d42c026211a5100604403550003885445040c00c5450070380020034242c22050810455680401c8256040b11081ca00316281 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 765882338 1250 765881088 765881099
    0x201030b0f0a0506090406080a05030309070602030a08010612020403021c0b011d15030c0d0b1509090a0f1b0806040506090c1008040201050706020f0a080106110309040f02121618 78
    0x801801e0180784e01c2500003240d80d5140d52690780c031100241010000322900d822450030310540e0394000312441d640c54810f00c0000300e0854400300944002e080349445810082e4204801501d01d90230803031035440c45503800e01c0008056541c004070742407000055031440920058500308106607502c16013040c040c03000c01c3d0410b00101850003078807651003518204000b10a5040000081c03d2200b000156940100c1020b041c5080c000b200d0304280c040d8010582481002d0011014000d004008540e46001600454005000301c2e0210703650518152044403414280c05d507401118882010b1604104040c0d4070800401c0104031080001a41040c81c5400815102a07400001803601d4914288403003002600808a0116400344081d242c60329030040007035459841c0c02e48022030f640c00940100000850400c00018490702401102c480722410b540a14500368580e02444003030020301c2000c1e00034681c02c1105804040404190070300800420020a54070507603a60f00400303000c6444140081c040701210200708 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 765883588 1250 765882338 765882349
    0x30c1e060f0f1c0c1715030a0812162c060301090207140102130b0c0f12070302060f04050624040f050103050717030901030b01020c03011a101d012007030506040201030b0f 75
    0x600d0000b404407100317165a8003007040e1060000c1d007401a0140300d41c02c0d5a5040200c684007410059004081c1e8100c96a10039501031122021914981d02003260240005217420192038540c1071406040702c03445c12092100040381d50744d402640f0041100e540814900d0401c0b84076808004007107100740c000c0d81404014400700d400c05c8114415401050000292802901c41c11301c40c3c100150b1401082d910110381c104505a1a603008080803401400386000042004641c650418000c0e6080801003034255540c034050300804540c03005080081d11030180380c2030f07140e07150701840b14035111824002c5480d5145140c414503000640c0c010088240144031600424107000003900e480d03200902c1d020900f0340141c80140e0824070050401c5070554203120b8403001c448482c80e02d417805100b0136100340704088151801168500000d03210b07180801103d4102c00c84075841012202000100d520001c1c03507400030003440520702051548126141d4110404200a540e05840b40e00300104050f60204030300c45030400080c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 765884838 1250 765883588 765883607
    0x51c030b1003020a09080303190b010807170a09051015150f1d0d0b07020c040c0e0904030908060f161d210703050703060b030c1e060f0f1c0c 62
    0x4150f4041504041d01d4420300c0c40100400d2110285d0707a8030700b800c2050b8448101c1042d0007a0421341880c02c1c2410552180c9042445803617107580b81000740c1c1c18031000149000c80038124081c0f8503212024280414400d000655072010390250002d10041c42800d01d016094440d401981011045012150300da03400056014500ca003a281c001c40c2d0018400c4008066100308403a15000004031740342900f000030341220540640706079000c0340c02c002000002c000c1581d2507001400c001404802c07407541c15007002001c007504103101e407d040b10050f4444020328940f0b0001c81318880314052020074080500e8580000c031002b51b025240a81c06210300208001400e0101e59105004107214500da40403c02142e4110b804001b07203209440900342c0da4100542c1d0b44425010a590306d034070b404c80c03254092600203100010400301520b0902c100c2c40f07254900b949a0910f44142d07820a004100141d42801003030014402c4c144882c90080d140c0c01e85070480c4039003242c54140341500307901d017441c0320000b2a000040d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 765886088 1250 765884838 765884869
    0x60c03051b16080c040f05060d02090c1207050406030b1f080a090221100203040b070f020f03190e0904051213030204060608340e0103021204051c030b 66
    0x1d24564a06010301842c00c030020390000e60054042c4404148004040b86000c034000080310140640d1411000f000d04484059500c154094941803803c0c4c01404d000e10070300e81c04007482a20301e00307000b4441140d12158a0072119240001c000042c18485c0355007511880407070480580340007006d10361101f6492074030003190240c1c0c0280040ca40000d519001e582d0480c064282d80178241c1e042c1c051001d0880da900910b00440d680160180b5020440c02055038800d581c41a504010303501e04a40313404505176050007154070800114010300b43c01202e110010001085011115040304803450b0103503030b0040610a44109440c4140c0d038410074440840c0c0e0010300d00b200c00f485000b038140d4030300c034490804604200c0ba40c002900300c0d0502100080d441e8008083c20321460b00c202441c11202c40c0035049584c08603400b184040c040c4200b50710300c03000d248144034801d401503040c10018035091042491110000e012a03007140e860303000014159112917644400c42c5000c58909003800304418840003c4c03040210300052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 765887338 1250 765886088 765886117
    0xb070201050d2408010c17090c2b11040c08070206071d04050115020f070807140429030d0908070e09071a090f0108040b13060e07080f07060c0305 64
    0x4410264000b01d104400300f80a040c106002142c0d50708009001e00b1000c0410400b103140000101404c09200e0b840c4d038030942503100a01051842001008010b02c0c00720800c02c82c0200380720b00102032180598902201d14041c50708501c40340000e80c01c210581d10608132140800052005012000b9000103c0580280b014240346c0d102100390202030181e4004085420340c4181004000200d407020360001e82e0088103103500740c0f00107840d0700042aa949079544501c030300a0344a1602000042d91100070001d0051006101182a041c41c1c140707640640c0703c5a41403040f201803081c81c0798807032404208820302d100c0c0e40c0c1024003240f858180090f88418646c0302b60707030200c0c0707800d00000d45038030090205d1405041a465103251a41512204112a80211041a000e0081c500c690602980903480c0300b441207030b000004240c03a558000c1c10500381401d480046400030b407155055030004200b407000101414102c0010301c40040110915403030030b0801d030f0240003405492104140440e41c0310080b5488058540030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 765888588 1250 765887338 765887351
    0x6060103022d1e0d0506011b1101120606120f0e0307110d0f0b01081920180c0a1707020307141c0f0825030b01051608130b070201050d 59
    0x90b1501d00e440b40b051604448a203c002d41110560b40704050407036031401c21800c216655540005681c1031102800003503511000500c0c020018101c81e0b04032074401818581698440104004417003038903e00c2d0400c10110301406a811080341c041d1040d178145c5890104140031001007882540d880388190702e40039294802e001c45420b0191110101007100e168000d03007214078500743d82040c00c0611000e0041c0d203014050a01c1c00002d4048090004c0d0300350340c0003a80f412a01d04441482d03c1041200c150031500842e0b44200010071030a484400c40c442d240c2600301030354402c03036224020010070000440e050300c42184014040780c941e0020941d043c0076800f003540061240d030090218582a80c81072488442085e6500c130540059128410150081442c2c540c805141c0f2050b0003600d03065081cad080001003020340d000c95000380d8800e0f0000340000d076045c14410324000750320b103980030a00f000190540300c401001410340e00000500782070000505050014a0402d082980024654414070742c0c004825600c404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 765889838 1250 765888588 765888667
    0x51014040b04090b09060f0f090c120c100f030b030a050c240d0606030b04051501050345032104020a080654010b03060a06080606010302 60
    0x512030010260041a444c06603e400b03401c0f6961104200c5503140000038003401b14042d105031300c252034011080070028040b0b100c1c0501c1032085034418040c0307804143c03048264500c110b45401c440221840d0305030790fa520704544070220140c10f58000c6401300340258032900c22400402c0e0081f48849102c9011030700104031100030702c08481140400e0710400307035005001403e090440b4555002c1c00888203036440c02e020f944a06010131040f13450454400c605d0310544121002558400e10095621443e00409241e5030035452030306110752064184288030031240940b5607007c901c006003031101410112001149001e010b42850030071002c0d89000800040465008503045548011154000d0403500c02114010300d0900440b04642c20386c203040030810b902500341d00510502820141c0030344001010700c4003241044050385800500112102205c40d5642ca4007085203941c113000c52070048400c078001150480c1440030072802c042d80a408907041c0741c030410800070354954003020203500c1480b503102c0000d0800ba06c0d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 765891088 1250 765889838 765889841
    0x11a01020723060c150105041407270603140a0c1202070201020312040803070305250507050c0a0308070611121602150a06030c050909030304020d14070303030609051014040b04 77
    0x15560b4021000b084404e0f841100103081040820030002c8004280d0b13a032018442200e002070780d0b120502c0c21910004d003070386004980d031890b804c40d2181303941010314140325440742e902899000709001a864103000601506084001030b00b140c04070a0411616080c1704015048940c41e1810011541e008580c0c4000c2d6802407007038903210030030280f11103400d00c2c0500d800503c980c403c5501380007081c68440443c0b1110307516039800340201920403498003403110383c50b0283d0b00c0e904100f50485052050498541d1542c55040a18005600c101e10b41070303c0d00402d02d800d0b82500c07085036418244010078094640386d043d4400c0555000a961003003031040b01401d01007241805041d4032440c2c00d41c400b03c024000d030b5404c20350040d003c60780145d420101d45074070348040007000c14042d217864281d64401d2001c10058a843c0c0c00240c00a84110021144188011000c500b04181da60050380400d42d240c00030801c0d500710b40185503000052010419000b03041034600301000303003d004214006c0b55695401823890721107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 765892338 1250 765891088 765891149
    0xb0906011b0305120a0606180501090501030f06090e030406020d1e050702060d0509070602150907030615270606020c0a1a04270b03030313120504120f020102011a010207 74
    0x84511298040c41c141650401403c6d85124480004070303041094110300502100d10300035100143e5070710920701d10f00001100601a5220300784038441d40e0340e100044100642c03203420309104850b00519102c2c1e190805c041c4c285207981c2100c2003030110101e00000c40c0482c45510004030747c038034140329480c0c00c402d0000c22224014480007601061402c07050100703010340022000212005c5500304c804a007408050002d900206036194600b42d403241c0c0083c000100543c0004d003000d500c9501e010481a510911003039122121032a60412159912242e00580620b001e04005042c050000b08000084400494030940c814403500402041030f108080e90340d01400200d80c018010f02920800c9076958440359007031980b01c05840014946407100799540350802006880c85042c10400080d40c503541515002e210290300b855032010000200000b18500080600c8607402a0248001e20701440c2c9910029084440300400790010002ca0710021881c0c0e070340058220180e6984c1d190211821158001a5062014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 765893588 1250 765892338 765892357
    0x50a0e0f01150c0b0a051009090c0504020703030b10030b090114030d08040c0504112805040b131a03090f061501030213080609210f07030c0f240b0906011b0305 70
    0x311105110364503103140c006c1c1e4041d80d02e00079104009a51015000304644003060000c200040c1c42d0005c002c03070310700750b80070300540f80c06814085001840c510010344448a00070001020036a03540c1010b905087c421280c0d0f024200704440c074030113034801340f000960391a0101501001c01ca00700c000142085011134400005000151052014034070395a80c0c2c802e143c014100072002800313888001c0f5034403a41c841646445400390f480703080c9803508151082c001a4450149142c80c140721590006407102c02902d04070308003001c1701c0aa6101e041420041c0e00f0000740000c02c0110303500a406100880c2c10822007034103086401d0038016525020020003403842d0480350301003c1c06000d00e00401c5081000801c4040c0820400300c030b0780709030640d0000d0008281c001d00e0041c3d08038030020310100001a00418282c01441c0c0035880300d0000100320740d0740b0181440f03421070031035400101c000781c161030908502404000b200c049814180070310300303038000900f401504481901d00c050980403107014140610100d43c00e160 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 765894838 1250 765893588 765893603
    0xf0d0e030c0f010510030218181501140a0e0a151a0c070602071202010f0e0a080d11030f2b020c0a02010e060c1506030f1501050a0e0f01150c 62
    0x2610031090a445280420b0118069424000040d141030072401c0808184c0768010208a03002000c0791f40400c0d800001803881c050001c010b84040380c00c8808111482d40d41110340c518848640c1010b950142403094001c04078040c0c2c0c00280d003404aa0003590000d5880884c51100041d10602c03810303405440030040d4040c110360302040d8040c242e580103160041481009840803a980c166581c0c0c0100c0e03907100d49208151200b0207800d001c1006603c11100d072280780400c7d180c160700c0603d9200005906e0501a17100d045e80e42d008442e03601481e9009134100c46c650250300051420106004040c400c188504a0007081d0f504403146404151030003021011010110b18408549841071800401d80c1e60b078130f00b08141e010610381427440c00949442c000303c030200c9200c43c011f031044038180414421000740140c05c5a034540168032040100c070104000d05042d08400c0800035000b549842e050050340a01900b00c490401c003002c0401c501c0000300b035413030350465101781d00e00300341f042007a28203e0f82c0b4059410000c2600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 765896088 1250 765894838 765894847
    0xc060918040606050a0b0f160201110f06041202070501020a060b0a1d0a060e0114040f060b270105040503120c160305010e06090624061612020607030903050f0d0e03 72
    0x1500d43c446401e50b14145c0b1602d203c0da44031520703c40700d4007a1607005440d0301e000b04400d80d68000c0d40d03180c9011451041c10a64001102000e0113820709541038090070041e80f0650400003440014041c03030105281e00c1c006480c20505020000f911162400c0c0003401c001c0d160080b8031140d8a903076100700001c0c417000305010b0340030481480d42c02c8010070555880040608103c2c2c085408030786a08184d04a0700010030744c2005440140c02c3c0400b80400c01e80800030140d032090002003108011004048542c00c0c15180f000d091009050b1141d4640d2005000b0b04019040c8420b0001e61030000c4c08448403002c000030991141030300d115540c0342c06560203200c519189913000010800c5070540140c413025882900381e550302c0d070b1386200c3c8980d43c00c5e04030b895018045065010303005454105043c59901400604854600081c0d202460001711030381c9812221643c01090100a0796410300006402a107203180c01d01c0302d4101030f00e0040280c040d0b0010590802030014402d00b210b0803d91028000c03805c20b00540e40c45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 765897338 1250 765896088 765896093
    0x807060e130c2001110a0e0d080d02091903260903100204090f0b06391c0908030304060f1503050105010807050607080a050307120615090e090c06091804 67
    0x6107035040ca1404140d05101041243c092018094007500d0b45500b0402030074401941e0045a01c03481000d00c0c16007002c070400d4640080b0344000010103203948a40000360f03448080070300b8820740304040e00c8502101e9641241c00c0c0700194400c03942107071294aa0f04c51041d44500b440780001d03944504640e4a900d40328034614845980030b642c007e88111050150200060000c80c00340c101910004e95100d41d001008112041d0450400d5203080f10012000c0000183c1c00304020b1105c000c00e200d00c4800315903507c5090302e41100c0d14000d000c015510380d00d07d40780055038a040901c5130b176800003400043c88952110040501131150382d00080904d006000120b443c0f40d6a81001c80c000c02d400e0140082501034600081003504060086414084c0c2c45039040c0d260682c480c40403602e64001421f000308112000088030034074000ea0041c4d0380032384840c000c464401c1c1c00e0024042c2c0600e00719030012070400c001c0c1c010003400d440007191440c5060300a90380c4550762805200068103080b030307035402007100801c0e41e400d1205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 765898588 1250 765897338 765897347
    0x130f05040609022b0209150d0c020a0b0c071e141603030c0b100f080c04050a0507081311030f15060f060d02070f080a030c0e0a0807060e130c 62
    0x84680584003089002d8949880400764030406040801d040a110f0144890442032500c846102d01015401820b10f00908006070000344500d0340707286c0300003000c680303100b1008092107041072045450004000c00c060590310882c0325a0000c183c0f03070805101150550501042001225181034820700e0081040020303d07020780000c140801d82d40003071290a0703440e035001310060880307000c0d290580c07034816012209594110340f440c0014820541c021030014002051094006180041c1503020003030b080e00c6042034144001c6070002041606024141824000d40f0340d000800c10390003d4114008101103003050411104ca440e88140c0285c042c882c1851045c2a4100804e0501c026014040440e407070340c40d4401001003440e40c00b41c030503501120030020f10701418203d50050880910900306845070b0301c01500e8040e0107800445c55480800c0d10b0b0820484141c0e806043c0b90f128140c200c44240f210707800d00d10044e646002e6030007408140012103841c074680e555215803d2042c8424001e0500281c0701d0490000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 765899838 1250 765898588 765898619
    0x5010e0102060f1f170607030c0e09100506040315050f040308060607170a11010617070618050613030201020606040608120a110a11030f030a081501031503030306170a0c030f0813 78
    0x600c46c0200000704154a11a01030040001c80703e07910840200404000c1140215000d0011182c1c00e409640c0000c40d911004090002503000d0800b1486445100e10801c0035100300070312a030a2159000c08000001c3d4001040c80d800c0075043d0782442d100c00301881c19405000044581640c402c13000714032070007a603500c14076540006e000d240c0244440350b51381450701e42030040d4a201d44499080074000748000d520031081035031140c0c100010410505d0740e03400030802e650b004641484030903100340070a01c00d55070100581a0045400c0c1c1d8108a07103880c041c102c035207400440071803d00800c4000b6080803190b02c40c100c0700200400714001d4503000c06003881d0140341d62405101c1c0c10302a000750402685149408426144d00b040c0d151140c007410f943e402d4070702000c43c2440f14858141580d5400b5250808035940c4144007452180c2c40024626040180d070030302401c40c0480244007035000e01040c1d000200da102c0180708503079100907401c0e15010729181c00c400600947c0d401000035484c0017000202a0715003000c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 765901088 1250 765899838 765899879
    0x50c0a0605010b0319110f090a0b0a0206010e07110705010305060a1d0f220b130609050f0708070f180b060c0d030f06050d0b06010908030a0302030103060605010e0102060f1f 76
    0xc051002d0304005e500507140b2011850060f080d041c080030718421580d03c010040d03d40001c00a02c1040d442d285a00e6240d00000c2c1c0c0c8400580c0060010b00050101240c1c40390019810f0601421001450b400c1c00e41c0e448460080034101078039800803a02680301d400c06a405072202c0d9080c20203c48a101e81c04141020880314025080d0610010900c06d50f42d5082040b0800004c60128440c0805515000840303203000e400454010b0030300b410000810741e00c0c49024200c5100780c000d800710000c906c5000707207449a00e070003c5042c0e07009400100801002810120212910000440c480b158500d92290040007018405500100001500c4440d410701081b01403c9031500e440c100040418021118111010b0f8060356400440d88108200418450301005034000c205142640c03085031221511815138102d5036464000c690080300520401c891400741d80b000d400c0a28040741c507041c1000000f035540401802a1104ac0950804070382802791002c1c030040c00d179080704c8848040c159a1360410b645100707070002c1c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 765902338 1250 765901088 765901111
    0xc18070c050309102307080414010210230702030307200c21011505220e0304080a150c09210c062f07051512090c1305070f050c0a0605010b03 62
    0x140c5104040d0174155400160040070721403c2a0901c815509444c54040805066124014201d0709003c40c90046500500002c0f65009129074241c900503242c4002421070000d5400a00402c00c2c025889020181074240d1010015507007000c440c480f03070400308120303100c5400070154070340501443c0c607000d0304001e1b5a0004008101400621510b07540850b900c0c06072035441510400140104d12426603408100c209400300010313074801807021180386510580c0450300680040d20000c092140c02600702d8111444580b051040440304c82005040c0351840c0600c854405010345482d03200161400d000200d20ba000300340f001984c0d103810028000e000c184102d400603800c01c44901302c2c0c620015003142c840340c09007001040b078142048100421021079295014981000703200003503003041e180b100c070b81c040c010b0103010b02280501c103c240a1070385015090441c1c81810074042c018015030082c6000304240081c40c10310b0310f0300401c0104a0400036250006403080342010000b0078119816401140a404007142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 765903588 1250 765902338 765902387
    0xf071103100608101b031a0a140307060c122a1b05040b030a02011409031006141e0906040f0203091e0c0a030605040f0b090a02030c18070c05030910 65
    0x681d0019142c40421a00c030315031814042c010f0446c080d401446030f80c08440c1403841141c80140200341581c072035a124020900b500045601d1038113081c0030a0001d08058984103d1703041c0e054403032445a0348850b03d400d041020702207128a00e004045142e203081c4082908003802804503090440610345c00b00140f0454500d000000110f900d130621904c605040094098440121a50015907100110025002540404103c4466156400c3c0521400c500340703410002145401c0506d025070110032161018000c07010400310b1200c210b18614400d51046040310003420a03030791080400d029200c00984035103c240040b040c407110b00e5003c26000d403074448588075480c3d446400805203541d2000720b1103164001c00802004c0c404110550011a400341c01520074403041e6205a641103014007044455400036003000a03080300b185030a1001c240340541c201c416881d1329031001c2e01c0f078a000501602d540244001d08a520f010414140207546014500500c403000c0c0c12980340014200348551403848417401c900f446c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 765904838 1250 765903588 765903613
    0x9190f06051008151005060a0801031707080d021c0501080d081b040509040503090306071809050114090a0e061603060f30080a05190309080f071103100608 68
    0x2c00c40b2046403a100c0050030024902c1840304d0310508050400850008144070126880d2650380090013011642c2d9103488140d03142d420102c4503803d250b141d080e891a0104416800b044207a0160385c02c407c40700100698501070303030b50304c041e0004040d001c1140c0c02d4201400040c8aaa01141c003400152054981101c41c1c0c0d00c4054228400c0f11140b0300703403603641c8c061205115508066880c2640b0034462000c0360f25103581540000c0c6402c0c82110b807034000405e031100401c100100809802c0c000c00e100d0340284000c1d4104416004901064207a850158204200061020046410410003182d140b4262801402c0c4040324000e01d420110300d89010a041c0000002d071094000050021501c0c0302040702c854500310524045004110194074071544048100540844d03001e0004107016821602e0741640c8056501407410f030315400040e44800d00d4981504400840d0450040b5a0012054001d442e6540f0951902c121804c0c51041da03d0340610508511804004041e40440113032511213044514074802c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 765906088 1250 765904838 765904861
    0xe0606040507081308070506010f050a0b0f091507060906060519080a030809120f0306010e01020f0a020609030a0501020f03040b090a110402031513060302100903030504050909190f0605 81
    0x1550414000f032060400212a04042d40340b040ca0a072194085e245840c8803600c402c0e02c1c1c0542071300700002440b141c01e007c1241c0d103407540c0c80c42c006051505c180c03420f00c1c100e404050940e00900600d980070340781c505400898000403008550003554010b00402c00100d10f420140300601d098040d0358084c07011100c65503510003440c0115400c031280c035001068191b41c9594120740004020301104000c0c03140300f0760307070f000304510001911881d2900b0201e180c0342e2926500050104800d080c10a065400000021207c41000b18001c040a50161103041c1c0d500800408249081e501d00c0c8050425403000c02c070300b02e0001d0f0b1100214003d50003840d65821984806040c5034031030440113001044d43c0c100b8080c1031080e0500383c019503802607440c00d080d158007850030045441c01840040a4665580d180c40900842c0b5086001d80c0b102096860245500c0b4155640a8142d1065024241c811020b40340000c1558000300311040c00c000b40300721b0314a42d4144c1481e01c03080112004800b00c031483d04010001c3c410030502c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 765907338 1250 765906088 765906091
    0x212040b0a06050a090908090303030405210a050d1a10020a0b0108010e0a0b0a02040512030307030c030501050d0213062d05031b040506040605030f2503020f06030a0f0f0e06060405 79
    0x1c25060f04a85400184001006c60b40000c4500721400c1c01003039800e5406001940c8240e006d000500900100c100c140c4140490002c5450031aa1f4140a036070300c425804400d41d00180408080000c0c01c41c506c003003003840d4803280e803030071a48442d20740171904130366038089401c130711481c070803070b90407019036200e03101107090340da10b4405100030342d003d680c0640c0818410501160044402607005160640340c00108000900d490075641c25a0300c0002070104840d41842103200c184d1592508000f994144000038145010b11280a0311030220311206012040c0b149d4000001800c0e12a0051950400281204020006050603000416071083d00280ca41004a01140f5000c1100c4081503040b19039400c000040c0070180c040f94005648003008076980e102085140312440b90b03080149103242c25020410500e2401c000703104600709090000f000186c58002d48481c2914084520079165911842480000c01c41e400780c41c00e00e00d040c10742090324415260720448011103604180c3d02d0a43e1142d00380000d440f030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 765908588 1250 765907338 765907349
    0x15030516050307080c0405090403110d0c03020c0d081b011d0c0a17011b21110703051c0204031a010914010905060d080c0102092b11040e010212040b0a06 67
    0x42000040d4003c3d101c0c00c46a03501c19030014415040c1902c075004204807150031582100803448144000604032802c0221855150040c0383c400480091540e000391a80700e82100c2c0c5000303116041c0341400b00821074041d1748000710314940d00a4800c030014030440c040c108010809607045100305c150754010358080307941e400807000036229a8042d45803000480ca00802c80d003103005155a50905003440c1e140c000207100b00781207250740e20384c40307150042454107024043e0307588807501525000c0f0b40703502400940e0580f001c6640604100303072502411601c1c10031000700392040c800c907103100007004403c006030b009426406401850305200681e89481c0504100c45100170340081c401c1c100b80041003c0030203900095400000903298405a1445544030b02661b042000d031402a40d4001c1013500c020700342550307114801100202c01480c8800701400000c1c003034044441c00340503036108800d0b880090720b41d40c02c6800103400d510002c5607240d03c1c000720040000816601290304190a034040341c0106000c3c05590181c6a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 765909838 1250 765908588 765908597
    0xa142a010f02070e0f040f06020a0f1202121603060e07020d1724040b06131401020105010b070609030315170607050a2c280506130306050603070f15030516 68
    0x110b888203c070f0301150005000311101d440300e0807c200014043e0004e00810301180c5c0700c00401c0c1100e100b014114119503031824210710303c1070041d80406103801c407825402800b40e08001d800d603040600301b1005840340e5001300c001c5604500c20321860b90350001d540d0000391810760301d00c90f031a5542403442c55506020303102503644507000807181d40c0507910b81c8000302c0c410900900004a60380e000d80440e02a801000324024441031404d020410f070070140d2205914445c00744000c000725810000d20080a014240f00505140d99450740002014040c3c0e10a0b90300d035520884640b007555495001d14003008245044038101d004850124035041c0c041d0081d14224100b60310365180345058400d40d120007000007001c40d020441100c0079040161075568110540b00710300400056200d81c228402c5421101c954010f40c001c803000c1041450804c1c04624510035258402008a41c54581000007481e08117035030440520407000400004414900901d2640c0010fa0394800380020740d9039107c08603c0748070480d00c44c4040b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 765911088 1250 765909838 765909841
    0x1202160e0c0c0106080f0a1a040506010e0c090319050d0c03080105012714010f02121801030b030f010b0a0501090f062001020d02120f06030a142a010f02070e 69
    0xd1503140580070070b05441000292490360380c03006500d032070400764040d082500300380c00b400c1c144000d44842c4c05642001003040121400c01e95902c0742c1d1004144900341509940070042010a0f602000321016003000604850000401140d1900c051650060071160b03841210044800140200c90782021a50103444084c803583c030305070054070701102144403031520100e01315124440309074a003a964040c001c2c84100c03003800b880003070002d0b10021040c00c40c4410356229010b0400802c0106080364180200b0050500c5c41d00c0d50304c401600130b04a0080307410b0303250090500c0c03890011740541c0101480002110032140107640d890066545610a00540b042d40004204c00c0c80040d0064010180c4100b03007205491035201000826800c81c0c11461484103455000115420341442c48003155800c911a00800841c500b450300000340c0c1c0310304e5008014031440e5652507400c1421018040a000b8412a1080e110b0f000e4902d241c10309082c45000d4814003040c1c0c058a08041688000783c6c00081c0c8030b0405884185 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 765912338 1250 765911088 765911101
    0x806030d120519060807050114130303180819051204051503220803070f030605010c06050601050f0c010e1c1205060a030f032c03030a030b0a080a1202160e 68
    0x34182c020900c070103c08000c14804449001442620700400200000d0540e6606210004280181902045c0b66603403060148a1b004044c0c4504c840071240c1c181000390031584903000040744a122540070420318040e1460000740b4003407070001c40c0700301d03880b807801d5914034483d202c8031413040d0007203004950300f008420010b640307170018034002075801088003a000b041000300d01c546114039419090303007100c05c40c10200c02c1c408410f8110054cc00070515508091200d241000002800b003113040c80003402803901c4e000895a80c0e401a0101c481b001001c066a5540b007003481301c0c0b180038100f41d2005d482c0b10300c07030600c1c0174210425071090300c0b00b14080c5545030700511000c0c0034510040c000140000354008110000040021803540c07804280920980360356566420403095076240c450001004002011840c28503445070307501100701c41e908601c07418001740980681c40070a01700c0426800480c0c1c988110100f0006004031440030400c0840c1950840b014200004504901d41d2118400d0030500808070b40410b80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 765913588 1250 765912338 765912341
    0x110603070f121103070507030201051b030c0a030b120d12050f0c0d141e0f04050d050d0b0a0e010519030809040c020f0a320c061c0903030c0806030d12 66
    0x120707002c80709020070211021910540c40354015909400441e0b40013400000301038080c050282c0c4595943c1480d413101403005170741c06080c400186480b03134a600001c0c1c107c003198002e500c21080600040c000c0560744c0c00c1c401c000303031b612401d0203058401703d6034100340070090540a000d518850580e003108240c0c1c9449180132510950410800c3c2e800c1c4540321800f010411030219074061051420b9986503480078101501d24000700d1000c0c0c4220141c64110081202003031000420402e60262481c2071582e402d450310842005100c00440c036a400420f00718005640d824148849040e25003c035600501d090a86600025107030892200600d400801d0100c0700852800d80c1c0f02000d0441e460060300c1c414001c1c99203081c10800b4a02c81254411707850390040070061503005404648000100c00c01e05615004201c1668801111042a1003114000307107551040000000100000b08850b5060250000d0fa142c00340107400d4444000c0d0000d1072103070010f0401d00d80090340c82ca080c80603072544110107840c04100700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 765914838 1250 765913588 765913607
    0xf030d2702060f1608031902070f141908070302010606020307050c04020f120412090503010b0604150504080f151003022d0d1a090601030b011814090a110603070f 71
    0x205800d014002c00102d404607414088800c0c0c820380e040c1e5600e280018008412124500307c21665038070510094000a074080310304a00b240d00001c2d0707440b03910865902240340c44070310701c1c0c40d841000713000007540e0070400c46a000d05a180d1298000b80000e6072220701c100d83da400f503804058a541c0c404d0707400b00e010342800e030b000f0001c0712051084549000041910710fa2880b1003960101d942c0c030207540f010030310203510081c42d9010300340482c02800742030f4881d0b00003603075030055004460810700035071f22486101d4011822140102901c00035a82d01c4034204070004d0f254a0310359880b0504000040000d408080074400c0d00741903d41c0100700080c074182c820990825121030304202440003401e20715a081564828a810424501c5030300c03907001c000720351005083d012101a080c2d5840794044001800018903800025040d038405002810484068040c124081c20515461220480324103050103401c55011401e2140c040c0035481d0314141080e03010a0141504c030413100c80300003c800c0619810b8052241e03a846 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 765916088 1250 765914838 765914857
    0x5030a061d070518060a020c0103050a0203100b090a15090609060206040b0c09010c02031f0b0d020906060c0309060a0906020d1e050c0f070803041d04240e0f030d270206 74
    0x821032800136138045801030340a082c1030400741c0e1102400070030940e8107000b2144c1c0242d0f020350960035820601d280003142c1080b802074101481d00400d8060481d140d41e035841006200d400c0054180c0900c080c00905082220300030100040ca05490104025000141103801f8585c810310408003035540880050107a048072880034100286255102c0160346c1c2040a6080c0380c0d41d421030410200040c0250404030788015030441c2c024a88030740400c025907a001d6403568000c0054417170a03564116540f42c103045220b4a2943c81c1d1043c00814aa11416400032000301500d07441d03000c644140d034141006440390300c0841180da1991807030180d0444081e1052010f8600910050201e68107a0509151203042ca90399030001101c50340086030802c84100700100340040d239804c0b54400e2215003026100c01d035a07004e454061500015000180045c0c02c40e40d80d01240a68a451064a4003120003030f6055440384e015070322858059003492849400d010711030f0403040c0c0c940c0501c0540644080a42e0170b0194a03000744410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 765917338 1250 765916088 765916117
    0x7090b0708090f030d180602120d0c14030906011d040b0106110307080f0c07150c03030b060910020106030201030e0c0915061c0501090c08090c0409020f06070305030a061d0705 77
    0x1c9001900d0402c41784464002075220040410000c006105840042e40e00080865000c0d0101030300030020003003100c20000800002294240701240180d545456024004402c00c400108002d4444c0d004201d45040c1e40014800d00104072282010b000307081d40c261000380c40703418040010041503000d0380c98038082d03161400c01d4030305081c1c0300d840f000d03030300c2e080081c0e100b0081c0c50004400041100c00d001d0071024103028440c080c0508100140206001d062903001000e15582d51103003421680d0704030540f4002d40e0000e0083c3d00107005c0c100000d0190076107205c100e0119007090500d0003101008030b0941501400905181d1140d59040c00341c502c80d544041074650040010015030b0740c000505240e0b251040300075400400d06525099046044a0003940301004014403482408101d0002103002d0041c07150441300460034004c64000a11003030301074402c15600040004040c01015040302c00b442c03203580000e008101441e40c1d142c42c4041d44800c0811000803454a800280d825070080c4090402001c3c1e8400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 765918588 1250 765917338 765917359
    0x62606041d030d060801050709180f0f06060e030105070519120b030613110603010b030f06130f090312051015020f0d0503040b070e06190203130b0403020907090b070809 74
    0x10003604540c000703000030300c0a80e00c1300000d02c4030100034019641c01400314035044140515080c0c00704c020115001010a4050710740401000c50100d40e04150b030f0340c0001c2c02e0304014150f0b440c0030103441c0c81b01144c0100c4c065401c2000180c9442d0050741a102ca45080041c024041c1211540c121085c11803142a20403103035842c19902d4050310708000107403040f41103141d10955481a8181008440361140d1a01c2c421002040107020071007000080d03c5d00044081c59140030350300e410001900465481100c900c3c410314014100c1e800030b403640c1100a805011f91552035503840d490200605840040300d10a9441c110303a0010840c02151045940703515050780b054551a4864058580c103200200789103100040c008401c0c1f001f48404034841c50340100041c201842c80384007600100c1c400b40520820700185102e40d000fa004190b000380100c800101d068058041110f499400d942840d802500040e03000d40e420000254559002d15103a07810742d500010b40d45d05040413036480e856150302c020000c6400204080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 765919838 1250 765918588 765918641
    0x901050f060a090209011403010b0417030a1b0206070611090f0d020f090402060c01060e041707050703330204032a12020604090e0c0f010c080706200f0406260604 71
    0xc080c40c040c1104ae40b000343d03624901407a108049140099200258108000b00d80c14660001e104d00080e210b4801041400305042c0009420750207420b401404250070020580c8403945041d00603c4045c80480306403c02a9103d0240030285040c900002d4008140542d80c11051800d06041c0d40d100c0d100501c124a006264141c040c00d4a032958002d106540640c0144010005052110042c1840d038201042c289400750f110b0a50b1615180b101801c040e84201c040900a900b400c602c1c410001c44410f0786c11071401110341c440007035002d4482600c0968510b01e10054541060b80d03a0326030351100e03404d1101079508100e16200c0d8240b507200100d9111108002c005200112402502400624031703001e03091101900d003c1c404015064500b5904118000d50400e00040c100ca095030344003500310900040c0d0450f030424a080c1c00303601d000303a6050180c000c19007000c1c400000c0e000b001504d00c640d8540c42c9a04c2803950703014440c80c5030384d00c251070340c0b02d0b1100007000da00f081e40c4401c013603d29500003110301c1c0d0b007100e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 765921088 1250 765919838 765919877
    0x803090a02060403120912051905012301140d0309060f120c081806220c210303110406051c091e140c15031305150901050f060a09020901 60
    0xda04c01c5400e0321500f00000d603003580000082d40105a01074030010710408590300d481e20341080c00192000d074101000303518288642540a244148903044400c85400d40d05006c9114048d000d01c00d00049000101c0c10044a041001100c0c004580c5030b10350110440c2044000da80741500604020108601c807100c004510401c0c3c002c92072401c2940d2242c4d501400c000b02c40c01e400203d1039078111444d60102e8103005800888444207004040b0f607101002d06101141b500040c41c042980c000032148652060744c1008101c41e15607090313000e04c651004c100700648581c40c09250701544c07281c080450000c2c06104a4045402d103000d0740204140b07030000e0805036590310200000c0f0f02c41c00c00a0302c0744010310701c80300304505034245c040224030f40c1c0004c280740c1c988000060310040e2000110f07d441c040220104030807030448511480080c2c0d10800ba21801d04811201d503812902c11034903103040d5803c10020a006180a80102d4000c8201408103402181842c0d2804007070f45c40010410704124240740e00040c4e26084c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 765922338 1250 765921088 765921097
    0x6010f1206060e010e03150109021305030d0519030501030309060e030102120c0d0c020c0a12050f03030702010507080703090302060105063402010f180e070e04140708100506070803090a0206 83
    0x1900c5100c50038480c40001440005c810341001d0090380030400802440524020190460b4400f0078090313612512510010000c40840c1c1c003c5030503218180604100c580c115010700803008035400c0481500758650011001e55000384000703030110b44002018031509108440e841d0322100090009458801c0382d800141e01a50103e4000729844400b2410700391850303803801017035055034040c8000d0002c00080800100312004a01c500c07080d03500b49599080420900307000f98880106141d040d20713143d2900a0010707001c3d08081303036060005644100000c42050003807141040881e0190700402d81d684c03c100c00d000e0154480032039041882010b510307401809648200c18081e142c030f6400031040da88018400900b8002440085109004500f083d80343ca004c83c005c1da80049130460080886151030f019001c0e650390603d0400550000d0825079200d80038600480c465008121681c3c6a00103a65902a1900c0e048401c2c003c040e404a41007100d00080385043c0065038110000005485c44050550300081c080c0e0f11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 765923588 1250 765922338 765922349
    0x609011e08071b1a040507080703030807030506090f0f2a0912010612080711040606050910030e0309210f0f01050a02041422050109060e06060705030306010f1206 71
    0x18010200301082e03030b1225410344840e44200c01c1204071882e030342e10700021080d484081160120000700160900031b003003060038010030200b0152603a054807410000c0c00c1c000215129004641800c001c2060703400c124423400e1007034890400818803a00c0c1c0444e022a034000c040c25045100410488061504030341d0152110a50030400c0c0c095901c404140520402035aa90400480c0364501501040000320740158196150350002d042a0f480c041c0f49091500e9030540080c843d0401d01d02034000c120960000010180640e08440c8800c01c1c0d940d0304d8040341030740d81405003450036400603c040c0020382001048030b1820007c0007405a00101c0c05c1c2503461500322480e00282c590b900c552900b0361044020b201d03440d0001c9818200754a4075082000b400c0c0c00c48181c1d804640a080e20f18800f032071040c012210030500144041b4140129659008903802400b440d0007410511020000460b2043c54002c00f1510500d900001540c295643e0b24019209a10705030402002c0c0428000340d051a60128030404020b0170 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 765924838 1250 765923588 765923597
    0xa03060906081b030d020c09101d011e0b0901110a020405070206040b1b04030f03030b0409110a0f050f090717040602040e1609032a03050f010b1804020609011e 70
    0x18049103e40d60f2141075071038002d40045010084156001c6800081c07040e051301d154030141c075400d65689031890142c0c803034400f6081c1700100d5012541c4051142c0d040314031710014171140d002008455001115640f2441e03050000030407005646500810740e030500f0b4480601235400e560b031141c0100c3c05a4070212039120040c3c0085003003104100740041d045c2c0d00422000842a0f20f611000300c009102e2095010160002445109c1c007010148260084c0014040180040c48442c6c0d0615184240d2100500028458a0340c0000442d1a580c800c03080412504010a03100792180c4450521100c2c84001d0f0000081242d140031a2941c0e40700e0221550045205940c0140c1c0c880c07502c03034541c00e00c00000c0d103030011820001c02c5e5581102d52140b12030090741c1d0880030328502007440c01d08a510030b84c481514004032040c108400028014081020380c00c0303541303030300081c0b108030600020040086030800540341114400000325003d4144100a4581544c0604151070444e42c180040301980640c1e800500014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 765926088 1250 765924838 765924853
    0x2090603040503121b07030509061b0a0b011d01090b04180b04060c0e0105030a0e070f061107090b030a0f03140309030c07050328020d0215180105040311060a0306090608 74
    0x440b0880713a056100f240c000c00005c4203040e000c0710007160701c10381501a042040114201c10141d6615003124280080c100c007484a0310079008210380c850f41c0401e401d40e80206480000149212028031380188402c101c2c0c03d01c0342c682e00703001d4400d004224140340180c00a03911401c1c03600c039951621109d1040d0340552000001c0f86024588941a910981c40d0303c4204003c409144031140d0700320060300c0d0001e0030003c0208070031201c0303404146400303182d9004000c84d04130311800181041e00098050680b0340780304140c450190719440c1d104141c0e081c03503603c01d805501100280c3c0101c1c0b003030180c2503130b4284203103000000c20056030b1446460750000d42d04145103800016600c00341100c01c100e00030007818103401800283d01702d40f03003c24001e0107514050802d6a824114141155185010302c610350f64020105c0302610700c03403d12094203801507490b03000b1485a842c0884c64a40c01b074815101100d81c405810004081c486c0180415600803510450601d900d454003c14500034a02464014003288401003860 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 765927338 1250 765926088 765926107
    0x30209150d15180e030f030c0304171602040f062909040c05090117041121030304080405011116140402130b0c120c0c04050603150a09021f2102090603040503 69
    0x80f10300d2205042c4c0242c0c402c1000c0541d64106400b0b0348d03400100c4814280c0c40c4d5445040800c2081c901707060074840003a00140c2070358140b03003041c85403203541d0080d00c082040e4010509407004691450203102d0a00c3d4044400010044603a200420403428605000b0700308079011021a0680e2030080062003c03450200309001103580c44112089501c0c50003503584214140358a0300c0344812003050304580100032204041c040b100c0106682d10200148504a07942c034a4a802c1003416600f02c0e008040c001b4680408882c0c40440006500e441d01101110b40302d020781c5400004440c08400c0c20045401c07580a101d0030311542e80300481e01c2c0003440310350006903541c01e8a00c030542c14254a0088012180014005c0140b41607002901220741c17041650009216203401c00003914140d01c40c03008500090600e0b00300324500308c0c03580190006910a4442c4a202d202d1800340608204002880e04001031a8101d50081c4408414540300301c0d80d240ca80c01071030201c03810b0100f8003035442100c09a8150b400016610740 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 765928588 1250 765927338 765927341
    0x90504030c1709010e01050d020906071a0606070b0c090f030f0607030e010c02030702040207050c360631090c050a0b0c060f06010504090603060e0d030209150d1518 72
    0x840204142c261454103000c000040c104a0383c0d42e1001d0304211021070308514855813981150f1751140010403440d1035540c280381c802030b43c1541c41c071803c030000c10718400300b100c504107403003596039055204c0f107107840c65600d800c441c01803900080382c8242d0115910702004195101030046880c0c2c0802003001d0142482c146c030001d02540c4c121741802c4480d03850310b120040100e60200659079010360495000d0380d200f400c1d0508500c1c000c4503401099100640d03080c1480000822490901e0441c3c1c1514010701c102280306540d17003a54030441c1c1c150340003c94450aa40158860381d9021030120b05180f052441d20002005041224103064040b5883c03044e03188103021514000016400410748000002c0c607042041ca00c568840038043c1c540300e040b84030080400c21a82c015810b48024001d40c0004110070b980e603080603400b800c1505050302543c002c0302c8540c50310911900071540f5a0b440030b003600c49a42880c2c0816011036001240c52410659500e03040c43c264840102c0c0b400041c4408204482c2c980312180c1c8100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 765929838 1250 765928588 765928613
    0x91005040203100f2405010e12160605070b060315010e0702070305060703090507080a022b021c060c080f06060a0302070c06080106090914160215091e12180109090504030c 75
    0x701425000c0d104100c181c8c2d0052040d4901c440c1599500d41c11011050218640b05046c0e05503410601002c002141c901c0d0300002405110340181c41c1001c041d01c0f00d000380344d110700c580d0b0f014040d603c244200601c002c103502d010342504803c40748101c42070242c1e03c1d143d8500303020007500c9140000e900c0e2034102013409000c00451001d040000090500c003501940047c4003413110804a0305040070030851074a1810480d1480c2e4405500500014000f981240d10490188607107034045070400d1600030f9008a1501c1601500d1003910219002c4829880c0c40040244076002880d1401c03c154003040030000196000380201c0080015444840040d4103100300500041599008080ea84e481c160806603048800030f406500514088810380401804900032801c29008007450a0040c440100f031080203040050041c2846000c403001039440081c0558080d15090002617202c011a014400346080c1b42403402c5806c038a280c14140719082980d0340c00f6100581c0c001f100c00790f0106100e000884240710f140050303031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 765931088 1250 765929838 765929891
    0x1050414010b1813020a0b0304030207090e0a050c06030a1e090507150f0804030e04050f06030601050118050f040216060504210f080603030c030414030d0305091005040203100f 77
    0x100d02800980c6512008908028131100204140c02c000c0003d6482c0c0c0141c5030080c00c51100000d54a240034203000e07654031050b01c0742c548210310300380844c4a101c03008500345140b554468042c0c01600b081208100b1283c001412000d901d030399910f081c41090800603103c014001e160300c00400c0200c00da0400a0500c0390a41c8000234101e0b6103268403c0155000b20b46404154441c2002520b43d12581011181c030340c03601c1e851030341052400741404405050540c0d00f5204032001c0701207440e207a8884004640c3c411500300001102c00e08000b0500c1103240c40300c0c00b1a25502d020b4001400c0ca100c51180c0038086820940c1601c50546d07400501c418042c4070784500350104003240d01c281444c000c58100900504020840e88200402a004a5004c1d5803e00803960040c035107104994845e521261b0710741c0281c80c0d4405041c440d10a82c40c01c505600e0090242500c244401e0005c2d00710b1081c0c1c000500050440104100d0f4580100f824030360041031503101d21180300740d800703500080020300e03144582551034910804 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 765932338 1250 765931088 765931099
    0xe010216110d03050d05070c02040c03020304051b0a0603180f03120c05120708190218010e04151206091506060806040e1e01061517010b0c07060e0102030c01050414010b 74
    0x84030b022a41100440380303184502d010018155441440071034007580080c900075489170810020b08071060303054001c0c60050b40604241c030440d04c00d0140010402c42e051070780301d0700001010300030000c1038044c0d1b00c5440507441400e015208111659220541941012001c40202e2030131303020a40207001e107100349862580036007092484d0443c02c0a246140c088001c00c1a4100108a40000c500b000204c40d0410500a082c00540d15401a070600c14030030186548200d0001e141e00d00d581c0d00520b02070140c10090301c1d9501110550901b04600c08511004000027a00c003030341c540c1d401500056000c440c1c002000c41410f0000790301401e0503002420fa4002408440c400d82c20080c4c5040a5139000c54400000c45840307d1003140d208014038400e014000c0e0b40d10000821001c001c00c281c0743c50704001030070501141c5002c58084c581c0c07101084074160089003003403602644807400c00d00c00c5a0040c0035003407203103505004503410080d0038008142540d404603403c0310401c0b80340d040420909424020060001d400b101d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 765933588 1250 765932338 765932359
    0x6110424030e07210f050609101104030b0603031308030a09140f04050618091e07030506010308131511010c140904020d060b04080616032a030e01021611 67
    0x12090f6440c24640500d0288003803403100d070300390404490000e04c4056417140100412200030b041032071300c40c10300700ca000705240140c003405080c07417106214105c0c00810303c01031079091a0860303c3d9802c44010081c0885d0f0544000c0100500005c11800c1010041500380015540d8030240800204a104030364030103038944201c0380d0f2280b5580e41d14102c14030a00c40c00d580001f15541c4a0300054100e052603586020702c0c82001061101502020801140c00411842c501d00380140401080740d40301c40b684409000e6400c004010700009211000420740d030240f061110b58602d031902d40660550000180b03401c0030960714012200111801c1c02901c072105481d04144000d130700d00344000b103002e20a00754000d11941e40010f0107450495030364801005002145085902c0ba5112030555503604000d0b101c9041440c0304080d01581584a030107003c44039088911110381d104c044820b15441d800c40800990185a102c00c44160552000d00c060701384604451900c801d117000e54107018000300d082c1340300140601014407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 765934838 1250 765933588 765933611
    0x606030203121215040204050d15140919080f0d0525050a1407120810050d020d030e012a0215030f010b0c01090807060b131a010c0611042403 62
    0x90029808046614030226402c40c4c40001030080c440c0f50042540079171600000000d1244440f032040304020b0b4071404105040b455510b80842c3c00040301c0b035500c994480b1401035140c03138150411491591142801c1401c0203038500340829980c008803488403c003a070700d0081051140040c4480403d0804068000c0c4000e04903490040440c45000b50042c240140e40c0112041005800c040354611604504082030701d11446c14000d140103000d07101a840b001d46104007007140e20709049042c00d0198000c0000b0a003181036030b001d550300003c16440c00e06210702d1001ca24403a0105104006500d0b5a110704001014100c0c0b04200c52903800c01040c074150001032041092240c00c0503425815243d51150484d102c0390301c0c40000d03001d00080b0394003c040034004101c0c83e0801c050798104014100d800c4402d20004c0c201c0c42806401c0f6800408500c000c01c8000c140000d555000d549220f21041c020360006c41c4070141e5911803031f510360281d880084512041d040030405840c0342c1809034142181480e080c0070400c401c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 765936088 1250 765934838 765934867
    0x1020601140307080a08031b0901120b041508030306130e060105120f010c02061005100f03020309030409140609060118062610061e23090904060603020312 68
    0x502414418030703001054000d40341d42c1005182c0051015400300ca0b0003164600e044100c40c0c100f61445200a0710390074014811048030400d42e0f0890b0410317500e00440e50b110300c3d260000fa06c00d6803601604030740d0f034640e5130b00c4000c24440380703802401c1844002c0d9a0f90900f44140301d004102c43c00440c042038540400350f0300304400400c0c1c05044601c00c442d11441c0841d000c00490801070722403400185917292a00141c90036070080740903486000a40160000c05584a081c800752104540222001480040b405041c550107a409150000101c0b02102c1c1801e03101e840880841c0d484c0040007450100c035808021051502c1c410103035100300c1c2881c2061a1035401c00c510704e142d54031800b50303000340701903482203d030f84588803420780001c0741c22a005540141401c2201c0408a201401450000388072110540359001080c075641032404d0007643c03100301c4c050b007024041da24502d01814a0005001c01c1251000d180d40d45108640902d01458000808600d1841054682100c2c078544451500003404020140ca494 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 765937338 1250 765936088 765936091
    0xf200a05120f0d080108150c1608090406030b010e0c21150405011d09070b0d0e01090606261c03050603150c04030c0e040819050403080f1c0b010206 65
    0xd440701003460808101107400c106400c11005841d100700d1009040c0264880b031994121407903101510b07035404103141c0010989004a510201100082140104100c4103415400909011740151380c207000c0420009401e0725090b501c00da806005c0400144072620b03c0c804100d8201c03011005c07080c40c1040340924040d00040345804041408006000601046038519801e112908018000c001640c6c5506518041021422040d0b200340c500200142080303100240f0b0805803107003800700b142003101c0b5420502c050521018002d1380c075500c541403031000902501861015080c125000c86c60038001c01070200c8141d41004407012254401e55042d045040c920a1007441d000341071402140964840c0f02107031800f04007030440a1003e03c0c0c00200032140405401500a0700e1181506620141ea10042c01600000543e005410702d14100080441c04403154640b2410710054141541803a9603a1a851419080150f500520100001c4c000300c0c3c0710b10480380e0040040f078059081081a50140c0000c0d9105c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 765938588 1250 765937338 765937349
    0x1020c011b08072a050a121a15100e0603010e0402060705070608070e09041203270c03020907020129040b030a08070201031d0d030c05160f200a 63
    0x181802a050107140960507158a15001801150b9641207841c00b905042d070094103098101d0502251161103801c24080ea03011110001d2000742e009007494080d04c0e0510500350200e4000102074503641c1040e00a088240c0b03d50304400f0b803464015801c0c41400b0004030540c2c030100801c1084a40c004440c0e640d6001e07641520540509a286503a4602c0860302510034158060594491004000307019a8042c80041c031881c00d996a02842e00401003d0008800054500504148860b03000c2030302c013071181d031004402e502c01c00b498003901e44000d4604c5550007000a416600018000e600344150b051034203d258200107207200070070815030408440f0400711b441c0c8101340d01102c001388109409603142c1e0049406000c000341603500c00c58103840c250040390300201c0c00300c4c04070742025174030f814403d08805032581240a00000e4241e4924041003100100713a1240d046062000a101c0302400009140c09a00068070a10700502210301900780b0190302d45025408804400058250100c60388aa040030011900e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 765939838 1250 765938588 765938597
    0x70f0815100b030907050a0803040f1818080901090b0a0c02100e0307090f20161707080703170108030a031a061204030908121909090f0c02120901020c01 67
    0x111100003507030079070005a100121007000402840b5038038202107183c0c030440b80f088030322011503a95038a40b16140d008510520b45014200300c020840d401080c03082d00c0e1141180e04000408401d455015949144202415503d0b00c0c000310741901c03036503007003c007040240120038041802c11711401d070300800d090b40c080c1c030007401000040706084004e4007400082190754801002c0c0c51449844081d440000d00c04442c1c000200c6041c07543d04691201070f0213004410725258540107142040824140c0c0d07280043d540c0440c0c084a0412140303040707008d45400360221030b00c6407214950381c1ea2107060042c101260640301441c80400c03000104440c0c2400400c4420508450401140700200d180403041c441c0042c00106401410005031242041811071120b84168400d032103031040103856620b00c658072100e00e0082108072204100150031100030365030008000a03145050320f0000d407500c06032419124101503850504da100d000e9a0702007034052000105d84054440405d08102c10000000c3d42c51055401c01f50500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 765941088 1250 765939838 765939841
    0x80a141314121902101503020d141e060603070f05042406021f0915022b1b02120307030b0d05010c05090f01030b09010501030f2c070f0815 61
    0x40c060256103203a03040c1240c00740e1501000814400c6684141643ea8014040c6801d0026440d0701407044100c001020202a0782890943d404c0c042c0c400c100540c1640d07006598010101c0603a410810311202c440d55402e00560240c0c160704252034a0b40c042c10040c400d130800441400003400c44c0004904a444c00c4a002c503420b282c0d0860902a440311800306c5001e01c440a401280c81ca800090600300c14225440c10f0a060380300b11f0407031040318202c0100404201101180181c1846190042c02a4040700002c0a140340b403e5042111220304c0144408841c54544082c3c0d1784294928100801280c4240050410154412811005803000525141c1816680d10b000c900d42d880d0200c5403000e940c1d001c00200040524010041c08981048520782e00c00c946005005c50300303500c24091010300700c3c00079000c040b640e4244001500030b045800d08492080d9034907215040301c01c041c40700c0c0d06941e05a09864254040000360214280071a81d00305464004c100c400c104420900001c580c1034803000315108040c213 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 765942338 1250 765941088 765941123
    0x10923010501031509140f01060314010219030f060302120607090e100315060b0714060c040509060603040f120518100f1d18061503100312051606052e090203040c0e07080a1413 77
    0x802c0c45412c0650840703078015074405540c000240d800d0150480ea22540300b103076628032035a1b401c0481240c411a070013004032020000514808407008020304500004141aa02c0d02a500300c03070303000b0401c103403003502030141d810b405610709000300354020660000b0a8505030409000c180c3d001d41c0901a5405007400000107804cbc007500b4003403004000e030700400e60800d0001c1f211009215401181c0590880c020701c0d9201103152800c2211484500a02e0700d0381611201c0700c01044e107140d40340700840e54500d000445559400e0b95540c4000740b004418820607600d0f07042c9103040c0030020100350840c441984041050040b800f144038501d500320b075809a10000444030001c403c0703c850040708115103100f4041c105440801000b50003240c41032080c0440d60060805001d92071104040400150b005014660000d20201d800f5800550303101e4010000e0310350443e96408004094601110850000741c010b00038481d01c42d55902681030f800040c900030a0090829422203199903101d00320050151480c1c800040d81c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 765943588 1250 765942338 765942341
    0x19110628020d0c1d04060501080a051806280507080c07030e04021209010b030606060301152003190c02100818010923010501031509140f01060314010219030f 69
    0x100c0000701e030800c0c004042e440f00042c2c082000045101c41c0020f0300d00c16404a82004d10801e42252016503d020154581048210003400090007400c00c0c0c0740c1a2100000000e8200800c0340245440b041c2d102d440b00700924051070f0201403240766241e843c10003003070001483e405489660070858000c502e9554440519050302c2198001c502d41c1e420034008191000812940003403540f08a946400902080b8219000c0503200d4800b210342070760003d41840148074400744151190701d401c8245c100b800340000c03080800800800c1010200c0240c0c3e0001a821910344068003800708102e9150a040c18404030307035400140001e000d503070b800c03040001000004403803040300044401d0203060040200704202183c181010011890b50616541000c0c40c4d500650700c00051003414122a00031340700b42e2409984240c88001b4105440099a440e00400e880e55055403043c41b0361458440760900028002e0700e58030b00084003420380c141e4007156910501030701c117510305030307044142e140002403400180c28805243c5290 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 765944838 1250 765943588 765943597
    0x14041505160605010311030d020a03050d09020612090f03041a0a03060513050106030c170103022e0504060e01030605011706041b05030a0506040204030c291911062802 73
    0x781c1d100744281e15041c410140d0080c0d059034040c140300070142c0c26980a256035220900c814400580c00b02c21450301007171044028013082c925135100420302d04900c0e000680150809100070700c581ca6464103000d1a1a41042000480d5840e44007950610380b40507180800105c003270b8140481030b600000d0100c050784c070036030001e0b0150100921840040200d0403212000b05000d028880100b4034001c103089000d4040d0540412500c2e81c0301d006285603017142d0a102e481c0300784100100344407c00d031100d0981502c95a0341e0100c2400c4a0355450f8842c1d02e440c0000346400d40c19256141450310380304061086e41d03484040e1890346003a00007800400d494002c0410000c1a095401c80d000f1100640c070a111154400e0003103008003411002403003107807980820001288a030b884002d08120140008111880030346007451090950f0b9400c42d11030031560010040c081c2c0c401d480015480030f10800c020340d850341060aa10041000100030480d5140603a03d692401c54070320040640b00610300210303101403420b81c0484 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 765946088 1250 765944838 765944857
    0x10e0d150f02041203090f0b0702060f0d1d011404080d0e0c10090509010b030921190e24040911070c091d0a050a02040905150c130614041505 62
    0x11950f895407a0303659a0080c0b1421030440000f01c00b00c10024116141c40c082c01c0c10380350090b134018035144082d401c010250380001d040e40c00c00fa1003441846052007040c860402c0c45a4044c420300e000707086a800c120700711565189030a0322041c08000740401700e440001520a121500c00000680e550100d4080380b5110052030307240e034006c40b64a84c80704240d42c0150001c0441d5015a0903003042d0b45c031169074041c203010491311603132103901040c034200c2898166818107a13102c1010640c00d14184d030a64204441400c0905500007007508101c41e4142824814401301100725a20301203a40c08003844407a461078811f5100b0510707160344840d401901408a0006c5840c8942c0c840340408400c0c0c0c0c1d400384a00a480500180c040903100503041c2d083d070000105200500ba50f10602030200004241d003000700425041900b43c6e035500c102c4030340144102c49940203074004c0211004054582c00d2003c40d9000b983d10743c0c0c00c54402c00450124507000c0109000955054030f070958110060703c00c1482c0700321460302444000c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 765947338 1250 765946088 765946091
    0x60d1b091437150e030d03090206120a1401090b09060f061b0d09060f0503010b1b0109051f020a08012108030c03010515040602061305010e0d0815010e0d150f 69
    0xc03019141c030061014002c84505103c45281400458030035a4111402000300d40c02d03400020b40d03024000d00c00e0b0704c8640900d200030071070390600c1c0301d6001c01001d500c0101c54401240e0380d200c4030500c41e20311403c080303401041c84c610248000c240340c00105d2814a00606103500032060b049125150f0f42d40c030070650f82d18107000d442c045031689008145aa6803041440d42c24042404d90a02054862140a56240da00c807a501d4241c42c5901c1c00242164550180c0d424941d5805414842c21143d1400c0c021207007024090402401e181c01d941c100d242c4168014030b000070b03540c1d204100511202c2d8000312010b0441d09460541403c52501080b9050055a00030006041520010801403854240d03000385040e0742d0107984001044050b28850512403080e40280d00142c1c0c06071000a40110345d0090b440c49140c481c50010480300040c80045141108495082020903003010400031800ea85d201c015440d40700074a8081e409045400124003d80d02900f40680700c1d41041c4e20400502481c0e81000402c04c102010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 765948588 1250 765947338 765947419
    0xc1b0a09230910022a0703020607030e0a0906030b04170405030a0204200c0708120a080c0d061e0618030c030f0c0f0e01050405181905010b060d1b0914 66
    0x140d901181c41059a042044054130440a000040000c501b8280c0c0d03400303042c4a142204540707003690203460381c80242d90321220030740022400f10080e010301c0700250700c01e0740e0401741030800c1d2030003803803540300364644111881c07046c00104225036000460750426a01500c0008903200340e042010340220f409650030000c0d440018400000a83c0080d85400716146801625000130014011078528800c00e000c200004010314003041e0303c0150380b8024501c490b24684001004c0356100080490300040111605401c0038006041050f90f07040340700c41442c058020304402c3c0190030341d61030140c80030341030102402c00f1020521140402802c000301e44060001742002d07050071943d601c030b013448a41c001d02840740640d09110100c3e00307123150700390441c038101012030180010b144400c4c41217500d00420320059540f0b43d00c60811a0f204d45401c1e0040a814034009004510000c07001c5100100290303160b44c5a040000282080214101c0c415001c460340c2c200700d40c00c8518a60103091944841001c40460008405445 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 765949838 1250 765948588 765948607
    0x120102040905041a07020d050901140c0114010f0504021920060c0d1a10080702070b0d0905010c08042f1e03010609060806041202030c1b0a0923091002 66
    0x2000c00e0f84d00b2803a422035a001c1d52090f40032a01d810b08000c1010200d40103000110036980a5500e20300e034800c3c1d02c0e24850800c8a2485001c0c29100711152402038090b40400500c40340d2080400c0ca80a080c0c01d48040d40390070100ca010040000c4a06d03c580208100b03840500b11060044040b103200303030005c004449041c10440c0c03070000706a01001311300c1e03a501c3c64144030780c01d1040848a03501389600014601000c60012504c15580c55100401240850140032400720b9501054005440c0c0500e03031100004118600e0b242860031103241000082c28406800100000104129500c040500201c1c14014407025680d070312030684680142c580354000003203660074104085001030311400e03c0d811802805503980e11040c002c01c40b05c5074000e04c2026004140018003050058462111070051881103c0c40c008064408905164401340d00e08041518402503100c58030748050301801500702c6010410602c24031400c810b11b11200e1082400e002c2e02502d0010301554800c1c401000c000d90340e28000d40d03a40c0d01c1074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 765951088 1250 765949838 765949853
    0x70b0406090503160509040215160c0807051801060e1903240203010501141605070305060a06090b060318070812270108040b040f0510050115020a03090512010204090504 74
    0x5010340c0f8001e2090f1603a03141e506096000c00c004031040a0f00a000d81d480355001c0c810480024004050409000c00101411031101122422424041c41d040090603052a990a0505e495644814441d04500b0800d15a81d85001022411160f560a00f0340c610140d4030089565a14083d01060001c81100000820f00c880002040030421046c12002602c03090344c91200b0480c0401e0003900d001038900d82800340da16180b903008144968207820514401421641d400d80307403051702c3d001200d40741c112005101002c545030080704040d03c41c992040c4255825070001c2103081c04010807944806c800703444128450001402540c0227001d0681c141c844410b1880044080381d441094a100084c0075842c8010076020f003028103001c5004141e4070074501d40ca840d15414501c1001400c1a14004a15405800001c408000b910240c55041601084540c03400404500d4400210100300554022104400000c3c3e40000c0d0501074443c00c50710999141044100c050090140742c100c000c0340e0380340505020a10000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 765952338 1250 765951088 765951107
    0xf100e10081e0319090b0a030b100516020609210d02070e040b0c030415020a0804060f1404080d1104091410030b062101050f0403031a01080a0e070b0406 67
    0x1140d044882e07007000880760840c0c50240d800402e6181d00240031103a1844403005840c0c401c500140303400000540c4032001c000b40c1c0c0d4000d48600c8003180d03480002c0449400c1907940300b0000549410054185044901c0014200c0005040203108510004060780c1e10b80c0d441c0c3d8500b2800d640148035070305040e51a0b40300c0c1d6850f0401c0c078074030015220f49400014040042d2491a204551000246505469089292502d034101410407541d006801c2c062120006052010700910417882d540c8100174107050405a088444103101c0908160030440e01c05079180316207a90030781181d80400116503c0c44000c102400034813a03010340340c60091002a000030303070503005d40191204003002e180c4007030662500090a203c2c1c1c04544801481103e40e04000340091404070f2001d90074103000000c0c603003100e0003150081d08450080b190110a900840103000500da8940716a0f140142c03c5000b02c1500c0c0010030001c0c1038a040140300540e055210109800100001e0180788020200100d1040d240c07519888040c059205 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 765953588 1250 765952338 765952349
    0x6220e0a11040908040b0a020106080d021005060609091b1e1306080f24150d0609230604090f0c03060b040203010b0a050c0c060d0c020c030d05030f100e10 68
    0x410040402180c030b000d10a451070180d100c101c15203014a0180d010701d03940c0041c0f104200395580d91200103090441403003c00300c1000e43d5400b0b8001e0f00d910748402c400301c402c0034214a010304018070007003000303454400c002e0760041c501c0d0302c5456450b0607030308201c9414405c0440030801000c10720340600c2c1e102a500e01916a504030881090407080d01c50340204e40007003044404540c99001300c0e0216880c444000c0d84559000300100307c00201d20703200008280345020381c1c5e44003030840b4030028100b035600400c4d2203000d000c0c20706003400740100c0c10300303151000384055086016844d01041c40c011420b9a61180d001404282e484044000b034406141071000180320b66120968085c0e007004280310561801c0d20860741603c5164010506001d40c100007160309801c0ad0072898224403680216004654a100280c079881c0c0c2050b0000c03d80a8040c00024107185071400751a001e54001c1411140b070316000710580758011000e600602c200d90312815a000038100d03560051303c0401d640000d1112800301d0100c80030a981 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 765954838 1250 765953588 765953603
    0xc07111203091c0c05090a06030606321005090604120f0302060a0c0203040b0d0e0105011e1d1f090c050325020723060d0e0c01051206220e0a 62
    0x44010b2090318103c981090010184151500c0901441c500b409055400c04600d00700043c14540f48c0c0e4032031040350b016401803101c00c861a00181c07805441d0700c1004d144d6100c00c2060b081496121004a400d844100d1605c070184080441d5085841e15590141c03401441e41520140d034080d40c50918208042148205134010701481002581040040c0101040038078164000c40c81d1a1030241079a00c1900004c000d01003294031100850155030742402514080c21441100c0e6440c402c211590080c200042e622002042a030410421200d01d20001d5455100002a0400e59141042e5604d0580c0080707a0700060b4440c0d03d801001160194090302862081801118690380c030100a03806406404a0b80176080040c0d0003a4810f0080c4400208024400b80c44605a00000500a00050107030740116402044960380d8a603a000c3e6207804201000031a102824410b10b49826070300f0007100e00500404c42c5001c0e0140080e105081c0d288102c540c1400e070303000c04040000c01c00c80d0294580720601003e080d988039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 765956088 1250 765954838 765954859
    0xd0f06050a0b0f030403090e07020601050406090b0108130f1b030b0106110a020409050c12031e040602120c0307020a090e0615010504091d0115060909020f030c0711120309 75
    0xd040100c9a0300039074441c070342d00b103003040c103a904240e006500c0240104d0030455a6007001070407594102503540904029005082d040d030400d030502086074000c0c3e20400226003440251429643c001d60025000801d2100400740d80e45203080108201440700c3c0024601c2200106c5009000c0c0e0b20034000d4140c80c41280c1c01c1c511641d84d8401140c1001c1d861031400303215044110060b0040c60140e100c10800e510850a0b52420360058002586540c84814502c0b078070740000400d100c804071084900142940c0024a46082c00d0604000030b5856101414404958070b0007e00c400c1009070400589181c80e40c000c00540d6038944618018014150310544c1042c0ea208500100b0329000c0d906e04107030908481a9141402c20345058607140152000c14aa0080c1440f040610010241c0a000d180381514440c185680302c0d03490900d00030000015035100c030401601c10b108402400084604890700541c00caa9041c0e00d9001d00c3c103003096400c25000006602000c4c4581c8c466426401201030700d0a440200d5030180c20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 765957338 1250 765956088 765956099
    0xe09150c070c0602370501020d0f0e0d051c06150c120212030c16170301031704030c180b0a0905090115050306070f36050d0b06010e04110d0f06 63
    0x449440d459002e003510141c45150b19441c1012082c681220181045c07090a41040d0f00c8450880c0e00c840312600d032040d100c24480000c410240180b212100c0400010000c111100340010014040c0c000ba044506840c0071021000c001142c01601c0688822402102070140c0704101030b10017030308120104c175030031041d81c65001c003035001003444e003481800346001519560f1800d44507007090b0f001050f18101464032a031044041580400000c03104640000a255654154148203d440141c04000030000781c0402041c40011020802c0c0000c6446044203507a13980322820520015060324480503400100070040082d160599030043d60103040e000c0c0082013040f07260112080c0d2aa8140502d540680c0083c0224510314070550403c5143d6000d458910381000c155510000400c2903010020840c258803d0f818a500800686600080c541111414030401d8a55141c810381c0000800540c140290f00c1500701c01611960843c00500e84901c0d10389a550084420082c000c0201c110354100592802c240400c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 765958588 1250 765957338 765957343
    0xe0405161d09040803190c1e1e0e0622090b06040311010c0c15030504170405010e0609030321160c15110f0f0c070914150409151d01150e09150c070c0602 67
    0x345100c2c22703a246a699400342a00740c0760301e1440501e031a04a141007028181800245c21011242d02403551413506d81c0d4504142d11059400c601c3c40203200d05010003040001500c3c07111051161607080c02c000e0300c0c0010754140080d000d4410f40c09452003041d04a00c00078550340c10b61080303125034460119000100c0c0c035080d190116010b81e0142e2400320b00b120909603061b141a1003e00041100201100d00d0520280484a0b03200c04d5040e102410b42d040c1420701144402400c441c001d160450b10300b002403111540c403158483c250390700500c0c0c800c0756281c0c2154103105106085401c02c8140140381d6903512680b02c40c02e542580144002000c0c0e0090000c007180c0ea00c0c10340039034507000303041c82664007280d00c500030406400d5074a00201640302d65154400e4000441c4007200e42c000e40e10829002400500382c03040303281000e45503500d188080e454040e52104d26400c0070b90ba00195184184600c0c030311b0b039032000902d28080c50381540759204070384a4100314000e10310b0401040002e1080154020055079504141d9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 765959838 1250 765958588 765958607
    0x50402070506270a08031906080304030506010902031009471207150315030606050306100f1406130905010f0b0304050c100e0405161d09040803190c1e 66
    0x1d03d0360304428030020110704141c01175a040919015441d00c1c0c0c0c40282c01d103d0403034505a103e591581c02c0450b041042c0b05080c00002d00400e85080254070310f14051204180d001801e0244040b015901c030700394070005042e1041c2403100580100d03290748031080d8072a240c080d21380d2141d404030b802c9000e000c00901c07414a00c14510f4000c6805009128150a18912150b03400b1080c1701481019581d08900e401c03221100f8281c030042d4000d00001403500e0600c0203050070134500405601c0c4800a02d101000300e0034003403040400f15a4885640011451a807001078410312401c4c10070860002d081d0800f0407504819403001c2c1c122548514000394495548554580e580400c0b43e0180543d0002e4a00b091541400211075100c6071a0340b0703094100c942e41a002600700c80c010303940000102401d91404d003900d50009800801d8000c031055549882d00c0c00350001d04c0c50600100001c01d0103501002040c140c148101415101d02d08420085c4003644031100000d050f0101304a01403240d80c203400c02100350174001c80184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 765961088 1250 765959838 765959911
    0xb0f0703153809211b01021c0f0305060102030c0a0b0703140103061506080c0409050c090306040c0801290d020105040803040801020a0813050c190b0d020d061a030f10050402070506 79
    0x3492120342e017007020b43c95038184501090542c05511007890307009089500e88201210036446095205102010060881d14001d01c56410756004012034245106c0c00a41d82090f03d078010010b00350365a4a03581140502401441da0303e50b14255030001c020020342ea0010621203003d84d600000103a0380712021180b0250659400c400c0d000c04200600c2280820740000303910900c00e0560304c0c6421002c2010914008086170141c40020305150f040c0315151080c0125056602c0b0300015500d8207140d10081c010100b08003410078410740c2c1d0781000c101164064015200102400c00c10340b5151645c0b00d1190340070391701841179200000c120800054541880c44003860700c09070858010800500c10000384000c0070100b00f02d0b41c150f0030f980d400028a0254074002851140e07050203025890300400b54504043e50b403180c12030070b04d00c20110300a1360020039940603650b04c0218408642d5254985944002201d80160009031b00240001040c409000d80011704900590072403281303090038003c05528411180204000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 765962338 1250 765961088 765961093
    0x1a090d080a02072301020307080105090c0f13050a0b07030e090f06120a020901080a02030c0a06020d200d050702011d01020c1203160b0f070315380921 66
    0x2190305070245a0142808620074141800d40080c01d02222080b1078104222410a85d0000100103401d07520000a9004040581d10360174507040c0f645514506000300000301e14101008a00701200040c9026440020030026010405060700c42c90100f0640e071001d8010341c041041c14200c0f10307060070f109140307500c909006003d9000680301e4204000540481040d120765034451040d1100c05031b81d51091141c000c00d640780081c0503e1000340305042c11301410000162080c4480507041081d183c020440448040c058980742c500c0040c0c1e9034480381d1030b102c08001103040b4401c0c10081c03400160890300800c8107900076245e541e035204e041e2031080c0003424005030550058001c200c07844400e0900550380500f510440040e6814a04841408200e034901c020b029691070425030240408200005503040d0004203510781804651489481143c81c5440c5200300700d050002603600070a8041e043c0380d2201a40312520404089102001900c411138000c0d02c00140701d800018520310780c0f61803025886d00f1582c644c801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 765963588 1250 765962338 765962341
    0x2070302011e120e0105070905040203040218060105070f1a1501120507170907061106070903151424030d1b0212030a02100606080121031103071a090d08 67
    0x90180d609210961500c2800b102900300f01001100d4000c1102003010140000340c82e181c4810010800324656200e207001c0d034410130501c40542c42d0079600c07a12200e00a40c5600c902d84170840100c515214149001d804507084146070000c000141d000140c13883d0861148040984030300c0000b4201d11051001c45000c10751002084c0219141a0003640e0f00c030300b0a0130400d50a00314012108800c2d03004407645652500001d100340b14064110b01c0c0503000010210007000c00b450300100140c00082c035400042e01d041080080e0322043c3c1d050ba00402103103185041e0742106030419520381e85003800202c8400a9103003842c14410704906000540c154401020394606a41035042c68403940280c206030416600034021808852a042e0200020801c54425a00900d6041403081c3c040b400c0328101d400c80c504200e11030004000403410701801640810304951a40021000c0f07140a44a41e401001d20310300c0703070201150310303018001401c3d41c20350901c10318900c09000c0d50700e80c0b4841d0b848910b40c01110717011400100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 765964838 1250 765963588 765963617
    0x703090911040605071b050a090e01140103081b010b06072019120602092d0f06030c030702010b1e01111524060315040f060b0306060915031f060207030201 68
    0x54050406c200807000b42000c00d86400110344070a81c250080810386403200c200700305070502407280402c0704c0422500d5000341d50640d920a0103500c14000090103468050342c0100140c0000c0d0701c4003191220050403036641d15460314146485201c2c0c40088809c0b4007242c4105501d9007460002c0c414201c0310400c000000c2c030300b00318004600c03a41f1101c0981d40c05600340310f10f0429481c0c00c2c1d400704e001d036540e9443d140440b84c000c040ca505003403203a030407074019403403031030200040e13114281a6a04907401c4100d86850340d8500e40203d004041c25008503a014103030130040039150b01500c422621150007039031006050504100080e98403c102001a1168090100083c1544031081c0224101040203070004e404107103180700084254000703071104030b11501e610052003400e2405200310743d01e42440c407100b8050b845c40c3c061004443d0000030840d9018400014a5800c140d441c0d507400c07841d20301262655612410500c4080b0b400d450150001a00c400604070b02280da02c1c000500315044a5050355000114003402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 765966088 1250 765964838 765964853
    0x1c1b060b2706040c1718070803090105071502071709120316021c050607030209040b09060901030206161713120503030a021b01051e07090308030c030601050f070309091104060507 78
    0x3420444100306420680649900013403111a00070040d101e807110f0342e0040720b0306d51400c2103419404084d46030b10400c411803a507600310060f2140d00740c100307903031503000140c8902050203882403001c010000488518040f101e8079410b000f81c0020700055400c20b07868002c12100558901c640b001c0c1d140c5c04d5001c4100c80c801403515800800c45102e40020005403107500b56a42c901e03140d0140c45400c0401c4e00441d801d00c0b141464031446000060403940d15070035050040c04100343e1801800068043d01c5d000031f10300c5c0c4c2c0e072201003a00507105511603840000070f40d45c0d0480450b030f5044016401c02d81c9501820000303100840c0a48121100d4002c00658515204c1980000003035010180c410100c0c0f043c00b003c2c1d51001d03000e1203038510070010507880400c9007000807400301008900508000a0020503002440820304039820382c0c1e031200000b40d800d03560707448a00060703440340a0000c114100d81c42c0010400200b42c1e00031169001c591001e071052005007450380c00d803e00c0740598024070b00060f000340321400115168 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 765967338 1250 765966088 765966101
    0x1270605120d1b0b040215091305040b0601090b120c0c10050f0f04081909240206010801181b0f170708061306020306040e03031602060901020a021c1b060b270604 71
    0x407c6111403501c04160040313001c4098a041260041d81d54200708000d00141040c1c0f076621100920303040540608003404420301e40034102d448119401801c00040050703a0640481d0125505030041303400b40103500c4a540040d02040b40d25100d0184104042003441540c3c4000c64010769104044034109961403045988161002a188003080074031b080000e00007003800c01d4046503004840307004480c0200758002030301d0301e030041c0d00000d0140c0c0f4200c014070704943c03024000c00c40d86078452103c80c080941161051034100c215004103844c001d280300700140340c51f000c004803009040130340c00340d5030300342c1c0d451483da9141c1501f00e415841c801d07000d00085000506c181c2c000e40d0f12001c010000500d0159400742c10b45960405c8400500c000940004280c01c0ca80401c28030307078082a640e00a40c6098203a07100291200103402d15103000508220b0101c0d40203024491000d0a18040b0b4054044014075080a01c06821012a51030080701c00983d0016030700c18503409100d040d002ca40c3c55418070b031111420700c07005140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 765968588 1250 765967338 765967369
    0x504050607020d0315031b0b0408014b090c060309020f012c030a0611041e0f050127030803060a23040903090e16090608100e09190803060301110301270605120d1b0b0402 74
    0x255000284002000641008080c00341d031390d0005491115803040c008c0e40d1504241c0103042c0400c0e141060f5845140e040c4170802c0e10075285240ca403102000c004a803511a410340020036880c10721204140c4e076850400504221a8400d13140c5015600310344080100d04890f002d00800030900c40c100340001d500856189a0140c01c46c01481112091001112441c00c915001143c90400010601c6101c0c5001006400a440903200c0c0c21648080110030380690002205110702850300c84a55109250060146000400104590308112b06d0031000c850701d0741503022410320204044400100344507216104a5224a00c10b0100b9400b403800c24018014041c070041c0310040390701ca80001e040e08807a0048002800c2c034801c0710702c961a81408000c01d800d480762103656410201d0184010001e4410f50410702c85000a5402012161444481802c001d084070b5005241c00c501c5000903480c000d20001490f0a506c40c4503036860302c1c0d4180d5a020441c24030640840130f8601d207240d0f03021402614080c8c01c803440c0c1c01c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 765969838 1250 765968588 765968591
    0x2120f0a08180102070f02041d06150d0c0806010317090f010c050712080306030d11100213031a07080a060602101802040504050607020d0315031b0b0408014b 69
    0x5440d04101c0c3e09aa10000c403c4408080300c160716011420303d4082e46220030f400d8503076840001184070074140c1d618801806010000f4003604c80007116111000c04400c281e0b00150f10f5110207842d0301e10706964039801e1100320b03035403003c00019403402d421050035980c4407140101461912010340004460541d04032800f2740e8980204540021140ca03c8900900b0300b500c41e40b0075a44a00d4014201402e10f03004080000500411100310381c0c144202041100740700d01c450300c00580301c1c00003c03022801d03d035154000401041032814540b00402c0c40c51940c512904256079401c05680e1100301c0351007514a05c0c0708000140e48001c001c905850750541000e079401c0e0080030020740105080d00000c1c2070320411340703040d90300e90807130400d005500ea030510016555800741d007020f00802120842c000c8050466201c09030000f842121401700e140042c80c00c01d001088040000c0b61142c1d201d43c0264000c2030313400001d84074503850801c03000168844030313581c203082c3d0480f0950208140d110944200204000c0584d1050035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 765971088 1250 765969838 765969871
    0x40513030806130608070504060815040311011509020c01051b0d0f0b10030606120b0a03170903010518070618140604152a12050a03090203010501120302120f0a08 71
    0x3c1030604c540f00040940d08000d00c00700b40341c03038140000c640d01600b002d021034104002007192000d0b0201c01030b810541c0352808034002450b60101e42d00408030000710941c0c00d41650000100400c064028100c090400e4000300f0841d1111100030324109022044040a00c2040c40f04640000d81135000c60300c0d000c0c080401084464900b00000c1091016200802c0440e94962003404070360ba001e2110300e88010350b1001045000d80780b200040c440c8580d0701c8001c100c452003000114400c54040141c50340e09030054020300a90415800d02001030300e00a42e00d41c0d540c81078200c0081d03241d02c204a00e140301c1321010401e550b081d04140c10280285005030b4070036004401000001b40c00581280d12100302001a5101c081c01a20f00c40000c003140092030100070240c10308520340000c104c1e04200d030980d42ca2b060507c1903407041ca81030190301407d100300d006540f40d480c0a000007a0010f0341c00004055a209500303a81039206070300e0508840740182c030100c2e45008400c0c0112010a03000750b0000350420215920310852 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 765972338 1250 765971088 765971119
    0xd0303050c1b03040f150c020d110301051005150f030f070c0803040c0812040308120402011418090601032708162003070602100213120c060e040513030806 68
    0x4900d500c01050410f03840003408001440341a40d00070041c0100600241e000307001144018078440308090040c4c410540210310030200004000c0e0786080c00c802400070b01640c9082140d1007140c1c0c107d441080d010b08441d03080c00020034408001c465070840e644000c5811034a03107050300035141c20b004000380280210207100001054a92010318415031046d0b184a00e0315003850506030500c56940c1c04002645d000340820b00c009801c1c842556242d007510018031010303550346e00040f5000085000c240c48811400074092000d2a40d10741912251081600d620142d40c40e1100110116035048030110703d000c4d00c0c031001e1301d0490b588585000c415401040f1080c101002c44550326562010740724101e4030300d0a102c800c100c214001560281d1018001c8000e00703103240c50000060344071340310052491100c0d81d0028204024100e4003500e14090512159071107921406403030a4141c00f0900e000751408103103d00108281c03494a4014684649040c0c9654040c0040c50754080e580f200000d40219446075040380c01419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 765973588 1250 765972338 765972367
    0x60f0c060e0a06092411040308030a060f06020a020f0d0f080a02150a0606030e0604080a0e0310020c0706081341011e0204032a0e0403020a030305090109020d0303050c 73
    0xa0581c01070b18000e070041c0400d00c003c0304801068400701749444c1040b5408184500010544040743d4000045641c1c0380c0c1d41d4141c840088c20b158201c50004001c03e940803c0d0300360700180030b50406200340c13241d0f094404603104211880702c82c81c2c9c00030301820700081444006100ea2003d040c00c5490345c0111004180902d88104801e00d08456403c1241d507240030030080654180201c03100c807401d11014081d142025100d12003035100d04030700f880038000940804810307901e003046001c0700c050340c13001d0031900d0305104415207858401a20035400090905008500b102d05182c3c1070010465005501517124448109004840140c41e80280d0107014880400481646a01c50481c1c007464a0000016038040c2c0820041045a60b4200070100c144144005d00010740e20614200c01c031130318003844004204003440080003100c2c81d900281c00100d03024007030104040c1c001034081415482510203101603550400b02500701e60788050080d5009440b03c00e00c0c008a40603500503500905064005807800d0005414800c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 765974838 1250 765973588 765973601
    0x3041505071506060507111008040b070e060c030a110601060207050112091401050106110c1c05210c010b010e061608042c07090521070e1906060f0c060e0a06 69
    0x18085038001841b04104039070090500300d0300c50115607910442030081401400c6503002032006001244038404500082d02075064051041c1c2c0041400b5503c048400e19181c5907080760311014045402c12201401d0b005010502714140c2c1c465a000b0304074907103414011a2102440607031503003407a0350742100070701090800100c005425183d0b0000f2985515005004248c072511406101c2c2a0308100b00356040750352001905820700d080141c0400a4801504140741808407801510070140c444819020301a60740c10090403e60148000820050701d402006494854000a12942c0400100120302c00580060314075001c9038010011682415102d45413803000f5071011180c3c450041b01e11328115088812690159404400c2d46403240508e032403d03010a040000c2c40701c45101d8042d13480f01c0e180c4151400c1004800501c3c80f07038040844ea00f856500025105108250a44042d06211010400345d0041e800d8228519050b900c0d80984000c42d2584402840c81c106440d10501658810002040c030500414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 765976088 1250 765974838 765974849
    0x50a0609050406090201090f1214010e010504050d0e0d0201210e070605090307090603021f1b030f02060a2007050703050102030408031f0f030f08120903031803041505071506 76
    0x20311310381a0001418500351940180b030010f0b80381e20b09114001020f54001e00381903210b0142140308034a0fa0340c0c1c034003408000c2580c0d8080d619080420040c0440065289004181500d86441318070700002070022441000c54080d0109071100c1e41c1e118884c41e80444441c513544041000181c03000407040b41401c00b25654400e0000880c04908103440c0e103000e004400007050034a0040000f00e1465004c40d800e0444401c01d900329000529051100340e008800034243c0b0b840031240500000042e2901a0061241f00d4280700107101e00400100704408034800c984103010b40d84041000c6101d101020707541c45d030140c40201c1d418000c4120001c0000c40900155000f1445000e0301c0340c813850a000703202c480301d40035a0712680c0c04803140c104200c0041c0c02101c0e032003940c1c0c0056900321001002d0410056601c0361540030341c08100084204005c102c804000303140207400f102c00040303000c3c2c115107080d0b075203001d170303000700782c840d8a0403005041c119002d00c0040009034400d00002440c850a40b81d00b40450b641a03104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 765977338 1250 765976088 765976091
    0x20c09041214070210050306010513090203040c090b3a0b09010c0c110f01050c03030f191515090b19020d050301030f0b100510030219080f0a050a0609050406 69
    0x11089550420300d003088440c40d810038242021203640000d002500001690745c14014000301103101648100308840c200c504a90712540c4081c0e6500d5540007d40c030403241502c40400100300418030100e40d000784036004000070b203040012848808006200d803c2c00e4005039000000e0704d8031221800e04080820241c500400342e1058618040500c0e900356038944e20020308000c0c2e0012040d0000e60a030303e07000c81c0e0000555403004a0282040143d03003521400300b984441d0b10002c03040200750705600c81d9483c40350344550381da50a901d10002100054404403011080584240c04050211041c03034861000d20407080e01e803c1744c1c031559521405c80d003a40041c3e00000c0318180384107042452501003091044164140c034040b840c544c90341e2aa181501138214000700103840c3c40000c10749000486088070064903009041007501034480d1b00140095000054144004100189017038032203002d56103061045940c604000081e980d9200200700405005200c5071f509035607008041801d403558464284075a200308030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 765978588 1250 765977338 765977363
    0x105090409150e060705030c030712110901020d03410103050a11030615100216081e0105011412070305011d0f0c130b0303090301111c020309060c0a020c0904 69
    0xc010b0709451001140305041e070b000c1428010344643c02002c03a94013480d01e20040d61a03440b28182200c000b0380b9481104080d41c241039200c00300000703503401080a40026002c4079005214100283e080c0ca4100c0f01018281034042160780742c0303040c0016000c401e000f40d19206001001c40b8450031000b10000e81060741c2a921051100040001510a10144060403001000f0901e01010080d0044c0c407981c448501072180001407145660007040f61795076807001c8542c0d541d271441e02c0fa02d0065071a00c10f00d100c0307440a1040d0340383c0b05841038180301c0d00341a00d0a00780c01c80c0500f1058001c1c4001120910a11030803031280300340010100d2007e00c030300b4140210341d00650100c0b568a22045140107040008410385030821426515617546104688018030510740004c200d481d204000a802c0d40035010f40950103500b0002011042516074000b40418185a400f943c1d40300c0000c00c005040740402c960124840d4802d5020801e00b2045001520301d502d801d10440c1c6012100714042242200305030790884d200000c400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 765979838 1250 765978588 765978623
    0xa030605131e02030606011b0b041203061a030402040543030506010f080712060b0904060b0a08040605180f0f1c09121b0b0d05150d0b060105090409 65
    0x141040200202d80b0714030681207200da000240c5582d0090142e5040c800d03030721034158107003081c00017402807140c1004411b1090b182034184103140102460400000a2610754089000c00701c0300744025581062103581401d40c1e03220350a02005101c080d00e42801e442015440b0101c50902e04008031101800c51404c21100d00202c410b1901c0030400a4101e0603d4100020440c5a990102102441400e646080c2d00b441c0c652810983c2c005000100c980350f5603040c0407000c11480b0300b0301c0003000b2003c0103950412140e0381e55050702c0e110380611a00c500000317840300040f0300410312503000140c02144188004081c504282401807400f0814800c0100c1600f01e41003020305844140108031028803600c85150040e000a078000b4032051460041001c3c5210b0a0800c00c00d00c84440d43c5c007404950000b104540300758031000c00140b40e0f0400c2204081c201e0420001544401c8801d41940010501616110103040c50750760781010264002e00203810400140171500b000c1d95140207038003016000b45a440b90280a41d0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 765981088 1250 765979838 765979853
    0x50307090209010e091e0601140a0201140117030a0f09050a06180b0310270903020a0b0c180607021201020307090e060d230a08040b03340e0a03060513 66
    0x70080b640c0704078044020410002c0d1721038486c5046c0b22069a005050f135941c50f0068070704180742004c00ca00c640c2c0201d0509407194056010f0702111068084180880e0707a1420725131081894058060416007052103440b070554021548010304500c141803101b04c260304c41c0b020401d9800e45500480010305001240842454107800c08000b9004020f44c4a1551414661401440c3d020781f0030350760710b94012421201021100142c0c040d00e07003103000e000d101078991800c00950382c040b005030649000d903154010641905240c0300f01e424026076510010880003950342040b200307420000090360002c0d00741d0012490b00800380700552246800d52183d1845904142849070b1842c40100314500074006205d802003c07070500d0015003006503090f03e5417500c45102c20750290408480400081090f0310109011800c02d40c594040c6200d6070038035100203014a04080001e00e013864038100c04496211030804d500d0b00c140702d420000c100001c090320700115150b030382d9160422907000300c0e188580783c4130000c0c9000c2046000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 765982338 1250 765981088 765981107
    0x90e160810080304051005090a09091a061c050a060e06070216140603060303120c0d0c0e0d03030e161206110f0d0513050f0f060c040e010e07020705030709020901 71
    0x8801060384060704142115035030f48554003500d4400c9040906c2c40710914407a4040b204901000f5004110f0150f6481a0f10702810303508500b1901030a0000c441d070349511042420a2203190010040c490140c403c201121240d1100c580030f4689000702810314001c0340085c080d00c010180008001d207024908060000d003848162503040025106100041140380510320500fa5050b00c200c40c095620340703400c13000a2540c0706008502d0409132402c02000a2014500042c044001d0810002e100170005044220340143c0c032541250b038080014403801c1d001c01e02c1390344100c1003810801e040360b5100c4064081000103440f030741e02900100a0050380041040700d6801501c021501501d10f09042511020141c040703400fa05a10b0300b1417036542e000055203c0f01003a603800c802900030069801c1100c00380c0000e522401000110a041d10980011803040754000084a00312601944d20b81056420302c40e10b0080031102609520442c42400d00104551ba02401128010004104010390301c0c140b510001d4804000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 765983588 1250 765982338 765982351
    0xc0f1101120e07170316060b0f060c0a0303050a18141608030a0e0d06050f090601050f0d060b03070e240d0c06032408010b09010e04050a02010807090e1608 68
    0x1d110340540c0c0202e00003007060a0311480703940d010403d2041c611561550151915850050241402510900c00780c1d0b80244007140041e2440315554600e1b205200d242e116a00d142451a4041c09030f040c04680700b0ba002a400228030304010500c3c03504803000701c50800d5004c0042d103100410039013040300e0380c4041000000000394040c10160151804140325128043e045207031040c00248074000c902c9075290000d0b403402961107035041050382095200190000803c40f000d55080c0f2a54001060600d071031703401c205400500074056000c250041c8d881c0005801603001541c0c05214285c03021891080c0b0240e0540324001200242030074402c1020010440c450070138403540561003030b40c0d0344004118038005040940e182400c021030b0072240d4103d20000e1060b1607054201c80401d8201c082100c84c01900024a0500212a20742150b40c80d589221085401614014420360007460707030400650290042c50303030050300d5080100c0360b1581c903040d8200c9007204841b024070000000403202011078104074031640118 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 765984838 1250 765983588 765983591
    0x206091501050d06060801050109090228060302090a1809021806030601060c140a080406030e060114150f030c091203030f0a0e21040504051f03060207030c0f110112 72
    0x40440291052a041c02042c3c0560ba01c1c1c494802070265a400040007414028002c03c030542e510b60044000703024081c0308910070711072100c00c0b00c0d407105944110543e1440c41526605a1483d10300290006d500181c3c07e19044103a100002071034044185120405081001000c68480d0706407040209035104450185078a90030b24080c0103083d1000100f06054500c03a0a00c00700e81102420701100f2451103000710303110740c454403508804108100000d1b10440303192b81c070f00f4460a00800446030701c400e0240500302c081021143c100603545009891101d40094150f03200346044029801d41c0207580c02111007640203140081d11038410304010028802c02c4403d02e010f90f04606060216004008019111107005512041d440546c0c1c4024030885000c410300040c6503001e800086618030154025104c0c013841140f80c5400100704010854403090f507080203c148040c11820342c1d0391240203420000f025801c01070f004500e4400a110354003190049401038101d190700798031100004000710301e200da0140c840ea = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 765986088 1250 765984838 765984853
    0xb01210f0e0d090e0a09060e0f060703270f3807020c042007050a06060b070302100e0106030212010515040209030c010c020d17040806070309020f10090302130606020609 74
    0x116032180008080d14807102d60400701751124034015002d8821110702030300140ca024480d003002c03c00054240d08900031007040d00c1060707480c6c070b070f0540440ba4040061107031184240c0160b4000701075150f000391820310030f01414030010080c0c0c032040031210075102d0380b1218400d01e0048890b49140c1c80c3c00110300c8081c00102c5d0000307142001d4004c0d16066030303200040c001e980ba504420031031001c4600c840350396542500750070380328405402c2c00c0d941c1c3c1c1c2e01e00c901503034420701d4450040b034038540303820451b22204d4054004090322000980e1400c02070140103c41980c075542d9100200069480480440742c0c0000b0200121705030801d201e45074141030b1040280c6100d20301c1000b040207140c03808907140c04166802d0030001d6107801c5500102c3d4285850520003011401040508403018580c0b00c05003040d22809400c485a60f582c81c0010b0701201d103042c0c0040d50003241c151702150140740125412502280d1481c140d03c1e6240d513540812011805c1d008841c202580720b000034002141c2c1003014660004a04c002040311 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 765987338 1250 765986088 765986113
    0x106060e01050306040b10031a090c0a110c0306070509030f0105010320032404210203122a040510080114060c0f15250807030b01210f0e 60
    0x21010031403049042c480040000340300b80d40c4691015100040c041c2590000c8013080400034001c0070010f43c3c2c001c420404003001c024030304001c1e480364402d0922030710140c9022a60402a922480a02031782c101c04e02c40c2c210311350000d84003070040314091215511102d4440b25880c08140c245420b0032103500c00d6a241c100100081007510000ca502c2c05200300c160989403940c5c4010904180c3e03074800c42c60700c8200540a29070f0748603049074035038403440c0203480060f0402210642d50030b55041d1040004010b0380240140d10503010000c100381d40125124980d901c3d800c0c080f44e81078460109d4003844407030034480030401b0025810160f04902492034107282c010b0f182d40c1005c540a540700b2031002c071540100c1c0081000141c0d00010405036003201502c108440540c040804490f10405049030044441c2d02da82340f00203607000c8181c4100200c0901500c900100b5035401d40d08900400d600b0307203024108440c00c0d455021500103800480038482902c400415803150410707001c820343e00590f07030041c003d13400003848210 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 765988588 1250 765987338 765987347
    0x12020f0a030e03030f1215010206040803040602030711060a060e01050f0a0909050a02090103050c0f010302091309051908130f180b060d0c080f06060306010c0b060d1406090f010606 79
    0xa010341e0500b0103aa80510720408a0700c0d40c080c140c2000c01180000554511030317004002085c2c881c040351000702641950030f000481c1c4030340c2c0070f440040c01003000b400441d0003c0c01607000f5540c00a500e18200a6030094140d20302c0c5064800d0300c00700141c42c0d0315401840145500034040c0c1c0902816545150030443d0080819024a9203100d9802629502d00601d02005000d2000c0384003241c0060246995503160b00b4400e48800c01004a544502204107011200e03500074001c2d070340c58040081400c40c201400b08080000340014040450b02800b405603a0000742490303440e0310414500540b00940c80700c04064040070700a0040d0045113180c101c107a020414940c4052616054410781d4a0200b000c0c007a00b00800c1c001c0c083c11744460061420a400d10701c015500940340744c0314503226103c07100103803594001c0c0002440250b80c02030015908c6400340000c5001c0e422282e41024014020310700039507040d100d070968101400a511400d8004409205491000f00101c0c8068024000200075507868800c01a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 765989838 1250 765988588 765988603
    0x6060f0307030f08280305090105010e012705070201091106040b030417070f08030718680f0f270303071715010e0d0c1212020f 56
    0x1d220301c21100040d001c2100d90425952881e81c086110345c0e80900b503d4000071007107012844000004c0ca01400a81c0b5240705015141c12104121010342a690800ca40c40c4168500101d0140e00d070041002c0ca146c080c5c2207846020300c1002d1a40c00020048094a1302e8003406d0703a6090211b2042000340010b00042e041c1c07504807600294003a140b045440e4160f01e00ca1064054050042c11401c007084d240c000340a6248015441070b805a0740f07180200364036081d4040c0141d1300d401170b01e00000c2d580c62802005004003101089810102c8805c00c135031044030015400e0b505800e12080c2c40c8005001700c80c207110707007a100a00c01403404080031700514a4480584400010000c1c10001c4407110381d030115811101c48901c500020f8600f200c2c078001c03a05114140b903584e9009452800004500b003801108170110040e82c54001c4404204031080e2140300344c01100c0c5d000e43c44101684c41505000000e00180440c100030f8000c0000602c0a44012468109455030702018bd0034201550400b08484007044004681c18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 765991088 1250 765989838 765989843
    0x403180806061807021e010507090e070906050c07050604031109060d0305070b040c0302040f051602030c0c19050d0510180308073b0a060314040803060303250506060f030703 76
    0x4072150f40c2e0034404a18111107006c0815040720a030582124078001904124800d03000d544480012a690b010710001d5a542111b0b241c000072139046003442400e2107040180380b4019184100d8000c1500e80b40001c03902d600c81c1e40215910903048002d41218100015900d500071003c555a4501c4605c07610082c0103482400030003011184500005010803106101d404086c1d41c024100300041c50000705000c00508058410700a00d000c403041700344e0003030703c0002181c50001004001e0900c1b881e0040c144040d259440461210188007004041640c1e00c9106c686034000740190010500aa00c5801c9038086a0940040740f01d03103044900904082508200d1554028405181040300c0c1190320400540400c811000d50700e115848203a20700200912607441e04517040c0884000c03d800347d503004c05508450441c480f03110409030b440009000f18980340e0140d81e1041000e800d584c540000c181001030008098229126050b184c810030106100e4104282a8840d400343c800c81c51980720719002a585842d5032100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 765992338 1250 765991088 765991129
    0x130b0f06031306180602030703050411100f030b060405040207030c0606051c140f0610060806040e0d0f020330090f0319030603020a0b03180d090909060e06040318080606 74
    0x1503002c0d54048804d40040c20f030f003012046445c0e08210303500030083d042c160340680c2e0043c1803c00688031407900780d40001c0989600d8692980d0042140020390181415081c0145d100c001400001502c0c1c503180000d0611610960f00c842c5090b4207032418200315039003604514040c1c0080820b11013419010840305880581180f42c070b4100d480c04803080b03460160001040c1e0150b01605050003000b0260f01c0304501500c1da00d49591409594400500049501030401c0c06d0455000c415000c608074002c0c0741820841a851050f00d01c3d02050080c2ca411070116403852091a240d020302080c422414404000d0700603041070040c18003c174500b0600383d81c0380104100c801d0034202c08011035204034001d80c4070400071a805444204c2076503550b00c461940d80c0044801ca14502c0364540b0031845003101044403d144142134031464803150500c2a0403008120f40e28084410307680d034032410b4500303600c1041101c0c07165129989200150313502e440c170050403034003550111080d64001d60510006030780b0b021050440030045c052 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 765993588 1250 765992338 765992351
    0x302070e01080a1103011d1617061602030c030a020c040c0c122019020f10080f04020105040b030f0106030b04020f09120c10020a1e03020c040e010605130b0f06031306 73
    0x3900402c070011500240c2c041f8106a403804500204003810f0421050011245241d035a031001104004001140441c87d004000068118800c82c42c050341640343c1441100d0030940f50717003541d40c60355000400800150740a101c4c107010034981406400c100400525051071051015600c42410f001030b00d00c40000d11040c08400810309c411408003009049465041300c0c0c207611544008080a0308101c0140e0280011091842e03023810040905203c08050766502d008564407035828010846001d0302c22070400008000c00a040e01810000c0c50181000311200151545410b90241c1120300c3e82400500680c0103004a15456041c4070941d603c51406440f07134800c000da178248290030519840d29040d801021000b2f041a600c0d400540881c44611032801200d2800070700440107003440c0c540c0c40c002c005a011404d403400b035007881d40060078070380d02d050b0001c689980c803000085c1d440581a003c00d0a01c0380d90341c040784c2d0a0f242001c80d203400b004050340c045142d401c107110600700c0c0c2410b1140c0501306584030075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 765994838 1250 765993588 765993623
    0x901050703030c02030c0a1b1d0c09041401032a0b0a0c060b1f26010909020a0e010605070201021b0105091507060c0306080c030114180a0b130302070e01080a 69
    0x843d140180c9007800c7e070f0113254040c030b00040c80200601400104100c5040003084540108070821145280d1120030b00d0540e541c4149020503601030854030350003584503a580400c0c1e800c41c0526034041d504c601074402d100d086e43c200003d000d201d10504030640c00368403031f0b04206940c0d515040312074054036403400e410715030010300307050011744901e496031500b02c840c122040e004c007c40110041c0880d000c40c0da03103c0003550f01041c0c005504a4041813513010704000001041079280d40e034170520b82c6900c050000001d6555901005c3c0740c109090f400711000c2440020755004543e814402c07801d41d08110f503281d10040d400240020b00d07500a2500540c00f0305190305c58801640c4540741035416481e4000c03014807485041c07110080c0600b1403807044900612803203861103c1881e041c0214000c000a40e180b4071696a030320150b01d8282d9464408040301401880310b0980411354040b05a803082000782c282d0008481c1e1860001e01e014032a9000c543c0c104855001071046200c0882c1c000e040680000480030ae200181 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 765996088 1250 765994838 765994843
    0xf0f0309050f10060f09021306030f09060f0204061b0c1202010c0611041401080402090f0a0603082109070e0103060c03020c030a1d0f090a09030507020d0311010605060901050703030c02 81
    0x21082c0040601c564280740c03e03540e255070010b40c01d42e41181c000c03160742da58079120002071340525981d5426085006900f072025038401e0384a5a00804229400308140440b0746444045491090403420741580000d000d0140b40d4110a60003181c038992500d042a5021030380f588640035506000d0400c03181554081102568820105100301a8000404001c05081b07941101e10f598002d05c81c0c1d51441e2210703003c500781c641c0940c2001d84207e07000381100106555200d140d102c020001400702400d569a01004000b054000c80644018035141d045480c00b40e6502040c541074090040110540e640905400e0020b40f204020160440c1da00c140301040e070b100025002d90281c0528580a4071a100c0403440356007107507110b15892032900351034491344101e21a100034888290150000c0ca0740106803074010a86420060344070186d2140a0324215050441c0c550004002075103030f07030050b40081c80c80c040d00c501e024000c0c41510010b0000720b5006203007801d0b040001c3d00d80d006001001e410700da51807a2145559009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 765997338 1250 765996088 765996103
    0xa0b070b090307050d0c2603070c1b0806241521040b070801170307030e030a020a06050309010f36140a0512210405030f070b01150f0f030905 62
    0x4213040d288a4207020b100209010013007030b000e0743c48800c1540e500c90488114014a02c0322007090712042e04d9552101d00548601328060300c2252a441c61041300400107032071403c0c40002d00b01c0740300030701502e08010f0a902d820341690070180c5c4502c62503107444801559003485510142c03810040071911114102e400300380c510074050007010440351a100304020003000700b5841d4410089134960701039690b00e6101d07a00180c090107619030b401d90310400803036011034010341042c0c00701c4000a0854007591503503400708913140950760185011560100030704c00c1d040d00070f00468804a81d4803170104001443c43c4600b113a00c60080c03400c0048910b069050002e03807102100c1d0b600322103811660500d0402c40798142e4030794418515405481c1401f880003580c1100303040a08440e0a240c26020102960701c080d04c0e0700c10018006042160305202c10881002c0900d40c0101401e0a68028561001e581d8900401051034114179010f12040004a45403180901d4001041c5c2c0464041481c0010f049641860200e141484 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 765998588 1250 765997338 765997343
    0x3070c030e09010e040210080601021902210a12020a0201090902090f0a06050a170402060d020a0203131508072c060403061503031e050703080c0708070302011401050a0b070b090307 79
    0xb8a20008501c004038030101c5801244280e411480c084000b1004440e2080281d40031030050b040000c8540300800100740103106540000d1194181d11081c4000f010a001c403002c82c1c0700c00b40c126a40b45030600c41da212641c1c20981c543c2c0090700072508113900080c0500d0081c010010615404104d228103900c44a0f08200103002c05010790b5200c81c2c031030034007428540098070350b200041d403000c02e064059100440041e02956010702460f007000f121098041c06034200051035402c51000303001640d8007184044903c4010b01004107401c8051a1012000340031220080c01ca000344110381540c520b65098880c07020b4080003226075519200d8108500103061072141d6071000c1c100d035040c80c001f40400d0381c5072603410342168400d46940d0b0340c542541d840c0300402c10144507154003240d401c0c414075021a0080d01495400b0040c41c80d458500115941ca212994100200540060b9503445030000c1c05180c2184040c05040c003100c40031421840c00d1804400387c40381c4400102130318642404203c68100800640c2c00159 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 765999838 1250 765998588 765998599
    0x50618190e062b05030c070e01050103110a05090d171c0c020d0f0c02010921050601050102011e09111c030e090c04060e1203031504060b0f03070c030e 66
    0x80055109044002409521000c45a91001ca6980e03e4410208814044881031016200050010b1241d06805040043c0c0c0c1c14001081042c000040074081600a031980d00c1112031f540d41028001012a4280d15100c065050200050b906145e000010769034610021640f44010b0340315442c00b040302000791114443c09140102d144242000c5201c10b6a190f00100d4104022400780c80e40b040341d480c0c0411442c40041210706000c96250340c81655a98803490060403c550199a100d00b11200b4604a20340c9401800c182301c0e02c5000c01106200450042070248001d2002800a4191989044540204d01745040c2d0b601070380020066500c8215000c03800040c802010701441881103110f403c00018228001182801031202c1032034184401405109408a40d80c01e00c0d040031803c1c0c4100100354a01035004d558000318012015080000b18409e8441103001c20425028070140425607100d9000308082103414040e0300801203a800c00e0380c0e405082880c1c140081081342c00d00340d0310000300441d02500310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 766001088 1250 765999838 765999859
    0x40c0e0702030711040b0609120102210402010f030525030605060f2203080403020402160b07091509050612060a03060e0a030e0105070f02040c0509040e0a050d090f050618 75
    0x641c01001038203445004041404500051000700421200c4c500c0c4000d5100b0b900f031149240604000e06004d0015207040c000510700070b041d5042c4d041e0107540c45c1b65551000b070300388200030465900600008564886080078000750501c00032490641c44941703c0428004003200714075440d540b01c4e402000007090080d000503514040a4548001648540c5280d0b003103040d2002c248120907070101101c404c0f250083c00d0386050504690800000e540400414030800c403284442101081400703032130328014803068031789056051030442c0b02c0f042103001d141d1321424861015420402c580341c0c6030451b40d480022840010640e580e1074002040040c0e59003020300030070f15201c010303c440c0c440080c0d0020941c0c040d0312200c030540c481d0001110365104610b00206140e04c806452401410aa045400c01030203506201c0c1c205070480740030500b01c400c04041040c00da4084511082880014443e605c40c1c030020b45403065115040401e5206032544502c1007038040d620000d0044180c110400c000003c1a44c01400105038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 766002338 1250 766001088 766001101
    0x90b0f0109060b0a080105060703030b040c0e19050117040201110304060507110906010f08191109181012020619120e071d13020a03080a112103040c0e 66
    0x4214240541400d851409802156022881059030400d18040e0b40d01030481e8205400e00c007594016000450a06466120320050740d031341c1e8060010603400c0740c1d64241c4082c10520030070481c20b514140701845074810b0701060000b40d80c46800c000840005a0040e8055140d52004850300300c605101001517010208000c54900c0c0d000004106240c0140114051401400300b0802c1c00b903020781e842804910180c50b407414542c060381100758001203043c0056100b0700d1300070a030b130292503c50441c040c0c4164001400840e91828515001c00500d0211941250340b806032182d00000019000342d0f644801150098021585c9400440c3c611244030001411110078480018013017420743d0350000d6040c0c0c1040685407441c0f07000074495044821601784952200c2588101e03941d8054003a2260182e17011b01003000d8050703119a0f07241d000541c40303022140eaa40c0d200600007000381c0c02c100343c001d40c1c580005100c500145559000d2003410f0421800d00f0b5541e44552a004025154541c02190b21000c5902009070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 766003588 1250 766002338 766002361
    0x10c110d0507240801050a2904080304060206010b0a0c021302041814070c05070603020a0905030d020a031404140f01110a140f060f0c1e07151a1302030901090b 70
    0x64403640081d11003610f00d41080305aa1000090040a40140c001d03102005519000415072406511400c001d21456200018200047d440f60304a1800f940c000134007004550740c100005401805488000c43c2410050301006000d140280b001a100d00414004d42d848500d055048038014032800d188660704140c0d460000340a000070110a4801c2c035000ca0016107010300880c52191a0355004000d000b20340d041c940250000d41240345e13500b04100031680040fa407501c1c01c1100d100d00448940080c102d00700c0034603004110b900441003180c058101408204010200d0007040102007004031400090340d826030004881500c0c105086003060320503010305101340001c0001c030300620550241a40d510f22901d50600f6904d001c01d41d115100c0d050580001481c651a40000d02080c140303046c0c50010103440c00780c10380415040a07905490204100c1e20910000d42c0e03d20802c803e1007a1410b50b080050074550000d4140f101407800c81848640000c0080c0e0040c1382940305949050b4402010040350425800586 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 766004838 1250 766003588 766003619
    0x321060906090b040e120c010908030906010918050c2218030f0f080114010e09040305040e06120a0f020114120a0c0e0a0303230a02011b0e010c110d0507 67
    0xd2400f051840c090800f0f006030b030001a414401000711019034221402e081c1c0c0031a0320005203541c0d903d040310000d43c1c02c000450148600800402865040194440407214107100700301070a904c0d030044200103100826140101c6104441561040782100b007a0fa8882c01010f800c40801d46c500740782440c1c10161100c1550060b80130741e0392036030305941c24101079903007044c0194031802041d20717240100a50211007242c000c0a40042c9081090b030040140442e42c212410b42c1c04801041c4c0c0864244600e0310a103000d0341e88540111403084040000036115902c070440800b001c0e09000c0400c4008065901500c100b600e00c20000c00391a60700d1905011240b942c0d98252140c0110310b003845034032840144030741e4000f103540c0030044c80905071921315074060703840351481c9054407407048585c1079824041004c40090641c1210320740020814071040f07442080391262490840342444044003500186991003a007481c031199000c8080c50800c4004c3c00092808000307500c008206100d2124041100400f0138800d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 766006088 1250 766004838 766004849
    0x30906022a0c0402090a03080c07120c2c01030b06030f1006030201120213060c11040510030209160e06070303090804091e0603080307030914120301060f08130321060906 74
    0x4540e4001000204404c0e441742e00c071050342c407105883c014000724031184020003156800e03d0468103825592800f00f0ba0441d22580c0075102e600048400300101031115001003c01e802c202d000d15018851401c440e01e000006000c090a40c1c01c405d00052002e0f1002c004400703403104210222600545460a0040070300301030300080b80000c40b0885042c62a0403580251240d0412030421500c01a080c03103821640a07410040076101d504207808809072540392480b03000e0082d551201d030412541e04500610000301c80107010144204500c1c00103602d02c0e03510180c1003070041411150195205200d0070114050201e001000e0810600002d00180501c411b03030003526001c042e5485006030054070a442c600300e907000e10002c0e041450410004481c00e10917070202d01042d21030f9615041020601c03010603e041c81c0c100c54141644400001401110313041450101404c550740380545051402d4404a8261140302000500b130101c5a910352403200ca482d0100c68511503107410420038640d83d8842c11001c0e0540c1c1c85403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 766007194 1106 766006088 766006093
    0x5100b0f0f03040b010311060304030f0f0512150f0a031110030f601a041503020307081503010b03100207020307061707030906022a 58
    0x5180500e01504c9030403410740c11441c1c0002c0500c448400d10f4440d08061040000013039200350543c25a515034580721075840c0c607000d0140c3e81809440f0b40190040e80b80d10401410030007084151015010032139076888000c45600078059401c14502010304410803001101049081511008200941368a000140da4030b81d41c141000301c440500c509041310703120140040c001c0880082d9405242c0c5805050964075420001d05003524000d02c00310b0351101d83c0b03001480e43c0d85402414846c0140030030719049140031b1940d02c41d8182c9074440e0040c00b41c011030210b0403107034407803003403003581d205d40d2041c0c41d45400d946030140e134007005c107284c111200d50545d294442107000d609c05110761a002c11407400007603100c5119104060031f2100c00c0d0441c800700a11503600e680614120045030303400100500340010304202c039007000d1000e84518018001c4078078a04030640310f400590074200f46c124414005 = true := by decide +kernel

theorem cover : BRFrame.Cov 765827338 766007194 := by
  have h0 := BRFrame.cov_init 765827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 765827338 ≤ n) (h2 : n < 766007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
