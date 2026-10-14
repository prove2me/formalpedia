-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0778
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:43:52.395541+00:00
-- url     : https://prove2.me/submissions/d413ac08-2e22-41e6-9915-b69f3bcee511

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 139748201 ≤ n < 139928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 139749451 1250 139748201 139748239
    0xa0b04090e010b060c160501140706050a020f0a05030604050a060b123301090807180203190c0804060605040603080a0e121b030105010e0714180a06030614010201050402 74
    0x51035012115562009440410358581c4c024191251313000d00145010004205285d51400303081d0400c034180010018500d0414402504503552903500003004551502d4075001600a4000c408454040280c0410044255540b10010b14444c410854040c001920b0359480c0d201180c00034001d501c0d403840100400e00401c0d107260081c3da000b80c00a00d42590811720011069004c0592401441c08002e406103128200d6034046034001c0600880d80141c8469840c10310225060403006040000c1c80c0d80201c00151682080781409801c880000e406010240510034000e21001048408070f500c180340c64000f05e8075080a10921080e80d50203600c40746080c007090010303902c04500c848200d41c4850703080e6060035104000d100c9010900005280200c501420600f09803d40740705030804051070022008201815900c00d544143d0725645c2e11841c0da46403c0e0080300c00103080c401d07008076004240c10720000f0740658140d00c68403c8075406100700c0d520f440c080380124203032a81510080d5100400e00c0c420b21500403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 139750701 1250 139749451 139749461
    0xb09060304080d020d020304030f03052a07230709090f0f020f0316260a0305090102070806090601092421060e01050f01081c120b0d140c0a0b0409 64
    0x2014001040c100b84103450a001641e0006400c481704640110034401015040ba100790703620545824140300070300e009855030104032000710200b0407014160710501858024201110202500302c0d8003481e00c003c445c117942c0c2068034488140c8295105240c4001440103141c8a840c0c48070f540400e8140c024a215199805800b40300b620036680400401d541d000507540402c003407811150304040c1c0c2510a4030b0410018004080501001c010810345c40308010381c4040851400fa20690604015441d0b00c5c08000403460030070160000b2940d8401c85c01840b040000020f0500e040350000c6805018811401850000c40c501008031588114100803007402840040104000c0c140541103030072042c65041d46410003920000e84806606964a03030521a00703824603090503024088841c000d00c40314001e040342410300d06d80001c0c19810030400302c0c030b070851500c800d400900c41e2481c020182c01803a14076042c580c51b400c40322035030940144511070351401e80c0e0070301c4403805c41210200c0208038141881c080f00c1c54060a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 139751951 1250 139750701 139750703
    0xa020f04091b02010b010504050603010b070f0f060e070504020a050a03200729010303020d081f080c0301060e0907090e12070803011e050919060e0901150504060b09060304 75
    0x2080c080840e40041034442e032410044000ca503940c402d03a00b80750203400c4810041440d0b040100400007449241c40e81000c880c11141d0711240700f035854089050100024001481c014102c22500d4200010701a03141c00c1030a650242c1e1080d5981113655104010403845602008804601d040c0099901640a640301c818450000403084038000011a003800d13041e80018400c807550050070001200e94640c600480b008002e902a0801c0e43e0b50640d1800b965a8000807184010844400005150f0f2055030074004410000050342c0f6110580b5120740d180c48017482030381a4081d604c0d0400c001040074040c440b0901400d07034040901003082c105466400070380f4204a90308039900c240701401c03206401640083c0f04050080501d03507140d5040080c2c80c3e44910400c04100041c11104030306109a69401400d90b810941040b4800007203806080202d015112039406080f00214100400031001c07010341002c02421480c0980b181015140c508000495485000e540380400c000d2245c0030450904400440e007003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 139753201 1250 139751951 139751977
    0x140915010915050a0908010213150e030a030305180d0e24030c04030c080c030706210509100b0a030f0204020a2102040501080108010c0c02040b01052502010f090305060a02 75
    0x11584629289041000e01091507002a9000604c0341d485940f00140c60080d00c8071328000e40c6410342da40d51803c0c54002ca0f010310410101200c54902c0c0c9170780107000481007908081d05448601c03603a4240500282001c0301c0081114060140310b06081001040368902800b254480c00e650f1b0f640e00040c07155480059103121540ba250314585100b441200000d148290480c1010a560f14150303d071054000780d03142d00034412540920f814841c141e401207030071019140d440c60450b4041901250036000c42d60407214545840f0724000a0104030328010607091300c103000261041c0036001115060104602492001038403600ca251910300040c40e098000300000c42403860300c8011617051104d441c1900c0c00e400011210700394000b50030809560400c034068010030340c0500810a5101c20f9030701800100c000071000348220b07a5880b070880766078040c4040e501c1c003001040c2c0f01704032561442c2940340051400082a4045800c80d074003002c20a108040e02001d4070360003400303001144c40300c0803c000030b5000004520300c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 139754451 1250 139753201 139753217
    0x3190527011805010b01140a08160c12030501050a0b0403051f29040c050a0c020f03010f021201091805030d090309030b0c0715060f0e150904120201050114091501 71
    0x2c00b41c0c603091541c1c001d80504000110702c94a4400541030340e40070300c901c01c0c075002d080c03100c4620395810440140c0c0c0580c91b11285100031051080458600039014401858a607074064a0344079107515501c0703e8165001035a64a01d029190119803036240518030000f0001c2e40b011006421900c511800154020000388000c201d41d00b10303070000e1040c1640b00c60326031514100305115803080e00d400e008280201045003480380c03414203020380041080303103884e101038021072514403442c030151000d40c480808078406400854940c82600c10000004900b80300b03504040e41000c40c0005602e0a5a4290421a0f4008000c604d084e01084529020700000356040c0e050040382c10000001c1103584a8681c0301d0780541e41c6640c0e8841c0c00349406895100440c40000c809454554180060001c80d01440182e40344030b04c2c20701107580c458032822221001510070b40d070080320310424001008590007284560f50642c0d0000e10141c1c0c3ca420300030107040c4c4003c00c0380d90720045240215494007002602300148480600d0401302d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 139755701 1250 139754451 139754471
    0x70f180e0109140d0f1e110d020a1406091905010f0501060e01030c03090302030a030e0316061d0c0a120f02100503150d0b070516060c03020319052701 66
    0x401c4448040007903403840c01d1030040c0340c83c180d0300780300c4550200c40d90705000d200250040d00043c601040245c0618030040241c0000740024020105580440369400880f1034012404000030344030340e005601200c007180d11203001415040c000c200d540c8a0414030009100d8501109504200e05060001c00c1d00c0070b561b00ca0b1501c0f410116400754a020344000d844806100003444001070480d808071000004162038000c003c000658040b0868041e5000f516010419014902c4d529003144200c1c9098005085288110410005560403034042d032400015811003440c031050145485402c64007030170354420444402480208101c2d14aa46220700450442510460b142c3c08103413a01e003031015010104102100b00b000b081081c0307194040301e071001d0b240c05c50104c0003a0f40b0311100150140c00102031100200d120950060b41d1808a60b44c907401580900442c08403103009002940309a440d44045100320311000540601d501946000340390501d003040320307805004800040c1c5051002c445815540f5903280c45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 139756951 1250 139755701 139755703
    0x914060f190c0501110a080606030411010f050c1b010f0503070206011a040b070308060f03120711150417100e0316020f0d0c0f081f0507120905010c0809070f180e 71
    0x1071700d800005c0320280e94074035401c406082e01000030055071007402c04000300300024000c040503c46505003801c080382c1203003c1070016600340c0185803440380b15200c1c044c6008001c040d0820300840409080c0c03030309040c03800322000840d0701d84030403512000564010401040f440c00c90984010034101b4842842c2d013003d442d4078004441e54480482900040d902c40c040c04514070307000e1005062260b00302c0c018000d050340d06d584e65a40703020b50100580700014060040e41c1c0d0341c551100f1101c01302d0580e0711440e552515042d104016109032003030b0540c41c2c803e03004081c46c0d984140c0706952000380c0b180000c604000007000440c0e01904500412604a1282c800b040d20640360b5038410503140d842050b0450031542011005001000164090801584510052a43c80c010b590f0f036400d060071002804506556505000d03103100e40e90351048102d00c2d140c00314040c18800c041d44003600d0b1640320f0b0340719070709501d540102580d1032002d070007a01d00044040c00d081080150380701212105240a90f0040340c00000c40ca111 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 139758201 1250 139756951 139756961
    0x40f0b010b09040e0105061018030602030106020a0b0601080408030a0518010219030b090403050313080c060403090501021c0f030b0102250302090f010f090209030f010c0914060f190c0501 82
    0x2805101c440881e010880389003d0144004102011000b040b892038010700050f4401c0146c003400382404101e00e4440c40b08240c105056000c0c542200e003e45daa541d403003500035621504c0c400c056a00e8500c0c800400d030302e5032159200901440d080b001e05402d507120065400300400016000c85042e0b0f45265020301030020070b001805103c69140d04107840300b454444003805581e00c0c0c01c80c00703114200c07034001c0000003130700301050b030b5084221004240086c0600d464031848a20420300c4c0195103101d80d00401c0109617100216030144d45087c1c4c01e40d40d50071201d8030b034401045040440580458184034645011078443c0d072200703184541c1481121042d260040c604202e00515030181141d40850200034402c1d42040c0d505181c01098451840700c00e92b140184911404900740644e501c0e9540004603000d10381d80410000d28412544402001404004400640b404009108402e40d01d092003030300c9105d51038140c05490051185403002c038070f040700030a10404194110700c0180c050200c0502c0072000301d8000d1150f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 139759451 1250 139758201 139758209
    0x6020a1206140316050904033002070606050103051e060118090501090e0303070c020d1a090d0801170307120207030c060f0e0a0b09090c0d0908043803040f0b01 70
    0x202d80d020142c5803082c07500b44407200344000002044d00704200b11603141c030456140d00c642c0610701150b181036070500e1a03200743ea08003458200540f071348155038000700c102d50040c81d600e4480c503002c22090b5075440056068520483c2d44c810005119044140c1c0e2856440001e980218140f4050120034050140f84034ac9105c0d9070842100913566400602860685225030b945890f5032200450840c501001c004007030f4503817084002c0c000c50703d07840c845040083c032400110341d584112620842914182c03c17866030b2496180c802d00002420300c000007542c5007082e900281480003140145103032001c0c6071a0020b0f8102040010801c40c46074400003c0440c104074401000740c0300c940c0c0c81400c0710160b110010140005946020300c2103500031400c03c19500748000b01c41c0d1070701e000d541c203404a640b000c81e402071500528200c00540c90904000408001004005000f502c8002221030140d41420800d0318034100d4103880740c40b43d2220b150303000c0d000380c1c41a40a554041c0c494251462000c80550300d009651800383c3c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 139760701 1250 139759451 139759469
    0x10c0f1103150405010e070e01031b0504050901140c1614030405120703050d0203093d09082404020607060f0906092f040903170106020309092206020a1206 68
    0x10f000c1000020b008215200c0714000060919a0170070140f0518641c041c400181803c80b1460056001210724080c00d00509000704100400c1c50400c2049010703110302001d0200940940b40060070f09401202074450200c010350310313502d9244483d52000c3c4601e80000a0401d00c0c40f0a0000041f59135a12905c080c80c4540e20740134244032031a500e042440c2c075580c074036803005540040c45156440d4581e5101c0741740030035120f00c05034421050030814540d590848861481c6251981620441d0141c10030700c0d0b881107860200450342c002d411902c061008000c0b0400762855010801c01203800341c40d2240241907403d0160900240c4080c0f07041c1410110788150f48200c81c5070ba00c8041000500001d580c0c540102506140300089055003044c0e03099048450450136446107649200001c280b5129036030340c890340100c2d85da481100f561034040107940d1b9000400c18503c07603e2158006014503000c421000800c0c43c500c0422207410000356180b070702030740200035040700b04040c0072100402440c3c03602401005044103d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 139761951 1250 139760701 139760743
    0x10c0309050d0c02010c0b07030905061015051305010810120b2707261509010b01090608060904031101051006020c010f020604020603040302010e100209010e0906010c0f1103 76
    0x4504207060a0802541e1414045003c8814001d81d8010403451509988154158007903070750080d0550003400150302c042c160388101d008008941410b4400c3d4010f503007583e14030f4501c4020400b03044690348100b400122403511155820850f5502882065404c00640c0007000300c070701d0306c83c2569217003000e00c008244c4d0303000560b02c00d0142c0411403c00a007a01180c240307000f07440700c1c250034501d40d0b208024803030510314058024850394050041011001d40b9801c01043d94080c07640152040c1b45000705803045c010070352030074100c00603660040200108480c004d1325500f03050340d42c0604005c42c4000003407054081c40032000200754160700030310500b4850800d904262451508004009203048640461541803041100354189401c1d00020450350141e0b044034080e649039075030315040b4090300c201c2900c000103206200c0840c052400a4024003100c3d5820703698441d0103941c000030400100030a40d600360100c1c14600c3c0c5c0c5804100c028480c0e0f0005405040c159012119400100e4038040c00903003045020984a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 139763201 1250 139761951 139761953
    0x20102070309060503072c060a090905060303191b0c0909050c04060f0306091b0617060d0305120912040803040303030e0a050c090711010903081905010803040510020f010c0309 77
    0xc02c1d2040b0141c00580b400074114508118090301e41c4114038503580f404140c0403a040110341403170800c01001e480240503541c55000540010709044030f240105d100c5241441c0000d030007070800100f0b50301b0106507030748010b0390384402c4801903e58011040c801e4982e11402d207201004581d001c600c51006245200c000610f14a40303003090303410200e20015482c841c5050600c1004110341c1d441101e02a83d40210f00052910482c0c034040d55484c00c0e0b076129030541e442082c80045c03856000b00c1050026540030f0089403065560798208500d03083c1604000703001c540305100f0f8100c0600407910b030690140481c000c90b8101413090320030852540265000000d5039100080c14001c045d8180203000d40140110024070281016a4400c0c0d01ca0071a020f019009542c07440c001403400344550345e00071920600b072001704445d6056040c02400c0c05403c89001102e49078690400241009034840c4904a45128000d5810181045e04010200701c440e004502184503000e01070000c00020f1107506444103194800160b00525 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 139764451 1250 139763201 139763207
    0x15022809051c0311010c02030d0f14011203090b0a0906030911040509031308010605030601050d080d0207050a02040507050a081b07150e0705060a17040f0b0f07080a060302010504030204020304140303070201020703 93
    0x780c4c003144030003641400072030046640c001090700c0441e0300d481c0010841c1803016108000400135124a50a0354030414000502042c0340841141128060358541c9606501e40c00c88000504c500480c10380058403803102007001511030341c410318610344a00c0031802c2400016000500b40d41007990680c1c40d0f5080020040380030b44080c000c620042400344001e01c00c40d450180003a8480c10144501c501813180d10400d9420840c4c01001c5030300701d07410688110b4803000541003141d2340315508501203009a16040104400c18040c9058448001169030dc0c0619a50b60345940a05c09401e5040100d455109006403000600c03c1c2801c100c6046808800042004401c40d041c2e14105142d071225000310020004c1030315840e40070300080b10017641c0764030100742e0342c840d45404020510032200141c10816440188040c00c200385550a018501c90390b0303a0300007030301d81000e200300f02c0d0121300c40203000c50020003041005090980180d9070003070203958916690b43c04140350905603441103070a480141d50010f0640c0400d50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 139765701 1250 139764451 139764467
    0x5061f060e0a1503091205220506030a0903110a03080f0a0603030f050c0a1e0218070c02040f09050f0601150f140715060f0315022809051c03 62
    0x18078008074402200c40110b900a841802142800100394280c1c0d034200d8000d4001580c030690020401445590090000b0010317000b10308113840c03402c130301000e2100d41668101d22100f0703248020b086e0b91458460142c0400202002d0780f00300c00340710746482d5080d44040c0a120320011240207450303a40300c9280458041c2246d010080c808011149442410700c0401e50000d0003403c0c502903810140d036288104101070b4945000b03e00010b00030000c00182c41c400664414061a0491081d43c01c541c9a030b00320702c16806101000c954103030005a18041140140c5419041074107071030b04100c00050480648d03207d00d410181c008122103500da1006d0b004000c810485410102d01c5009480c040e80c032022000300080007030a170401c5880604001044541c00d000c5400c481030f03021140e0740340400c4042d5503503081c2c40f0207194901c02500c20b2104608000298450303402222180d01c00045402c1d0181c250701032162013507035005104000c03c544510080b940d40c4802c0e26074114081203061061140100c1d25000741040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 139766951 1250 139765701 139765709
    0x3080901020a020d14040510030605031b030607140714281112031908060f0102122b0507020c100309050703080319022a0a0f0602031305061f 62
    0xe841001401e09007503002c280840702c002280f038185038883c41000001310500542d00010342c84980d54125018848d0035510442c01c903071007a81602d614a05104e40c40038001201002c0c260150400c100042420340720b030310681c14030040211014104409070310380c0d01041880503180c030302541c0a200c54807601119498100101280c6c0105c03d00c08414540d2070b440341007240860180035074142160148071400030300640700c0c0784644640c00d50311044039020051001c0c1055440e11b0084036150404c503180c0d4400306804a40c85400014140b034544200240c44e01601516210051441c07445e1400045803060f004081c014810f543c002c160440d440404c0144080140c0761a905140c0740400c00000035502281000c110b0340c00c685541c0d01ca95440032070800c504000010448000d200140076842102682141002041440002c01c1c000c1c1c400d0810680c2c81000710b4000c0c2c443c4a8a41210b000208160029035011844001c0c86000305040c0e03a030540342010036140c61842c020954040a545000002004018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 139768201 1250 139766951 139766953
    0x403050c04111602010c06020c030706050402090c0a1407020a080f01020d2a080a0b280902031b0c01090606170c0103020313260415020c030610050d020121020403030809 74
    0x400799501ca20310315920f03140003814010340083d50000d00c4210b03419901c96114510549545141c2460404010081200d00301e10401c843c03404203048107140001d88100351034176141c43d00c0074410041203d5540c3c1000c00704a0f44213104400100d8280018882107201030540000562255201b01c6a5001e480c04d039000c0140000e08406045910480407980003c03040150a00c5441501c2e00101c60300038010800025810040a0880100b41400715402d9030f4220920a41c02100a4a0719030b82000c0e03100598070011004915070403c1034000324040240303032034020720000007a08800c40c0da402d401d54185c0e0b403080d2018000c0000c4000701c03503400c0c44000190750091804510314039054640300304a0381288c0d0701804900546c4000807418503110202400f0184032041703940c650f540c0e030300c0c070101344001001c10038018000c481d000780040c140011018040d881021120500c43c0c10301040c0031b50410000d0040e81044502c4a071860641c1c40106a060907442241e00503030344505600f0058022107014001c801c0d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 139769451 1250 139768201 139768207
    0x3101401090302011b050f15060d0302121309051503010b01090320060d06031b0905010302210c09011e050603060a1e03150f110a140a05040b0403050c0411 68
    0x980c0c1c0900c07803905403503090a0941030f00c3c401c2c40c00440b04243d1920001c00c1445020300000b00c074100061120b003901c0790340320356951503501c0754144181c01801010050240e030000520b42042c0b44868060510103103888000c0100d16520707d03011064940c155566903104010101014030342c18280503800ca0203200382050130300e41c1e00e15a912007240400010b15401d03001e205003079814560b10101101c03400d1420308070600080d5140e0512245041c036050000440040c10701002926403414064241220b400800302c40c10f490703689401e5020880d51f040c1c05122802180e22140030741c1e94901c4120701800310240d9030300028440103102e40c070240c0710303800040c801c100500c00c20450b9554103413440d0544415151990b0703031900c0b00341c1080380341b9080d810060400510141c0841d6039405a0300c0b04030b44404140c41441520f001000f2007280344601c00d40c9500007119100c050201d2510b0030000d01400c000351401c0c602d0940d9803214400f00760032681049503150806404104945481e00551250509413408549 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 139770701 1250 139769451 139769489
    0x1020304170a03090203121b21030a060e040b010905012102060f070c0b0d0f0204060f08060102070f080601080606060c0307170d0e010f0c0807020a0b040c030c0303050310 75
    0x300d003503540c50030540c1d00800062440210b0740b103a002403422a50250499403408000345d0000100d82011004640072040b01a5200c070700b20300066078004901d41542c070341580f202c05e0031441c11203a00040c40090499190f0b003001503101c480718162840389010b01400c03001c65040100c40420b1b41c0c0d0691022003410b000b00040503800c0510072001d141507904640007990780140c08000d0131503000e40a409042d04001c0000011012170001c01070281c42c1c10050100036010140c00b0350f02c03c03030245000d80320000310603d440031109800703000c5036500400e05004486181e540d402e081060340d11981c0101c04a41c120200401104004208098014004807403250030241d1000c00d15603a8003900d40d024202a100c1c80c2d0103030355070ba10003045550507030a501c0144140c0760f410070b034a400303806e5809056a034245400d2076080c03035078031817107019000e00c21a03406003804218645500c5525032010304140d8201c034010318000000303500205c5050080d440780e1502505e901c0c010401a0001007190310484241500d10329000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 139771951 1250 139770701 139770713
    0x40e0f06040f270c030501050f070306080106060e0904050109020301110d0f0b0f0d080408010c0c1103010506090a0e0f010c0e0315010b0316031503030201060f050a050a030303020a02190b0403080901020304 90
    0xb83e44411500061000d07005800e00b442d0070300c034590020b0100d500c0c01c4180700416600094491141c2d1a0782c4041c4410b56a5810340340c200d803580e1141c100095180656020245050002c154220303020303c001007200b42182d000030742108d10b11000b41c4c4040800007072041405006000f5a904001d01c03620400080891101003a0800c0c0507a0200d845040b00000c0c0d43e0800203004240e40246c0080d10080103034003e18600500503d13001f04050b1404210500c4c0e4009500e01406030318811100039012209980b294078920026103c0c0d130408410034011080710241e040030134483d420110095607502a40290301c0000c0c5030410343c21441241694003500700501a0040d0741e41281e422665a40880030102d0850008a0007059130749501c00740740c00e1201c000028140c0c1504604140c5443c2d9202c03002d00f5903074a0403c01403030214800d10342c0107c600748080000c24003030341c06072401084030300542c3c1c0c090074048000b0010018545044030040d810300280024194003000c20380d40640900001c51030f5040903200c0c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 139773201 1250 139771951 139771991
    0x6070c06080c04090501060909050903092209080d15051215060406181505010302070213020717070501020a090e0402030303060d030207090204230301020a080c0906040e0f06040f 78
    0x302041c420000c011403001d41408080fa80100164a010000d658582100611035540340c45a810718905180102d0003451011084070a0514000d11400501140b04004a049186623606c030340b0103a601c00348800401c206000400c0c820303010b4240000da03003825110105110125800460107581d11030202c1203000130000325050110a644080c9030569114400500a0a05d5420030708400c1c00d0752038945d100c0d00c0a50004114a2513400c0f050440c00c0d1900e00441c101d0080c103001a500401e0903034074400452080d4014130003180101c1401c0b580301c1104da0390031400d5208800495036a0350002c0d01c00700447e030001c6103101405544115003618101500060760b05d0201401d00c0348582c158944d8141094006c00081c001481501825916659112656114054810001c00b03121f00c1d50b41400c0e0451406100700c41c540304203601c0f41901a00c80300c1f000421500328103092070300070008202c00b00d44c000a200406100e08041c0c01d0882c66407404c031040c442541c0007460f402c88054200004400c00d03411820385 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 139774451 1250 139773201 139773209
    0xd020d0e0d02071d09031309050402040b01030507020703030c050c03010603150501230603070e0316080f060403020604200a0f032f1c02120a020109150509040203090a0605090102040501030b06070c 86
    0x1c0d032601a1900610315044d071003032240c1c030207c03508006000242072001d0382160b4825030003200c08001015100d401501130301c00840d1440d0060300151018400203005241c2561203074002d2040324a1101c142c0c002c01c0c2190800e0700240c40e840c2e40320400e8584105c003400303018090003001c12040305048991102c0050444000030141c40391101200085045e03100705900c900030b15000702110f000440790382e403003c50f0001600031841c5502818042610904001810380c0c051344d49580100031540d5292510088080700021408180c401c016284082d9640c102015019100e0134a5940710b0603c3c0d440c20316201200e0070600004c0034800548401020034401420030303200000d54000f50144644490a03050500804009500120105004440b1030300042e000300c5c240d10030380391070340c4040d280d844240303c43c040810b0300c8002490410000c013103400c040d00550b42200321202180c0c4003110a0b525042500c104440320306160f135010404022039030345805054081c04068402c1e52900589440da02006441802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 139775701 1250 139774451 139774499
    0x6122307120f02040606080603100b060a03180f0b0f090c13021c060b070209070212092e0201050a110408101107020303030403020a15060e0402010f03020d020d0e0d0207 74
    0x5500a104a61200b500c5141d40107008024041d291301010300700c18415142c05000384101452035007540906d10802e46510001050942400c55000d0110003806400c151005450f84150054000501c2241c1e80c55200b07106100780c00c00c92502004581c10181c000f013075450250b002220801194440e1000108010303102c0501580c5d81c40103800c4004e022401c42c0310b0180e100d103840b8000a50314420005842c495108603143c242d140c1300c018007260303a4000244032000d00c00040040f001c0d14a0180081110f44040e280620000c202251912003420b00b800d07440c10150351202c0c2081040002c0c0d101d400d0a004485001c02e040a04041640b6502c2c984402d9088586580d40741003a1003e00f0481501d1030903134001c003165540d19051500079251000701c10201c1c0c1420350705d01c000126034000d004400513030310640d43c0300e03140f695141c004582c1e666590000505250703080284a900c0038280c0018181100725000204110140014071407922000307280440c110b4200311405d0000000100c0f40d080c80b551824 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 139776951 1250 139775701 139775729
    0x10060e101b030e10091a0705100504060905010b0a0f030b0907170a15050402090402040b0411180f0d051903090f030c061704020102060c13030606122307 67
    0x450507252290580071000140245200d90420540d2010107914181c1c0282da8250b0b00281261003030b9008a264090040d00705c0884100707000c0030311400003030240e80e4012400c4801c01d0411004c201c040b42e01c2960140c490703d840300a0a420701000b4010212010310075170740c2400036858450034805c055001d020003440c0000080114440d00c10401848003c1c0010741e2004c0b92000d10054234503034a180c0c44070119451040b00d041d401c3d0300e800d00d1040c64819600a01010720a9646508200c0100400c0342d003654050740d1410003040c1d43d0000c2d00031b00428040c3c0d950340140c481da05810070130140e019440541c4541d881d200c1e0740700029008903200380501c0203280c0c00c0d103545519140c10b0380c8485090f04001d440071800c102c00020b002c81070341d80700300b11100340d103c0041c030100380c4001140101044030061f000d6800440418441c0702808000c00a503024040c0b50075050b500c9540f1017042ea51958010b44840d200c0294500502104003d035039601d0100b00703031400341a11402c207916201d0a840c811011404408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 139778201 1250 139776951 139776979
    0x50c03070812070f0b1003050d02010e0a030f1709060105150c03090f01020304090f0203070e0d020a05090613020c030304120503090703030804021203031602120a12021312050307030810060e 83
    0x40d4000c9442c143e0b011300c0343c40c1d4502d002806e05d41180300070300c015901449881d038046862030040c864481031684200c054584c902860300e096580d200802c20410801582281120140702511601801000804081d0159500d00750030001e00402d00c01c00c8000c0d01c1030403c0362080c01000082115038221040d00e44a81d45902500144c3c190301596021400150908010f10003045960740214460651501e8504034000e054090007140310341c21030000c1d001400700c4410710241c90001d05c56a441100100300381607032070260810600ba604220402c004c15807002c03050204025902032210501c0b02ca9103403a03400e518103080d050b03644900a1202600344084070700403030700b90f460f0100c030301e41c2500c00b900840e80c0c1c81c14012904488580c01c6400ca00060040b03040083d2404200c44c00c84204080307a0340c4d1001c030841250060300c0254881c4180c0c03100d451103401d00150604801c1c0100040a010300003854403400c09050103021a413005100c08000034030300e9401c0c0899a04140611813003c0182d965000c0b500c41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 139779451 1250 139778201 139778213
    0x30f0a0b060304060207020a17030d0b0406080f0309041d030301090504030c0204140f0610170a0b03060f01060305130b0118060302210f06131b0b0a0309050c0307081207 74
    0x100c0e8180e0001d100100b0003007800120340041003098420344420503255505c0e040140c030401c0c0041041c84581040011491210198102d4111480000d000041e00c07a5500241450300303005150340a035580000c950614149050710403000308556541c902d01d04e28040828981d200e100500600d20101e07583c001103424140704031000390340181d001d03104020b014001c0802e9503d10b801103c80c0c00c1444001780000303000741440b0030130707480c485000e4561040001004210200c0060014880d001080c0d50340103849541c0e4080200c11301416122054003015410030a00806035035008040f0500c407460107030b0420004121001d060304507840750307078100086d02c00001c010000c0c084640c00a540003040b00319005520051502c11010700c0301ca2012512610010900385484103004c844096205800c84c030b0003000700e42007001e01070f4912007100320300100982b9590b1026103504401200c1c0c0000750313105900810450100001100c1020841c0201400c6c2e2501d0b11781551608044400f0ba03036464041400300420030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 139780701 1250 139779451 139779461
    0x21f09170d09020612010e070309030f030c020309041406120c0306070c061805030c0c0f031b0a030c060306050a06020a020904020402131a03040b01060906020312040c170f071a030f0a 80
    0x83d00501c0c65a403100740c1400712500580c203000e4101c95008941c0800c904500134402d62480b940e164850034004044040240c008000704140c01c01980401c003c54070665940d442848109100084400d90500340f0b1028003800e01c00000030060300364400c070b44100056030300040b207a034082802d1501040c0002035141030f0008d04a58084c3c0184203070b0340500c0c401002408009000960a030008039800803500078200301001c1f40390b8072201d415801c50004605612a03034103640018074400307025082c9203a030300e54545014034011785c840ca0000743e03900c0c410320913440c25070054801811b091005004510068000034925400648000d20503030303001810f050029140b0900400034524580c42e010120000001800e280c0c1c0125070403540c4858500010031400d0140005106552245e40150709101801c850711071901c5000c0c005560192916800280c598030362601c141d1348982c15806007003002c041c0f000040c0340511b1a041522a405a824a03032659402c40301640d038407200500340c0816584801c102030000304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 139781951 1250 139780701 139780703
    0xb040605030f0106030308060a030f02040e01020c0d0c1101090602060a0e0c030a150609020a0816030b0d24181b120c03050d022802010e060406021f09170d09 69
    0x2c012900d501c4405001035110b4030460740242c54540c0c0a503600c004210100205000003414100d030156581d026082c00e90015003020250b40c001031400040e0114180360066102c811000100451f071000c0c100710b1244060740300c02000782049060b8500b003e40186d2160340c010f08041b5010355607042c803d0119010440048004000340030b0700c0c5243c0300c80c1004410120368800d50255241080000903501c0894821a804c414041d070703e50780385445184101005030a4880c0a200301511420007061542c1c40b42d0380045c81d9031040400600c00400e485039200118207190000540910300030540c40a4107000d030f40e00c894260300075050f40301d09404081100b00035825411000345811700d4000c05081100b001050302c240d81c054401c0f1541504103950890f03032141a840d4610300400d85a14030031003480c100c0c0c03e240d207592050414019240d07203000401c4c55a00039500400059006598218006041140c41805950b580c4401e000d40f9229440f01c0f90445942c0403600803080002a030301800d0604c642c4088021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 139783201 1250 139781951 139781953
    0x204050405100c0203120c04050307120f0602040b0304020f03010c14070f1502040302131112182e060e0601050c1f06030614100b0a05040812040e070206040804090b04060503 76
    0x3e030604000295a5081405544180c100c4000400c12800d0030800355011a440180180560750901e0154070804c400e1040032504810080140c01c0003a6560018102078499040125241d01d403500410107036240e800e081c0e9010742d15140304c041650790f001042e040130070030300d0300390950b11f40c20352070030b4500c07500f4081014101c961048222038029103684c00400841c0e0080f0f50340d140c0003550340244000c41e140444200c0054070200018118241d03071000d010f501001031018514202c400004181c1004590380c040303500311b141401d0400611030014065801201002c2003008054140340e065054032101034855814000f0106002e451540101f041c000c1c000702400051188980556004000e4202800221001400c055100c2c015080b2503450303921031408682e480070428541101c25500f580400441d07420480c04100115014804000711842092000801c6550b1380c50203007446c150f240c000c2d16020464100700240404036940c00305940c1580c40c1c1c0c070400904164101c00140041c00301754052501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 139784451 1250 139783201 139783211
    0x50c06040605010e09070b09010f031805060403081b0313080405150a02060c0307020d11070515070203060a090206300403020102030709050a1505091512010f05090f0103020405040510 80
    0x20407566411a9040718203c032101075040c3c41c1d50304480e803110340a00a14425402c00e1040311155031041c40052590103d034100002c1002440d0b009500010410718290b4807035000e123042c4010103600c03a0505034007981c280c45085145c60324600c0301b4107911000d000c00d54a80714401111082c001803d00312030051000500440c0480d403900c00303407540c94000f0320085015029050028046040c0c240890303119400303942c007134540c01400d80c0d410703a090501903400300c445110302640403625403540422124401c0d81c20044984906191040601c0d0640042a0000507810f00c0c40340300040c3c5440e820b44d5540c17a0302110340c0c02c001000040680701c46080920206014050400340014113406500131809000c0c5540c401808503152802d004003035010f0b1041c44501c02c4940c0c245003606100e04041d200b40d072002081400c0103010080d86c0d4516400c400c8031141d01003040c1d40100808400da001081c000c0905844114003031500c0d48411080320414030010703004070f8440d000141045402c2c4103c4204201038407007081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 139785701 1250 139784451 139784453
    0x6060509190b030304050f0913060f0b03070b040b0313060f0c030902100e030d030c090f032d0b010b0c03091f030605010207080a060b150a08041a040203100b01050c0604 74
    0x281c1d41044480801c5624a050580308050070040115415541e002d003d800d0651081402d0004907440145502c0050100302c04a01c00034010b8000c140d0321000344803011441ca000c0408050414070342e94010b25402404100801512a40c0000d4039807080001d02a864100075030708044c030180800000c81200249440300301d8046641591204221600a403a042c04002580f602529103103400c800e1594540e100303005c2c1c002054441c0d005820303040d150780380c82048141c1e2000d1207801380c1c000b5001104ca800311014543c90480714000000b500a500036000a444002e6171900c507400d440600031201c10400015100e229501c04004944a441003c2c103610400c241061029811f03504980740200002e0904800003281c3d031001070750704181c500302400b03400300030150781e56100100340d0b558640b0b03002402c590008031141c1e05a4090b042d090b00c00e464200c4585490300d05501d4070644201e80b840d0098100b0705200140c1c40000311680c114022a900150b840021380041c1d800303008046c82ea101c6481b0b0601000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 139786951 1250 139785701 139785721
    0x801140d08070f0b040b01090c0c06021b060c09091e1302010e060307120b030d0212030411060409020a0e01050f09012304030804080d02060910110405184006060509 72
    0x4d486a070180018880c1039032184428410703101e28092050024012246440205080d0350081042016010119014540b22041d01e41484030071a203028414001040c0c1a80368181028900c2c2c0c003907480d4a0300e200c4461210180f40c5d41c200b0142c0036403032802c1c140c0d51200441e40502030810135004000c00700754582c40c05460041c10a80d11052100c0ac0b0f07410306000c00d1a9060008640c00603892940203045403004204050105800c0100241d40d40c44408440c804a508c1d101c0042c8054803c482003d0780d68804103a0161030010061213107410004108103898142c1240d1090b075448590901c0c1c407160f00d6501842c4420142241c110303d0304001800540007080102400041084580300401c1e10210502e82d10280e0720703000220381002083d00102c1c400c0c1c10244980c2c3c00109800c50101e6a80c0c123042d1607201240d0aa00c41e108407024000d42c0005102580080c805015800c01c4510083c09042d08161644002c01240c00e0903120030344003130310001d0200b0490760000405000702608802c0c0c2440e100c0803071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 139788201 1250 139786951 139786973
    0x1021312050d0e130b0f041b03050f0f06090702010605060c100f141f080a031106090a020604061803060c0806150405150c0a05010c1d010801140d08070f 67
    0x111042d12928401e81c440b5406240d00c0780f8111001400201c0101c0700b505144c0203400014080c59200203034100c007414070f0751544620b010003c1c1d80c200075140034003185c80150854801902000041d21400e04021814880150840d1b000e44155201980c907103070180c003640503004903080554001000300d00d20070500e200040150a220070380a05221840103125048110703041d04002c1c2d0000b030325801c002180040c0c04569480400840e140001039070b0b41e00c0c00315a090444c00380040b0002090440c0c0413403a01000c01c6215004280c81c4090b080c1c02115a0001d01d2920442c41072030140410f0214442d04031400807a5000256080305060003103408001b4010b0540500b150054801d19201e50020a0710340d080058406550000d0f00f040d89119808070314038800c0d088000e00d1481489400017280016500303004001261402d5140c2d421500e0194500896514401c025941080320f034000400c8030b04110a00c40728485000c0e141c5452070b11850410303c141d449a904098680c524816602c1d0422040c2880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 139789451 1250 139788201 139788203
    0x901031b0e01120f030c0506070c060c03050f0609070224040627080d02160c0e06040b0a090b06090907080f0a0209090417090301090303020c060604060609140301021312 74
    0x40031200030303200c0e4039181d2514020f0051100340d94222648200151600030581c40075802414003441807032850b0f90322894548112641400107044007104002c01080b801100b0b848185400c0a01807460440d28060242d000100301c5071141d11400041900d440c024002000201c00d17541617442c1000d8203c01001c0290020b83d02221142e02d044003800980c03943e1005104803074174102908640414907140c001807504102294028941d01704424201c0078084481011994411581c2009251414141002401004203510700480c01c0c08281c0d08141d40d12252a801d0b07a020800000300441000d003c584a40a0381590b82e410404035010702c4481da800103105841161170701c40482d400d6451a40e00f10590103201501904001e003400450300113003c1061407a44015030081e40b0b814406544006801d50380d0600082e000300380c0c00504814500014001c0c00c2e40410705540a000b405d240a4005001005a10541c03001070031200b00c0c6400e9990a40464002d601c0102807500394548408140624a000b048 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 139790701 1250 139789451 139789493
    0x50402030f0106030203060109020304060b04020a020a0b1b0906070c0909030203032a030123040f0e010605040501050609060d0f0615110a050303010909060b04020309160b0f03060d0201020a02090103 87
    0x1d01a0014001d040030f0301d5024015000e41e920b03281c2c0701e9010f034001074011181151282d82c12165900e0b07610140890781d00c154000d040b500c5250504000300c50018080e1518003044001e80709542410804460602c401941e180d41d039040b441c100030300608440c0e081006480e042026000c141580080518010440c00840c802e0100c074552254541420500d20400c403032500348010851780201d2188601403501441404510422120000d0100d8009000600741555078500803e01b0b44000d100701800380c40306039802c0065505260004260b070140d00c0030980704100004040340b00c1d0b240d941241383c0100e941082445040e0702c44d50502c5000604419900c0040e282d074904040c0040d000a041c951203810201a611f90b90909440c0c0015040080d003c1e10301c0c640b1100380090540f03681c03009520400c00300c0701908403161030002ca84003000c0c2d1580194015031091007076030b42400701c502c110f0380c01c51001c690342c4d6603024040c40140d050082e145006135102810790000000c0c00004c80441136a03c1000d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 139791951 1250 139790701 139790713
    0x15071a04140304060c03050705010e060f01080106050307031e050a0f1101030e03030f01360b01020c0a03030f05070212100b030f071d040f1202010209010906050901080712180605040203 81
    0x715050341c82c02644034507800034500324840c0f0301103405040204a02c0b4061400071420034050040c00c1e1500f80305482420016000702c1c01003026071028441c400140c501180540b2a651854561440010906086410000c1c08280d0041004820001c0520f1590303c8540c04010a01d50304050f08041400107855000c80e0a121118a8a60002c01240c3c8a68820481610340c0e9090040c0308421000d001031480c8441240003044692a160802c110107854010001007042c4480500083c2040e00081e101c40c040d501906050000070303000521040c5c011464901700ea1a0049400050044d2a1100c1c4030010b81c05643e0b141c40c18000150030440007250140c00301c8464010070410107a4a00561081c0185543c0c641103e01c1d901c498842341e103401a0141010ba0b0b01038002d501c94081e24a500489080582e40c00a2103400070b580040085000301058140682400d40d04400a0401100144100100083d10000a6044105621918800800008010030000c41e46400401400190350980c4070340700384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 139793201 1250 139791951 139791983
    0x10e010f080f0a060b121f06080411060f04090e16180f0209090f070f02010603080409020a020f010c0e090114031906141509070809030915071a04 64
    0x24000c0c20400102a9616012903079a04208090090003410502c4500e8407501c00142000740400070b04120205144040500d003400d01403900c07400308210300746118000e9034408000c2d40d074120704119485500004031603412041c04000444502c0ba4800c0e40b8002c11011a000c118508030b940300c446028030080c02c44d0b051111106400d50b4009031441000341c66845c10046038803a0006030401044445410400350070291281c1c00681610400c9407000e01010000f010086d1490b4041e54030181c420b02030000b00001800e42e202e1460364401c1707000703001c20145c00003032441110348208802d40c140400c08000b0410b00031040c50040124504ca40f50710320038000b203030000c6420900307121079005280c401002012110079035865000f58201440041d52a1139441741902001141a05002e22a9841c003c040c01d402408200300070131740b0009011501040b50380d00412010050020481e003e01c08200e07841c01c01000c901c8030b000854400d001c0028055414902c0d001c08120029100794021407041104402c06449 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 139794451 1250 139793201 139793207
    0x302180123061905120a090201080112050303131b030c090c110a061104170718020c0a020f030f0f06090f0610030219050301091209290a02070e15010e01 67
    0x14039550a80d1150701004200041d800f1035a40d650652150b060182c10800f540201031401da800f10740750b43c241621b980e81d60045692024000e0b001d00303910482c000040307645480300313640c1e800700500d00361035010219003802c203001d03c1120510465510020006042d510f03032038174504801c90ba1081ea06400c0c2000710210000340030340c1c01c01c800141030400420482e220b42c0c0700c040117880c03002e890340460a02000049a0043c0b210042c401c2c0c1c02e0602c0c010b000e801d140130740f855511068071605070819407050040403c0300c50007040c9940281e80440d041c0c103060420324002400c10122442140c3e4610966681070115100820303021b100d074203210240c4024552400c03819456a03002c913040c44400541c0101800149001d44000080b0382107018410303002500c69011900710341444000703441d641056000c40c0b00a40d480790344540139048610800a407000c000a0341c100015142041c000e001801150301e01c0c1240c1b0802c0640010b0629800c072042038100030788485840221500414001211030b84294000c0d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 139795701 1250 139794451 139794509
    0x60d06030c060212030f060105040f090b1008040f0209060102100911090c04060801060815040203130204110f070201142104060522020103020a0c0c140906040e151003021801 76
    0xc4c00f2012441c2d5a100c501800c40c600c00100241e040c03000500c0301140c1032000d00c401202820412400048551000041080001e20880a0700401c0080e20820000a4404104140065050314107281940315080180c1c01d208805c10110b041034a07044061050181c101111140343d902611480425280c14035128400d11543c0107030004100120010400386108004585c2e02000004860807644020740004040c0d9005881d14162000c481903000150300d80382c400c0c3c603500048003000034501441001d40761401d0242401c003030b0502a01210720003441c002c0030111001114450024224810b4440000704022030540f01503510500d801c0020f5a440311880f50002404004291581030051550044002e0746c00f02d0a800208520046624000b543d00c61400010344902009110002c1105041c002a80b90040100c0d2140e0300f80244451101d030003140c1e00c0c02000d840c43c2d0502c5955540c480e44069520b03d0b034030082d0000c032288080c1d000b20022010b182d05075030507806010005c800c81817103140181 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 139796951 1250 139795701 139795723
    0x7030f05280b03030910022415010e030606040f0e100504150207030804320304090b0d080409090512070503090103060905091f0f020c0a05010e120d0504020a05060d06030c0602 77
    0x1e84204000c803000e1a0130341d02807005c0c3c2861f104541e00c0030449200700140031130020843c80011101010701075107402120b20001a85000e20700800e48013401d600003a070750b0783d025028a00903540c0302d19800c802c05003500a0415281007c0403120031032060f00c03039079005010444058840440d60781440c40382c0703103070ba0080720070301501584c50035144c0d115512460040c0050f100e2100404002105070b00c3c0c558440300d118030f00726807050702a40e19249803404013401c0c0c644090070603101e24400c0c28040f0008807080142c50594107030603800034080c691850464603120100001e401d00c040045111410080000010700d01d004003a60248802c594070702150050355030649070180503070010010300b0131305d42c0010240c41451510301000304590100c41c92810490f4041100e045031071f00501139160502400340500000e2800702d40c01420402c0b4504100311260007003007140070407544c50f00042411366441e2039100c0c018020041c66240d944010303200d048010411440121059025480009015400421062401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 139798201 1250 139796951 139796953
    0x603010b0901082107020910030b09070b041e030b100303120b010e0f010318050f0d051207050a0c0c0b031608060f010c14060910060e010302060f0307030f05280b03 72
    0x50f40213000311000c444500300780401481014001c000250703681c0c800d01ea000b251940c125155040c00d5003000c040d08680100445104d91001c4001c203c2010110126411602040e051900c540c985e118840d0003034200303a001038000c500a07000d0140301000b6200e0001100d00c03d40713031040104036111a050a031004540c0160100c2c05604080c000742c10800d0300c0540d80c240516002410407881080030042441c0d035101518680e00c500c210742d000c0c0f88100243d103859511800c0850603e03040d5504460408402003041c0108034000c10010041400b03041c00460056020119214460303d5003400d10294000b101c0705000e14185454000003907000c0d069050041d0030180191594042500056030b1105020030112034203112180050000e4609100e0103002e46a0000503103040e049280780b81c02981d60980080c3c0c80200a0401040142d0741c0500303c90708a000805e40300e440780e89100c82a4010410700201580440c2400100705a030300400044140203240001000581c000031902c0608540702c841642e901 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 139799451 1250 139798201 139798213
    0xa050f0f100c0f050703031d0705150c2d01020406050703121a0409020f030105010e1f12021e030a0c0501020f0303060d08030405030409110a030b0102150406020c07051203030603010b090108 83
    0x5443c2c07040c001040000e00030b04010484e03914a03071003900110761740d900d0801708d500840c4040c0310034030b0400c000c0900b20745091740a90510601710078082c0c503000c0c1481d80c80800c0c4162030701c5c80b20348103601852680094086008540312aa910750190040c1d000107411000030f00700004482c0e00c40d505105201079a600000c081110032011402d0000500300c200050740d01043d501e55004041d9000d016460107002c040c0d040700000e090420382481e2907000c0350b0043d20a0030144105200c0a15504203a1a04c00d4048070141c0e0710069070703a1900503080703100c1e45c02071b058060b090b2500248180c201d5198200c580c00e0b400c84c1d02c0706540e0744200361a40402d40f0701e00d40c4503410804101c0400c040c48055a08580181c1c241d910f40795980c409502124158601c2801070400403a0303d06915416115a425610f020700107411002c0f11720000e00ea0000780184000c1020398007042c10200360030f04222000103048040c040b48481c1c842526116540c3c0c1044980900c80d6003007141603600ca0038004901412624188002c00b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 139800701 1250 139799451 139799477
    0x40510050f0f06030103110103150602030a0c14010c09030b0a0c0203030a02090402270f09040b0403032004120501050705190c110619080702010e0c040506030a050f0f100c 75
    0x301c0103540000300740c1c4200100100c426980c0c8030002140218860000c428a030307504003001605a402070900f08400c660306030800c0040e55004421a00c5580d001d18000b6000d81440c0340100c0040d0390030039034800d158a03004090f41c0c8241c0000010040e139000d1001d800c0302c0e5854030940000d8a4103046880c1c010b81052011500610302d540140121000007003000d4100302c5c504515001e100400b42c40c081d104800194a02c070281070000d50751306040020b680303451943c649074030b41c8400c07000b0192008041650321010310341c03c620310050320b40011a0420307486035184e5803070b4980c00c107400c001030003525154a4a000314500901440c121500d00c1d020301442c0c885500040400d03280248916819103c102081c902c11f181c9507640801071580c0061140081c6034000d40c510001e041c50350042c524400d680c0342a0385001490000104039440c09001c4502043c2e0b07507100400319040a18103003004010784a6004414510003001c1004000680780c1011214000058441d1105841c1e0000c20400443c551402c904 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 139801951 1250 139800701 139800709
    0x41805100609030b10030519120302030408030f0411060f0c0705030714090c04080706030c0e09010501050d09020103090b0405010501032001091502031b0708190206030c0a140a02010506010e04051005 87
    0x40d034000a07083c1d240449030746d85e0300d865003001e40118111076002d610001d24800c01c10f503440f00038280c0000d49030460035440c1c00c2e0341c0d64005110240076414800490070014082001c1006090010389002d00780d5621080740040d01e80254004401002e110b000c0d0304001308581c100041c0c02e40c00c45203c42c038001550840c0600348034090001401c00640f80b40c0400c000700300038000308072190061409540000b1a0b20301e08600821800c0e125100f0741c031600e060001001aa80c1c080240c850107080803900140c101a9480141c00030320b00303a58014842c3c0866010401401010760005040300d0080c504914265001807050200c02071b0911480e02103850320340140441122012101c1d58000540102d9240100314140c8641d249540203c103245ca5000b44000d00c8828000e11000d038050218226485010519034000390040c00020084122103e020a0070b1510510908202c903031000c8111b17065603101e102c041c00a002e0b107403c42d201804034103191517040c1b05080c503101c0c80e4803e40003411984d0105051401304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 139803201 1250 139801951 139801973
    0xa050a060e030c01050c040e0717070f11250e070206040b041106070b01090b01030605061606021c0c090e1909081306030609060510080408091504180510060903 70
    0xc1041c034032051000360f002040c2403003214015044911000e803a80c0c9001102c4205440c010194400c2000e1038036803521030782460180c1c80c2c221189086c00b110f4890820700490307040b21040d44c206030900c03a0325040721051a814218103c80c813401c081046107079440c1e004000e00702e04180c42c200010b900850010f404210b403000d4003504035204403500c403403044800f40054180e800221081d5843c483c01001000010103a11800110700c1080c00d003031000c145000300007490741c02040b1004190002c11200a41081050341c102e0f07140b524402d5a0f0780c06d40140040d41c0004240e01d10004c00420800b01d0003103544082c1d80c2c641c5101d076088202d000c0c000c2145881d2140079240080d822941c0b00414003107442219030030410700340544215940012204e15000c005015650315074040f50281003d1440700141e035910107051584550015001e59651031032102049203040c00304035a4611000c0414045003200c255400c800f0401c4000d0402c3c07045481d580111800c41c00c2c41c0c030410b40403035428003040000400d20300c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 139804451 1250 139803201 139803221
    0x105010f0b090a05040903050c070503070605040302190803030103080c010c080408030c07060f020a050903060114150c1603150f06050a150e04060602010903080a062114010f060f080a050a06 83
    0x3c0f0455590756040468191000c2c0c00045001c0f860205004983e07a50401c08140200402c40080120918041c000741180c8110301005c0d0085640400380240700701003401480040091400b100c1e5250fa40382070403805a00010b10f100c0040d400e00e804110821f204400b42c1c1d020b540c02c903502525685414990341c01984c000d000c104d60349501d8070f4550440650303601c040d140741c0c4110340703440303603500410310815041c40c505030000c001219241a51031043c0d281c500070284020318007400301e555400f140114503d4180300030030030310344820361090100070841c02c0c0e10700707402a00b4101001e0000c0070f1007805810554400d070140035001011907400f0000100a807501e406041c61302e00b400c5000c654260702080680342240c00c00d00140c0e440310000410180d03c100c0d0b440e03011300b4241d801c022090420250120310f890300060758903e811006124414002030a210b2441d1614000003044a0122484280043c281c01d200d21414640001c400244050010a03c459174650107000303040d099003280d42d07a100800103962 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 139805701 1250 139804451 139804459
    0x607120b060405060c10090b0a0606050f0906090a0f06050403030e0108070c03031a1215010518040605062d0a06031406040207030302040f090e1207030c0f020111030a0504050a080105010f0b09 84
    0x3107501b030a6030fa20030649414003614044444d880e007001c5681c1a1a0304c0d91000080150804c034054508146005840c440d2500300d460380d903148298000070303154103a180c102d5400111802d0002a0054102c002030040302e00c40d84580403000d002400550319070b0411284c4802080801404000192181e0301580414140b2181076509007400008214014120180007102d5885114101c40b003d00a90401d401807104403100303580c0307a08040412a5000c1d0103070004040310b40b5038000c217845070344000041308022100310004500031641c0c0c40700d80304400084900c50007a24040d20102d40ca9200c0c0c083ea514098000341000c1090711000c0622000b9840000260b04040d4284004030b00c1c400d0b4034a1102c0244000d20300415010742d40d0701c3e1181007149034524075140f603030100858070009800c8501c480c0080c1d0454182c400304502400141e40410b0f5018450295000000b0903207462a0414042c2050342e006464030143c89488480041c01c950007805580c0c8040200708081245800c070b10000e2900c140094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 139806951 1250 139805701 139805713
    0x20108191805031c050103082508071a010506090321040f0f060e010309020d0602210a270c0e040302011b05090415030c060e0301090b090607120b060405060c 69
    0x115181c4a4180c250407582c9810000303004c5044841070507200602802900200160352541d03030703000e40c2031207480700340b8486a0603000e01c04109010361100c4410f180e00261b8a40c0c2c1c4a049140103001c0c100c94540070080350036100004030726410140f081e611070f204082c00500d201c408003001d042c00079003900ca10b61140b0703104110100d01d510942d402c0310028500d11141c1d145450606401521801220788500e04040c940400e20016959440b244140c9641028005907605d100740000604c11002c02d0030103041200a106000d140d110981c032490390010041107c410444013001007046100b000f6802a000d840c802d00103011056042070810b401031b00c24000040c440303002c02e5813050040d0300b105840c0d000c14008a50342d845030400f4001c2c80d603400c054a0ba140c0c1d0700b50039565070410754042405031004000d400c40320b20b00310762001d5200c509504d4001c07821103024a024412035540d10300440d940300c0050030101200c0040001750103018031010004201c241468280720078000380c0d070090410704806110390 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 139808201 1250 139806951 139806971
    0x260c010c020a1a0307022803120b090108060907080c0a15050c1501090609020703120f02040f08060901290f0402040e090604020f01020705151809011d0601080402010819 74
    0x10b41403ca8514181400d50302c0b894051000ba003454482d504050725003820404540202d035035020038600c010350608180c00341d5175203d13084500400c4100145134100d2003410020959000c0010344601c10b607184022144401d80301e40d00d00b51141d80c1d204402c2e801042c000410710010b603c1c0481ca031010412460f1a90400c03142c011020315000010724611a0a101c030350042c45101198000c0402400807200c0c03e500d81401503400500031488150000c41285d030340c000c4881c51042d980c040780c000388450359803a002c05480300380b120786880c029074800c0c980b5840c02c80784243c000d0031072006d803945408011141180440003070910151152850f105603003c0d07800c010115580c1110a41c00e8007900c04030300145490318207881070001c1160088015815075100b00b0b801c000580e2040b48051003144505005d039200e448000c00c514403131001e00d00c41c50b0b1101e158400401e101c800c4215011581051021880c4151208801518142002d80380a400104140d00080707a0045012441e142c46001e494009088184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 139809451 1250 139808201 139808219
    0x703020c030f07030201111207120609020f040906290306011214090d08010b0904020d021b150c07030c02010509030a0b130209010905010e071b060204060306260c010c020a 75
    0x40a039001c442c5650102d000c01c1072660910440c0d000602d0342d0f4159140040c0c04210b8410654000c140d04100241102403200c088151b400c103e0080034620000d54a984080c01a400305410601a484050b0f207048000107200004442e142e5000002c5480e00960000811005600d5840104200d05100c001c01c1214107c00d01445564040d602102442e40c2e14104012500d007003503420841c0e2801c001400c001408013601d414210b40502ca021580145e6580c45c04201078080c0c01401010030820440c0e40044020002c04104c644213180a00450600e075600d4240d200304900804002800003140a15003c00550041000b01002d4000808481100c12240e4540c10340c0b04040b21204880c3e001c1c40345590850a1400b0440d025140001c014441076040c0766040340e03242c02c02044030b000c11800202c902007049441e041503c40a810031010b40d9540d0b15040c002e0003405840c4660416001c5404000c0096205521694804a145000780940c1070b03d200046a4461003400180da01c0104038000085d2051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 139810701 1250 139809451 139809457
    0x6020f12150102060402030606010f0207030501020c0115061103120601030f050405100b03070815060d0b0108061503060402030d030f140117010c0c081c0b090421050a170703020c03 79
    0x900481803084525040d4a10480071807a490450305640c041c20034000107a03000302e20150312110070710b4210340410510000302d1602002c1d41c4042c00301d510000b4400000b19064001404000882c5500d61110b50f550b9001c407105284400010000e030014807001014035031845080341c10503c1454041080310046107007102700d9905617030440d1103a0001d0300c1d003000e803144c90042c005e40c410124050320f13a541c9132640032038660b0b241080b620400c103031807000101d07103607181c0c07400f9803000e500403030001200e41e11080516a140b0094405520138184904041c489240015480c1c1c42564094007914468a40c00e000350b02904a504800000f1501c0341c04120380d01101810a9000300060f408900f40301220348880c0e07003100c4500503928200b0075510340041c0844c1e90350040307600445814800e00b2200ca48212084028070b5202150781e80703c4004028481404000740c00701c0c0d5043c000e41621959010082d00a030b41c030388254564180410303c1c440d0b0b041c001a032200c10321584092a07080142c078140c0601300352821a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 139811951 1250 139810701 139810717
    0xd0810051305160914101b050105010e0c0c2505040c2102090901030b072606130506011b0c050303040f08010501060c020d0b04020f0a2309040804050d06020f 69
    0x156031a0304100c002580042e103010740c603c2605100d19864207000d07031a1070001410300028062000b060185044900c9410100114084c07034044240409084c0381c102e02070082841150020460701020400b00c3c42000125440301090000504403525400f10f50041c17800d0500040c880563700b418001b03803540713560144482a0800d59103209030940e1781540032652104100100005901c140005c1d00c107a10f0f2645000d05607500300360b4500d4a41d5a07807001311000098034541660300131617038003002032661304400c0440c0150400c8524180d1448103e040c20b0465504071211400148007009484200316000d0704507210314090708010042a441c0c07008286941d001c1c2d4004004850352807801c0103102428403680b80507215910741501110b50070b80004410650310070300a801c51600d0804201117651301d805040210760084c1c6441200b554680095601c1001d0b030344030b0300300007800c0c0d8a410010301e8a054198402c0d5440b1404500302803e2400744111a09101c1040b140e0540c04c005802814003503c000d00600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 139813201 1250 139811951 139811989
    0x705030d030c0206100312140c03131706072109120e01120c1403090307020312030702011a03030a030207170c030d06090c20070e18060106110d081005 66
    0x242480e50021318000004060075041600460184006000c812030300783c0c0714240340380c103100c920704651110711240f007180070842c9075110004900890b025041d1903a42100c00e805003a1091108518103942c596000329100d60000315a251f500b515140740c0c2080c4220260358550028011203960380d0a0906c00914074032201149410a02000544c0c2c0001001c6e0303003400d1a6000e00010140100c0035010030380c11f0303074030032a00a0048002542c00f04100f06840d1590b13001401c44002e003640100f8404242d000b500c031040103508041e483c0c074805403d40d8034014118030180c01503152040e03c480c01c400a40000104880d1507641c424500d003682480c202600e03084480001850752200300c12a9201140d5941c0d1121404504000d124031506411020440350920011003442c500074031503003210308190003600601c0490617040f0600880d0301c554949010745009040c110758250741c032042c065a98034604000201543c1c001140713400744a2044400b940c004c044d604c0ca07443d03550740713039000241e0080000e041c2c601c031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 139814451 1250 139813201 139813211
    0x91c030b12010b0901050d150b0607120305040b1003030512061c03090816051311090a0f140301050603060406020d140403080703050708070207050904050c0d24020316030506030705030d03 82
    0x1561134003c80580c018201115075070400e2880b9901e01d10708940b9054045904e076030703891210085851342012242d4450b4010240302d219a01c582c000741c0103100941c0c081da01140800c1c002040c1441c076410400940c0e0701a29000d04004910a089114410042c80c083d08115018071804190541d000c941d022588243c541c0c1c5d407424100b6905074030b00f6a403508031060781b61881004109035140d90b405140c600c1001a0080f8120781d160b0040400b40c491010782c1500042001800501404002c4140d010f840071242c0f00013100440100301806d858056640c076034540c206001140c00103510354014583c0c100d1206000c201010050041200d60754102c500f54081307103600040240c415418400c1561110003810510f00c14240b020000b5501c03480e5025590007003013840082418080c003080f40d16010075000344040c1140c6000c0c90800741031031940c41140c03104020400b00100107402802540e200b1546c80140401c028a000d40441c09800060300640d098000c14101240503181480582c000322015200450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 139815701 1250 139814451 139814471
    0x6040806040507140d170703170702011a0406050108010608090a02030604060c110609030a11013c05040209040f02040f09050c0a0b0405030607050a1b030207061403091c030b1201 78
    0x2c0340951001d4400c0c170942542d056a000180c03030388205040301071114403054507103900703250503159038405412000b0301d501d0070410006025030540140041c0c414241c0000e00030b6242d2002e11081d14117030701803140415164801400303800e114030340099100007140201e40252149801080c10100103072001d65005444038100c080700c1d074010407103480780190701000f03021902d0910650b90305c0c3e0040315580d40410180c4407101c00c161809400c03401840340d00d20420505d1400200c0303442800034005031000141c849c0490f003c0a075030301d0303031050740e10590f0040e100000c02d50741c50750f4100d0191140607080f60f103e5541d803040e003010601445209091071150300205201c1390800300300451384010b0783c0050140e000070401400786440c0425410340003201424420384544109105861051003c0414500b000f0882c41050a03d54000380300030407141c00c0c0d2180003030000202e0305172095110481b81c40856501515864101c0010110031980c03404807450000794903071000e400100400700a2540c400aa910341070f03040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 139816951 1250 139815701 139815719
    0x30a020c070b220e070c0204050a020d11040602010509061902070204292b08090a030f030c0c1208160503090414010503240103030c0206091210050a02040b0405060906040806040507 79
    0x3002031310582e440590145802000140300d0782000400074060b945442c0460a21040c6806a6001940d0110140300050103143c901d5980c1d0018451b8000642c00d000214410402c089610f5019100c515480d4034090141401030000c0e512001c1c040303801585d03c211022660704490070007040c0d40740c0c42c0501c01e071100e0b5410400402003c2d2044c1d000341b07240e55604a050140d40040c0512146074041c8000752118a0030000130003010013640060300c521081c0740840200b503405070480340114030850300001d040e511030000b14401199060010003080040003c05103000803031403d9503200e8820402c40745409900c4d4040780940d5012103242014007002c2c001804140340c24002001e04800c0c0f04030154a500c006401205061010312000c0c041c008034140e00c40a40d12800c0490364540f030b010740500d002800b5524602d50b1000e241c01c280507514600808105900340c0c038000c940032510800f80702400c0074249002c00820746e020800e95031344074800b0007001584000c00d121480c0b207580030340e015000c40d42c5440208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 139818201 1250 139816951 139817017
    0x15050918030d0e10060906060f0806030304030804081606080c0403031101061e030506090102030708040b071707050403060506180a0c020f010903090f0603050f041202010b1f02071a030a020c070b 85
    0x101400d1400c1200c14048160300c5224404500727a41c0c50114040c1e181c140120341144503d0b04050b12103007000402080000c4001041000300000c40f0596003007680e2000c08444000c4191804071104108100030000303c0c0c454425403004055040000405035525904402e011110541c0041144950360040060042c24000c0540c046002030081d451480d104000909041009000400c04410080032900b1076104202d00e1508a000e880d0102042c04c1c5480301900581003444100c0e089414800007814070b080130080300040740361b500100d83c000c0d2510100c84000e41410206c0c40114410f100d4160740a0500740100c00403070f4020f0315000741850030f1807168031406605401203070505052a050220044110600640c8a030f00004410034002d20804c04901500142040980c051207850303140540020604d5115513044840e000c0f01e5203550381e02c0c400810420f090030420442c65007440090040c0010341c00070f1081c0c60140b020341d009640c50f00e4603402e86030004035071011900905c88518510041000310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 139819451 1250 139818201 139818209
    0xa14030d02190303020a1413050918060a0e1501030602040311011103041415030a0c09060e06030f041a04051b01141602040e0709050a15050918030d0e1006 68
    0x142c010807105050481c0000355403032005040650003d840001742e131081d115200300040301c2d1025580c44a00c5200260344910b11701646204401c060702107940c1c1c038190100402c0d0181c0310406403a50b5a1108984c00080104911302c1c0c140340107000600703040401d00a41e07940610302c60040180c4035411400e103120100c0120480c1410302010020600c0e14900000a8404440301c245414640454510110700034070f00800c0740c0085075801105100d11180140c02000401000c1d0f5600c00845665007400c480c101001c240306600700400308081503154118110041d03019000c2c100c500c040c02d02c20301c41c88120481c210f400703444ea50071651110382c4a4140e040403007040d1009107170038000c1e5891108041c1c928440c070103aa61a00d462941c20304110740390387e0407a1100704034070400e031888103603a100a00082d101c21110001d00d00d2030400c010000800840d094420743c0c5000e0720005071a40c1d01005485050401400c12003548010701241884001d24081c030f5024000c4500501000d0b40d003003000d030381901e4440e04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 139820701 1250 139819451 139819453
    0x90a180c02010e1002030c1204030e03160b072d050a06180b0703020a0e1207050112140c1e04060905031504030e0613090504060606080c090105041802090a14030d02 72
    0x580711a05040004c2c08003a002c950140069503602c49441102d50f5202d01407004041c0d0001004000626810001000291105078241c2d0081040d180004031606002d00645004110038004500824291152400d06000f01810501c16820020390608040720440d0216106e03400f031900103041101d00e0088807076101d00d000d59a9550a400c0d07558110b014002031402c820035a000c221100c1282c4140300301e0241d0140941508452108a094107840b40e40c01d00400780803e280c80720100d1140010f1191007070310b540358090010651260500c8042c0395000c01e044800c0c1b0480700040d09880349000c00140018800740c4c03166101c1c0b0749404180b41c03c080c04241c010751080e41a10402c00440d40040c020a800d0750101c540940d03601c03521744001032040c1c6540200c4100c5203080c0401c810050303654451030569032142c1701c141e910341e0340c00d01c141d010344a0542c8440c00100140020001c20300c048505880880400704058108450355022410980316903000c6035482c001e02c1c00811881c28288055100120702d84 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 139821951 1250 139820701 139820711
    0x305070206031f0e041a0a0b090115170c070f030504031703010608130b0a11040305070e09010b030d020703020405040c150c1101030612150213080c01020c010e010c0f0602090a180c0201 81
    0x5118031243c0140b01c410998104030240007d080000103621402c68010f00502000345075031074156028222903941180f101040304022181c280c4544041c200f4070030403590ba1000d00d0b0940031303645e6010808030b1000440500c03000b4403000c0006912103038504508902640c260b9100d41c946000104109805001c008001c20008051404584201c0c0861360240ba6068042111240705a130700307840703200b542c1c0050310b14010030601103482c8145800702030254201100a001800b00e020800d525407091303040400c0564000383d020001810540c01c80765005014095042c001ca94682161081c0282a900d41c400540c08004110410525180c00c100307280f428a010480203040104910700f0410001d000750440c0050b120b14006a00c2d05d0301200ca2a41c0e00300220382d911541c5404260740d8010b628480b5015009803004540700b944503066114900703005a4030400032406c40d0302c3e140e0061415400c00d0702c006c0c0d002c0002a0b11501c03420904002410b1001100351031003c0d6504c1d2108541c03984907042c2c1164146 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 139823201 1250 139821951 139821953
    0x90807091e0204290f1b0706020304080312060301090807060902010815030307030c110d0b090601060c080f030a0b060408031209012c070e070806040f05010605160305070206031f0e04 80
    0x32014034005458040c09510b602101350360101058051380018101d4141c0c00103800d42081109481e00691034072003421141c400e500c40c4407d0785c07640103501480d1203e50090000031030041005171110742203075000d00009520031183d191040103078041001a62295114401c1204550340140c1c01d0307500100d41c1c50344200070003050000035100c0c841d140b0090200308081c0c4807070080c060510501d1782420f034014200344098000d0310300841002421502401c8034062400000381e000d004080c5540c2040d8454005480d244580b4510b00ca6070b00041c0401000603943c0c0c0c0c91484e00d0311004000d00c007602d2001e0055071220014410522600703802445100984d0400c046013800c03001110001c80010004505804278000300411245040020380c010140c40740c01405111408d6008024903000d07460a80e803c1c40311722a501c1c08041078901c20301c2110001003082001400c800c0c401023610030340038400d2030110310300211744e000034075550801e41c0d2080e101500351495018994540111400500840c003d601c603070310302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 139824451 1250 139823201 139823219
    0x303230106020712050c19081009020616030e0901030b0a0c050913110c03040f03060c020d0807120906020d050901061d0601030f0216060b01020706090f030210090807091e0204 77
    0x1941c420b040b9000c0c2109030304020498148403103243d07150b0203420583c3c0381222407c00c282130001441100c403240036505140040548901800c049140c010b440b180c5482c800d801c4001c011060f01006504100495410b031205070303113034010340b40214002c40300320383e2505210580340300700c904081c00355085c0007041181c0000da4880d1000c99030350002403a40005c000b20a104205890311800b041902c2c00c0c040000c01080ca071403110b1598058074000c00041200c00540f901c140d964440e24500c0d940031905840014080782d120303005251745c084004001040c0203440369503200598001c1d00b215440c11303480340d013040140e0342c0c2403050000401c4201111800b0743c000b0805040c40c2036018140d07504160700c2e6500f07002d10211680440e1402c0054040710900444a03040500043c05040404c80c010b02500400080c16031207401c0001c140c8114406c030b440900e180d0740c200084582210410b0b000e100401c4030004103014184130f01002465840000300301c00100c985126604581d006006001510500c4103014000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 139825701 1250 139824451 139824463
    0x304110f0a0509160e0337020315091018050d0212120a060e0408030420060d090501090c0b0d0c05040b180a180e0606040207050d0f090305060103030323010602 70
    0x110350410214a1207500121000b105d0080e10303541501c90401c1c01d441d840840c240c1c3c01c0e00c88510f01209850091103039844448015110006035056000380000032005e80c800c1c41d001c0e000340c0349000300d80807014580d4071841502c0681d2202a080303613001c400c98050000c01c0c003a600e94074400744040d10700034450034078004c00741c000d26090440c000e41000000f000450b4551054020345400ea0801c4c2940c41c25241c541d034983d104032000c560302001404a01001c68100600c03810399680202050f0806120b1405440141000c103015100d540d220984800410303005408200505211a001c1d81d881810003090340645580c00c6400c000c00c4802c01003000052926015030b46507244584c881c45003008540d00160b060140d0f07030443d15441542d04000036030040c00f5842a000700300302c2c8082d100a99681010401203006814014019400944024031054814440640c840025003403031709825450380c075170504c0e10500340c00882c01f01750f81e0742001c080c5c040000c0c2540390321451201420a02d40c10240d0003501c0385 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 139826951 1250 139825701 139825711
    0x403020304030b0c09040f06060e010309080405011b02090a050108060903070f11030a0501060e06030c03010e060a090215030a0f1b020a080c0c03060a2307090b0318030304110f0a0509 80
    0x43c111802180740004000111144040010010b20941b107086065000402c407902c03c50010502d0714030000c0e19540a03004044015412495441c2018500030043d101540909020740c241040b8141150040e81c86400c61805042002070000d100e606003004940f40800240c495481d03603000f8407280c00011200000310300a60f40c0900c058a12903080000b00c0c1c03507c404000002c245500b0a031001c10240003002410f44607407802c40480302e40b406090185800c070340171580350343c1e103d41108000400840042e0030105000388003038040568002840002c10642d0801e03501382c508680c8030000c5180e1400c490003800c03010310082e00780381707948002c00d000a0741c3e840004000501e03158002c0b821a9450005000ca50000c40c400750540b07099180c4075255000a2072942c046a0941000d00c04845c0b071652012400b0b8400d2426407a0405110b043c90500005900018041e0043e08403811010b081040103001035800303a445500041c191086043c100400d0480c000003ca008182c00b813010440c50350350010480d000f07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 139828201 1250 139826951 139826963
    0x3150b0f061e09150a020a05070603020c0303010902030606070c09090b0115020d03051f030b01080f01020a050a0c02030709110909062b020d020907020d090801091101111e0c04050a05040302030403 86
    0x31405540480d8003041c1078010404c0c0a0b40c04a15102c1c410b4001c18890b401600c41d60642d43d220b0780f2200103030100d0248840c00d800700d91007800184a08540303540110341015000b01028105141a130314000d0340001d41d0006c0007116195104082082400000075001d08040c2d15040f1042d038903e83d00030740c0e80d0401504041050f40783e001140c02c1c026070a99001589800c00003011000303850307050808000e0428425545148102000d266248a062098a002800c180d40e014504880c00702c0482e800030307100074280d0340341c011000b00051080c0b42e07200380c03031356482c8036600d5a89810b000d00401031046001404140290404c041014280b890039885d405418405215445e07404541d00100e07804c2c01c58200000c0d00709084a05000c0704980004004089828a030f80b545034075601c400c0c02c0350982d007180c400203040b840c1c0c1c5410300d41c4560185008588019a100454000042701140c41d210003000200300001600321180d4407895041c40e004940d8042e030800d20030310540c140741e80c00a60740e07c502d220180403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 139829451 1250 139828201 139828207
    0x20f0d02150f07021306050d081b0d0806030c0103090b06060c16060810080708030706050405010b130b010e0109050a0b13090c1d0108071709030403150b0f061e 70
    0x85540d249252000d10392510000c540752030003107810320b81c03651211005a1182402103040446040c080c002c0e4016217030050882e00800b04103035107a00c000c2d0003101b48925a54241010041417600c1041264054400e0380d4034aa107504010040c5814102e40e03a080300e0400d820011000081501034110f26000039045c0c804a07554070038501e4240c285418110300900c416045440010003c0d8401c034072a001e1216005a9071015540700101952403607144104805a0414080080412035640c04a5402030040c8000708203581c8101c00140300c1d000d004240641c80380c0c0c8551140c01564040302541c00c03a070080c00c1011601d8105000260b5410302c44c45501101100002c90841c03200e221100d13000100980002403103803004020000d003038050041192085003610130303104100ca40c807480040e4016005610350450004407461900e2203250020101c003141c4c0f0080000000144c0760313521380003204081000006101c00000c00300300c0007071101003000344181001e0010303a000d6004025018521143c580105603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 139830701 1250 139829451 139829453
    0x3150123030307050601060305010b070f08070807020405102c0c0f120403030e100c170939040c0f110a020406090504050c190303031e021b0d020307020f0d 68
    0x340c0c0064494805415001c041440030401030b0000d0614107072012520140130580c1c0fa8001d1182c00d0140090151034640d544000303401191400d070081580c42c2c001d040141c600142e54001c1401c0d076805403040400b17584a21000c00038007030852201102c0c40a4050284892030303415540b520902000340c08010300600018004003240c03c1c00d0102d90707280c82442c040c0c0b6810700d01410b000d0001c010400d105405070107054406140c2021500c10500c4420301d039200c410041940c100c0801c59180c00528034481c620501410407811101e0706559000900e801c000e61603850766024190300c000d0340701d0500e18000d034103140c200440c03907801c0070001c1c40d640e00d14903141070440c90755400315251000a20029401c14038007680410401c105800403445070f4011300c101c03040b8600050038018048000304040c10322041030001880041e1107500845001c111903003130f4043d41400c0415507002c99114030321091704151040051243e00d001031004160382030f5180059800c1002c1900480e0a010300070141622403890014210 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 139831951 1250 139830701 139830749
    0x5030f06040209180a06091b030606050306060a050c0a14010f0e0c0312030a0b0a1203020c030d08150f03120304020111030306010914031606030b1810060305040f0803091506031501 79
    0x1402029568010308c803800315500c40e10421044540b40000127400c082001c20018040d0089038042d00026003000d1421440c8401210b190f04003003071070600e078001c600d20600411400d001b154075032400d400c000516000c40c000408101c0d100e0260f40031054100c0811000c99590105809005500001d0b15550740d55400e0700032001046014110741d40301d040c0c000042180b00c07010700001c40151182d0212142e1503104410036680b180c01200d414001004240003508291004080d01204d0f44090f100c00980c500804c000307410700c940300314080b681280c00b00c20001590b90090780f040100d41060061459411b0030030008245c0c0100c1d001c1e9140c0ca0241c994500c4145e02d0420540d992184880d420051550301ca44000340901442804544900081e810340b02100700d04440641c002c0c041d4a220151051402c0030036805400e0050090740c600c0d802880c0003000c079142030300a5102e848504050031b404e241d05045141c00000140c80d00380a9030201400302d000038858400c65055442100d51008c10650044d031803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 139833201 1250 139831951 139831961
    0x806010c05010504210806090103030f030609090f0b06010809031621111204051305100f031511070f0b0402030304050a0e15060703090b130902040605030f06040209180a 74
    0x422543c0381100300130600c180e044d481c1564191141e00ba207a000400601294186000d5072641d5000c506d1100400020b40504489200045941030100304140d84000e050100c5103042001d03030300d040c550b910580c20044c83c20040c641c820000d081100036418076410141e50703406210511080c0105000c04e03842488a81201500841043c1ca0701c8290f6002000c40146145054010b82d43d042c030800b0425943c04007808256801d9031000ba01e25241a10030402c0c28010381000341c200810051007032004283c400e08030003a000518018104a030702c44178003181c1c0c0811550a07028000e079410b000d00130304002640f8280e82245241d000f1713445402c41e45031400020304611a43d4000340d0302901c2000c00003400511041618070034524500c85486070224030050050724810002e0040028405210600ca407071405000ba007a641e022065001140303880b02c0b00342c802c0b03a020b03410500c003152020080100985c4a0b0303101c103502003810790f806c1d81480a148003060f03082d000800c000f60545e0010000401d0a0300b01d0b440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 139834451 1250 139833201 139833203
    0x12606040f05010801090b0603010506130203190e0708060903030c04051905041e11030417160804030605010306230a0b010201020d0c03060f060212091210050c0405040f0e0a02010806010c 82
    0x3003000b02c0c1d40d4584e40c0380d00030041b140c421202c415141d400104546810b204040c860302d07028141010701d110802c04a00207620003042000c8448000c0790010903408240724080822180c1d5004240042c100100340c0c3c58001c00801001080d44100700f08080d4105800030744045440030746101d501d440d48108030b60090b507400e80281790032518041c01669804200704e90f12990b00c0450b0700030420400003650410310313403208550180c500005640d49015036250180109491410007000c071611640c0b682d81c030b4003194002d90050364000e44800061082c007070107100d01514900d09505810740304002070b001a1907040c005100c8000d613a66086810401d034002c0d01200e00381c030a113050400565a0003903003c1d000700003e00420807515408400452514000151016610030800240e4181107100c41040295030000039050712500a2028076002c1e400c240c090540655070102c040ca80fa2410b0106101c01c43c2c20a030b00e4600070324141450840d60741c90116560040ea81c080c0f0307207500955102ca0050300c001e10000c1e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 139835701 1250 139834451 139834481
    0x9020301140a1a040908090906011b050102130806270304050d08040305060f0708270a0c08010b030316020907140712030b01050702180702010615020a020f01260604 72
    0x8100070141d2455401500d400f10303030800c003000c16a80070003807200300c0c5c1c0742d250010300c070303e0b001c02001c1903a240c000380c920790020f014502040c80c48001641e180302081407503c01c0391544c0d008240007000c038100c4001c0703c02400352170005000901c0d18203c004400c0d550062555411341d461743c04c03211030340710900403074014041c007618607681c860451414001d030b54400c0c4000d48141c010100441d88820314843c1d254052085a03503429542e8803440e20720220704110310440000020340320341a1990000038003d020b4901e01803011000d480b840c040c202801d403255001c80c10701c1394100b00010080c55501c4074880070b40640640b4094580d66500c074080d03a00790313410681c100d85c0310001b00323030710741042644c2461040c501800e130b40c10700111103514010b681f540101e4500030340c03211004403c2d00c1c10303003403219046a04c0705092001140c800d076900e491007000035035420001e0040e00614581c400b0350900210340c014481c001e1800a512500205440b00400c180784840c0d08020344000c00304200e65182c0d000800001d00700c0e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 139836951 1250 139835701 139835741
    0xb1303050f160501061505030a48020d021b0a030c0b03040507060918020702010c02060a0c11060408060712020d0203010b04140d0206030c070c0306050f062d010309020301 75
    0x44000348500300d201d000c403403030740c20490b0201b014124509070f10102e90f410340780d080c00c6885526444001c0c2ca9030032042070391000c0030b58020040050f52295400310b41c01201c011115180202040c05041030f00f0300010b010b65000b2010b82d80317a80d0340081c2120364402400c0b41c2440102103070707000076102403a80d0b00c0506500c544420114130000e4050085003d58450421078100950701c5800352000d01803032146402541081d81c206544030b03180c0e002040701c02c0c41450101000c0280764005002504020140f81c0007924030b14101c020004500d6600ca0300c010f0480e41d0b64202850700c1083d5130780d100010000410441e0b5420f5144503903d2a4068a0354140000e206548940c0c4510130442c29411910a0500c6c0303000c00142e580e003d0409005510301160003401c1c55140d0b07075801c1e540f040701d0b13400071900b00c0d6407141c8114008041049031080700c2c0604403001d0f101e010f0b41442c2041000d5840700f00e48600c592041601640703400c1c103001c6103c400704c14080c00c001c0340010300c03400080d00400003240c420440b81c0181c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 139838201 1250 139836951 139836967
    0x9010e06120f130c2117030604060506091315090903030506040f020a0909020306010e03150f1821040e0708040213020a020a110a0b07030201051504090b1303050f 71
    0x20a4014418102031841e442d03640d4840e4030120b41c0c64070610000d041c05045900c1403040300c90240116903c4092903200c218085500d50b07510f00855080b04507402c85c200007006210035481c0c10302500e8010401120898241100b5000085184205070640810103a40386004111045c507070115000816007001c1c10403101c20031341800b074050201202d42d144107500d04030804031180c20700c0c820785024805540e07278845801e00b8080d041c002948040c11107030511281100074280c2c3d9504125070302c00001c0458013104107080184940420804c064050030900b0418026441c40ca0310000b0041d000da840c0c000640345400403000320407110300ca03940000503199043e40c100100c65401504081c05030348244c5d214801818205003450490282640c2800142c0101c1103040c0460030b8214100c030b50480091007a074541360303030b1418103400340d000c0d07401200582d449904001650025000074044084192005d11101416a9900d01c208500a201d100803100540d1200c0925100e002503c1e03410201e0003041d13070385981d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 139839451 1250 139838201 139838227
    0xa020d1805060a1808030703200408070e060108040503120a11190801050618040905010e06090a170301060f110109050712060f1a060a021018050f060402030c0609010e06 74
    0x1200c045610505160340070340c0804d0314500e04d040c03940d041144182503445e403010072006800e00b565000c410405c87c0580c1c040d803031101801000146409002040980c0c43c0104107040d0b050002c041d5818040b421003004003090020007100c00c1000b085a15070b0b031554405007007074000e1060031104080010013054080c45085401600403002c030312034a840c0402da982d9810068207118804440f074a00c140e48001e17500a042680020170014070030800401c0c44107254550714038141084529565071b6110700030070420701c10f0840d11940010b50821055281d0340c1407000141c0785070f800d05c41100c1003100f00c464030b281150b001c0d03001001155008007603c14250740d910f60100982032018090760001d20b0403949004403c014402c181d40c16107101c07a0603031040004010080c554020040a006500a04400704c29010a40c801c0170391500030841c0c030001c405102d04256140000c0b413280c01d05541d1091003807101694002800c41701c2030f0b500b210f145a40d403010200407960501c84214958004001092100701085 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 139840701 1250 139839451 139839463
    0x6130e191406090612071214011a0a09090c061d1201020a12060302031b0102070806070c060c03020304110910030b090d110703030906080a0204051909050c0901080a020d1805 76
    0x844410203e03441c2d0300d040000000007117401e030000358001032081145169500442c20118040d081c440f0040384902000350943e0070110b26000d800015031218059480c0080311030b005481c40543c20401844a80d0f1403010481c40c0d40201c8041c40320061025849044040008000440290000c01c404501e0541c2d14080d401070552000800d890340214601203d191048034204d07900180100300424002e00c04203c03040303480100b83c1c11070050b024041010001007000700c3c001c103074560b6005070022036800c06008031203030084600308040c0104240300104e1030500c00403280c0303082140c82400e81c0d2140840104500b0a03540700500401c0c809080043c2400080380c80b4030309014640396001a109001441c0380ca54400e4003004000c11007030703a0107002161080e14103650111039404014502034030380000890040c103005005520386414441400081207500504d07030031412041001d81810b14040c000b904415005101d280c0480d0301207107500c583d1002da000741c0307200304040307031640b54654503400c205c3d899034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 139841951 1250 139840701 139840711
    0x2313050d0f15020f04090b210a0506070807410301090501080604030c0809040204170a020325050103020711040c050408060c030c0f0d060e0c040801050606130e1914 72
    0x21002d664a03002d544942c000c444200341030703c0c102403403c0c1c01d001400b4018940391320b0960f0004207000c462445c1140c0711441142c4444c0b08002014410280c0c0703000ea24004005044008000745003092180141e04500b18840782c1c080c4c00301001910b090407040403442d6086103d2a03900450008100040d40f40000066040e0f4403140020303c440da880300c5500b41e40e888252002000600c00d112744001144e250405440080c1c0c0051015180540d507a00004c09160300404298140e004042410114034041005000c80712103445986030034211980100c030a070545100c1d0f1810f15400040700001c0000342a1441c4150304014000c100703a4544584c000c101c0e400c00d001d0810303a4420340700455819131003641901d10440c00811154036054915141c8551a042040794150340303902d0302404116004100d0032035208041c1d488001e070300c1301d00d00340c11603096403401fa02170750080c04104100c120070101c0071141029611401c022220980350034501c1120891a5a001c0684030f20345890401104460312010f4018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 139843201 1250 139841951 139841963
    0x10605040f0b120f04110409060615020d0e010e1504080106062a0201030f021e0a0e010801030209010b0c1f06030b151f200c030d2313050d0f 62
    0x303585482c2000400c0c45038000c07599050f100f16001602e4120707400c0c1c0f01c3d64400d1050b0140c880b40f0140001040999039001c01c1100c900b030300c1c0c01c0144115040142005081d0305284018044014401000b6007c5121118054100016101460100d440340301d403050404d84102c00c601d41d250f40d9549610b000300078034060300002581400d100060084101c0b450103020b4440700c4201c0100816a00550041100c03401c1c011015400f40a0888000180c90183d03e58000d94205035039a42c1d12910010500b980c400720b0715060100903401400503032030b04244203040d41d000e60119071b5205c462036142840d04004d0340340114001c0d0108020207400003180c1001c006c59200300354404140d01c412810031504001580c1c81900700c40f81001d40070500e941109a8540c41c416418014207803d0080c03010034504210354011040b9502005800c0342a040400224590040754504a00a10464881080342140701e00e5010744401d00031800640c0c601102c1418001481d00a00b00c0c070780e95456141c860054942c84070103a41e6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 139844451 1250 139843201 139843229
    0x180103020f030d0f030b181311100905040b0303160503070213020a02030a0f0e10030e0d0309080711042310061805090c041703190f0504092301060504 66
    0x60308000420768503140c0141c5030f002c0503220070130b411070080104403a6075511100c403a200c1c200204c0c000203850f001b248503480d0072013910b5107400c00200740340b03d80c100b19000f0501440310100150340f0140e0f110a03240c2c01c440210310344111340c00107442c1d8010000c5068070305c01c54200d00703820013400200409026100f5682c1d1944040c2443c240001ca0180304640d41c09038004010f8004c2480c442c25030600041c00d9404d000461214500125640501841c1c0d42000300c0c3e60780c01003620030f4034204640741e0a0b03641032030b083c010200f603582c03000083d005910005000981e445441c0040741d44642003284001d001c00184418403280425020000da020303078000a8500d9402e0012494a10558160040c03000440703c40407020300d00380c00d101040d200140305401d0b01300c0602020680d82d0840c074049400c045408000d68548507040c5050000006208610003404042a8481155074100341914100c0d0610f100010f00d0100e000c10810041e96480e0307001803032206030b4002250350340d0014050000d40e170b0600c008030f02e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 139845701 1250 139844451 139844479
    0xd1103030609040209040507030b2d0c0a080c1c0b012705100e0d050102090114040e010b0f07050f03180303070c15090305010c17070516061a18010302 66
    0x18a80c403041e00c0781604a0365000c0020f0245c1408111a900f00d8400d0f02121585a40c0e912480010201550543e141c4e4500760710050400380403a86103a244000c0c0450070301f0f83d00349000e040c0601c1c405c450003202403001c820000f546010040e4280d81150907074100b48000742d00b400503048000e1682d04030250215800d2201c0050b90a80ea49031003282c00204904000301c1801d020411415000c0c94843c1d07404c011191000030b003070781c891603039040302e03944580c0025840b220240d00152012a903146020f00e43e020500082080710600380c081c6d411580036600a030b560311450341800c2070500c10b0410240c098441c6102c0d0b0441d0f0200000240800701c1c1504468101108407020151240300d82e84002d400380d490384d502840311b400300a40c00c58283c13130710381842004203541781d98490a4500969100d80450f0082d211000900280030555500440600e4814907208002043c02c102000314400941460341e1841041007820a035881c44002200090060000d915401400304881d50f007404124096200703140303840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 139846951 1250 139845701 139845703
    0x2040f08031306030e030c0f060f0c030708190b03031201030c08030c0a060209011106010602070306050f07170402030106120c0503010c1713150207051b06040b04030605130210020d11 80
    0x14640400101a03034910b14070700326044028041400ca62207103400b081000d51121a4100f00181034203228502a161074030300b01121001c1003030005d001e68449142002044100e40d40203030108c0d44a0301a040011184456080380c02c000c04c64550561307010321000403c3c9050f01c0511003107034120ba218041881e0982c2e2500807140d180e0103003012188966000401da040011320390340283c05007040c18540b542441383c14448062400c642a4024800f60b0001c0d2400d0003442800e0081991040540c2d80c204c03218100300c0302c000c1043c4006110f00c2450050a0046011903a082d008000203040c0001c4103013114917541814011144284100c07440f0b5860012601c0b036440c040c1c1c5003031840141c5420b00003059940c0762100c0034a400340c280100d074a4001003e84108141461016004260045001308104c001480e000200b0018070202c040c40340c1024041041302314540e070212819260700c18408101a202d442c1e1150348035501210003584080038049a01680d80d0020750142c0e462420782e41c200038680300701042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 139848201 1250 139846951 139846957
    0x110a06051330050d0209061603080603010c050d0c030e01020409020903060901050c09060d020f030c0405190e0c0a020304080a080c15040c030209180f0d0906030204140d1406040602040f0803 83
    0x4020140d182107500d090900071800b420041e104540c005d0f00d003113089800a1920780c40002e001c9940f282904002c0b040c507601c100803690082044e002000214010113024180c1c1c020309080191a03905c46420040051103a0050f40c0c0b0a100c41000b55100c2d0b0312082c000000e5004003400c40c1c001d100d00c00004502c040705000e280d000e62010440f461811001c882404044d5021076032408810740c082100c050380501500c02140f0a088440145403164140400c0110f08082d0b20594070654281c150b00317120604142001903005036241400c90f94415400d1005d0341076001d1680800424010350042805004a81004101903102c000560b0001c0c000107c00b950510400c3e140a000d8070f08146042c001130501c0082c0640095942c0c10181195801c04015440d101003001008081e800640d510801c07142c01a20b03a07806024070b4103056080900b449140c0a621403c1d640d803038400c240e03119060f0180000d03040410711000300c000c20390b925454641812000b80d440340c801c0231200340541100182c01d00011086d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 139849451 1250 139848201 139848263
    0x1030510140c1812030a030b1e01020606010f02070b030c040f06180302010507020117160207170a0f02010c05150709050d020108040f032a0b070206040c06110a060513 73
    0x16241c1000c1044018402c41d41c500c0c1d10071070708144c9240d45108840c0c1c040003e0b00d103003129a500811656109410300c1031001078500142c45034002c041386d4442c50303a00840c0566101c0c6e0207103060041c24070948400c91820040740d101e101a403000209001e10008a0b03c0103100759640007141c20701155940d64100c03514070f0440c5540c5d80e49000c0010a000540c071030001400400d00501d4114420510040384586051007501c0f440080c2c80d1b44c00380c020074950148512801000300064114a2040000902e52501c003210b00080c017a6a41d42e90901c2160b01514241c001580c21600315202445988141600b50101b03403020408a2030000780010580703810f400d0a1840d0340e041c4d48200140d190b0380d841201e141c0e0503540440c2800070005402d1003140c1e1705030010024950101142003000958141a5000c80b400303040903045411041c108000300791449210403c9034190324100100301070001190b400d003468800028112070a29090003644010b03207000644540c0182c4014040e40f01c0c0c0c0c41006c610943d1144 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 139850701 1250 139849451 139849471
    0x20702041a09040602030703021e0a1206050a090908120c0c06090c060f0d060b0c0109020a090203010b070f0305132303010e100b060403020301020a0801170106080a0b060105070203060103051014 85
    0x10f80000d80b81d401442c1c2210090402504066110350440540d50403d504c1a0024401294001c80c80394007491159a02900b10000c111890901d000308045a01d1800360180107519120441b003048520402c541c841a20300712900d5207414092602c0c00d0942c411900001b1031712030782d004182c4c1c00c2c0c0041540030f186200203210500e801107500450010750003240d402c0789460b55408000603403001220081c04880c0b610030001507010039910400550307005a8200c42c04442c410700c01445546110341c00c071141d081e084403141d90844042c3c13604482c0f9104800d181c0000d00790200c00040d94507074180612503880444d2500c03980d20012082410700300d803500d81d62040071754010b0b031002c0030000095102a2034000d01800c040d1425890740c01090076a8801e510a0340014060401041105905c44685190580010003800f40600e4103035048c2d0b4511110320098500b40f0301d1008a000c981c003650071070364030b83d9000e010366a09607500e040c0306441c1c0b014045161066410456481c6051440310714042c440ca040b91 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 139851951 1250 139850701 139850719
    0x120103051c12270c170a1203021c02160309080a0209150604030c0e07020601080a080405011b0b0403030501080d030e071a0708040f08010c0906020c090402130c03020702041a 76
    0x1800c0b8800382500300500c400041c1d0302d08160400d11081a49561001e0065070310b107502c90f103002d41c454224101d81e5400c1d02c0b10f400403015400002c1490307204800b00f800d240f90140c0c0314960702c0c4a9210009260001000852002504000045201466820b01c60013078940c0311803150364610064542201c100d00031343c488072107400655400c4039000303242110038000c1d1500f810140c40340e6450116003019000f4800745003900c0f00f00302d01590304226260241c43c140020b0102c030704071683d803101c47e40510300402e4107000c0d0010706a03061000311080224015001071400130380d4103060030080c00401d0700707001e107503028084c1540c40c56200b4086e006070b8055424460042003407070b20b0038840010212a10030203026105040261402084407600504041c2ca540360748210042d182c400b0a40c05c41d841c001d0f600c4d041c490110010080940c01142d906a001415102364520765a80e2001480c951484105001c9492801410080303ca03455030240c0385c185d1003a541041500d00501d182103000c0c502c0701c5581d0340600700d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 139853201 1250 139851951 139851977
    0x100c090b030a05071b080408120f0d0209030109350f07260a0f090905041203020307020c03030414120304120f1a19051b030106030c14120103051c 64
    0x2580242e44c02000c03817134400c2c540c5480c28643c51281c14110800e41d0056000300701841154824020200c0c0395050440030382c509a0040c04103001405100240034845502003000d030302e075072402e4001110036030748030340316100c10106242085580c180d50145845440c0001900360350901640048a80e40344805c40d455061103034554405100781581d105002620301e030341501210032900113000d001c03407480356200c5480700b901c0e1140090800080d035200a080c1400d1400384004140304180d4498100754a1030f01507030761303540c03d50160314104e1160340070354052100080003c0c842d51468001d070000d13007044502a649150400206569026070f0080854420038080090005511b619080320311622618440c000e030760318160010f6800b4030032208520000380c0c195031109003450700d118099000190050421420007038015482c041e00050080d01c05041c0e031416906455400345140b02440b549031100d003503554100300202081d03030400b8481184c492042c48400d03008d50100e480d101c075500d4059518080354002c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 139854451 1250 139853201 139853221
    0xa050d0510050307180b090108010e19031b02061201090b010212040803030105010c2f0f03031612030e061914070503131106030703090308130c091d030705100c090b03 73
    0x811980c00a1786030369941070411500d581c01014024141d8000005108950985003401c001009c28180850280d02c4403002c00030303030007044848281020b071801c00c00d0007210307202084580c4594242a64840000e100024411819800001c000a020f81c01e07200b100080c00301a65043c043c50040885503002400103002c0c1d548205c04032072915004a200c2c01c20b012092255002080300320310f283d0b4504040550080e4942499400c09071040e1041e0011031801200510b01c026800c0d58020040c004030180c60000f050754403d0700304aa4020380724090b224141060360040380e8100c0c101030081c000c5420041005d07514404104d1040c4903400075100c8524540d0382000c0c0c051443c481120889040c00740100c1600c2c2915042c1c080c502c0791500c0e8070002807125040c10064102c000041c5809001c038414401500081c84c9120700500302d8048807000700740e51502420310111000c084400522500c030209600090100020300c03000c8040703d0300750411400760b1000e400c5070704c060980202e108135003040011030b250001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 139855701 1250 139854451 139854479
    0x10e07290a0c020604030807030f0c080d0506121005041109011a071727060c1b041b05132114010b040203100f15080601050705070b0a050d0510050307 66
    0x800380c03030300c265032910b10ba00241281d0041e070401d0b1492070002c0b0b81ca074109030f004101c0d51560000b41c01d1507507a801d90755507403202611482480c01c00a94454001c100c50740ca0350113284008110000a0791540364444a60a008250860301500c0e414070400042c403203801e04400d140e05854401c13a11500300601500520040da00010003201e203041100d0000440042c030f0400340034210319035214a204c443d16a54282480047e142c605442000200f140c1d00d4241070009410340c01046041e2115107140b40000082c00a149a24142032600c00c489030400c950b41c0c1c8170f001080c00d40d143c00004850a500c928001005d80064a80e0390a200000c480b0f000100d22528504540310b1080800400c281140d540410240d81090366810403202e040c810900110300c2c01808100a02444008259140c4403150001c008902c041c1c10310703060010005600702402010b101c0d4001a21b106a02103a4520024000070119031201c08000101032a00300031400517906000c518044640080c0240300e501d00302803000340100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 139856951 1250 139855701 139855717
    0x1709030705010c0e0f191401092309070810060809031c0b0f2704020d05030304030509010e0906100f030b0a030609060c1b120c050a05010e0729 63
    0x2100520810300016030074010596003a1569075860700d00050002400720346200320400b58400c240038034055090301c03840c1c0040700803994502c121615502440d00180c5074210141c20444840d00000301d20303081c1c40340845400118200503241114107503203a840449100700f041d00c0104440400001c1005024420900f6a8118130304c0d1060f01d00e0718140c21b100b460701403084000408102e486810300d80c0245060700c80d00140000c282c0d6003181142d41082541100714030002044105048007003c41c0a544030722a507900c40c00e520004890740d030f00706070502030146e822031000c0701c0c0040d222560940b002e042c98419280142e4024010040c0105a04002da6050780d49001510400d565864040425a203010070000114005e1030005454001424650282d4014148600c248925400802a00c8190002d0415450b41120f03ca80040002a4048528414050000c1d006100d10314426061041c10b45c00405d6041803041161445641d43e03502e1050002c1385504900b00840351404465544050f1000304004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 139858201 1250 139856951 139856953
    0x61a03190506010609030f112701050102060a02070302030f13170c0939190c05210a0f02070f1d07091d0618010b0703110102130b0703020109060203092a011709 70
    0x1d19a903440c01c0c160203000c9009006801d049c10300400203540c05102d07950f00b24401c80b009626019080c2c8002e5904d109011850404010004030303000c01101002c19032014042564046106400c2e4107900c41e6103084004049100705028008100308040500030004060110428207410580c1d00e0724100b81e4420345540f198403590201300c5500340d102c0d03441d016a62402c0d20344501c102030146040c4603140809080c0308620750010312100741c240b54881d000b40c45d984451850200d442180c0d24000302e04114156129017000d1100f06408119a45001da140000340010000e084003039481440449101c00c5500c25400c84039613141c1d10742c0d0103060030b6034190741c40a40500348109501d003420451035100d40903842f40028500104000c1e0030140e109021282d40449140258140140810b100c0c2c0152144e1068003000035002410b501010f000390043e80d80c19030000300071901c030b103420301d40580c4440d44041610b69104686e562076181c42500901758014400c181d49000020301c1c000704d10f040305d0034003400c8440d079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 139859451 1250 139858201 139858219
    0x3010e070518040f0e0d020a11060403020f090a150906031b030b06040b0d0507030f050d020d09091e0f0b01090807030f08030702030f0d090210020613061a03190506010609030f11 78
    0x1005d41005841d0444802da0f004089600c3d03a420080c80c01c20014031031034840d10003048100b01603903401013140c400d036108940c107492603240c04000c2e000a00484141505480c11072400080d0f10b519035115000b00d034014003401803401c40000200e1180c5259000042c1240c0b41c4001050041c00c0035805202002001b800030110032000ba1a00c2d0b107031404580c4201d0b04000c44100d030310304025043c80301c0540401d0500040110841480001c2d040090502482050315650b228200d4000c0c02c8080c94440c00020881c20400d406c030500c051b43c040c1c01c100302880e01041c40028000b8183d980043e12200300c03a0806107a194083d41d595806205510180044045100900c403506425a5141c000c09449080b1440007403d00c14901c1446034101001d002d51055410407420807100007072640c2c44410f0254400000180b512502e10200d03009502a180c158051140784400c1400c0c402c203240c2d40544074055800c8450503030f42c40208407001030342c0d4080103041d0700f40501a4400515807210600c4003070801000122 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 139860701 1250 139859451 139859471
    0x12230709060b0a0e09040c05040c0909140f01081504060b011119050c06040620010e100e071509180b1e09010602030c070509100b0f03010e070518040f 66
    0x10507200540c101e14400031000403425442c0e900700101e0f801600c0c0a460745141450700d41c54100720180288101405241caa408a0342c8803031060a069018021150007007001034107602c0c00c01810f540466a4034440c070841070000c030701c014000800d0890595000b130764503038582c0d4564034000541403a0440300c1c180610548142c5103007106211204001c2040c11504a84080f181800b915000f81c000129016603c01c000900c4505e42c000d40301c042c010034909010000152a40e116401003000c56111901801782c00480d810300708894020041c0840641e01b10750035180c40c2c2544c8000e815580d604800482c041800800200300c0e500300942c01000030440c0051a0400303c00403400140c030b11549504400b081c100e42d40748074942110000c2c05000e00c1d2001798105401c00c40010f0340c40381d0a0054920a07081c2e60005004180c0d0b031718019001c3c141089006880e505540a0038001c0d27007080c040c002d10480c50f5000a010a0300c55020340e11501207228000c4248084c06061100404080703800100003611110105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 139861951 1250 139860701 139860719
    0xc0512030708160c030f05130e0a1d0c01020c01120b131b080403080c18030a030504230907050a02010902030109120e0402030405060601080c1308070f122307 69
    0x140c07040015803a82c03006841c00c0c001c642e0034400300c03181039410b2045040510010a522500006c00c25680e410003a65506042000c0407402090360303c01c442c06211041000810a09a08184000d624010300c65140c0b1642c941d11039111881e14000c64010790100d100c0c800030b984500c4401c00380d512400c00004501e05000b0108407081c0c1801882c100f01a10307004180409803408000e030780403804a1a244440c0d040a513402040c01c0406002400700300c4001c1142004540c00340700780c0441d10001011100c4035441403501500d01c0c0c2051007842c1310005026401c80700508003d41c00c1042070300c01051040d80d0f6482940542c0c841c1c0024102d40c0856580e1111400107840034481e850991b4081c0541071294484850014201c0c014000c90078051070042c403d120020b00001041345d00014242003003c0326503a040610481d5000340360701d05800e00201900001d260001017140d0099070403104415040a4440300e40c910405060500100f40c80c10741c3e00d0300b0046410095107143c0d5145804180d4082d19a1501d40c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 139863201 1250 139861951 139861957
    0x80c01060602030307090b03150f06090d1103160b19030b0d03031d1b1215010b04060212030c03060d0203030d0e1e010b010c030e0103020d0606030203040327060c0512 73
    0x1c940540e0000007801070240c0c100300321000030218a1141071441ca024206130103d048030000c0c00e0b00480030302d108200e09541e01d206071502c2e92005000900d1640705428560080d845c0c0e5130340781d402806003442e95444c0710014000541900c03417450185141004403003081003402164040c1208042d91410b140703a4503078809a803080700b14041d58002c200c00c11003003c0d840c002c01a0006080b0907a000385160350310740000990040000700300700c40000440301d143d208541854990041070000390b4404001186641152014009030741d065421140c4110700c0000c2040503210a860501c0301150a000040b030f585030002081c2c0c5ca2501c050140d0b070500c2c02ea040408203440c130048520700c1c0b40c4c01c0b10209408903c0191240800d00c0703100c90091203190000c00003e088002c41000260400014485c1c2c521240d000f90100c43e410b02c40c1800030441d907951210010001c3d00142c0c0c044000400d0040c4058400c808940f002020072450070107614042e103040015140c0f4050660704540a00501d2143c034004040000a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 139864451 1250 139863201 139863209
    0x6050a020a080114010926030a050406080f010b030a09060f0507090905090a0804061407200102160510030207051501030605190c02060115020a0209011e05060304080d020304080c0106 80
    0x20250316600340210103021004142c0150201900c8450403c0150b07a0000301c0d04115103014000700300c03214012101e802c0d050312000c0803000e24031000030a1170585a0101c0140116101a41d6a0440391500b83c484640d90038284180e4410480c01d20100d030592030180c0c07082170024416000007400390a10300900003070b070b10212002000309032007039010441c22549002c1c244d444642c0d50f000d022a84100e6030b0b03d000038050341c0a0314041181c500007011390701c403214085808250300040422422502100c031919100ca0700e03010180180076040307a0714146014482c42c502aa24010b005c0390034164001c208500079001600705540c40d1140c00a40300042860b400041d0107140030705e45c0440c543c0f41c68510008a025030034100e0b003400e445d00c01c1d200785103940441c2842c1500c007440c50001c0e1541080701c040f483c11552090195100401c90b00001d42c444414940c42031101c607980e90b800c140d5070b035201005000e000032900503082100800102c440d20110380c2c02140c4c040c0c440c1008a05080890200c50300b142e0083d04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 139865701 1250 139864451 139864471
    0x509041503060515030105040b0711070807081b060309070303110c0d050303060102010606020d0905090709031406060f040207050c150f0408030405040f060302030c121e100e0c0312030a06030605 85
    0x1c04e010b05403030090400024204140c000f44828145561407003c00c407401440b01081007a8008501c05c562810320005004219030700448030310307070f4546824035240d429000216001c0c407a40e00c480c02d0582021130503603208000d0f070b90103001c107245162000d13252901811000e0200e805400da065045517a2801603040c51400340b0020754030b924042001a00b140e96076042f050555011030714006000380c1c440d546e0816248180d803d01101c0e00e840c1020b80d41480d076030704010b055000c196a0b801e50b4000000b580c5d40f28003030450318180c00100910500c0100e1051000c080c1c540c0e00010007200b042d043c01106501240c07000f0611a141c08209201114a50402e0300960901e4100242c01c01c40c618060007039007041035840c001004010303c0c40d40000c1d910107040c0121030064064010340641d01c0014414824480d403900388500110444221083e12406080b0318840c00c2031811001741086500001c030034804032806401000382c070006065558a98000904050010b61145404000510345004042c000c068081c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 139866951 1250 139865701 139865711
    0x8060d0503041203090905010e190f0b0402032409160305150a0b070309050a120204180c0609031a04081b1f1d010527010204030605040c1503060602030a050904150306 73
    0x20301584d0507a1f9041e444141c07085c055100b404440d06600c924514140100140014210031075004200505011102654040e2002c01001426414040e240c40038a040c216004521a0703d141000301c0e4100540c1d4104080034000b240c40701c11340c080d40c40290080035070204035041e030b4800c0c40011903510a90300942c20780500844c008003010b40007044480504400c40710001d890b420032420085000000001900c940d480b5021888642166a41091016003180b014045c0c01d0311400050212502840304440424440000d1740752401802c4202e4007840c1d00c022200d00e0554804000d540c04009a80c400019004086005c2c0002c495003810030101d0888600100b01000030b40203155800c42012203240860341405c0030042085440380e00349800103000b038480c51148054280081c02400717190001803419140c41c0034401407001e1700704200c007240c50705a8112421358404000300c091706c0d80c1d40302d4800980e100744035001182d80a44040d00c50004041c000140107440d003d824806555154025901207a6a07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 139868201 1250 139866951 139866959
    0x5100206070807200a051f0501060f030209010512040c0609050405150114040803190f1701060810030602030f06090c210403050c06070e040e010b1302090303190807020c0d0308060d050304120309 85
    0x620542003041a403881c08008c0b9600d040307009024018001080390400d940018071402076800b40090b02c060b40720307080403071103286401c1c5008001c4400c24010200404d0310f1000000d001d15050083c140708020544c201e0040040c120019940700c4c2c2c81603202034a4403810b1001041021042024110211201c2000781b40d58003000e0b0060101c83d50350807580e0801c200140e54400c44240f41d01003604491282c0303000304041d51195800d6050046035000140014000001c0c054901c0c800001140224800c5a41250b1070301d408400c00c00c40d1180c030014003d0386400c42001c078608801021400c0e0701a000341030180c549000310b07a4650810004035a0030340403502414011a90f810107100746031503445008000c001040e0058001446410f00d614010b404a03000107024895840a0060b2144801003422007128005504005820b02030100d902200500c10030828405174540203042840c010380640300d2000c661150700902181a030514003d451074841040b0004402c20040124240c4030b00a40d9040242030034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 139869451 1250 139868201 139868233
    0x5090c0307030b151c0e10052413051306020c1506040c020316060f06030503120c0a0519090302150901140a09051306030b040c05100206070807200a05 66
    0x721004441c042c8050909002528012004595098490109100c00610070840e18001b4003005501341c0454080d825001d061810a81c00c0240640e10880201d07001d4000c2400380842c5011809000e43c5c48251101110050205548401c1d0004140314100030221a240c4454069070b01c070302c403905030036801800d04c06540200c40c8081d079080300c411917091009480c8810001d68a005e5580030701c88114076100b01c00100b28455100c01c9407214440c1c0d09201e8242d590a00c1901c039048000d80003102080b5200041b00c0103000b80440b030100344242ca079942804045031003000080000d50380c01c01800620013020002d40c2d50500b000c25401c0c138990816549420580c001000012001c000703c000704004e001040e009500b014800d019214189c070b40f050091200880d00000d06416840605410030b40000c0c481400944001c43c0d09036203040e103041030688400d80089030b840004681075400501403401088030342e4821000003420040e030314a442c94000d0582527603400c0501c007201c12501940440518041000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 139870701 1250 139869451 139869461
    0x8031006080601110709150f0303030b010f02030405030703030e1809010b03010e210703020a140d03180309050928020c0106120323120a06090b030705060f09030705090c030703 77
    0x2804e00c0c014a044c0070700c0103c15034442890080841251700c800309811000c511941703040040c0340c21030140800c0d030f54034140a0010100c21105500152a01d040348400380d00000031141214000340c02002c0c00d51554a0880c2c00f1100800790036800344080251010b02d8500410b0b880c020a640300001400d0b0124604260071120410559a1240c2029010100b003004894004a4041010a074240d0307550781c1c2c2c64220f0400700c500c0b00050004800c0075100241210010351950340e601662020001541e003068408402c00d51041d004000480484051045003840c1d4007054000e039001340b054074820603030384408080454131480300c16000c0e408200d5584914090048a00038034000b001600c0f050303c0c42e203009061100c6050080945c1031903503200c400302c03883c4201300d50001783d84050301001400c2004c1d814001d010b031031007089546401c0800e01501c9150101e038030021103000030051850000c80781c00c403100b660000380409a050080540001300c80d1520025070b8031400074a18074a0741d91400000160840d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 139871951 1250 139870701 139870711
    0x705010b100c0c0b0315031b090705030c0318010612060207021504050a0909020d0210080708070801060914030c030a0318090908030703050402040914030a080603010c09120f0803100608 81
    0xb40d64072444007080c0070242d5041994501c80340c0d02e0303807540c58140041305a0307110031600780c040c80740a0103488140e44440385e41100c0700c41203030303c075035030307454103c001c43d100c1c00f090750f0186518004201181c003206546102c1e54030311456200200d034490384e4000401000c80030b2042030301c4068001440108515012807107a1f03a0341103c0c0d0201e0308203405c060101c0d100107a14090034002c141d03200076040942d42e441100e1a032096000f00940030048800f50010702c5800f007950030718040303181517000c42d10190282c049907051300c2050359020a12498a61750420b400c07a403c040075094050760300b082c91192014002005041e0107070311013401100400c0382d20040c20b10154030249860340b525240100042d208011290008918500896181c8035800060000c1800803001480400030440001440b080031001c0e020404043c0c03a2810b50f07694a0052509940900506c0030014502902c2845030030b1181da0118074240c025040c445030b5451650700c1660641c01651510885d002c022402c0040340c0d4403641c0203600c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 139873201 1250 139871951 139871957
    0xd02091504150609030f060906110d1821050f1216020109030c080306040e0a0b09190b0622020409020d0e151501170406091a040f081c020705010b10 65
    0x1c41c0c43c042c0c00402c0104680001007014041c0e6403644180189500504501e641101082040c0c00800402c11000d903c818411030016003000b100039164000b007800c130103030940c000f80c1c80004800003840c0850f4042800601a051042c14050324208044d060094040c02d4a40c3c8030009050404041e40c4580462045100d411a81800e8103400042c2d8401d504458999110044503180d49484000402801c1079007400030031440341d134140906212801003c5806215614156108141e40320103244121090705000b414224009020921504042e07004403050148080740c030300d000a4548403441a613006038040306480381c0124011420320101e00c030b985a80e00140c8001c101403001c503603a10904420050100103101c000d090701fa00300e039005007003022800c448200070030424506403130440000d11030b09200340d401ca4a140c40082d030605003219114021030304410f0306070038000707107135210021540300d4112a02c159001b0181c00f02504224000b801d1254401e90000c1800e140b10414440d007006002c1d098410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 139874451 1250 139873201 139873241
    0x270117160807060509040603050f010b1e010221070b010b03040606060801260f0d030f06060807120203060d020d1202010b03011104090207050a08040308030a06080604200d02091504 79
    0x81d0010024040d0116401c0b418516240d81d026000203009101d146c2c0081e0140c001d58051010f5100103620860761503000f00c503030391003566030010504181a230003240c007400350380320200c0180701800e2042c00c203c114144045d60351428030555503007681e0000a9208590034500807081c03000b04030035400748001800712444d10070305940c0b42180ca007030694003101240c2c0c0800c3d060803070b028104900303100510301c1042c803004440008002c0b41d0014014921441965011850f04e00c0102d12640f044541d58000c03022543d646e490303041c05e0280940290b002504080e4441840d0704040016101c400346100218041c3e0301c203400c500215100a820743d242150aa07100f64900001c4980003841c8405803000e5840c2c090f80141c41e14120b1401e186800c640c4440a00016000b1400208104403440150701c41c0304002401d1103840e6445080d56504c00c001d03a001801e01081a40907500240910074901019400400180101106402040390715006946090361503003000040ca40606260081c0c441500c628128101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 139875701 1250 139874451 139874459
    0x41203020306090424051008010b04060f0b031003020301051503010f050601080a0905070b0d0912020102070f0807020d1205040801060e06090a110d020a0c060606030e06040227011716 80
    0xa21128003e0000301015684c52641403811794400c181d04c4985101d49081006092032595032641028511802c05990309013601400f0303a0802e40215030440701070b8000740c0560382c208407100c081380d08000c008505c2c852805c1e0b80080542c2c2c090141c1801104080e01000c40c410a000515007075807a55801d100203141046c0500800d41d03070201105070b21007094130340080d030000507240c01c50501000703a0000f00000341c08030740003094030b030981c1c842d400305072042442c4100d01c02d5002c820fa080c2c0c0282100a40752400425152000c10120700080003002e100808e00400c1c040303155146108000100305541c00120041801c0c44003510034404d04c00500b070684909403042c5040400610550300c0148205603941d01c1d6982d050b04825008140ea44660710701c042507454014000004003001d440800c151503460400d100083d90340d0107071080220705e00191b8081d201503070721902400884040c8194060480e210160369565240701007241c02d020384094034020340c0e500729404000e464112040084100b100c0609002c00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 139876951 1250 139875701 139875709
    0x1203210612100c0203120103081b0712020d0c120b0f131104150e2e0501020307060b060d02040906090f020306010f0c02010e040906020309071703091e030102070308041203020306 78
    0x3010b03032078800c000400d818664000c101e0a40c01001c086502000a03000080f0821240341d000d02001480c5513140324428801c50035080e82e4002034400c0c014103d281d268024058144042803551082c0210002002329030355075100045c640c01024181d603001c4c1c03114180400c110aa14890342c02021200901420f0300e06600e5500c0c142403640380080c031903a030b941c6048031852000c650050081c0301c000403641a83c41e101400b840141880740d60300400c080700f02426030003031180e09d4070401991010780c000c1d81010740e203641d080020481822660f0b400300e000d0156000c11003d50000f8006403035104000715031949005011810745203031003894200d041c01401042680c3e40d002c0c2100320030146a2a0105946045000584903040c03601001c6402c0b5042840590070700070990020750042038140c0032a1000c81c0c1ccc90000050310102041d82044070b030420840080149404120441c40b01d502c40c24a503405110303200002e0890384000710450120340500204010b00040d18400600c003501420150301e5490120002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 139878201 1250 139876951 139876963
    0x906150a05060901030e0c09011706070318030c0314030a0902030f0a02010e060d0b031027080a05090307080a060608060c03090601061407060906061a0f0a0e1203210612 74
    0xf99041603611072450170541c4080051a50200001c1c0c008025035031540400c13690001c071940a0348280c032452011401c02407183c845c440065010b04669103e01101d07a038101c60000e041c81c07080d82045000d050180700c504080008500801420000051076900c3d44145420300e40072496078040ea4010100e64005070b600140e071f0b41c40742e2400f200c40703aa41e25520043c0c40000d00050840701d030140300b4182c0c0c0da0301c4028103034000120441c01c0f201c00c4a0548040d140d9411100324600c0c000c0200105204164440d1300440250102950080603203503501c1d08d4901c2c1c585440d001c894180c80503504d1700d200f00068001070080d680c02504500c00c2914514010110b540c3d00e85042c800d0030204140041d60078095007900080d00c3d0303420361000c4203004a2489007000000b91043d40604820b040034555101c0c0b20700b00f44e0301102c506da06100c00b881d080c01144201500c0da1078910203003079000380140a880c20429410710090091100f91420503024550300103100f0b140120040c0f505000d039200451402c80d0240000d0b41c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 139879451 1250 139878201 139878217
    0x10f02090307060c140615090c1c020306041103131703041703150622052e0c02092809050a12031d0a060f0203101206060e0906150a0506 60
    0x40f100d1132070032610305102c0b254001c071000d065a00542c0140014040d02000c82400b0300310480e81d4482e01c0e03d4801c2ea0352558030851921910403110511500c0205441e82c01542e4810b070005e01c0003e41c60494502d4020036442254454000341c0700600c14002c00c507804400b00c48082030078100390308602d070a44d2080144551082c0000030040d0100c0003982c60301c00a1840366140c0c00203000d594440407020407140080701080959040354660800206050600341040c0384d4804058001d40341c9016040f030110b446240b05d011000421128005001c0507896040070980101000a66154410003820040d070300300359007000b400b01c3c0e03034144078158003c94000280722091a411095a00030440030b0003040c0d0003030558904a1070700101010010307251041c0450011021800b541c4140302ca4801425240102d120403142c07003603c0781b10301e0b40038411082003091045406205a2001074480d03100c0d805407075001c5089603401344640c0f115040007005254a60200ca04010554010700200e04240002e00c041c012048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 139880701 1250 139879451 139879457
    0x613060f031b0909030e150a0909180b101a03060a0e190c02010606120b0619020f0a06061401080426090603010308090a0e070207140d0c1502010f0209030706 69
    0x340040d49504207951500080503d000b041150310450300d405024840814500c81c8101040303c285c04000c9401021903a0641142d504c180a181c02c10030481d00521040e552034800d5022100b07003030002441424181d02a0181454840c855071034841e4400348403441080e01c403507425043c000e0040300d80780c40ea2524103868242120030708580c1c0708941c10107072200b0305007586c2c0d800c3d040c40101d0404c0b54040d0b11400555083e642d40d6a04140440da0041c02e40761492095500600100041150140c036140729070361034121441a52903d18a03d1500c0d4608543c0403000d80b1203e9075600200030fa00311401c01c001985000382443c11852415446070513075a030700e800051804900140d0900742d0303040f1403011036503640801005191656101d0400d015590000500c07940036210b0030f00003103005007008200310b1060910703600402107141480e00c1d102507104201d694642020040329001c1c00104d441c043d82c00580600c07043e0403221841210003d081d0f652407450000c41d544104101159524007040840640304281 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 139881951 1250 139880701 139880723
    0x2131e060c23150a060504051005010509031002040f050907020c0d03030c0903020303130609050303070506070507021519021b01020a11031e010605030c0a2610020f030613060f03 78
    0x41000d81d903514000d04940b6a9000e01e00380c0c103280039030f0000120702a011040301008660380f20014402100c2041e220701c40c4441c0401420801984038400503e60f122003e01520f0481a16032150390a9800c15008190035007540c00003402203082031086c4580c00f14581c40100100c1c50b0710000b050007031742505000b50030151a4103040f50540e000741000c8005690103000c507031399204894030300d21200d1040d008070310015004c0440080c0390310740042921800ca41142c040c018540b919481501c00c1e0784880401c070f80001d0200c1c40711403a0a0048003805444404030b185800e9000c12800003801c00040c0d80400c224000c401c90100d030166400680610010744c881692402e0900000c0040e190078900000c80300102841c0400400032841074100d5012600c05400f26580c0089010800000b4051030040340c81c1c04090651b02d02e85101c1c0929a03042408c9450143c40b000c00c05c0d03c2840081c3c0c0c1c0030a00ea420900000070521415013441036115a1807a0710300c804002d5681010106940c00ba0944000340504481d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 139883201 1250 139881951 139881983
    0x506090f06101e0315060f14031512010b04061a07150209041b0908070b090405100e13020109080c0d120207091515030501060e010f02030d02131e060c 66
    0x101e03488920140080f0440d400200e45100040c003500784100a6000e00404583c0000d0140c001d00c4006054a038a4071103203411580a502002503410060154120f10521002110983c950001c903040c000c41d010004905088038005210590300c00703501c0482d000385001c4441007100010001c0d101c0ba82d9003c211000c80411083c0c804019001c0d0300b0072540d0092504207440324070904c4070282c15a10005031542d0340030310b40c0d07000581d4468410f4451250702003002c00800700701c3e01c0c01c0c1c4d101c254000c2d17114444d04500d5444440c0d0700c030803ca048400040482e03400e14104255030700442180001e007883d0009140d1120103501107801d4030b405100003410314548113140c948041c0280490b41c003509451008028012814218a0103401039100c0c4420b14800b0320314501d15244a030140d1816902180c07203105034400b01d5801140e010104000e14400c602007841804410801800207001181c5c11000c40d80016052442070115018140c0610794154480380007080b005030000c0105040c90703000400713900c00c0020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 139884451 1250 139883201 139883207
    0x60f09060e0409032102031009021207030908070507080105101a0403030c0201090e040605010e0a05060a0e060604030c1217130522051602160506030105060703020f0d020a02040506090f0610 83
    0x140d090240e85a03001741c000d1a000c080030781c2c003070751055802094064159683d075060394200c4c8603000d0016a403903c0000002d010302e0003500081c65051058000c1c2e450f100c41511b0b00c130301700526500000c03156515202805544135061283c00c1c0501f0b01c102c4145c040340c03140001d4031051300c01d62100809210921000500b50f80c01010750700300a221510762100c0e285000c0c94040c0013851709010b00d04030701040134080380c4031400178800d5621804000e8500410035084c00d08a03445103100414296005504010101c0000e10349401c000c02400710396801222103100745424881d1262454641c400c0240603c85076001600341c40085040b6001900c0e441c01d40c0250307810300542d82201d900d40d415071906140c1800490400b6040850203981d1590030366150040c412900014107402d0310590b1351080c802d000611642c64042c00410f041c0c1c0c468011203d84846000005003080f944d480120090f8005950b00003e600381800780a0380b04100b220041203902d01201d01d80c24044018188034011f4450f65100700040b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 139885701 1250 139884451 139884467
    0x12032b02090307080604120314040f05190605011505030405060a0207020a05060a0e0114030601050d020c190302300307030c02070e0c0c010605030321040501060b04030804060f09060e040903 83
    0x4000e8180c0300702d90f0300c841d40c490f45e07a14159011107503855010344d40301e400c502c6442640b0310783c3c442440b50041354850352509050b801c1051026112801504920488a40c2079503210b1034075440f50801080c0c1e0f6141c8031810142019101d104402d10408004210000d200030500c164400c042107401a02c45400c0e00200303680c1da42581129802510010356443e5540e00840b50000703191003660756460b0481c01c2e15003036100f8041038a119020503402c0c0401c440141c2980c02070003a5004000446107026002ca0304a080e848031004141c002d83c02c0200075214600d03280708107114040c01401190941c14440341011100e02c4020111010076130746500201c4400e1013030001c48024110401001c5841c1070080303040305994010595001690f00e00300f4002201d0034088142c0d05010f185810186000c112010344100800000340112429582c2d01d50200740441c00300050806180195051925241000006880020112800800d2002c004020455140d00111030641091700b5030300451420b10f285026100c00e2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 139886951 1250 139885701 139885717
    0x212030c030a050c1e0c0f060c01090b0f0f070905012007060503090c0108040503090603040807080309103b0114130b01150e150c160512032b02 63
    0x2010000e060303140c05903c800904400b094010a581101c14003800f409001d80800300c051001d40c000781c1024800380f074441e106440c1d142c00604550714083e25280240d0031120141411680320311040309000c9075a0312105c501d40c0c840005000450a400c2510001d032504c41780c0d1242a0400c80a40902060b03486162040c0d80120001422201c1c0e10303403203c4c4041d1841e0012113541d07440c0d200d9200342035420f40c81820000e0144d6008000b035480c0c400c2030014450395a0009009440c100c004116500015800707000640c42846040040c01c0c0d014420a02481918100112402c98100c0a80545412441ca06410690070f000008003e00c501e0b410000902502000c5807006401c0d440b4410003c1684810445400451040e054401079a803a40416405003001010b00d03400650903040362507041c1003100900e4050343d800c0c0400341c01e003000c80100c0e40c0303082c1c46904030f15038002207400708210030708001c142581c1d4903510b00d000d141001c0c2c100700b0070420030940c02d0403903492460852403003501c13443da6030480b40c4203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 139888201 1250 139886951 139886953
    0x1703190504050601140a030c1403160603060302090a0b101d0d0305090306010602030f04120c050a03080d0b061c02030a060e010605270d0b1f0801060302030c09090304030212030c 78
    0xe29050030300580f100000d114450f00daa000e981030140a280c8004890252079105586c121400d0602c600301c02d000a04680c10340e01441400351880c4440400599000201669900404d0340c80c154410b1124203100604515003071800e1008010840d40c551050311100d00381c92034900002c00c1807000c00c0d4950302d840910705801c051020040350a250b4858010203000d03d083c1d040300c1d881d0340d881d1000c0340c3d0ba120380445d40c42031140c03d00c02400070801c485213040c440390040031902d021070340310400100140d0840c2c1c42298005400242c103050a44070380203c0880d0340040f40c5403802c2501c071241410081001941254115500100081c00418191301a00290070f05904500b603c1d0f864040160403580103038001012a01d110341941101c0d0306e515101c0b4440540541085426115a500d030390241a001d04500c40202e0350104035100c264034040064000d060801c004100c040c41d50040c10b0138182107091650007036803190300b04040d600f000401c0324110b80e41030f81e030080d40402c201038190a5004d0016070700c241d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 139889451 1250 139888201 139888211
    0x70f02040e0709110c0d050a1e03020705010b0a0608180a08070f020102060a06030f03080a021902030a0f02070e040b060a170d08010b090a030305030604020c010f020d1107170319 78
    0x40341c000051980c0503a000c12404000c61030750107140d02801e005485040742280e2000b140f1446251090b4040d0070000d015003414990520300441d405078442c120342503003001907408504081804024003940203900400e580d4441d599050001c0140030384c41c01007105401c00798010305140e29440402c05d20f01069000504141c44180c2840d000c80183d003410020780c01803141001081607403810707110f200120ba60040d0038000741900382d038090315158002807a1112041d070a10140d200c0c422500302c040142c500d1a03015581c0c0c1e400c01070780680788402002e0f2190855002000a100110081c031600380c2190304608900200c1e41c600703002a000d00b80c1174210b05445101420305c1c007222800024030708007038011502d918811360f807030b10210071003406009107869211000103002c0021034003800065070401e101074005031520f090707610b0b03c1e42541d0f422000c08124542c0002d0b180c0040d00c45105103030148031405080b519010361038440507010b80001815080c40480000400c4444580c0850300100c44045041800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 139890701 1250 139889451 139889471
    0x10306020403030e10020606040510080a0f0521030a0f0603230d0305090307020d020418031101151a0315120c130209210c030312090c060a0c0206070f0204 68
    0x10350840e02c0200c0c0440e9448030641641d18160140c014081e150354000c050fa66101d004001c041c000203411000017030184c03031010800107414003500384890300640e0007080c4101c040c94214904000f0030251120311a408800c401003080b0542140c1c0c11081240010400b0041c82c4588401403880c1d80c0028104868180d07100306810060030b03030090110b40b4a040d141c0842c0281c60507415103104a0b0040f90740c0d08100082001840d0180740f91103d640007410016980d002200034000c01040a1810f03404a074210f000181480424000c5002c01d6200302c0a83c56224500038024880c0c2c40d202c009003100d4a404030004020703001d0038802c03d00a1200404212442022085080d10b501442c2c0e011030003640d440d0058112040301d4000c903481198003070040b400d036040b40081802c101e82800c201404ca8010380d00326010750360f01040580894889500c0314001420211020b624061003802010300510040c0820003a10344c00c00f0380246c0058054500690360b82c01c620741026605d000b510300070341c000d203002a010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 139891951 1250 139890701 139890713
    0x19020c1e010e0105070f0e030c13020d0f0c020c1c0507050112020c0123130201090b0901050403020d0506061008010e0703020a120e011e060807060e0303070807034a0d0501050103 78
    0x100e03110700340c56203190b07447d22000303041d11101d48403420342d0000c0c0c86004400400320b465000700303801d410300000000c1d640f44051040c1309440d15500d42c2c0005910460514076246001c50f00c0c0c210003400354016071000021a651151034000602c155070601655409168040070750f074048a02c0000c002c4000c22440117035100c0a0204027040e200c440481015100088003551070190b40e030411a016164840c58505d00703e040c12541c2e000440076410002e062000100580300c00e508103005070311880140c0f106203041010301c07030b6400410314940100400b00c2c1c0104445409103c401b07030048003510b00503a84504048040c5e0340c1c55200a520300d12540f070082141c00864040d0b21078607100b07079010401c1d40154054005c0307805848c043c0c080c4412540010000b00007160145070400304084000e01981d041409507200c0e2803154000c0c480503404264003458140c078417061042c030501147c103582c402034020204203003111084001d500d114080c80d1190119021941d0b10380e01680d014550260082c015581c59280c04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 139893201 1250 139891951 139891967
    0x91003051e0106230313060c0c05060a0609150608040210300b0604050604090903030b1f0f08090a0308070e031002090f01020c0102150709030c030b19020c1e010e010507 74
    0x5811603038070601a40920242c00c101c138040c0154102ca010004803981f9103a006003204d585010500c41e011580c3e0001690034050702d4468102c1080001d1201d1801c8442410744d1482d5455115050fa034200510145400604003a00a5010303203403001d1403c2c218600f40c4004104c1c0c400020040508010002185a480081c640d024a800400c0c84030100050522006010714020241d006c0c01c248818003100d541070340a281e03440d010745004104070244c100824070700002105000c102d024160960002c040c0c100441d005005041d01e007000341490010301c2d80d81c450720010002800c01454001281e03043e0700c1841c1c202d03440743c401405d5955040d1011b00c0710000b5880001c585004103604409002550f001040000c03040b02e06801411181400c0c042010075038000400b100140201504080b010070b10b8001d9000c05980b04026101c1103040001c0d89000f4401c0b50580444514010000c04210030001700d140380b080c1007114607851805da5030000881c0074103043c07250680f0350b6284c071042003041c0da444001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 139894451 1250 139893201 139893227
    0x603090c170d020f01060b0d0e10020a050c070501020703080f0c0111031911030c0406080c1608040504051311060d09121710030c1a131503060b091003051e0106 70
    0xc4442c640000007aa85c2030f59801c4c803d41c040c0c0f00d41400380c0c041068446e000a01c00040d100280e407446040740072100d0803600004400c4000a0010462a506c0d11003005110040c16090004042c400d20b16902d26041e441054400d03890341c0c00c041000758002200350842d50035209440c0d42e2a440345000110000000701c407074450607045041c0040042001c1c11b00c13040701e01846d24206207601c0d00d4103025055030190005840e482c0c1d81801040482c0c00c0c400c007a01140c013001d02c149130b030b565603030b14180070401a80c1c070103841c00a0a0944c05d02e508001820301070380d602d2030310341590525203404400410b6030007885020005030100745144400c510303e44d404070800c5104150704040c1a501d0702c400b2807034810704440d4000184007441101c01802114610b0040c80032001440143ca45000c48124100080e5850f90703008110071801e1110748200030740c01d4050103025100d0500380340e003408160b50004120440e001c000c0c0e000d065544005c150744040241900c100c151000e0310003201c9503513404006203050f501c00d030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 139895701 1250 139894451 139894453
    0x60b0414071e0503060d0303020a090e13210906030b060d05010b0d06060f0c0308040f06151404020a0801090906060f06050a020c1c020121290402030c040603090c170d02 74
    0x184101e00d0760240f000e4034020074000d02150407484050f0b03010b400075405017176803005000c00c4e00c60000701008a6910144030b5010000d045102e03104608c2d05142d2030303542ca28076003140c1d41244900040315912071300c1001200c1e803a00c0c0c041455003580300421110301c503980501c000e55041070004500d004082c0c000f000c080c1c07006034040000c1d66480c541150040340501041c00024182104040842d115044550300a0b004ea007109007404403d0303491500700e466100808480c030340441810810850f4842104152001c00d940a618000076400001c00360b02050107000c810b00e40e54039180782070040310381c0104040c006c0702800340c540c0c80e00d4030380c0640b2a410246c100c0b0018801d040c1c0d0983c2a06001d500441142a40381c400002d801c6c207903006450124640b29050b134014444600b460341d40c4030900456440f02145203500c58400301e0280032400c2420040080e501490040040c0021421441d080340d04031580c5280004e01c208251a1a90000b13005512a214501d29030140c40708079100403404420030803250b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 139896951 1250 139895701 139895747
    0xa020a09020702060f0c1005040b04110906030a0b0a0221101d01030602220f03031e09120311100c080603070e0c0c070503070b120c16060b041407 64
    0x110080580c450500002c0d00000c0c21700103282d084c80c102001d0b046441a2505075a420305a003c4c03d4030031100100d4064440304480c00600c01400f00030456004180b500740d0706451b191401070040b070b80d24602d81c42e0040800c500ca01c0003401c0300402c3d5051354025400c0c15070050032201120083c600302132080d503c1d1000113032102c00016030355507418030b0742e070002034529800e5200303a00c2d60311880c00a4000941c021100742880c80030102c0307100b45206a50240605082100f800d40c01c44c2801403013040c04c0c992850341480c1c003403514500705420184103001c40b204504003010258180c6011a155094560109110b100b50329000741c10050b1a04030701601241580d400105903203c404144d5500c0d9244030314100d2a600c1c1001c00c1410086200a0149074100c00445004541d2540400c3c038020300c86d804480f0310b03203000c40c4903415020b03084000c980240004040d10b04141c081c108041c103c0221207401030143e9134410808840352144d40181c019502c1122140c40180b034101800380000000101200e6990540307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 139898201 1250 139896951 139896959
    0x601060305010611071d0606090a0803040918082203140102091c0f150e03040e04060507050705120703260703060f12020d02120f0115051e040c030b03030c0a020a 71
    0x282c003100f11801b800c09046a40001b03107091042810142501c0c0c4c01c0300c4204010422030f11008248801008000c006565035450441003404071030b445c8010980c1d40a288103001c0118010209039080340c2460300c01010704841d4400f20396180c2800d54002058003142c0c2607001ea00e10010b5026005440040d44c80c04a000d9118000121019060b10010001c02d02c61040d4000b0030044e440000d282d58401e0000691801c40c14003040c0b454006500900c0c3d1503050504010811586000d810f4012401e82002810140c8a40d615500c070440c104149140f240c010a00300f0505100710f090f2071220399074401022900c4040060005450b034215055800f1905000d40016216010700c402000c90360071807004242200140d08001d0847d03080d0000f680e1100c075484808400c0c1500703000c4e500249034000000100c0c2c000d92094011250b580d580324610803504500440c0106180d10300c51441714008540001e00c003403d180081c1c0c0188880c40759980c0503c0081410f4609150018000809500840c0c01c804007a6503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 139899451 1250 139898201 139898203
    0x1506180e16081b01030e071202040b0d0816050c04090303050411030607020304050d06020c010203090a0b16090603050612010c05070212010506011b0303110f0403020906030f06061903050601060305010611 89
    0x70307218109065000b4840324089181c0151103c01d0703107005150210300000680f140500d0b00400e40c0140060035a91203240b421450b1503c1a01c03403c81c015517021075000d603641c68085403400380c080c580a00c000040c0110007046801c0c031050300080c070010010413000c6c406060050042500b00d0742180c090100400c0d80751580ba00040d031741e1096095600039031030141014148014000b00c0a000c039503168080c800c08680d040e00b0b0010314480c01165000300300488041c10552440d17070024000170352401039060441c0e8250750008512041d5462803e01066a8880b000030607903a96135101c00390495443c00250904c0c81da482002807098500032108007103074921400d0b01600325035007915400c0c00300b01d2100d4071201d410307204030101000c1d50080c280041c0003164002e03440516031000003440d0040c50005020700440c6004c10081d500850705030000d0045810030a8019504c5401803c0d2610a1504050007400b4a003414400c0e0091a408402c1d9561541c2d07500d8082d002d84020700451000c124416001c01540c04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 139900701 1250 139899451 139899493
    0x13180b04060e0604080d0b010e0d030320040f0b1605010914010b09091c12061203090918200a0803180315040209190515010801080109020901031506180e 67
    0x117000f1400d41d2038030300d421814500503c41081c026043c840d0384c8070340c0315040d681c0301c1d4021030040c0240c40105108004001030601120842c03881101c500341480140b11010042510a00f5601040c0c038a61352040f80d20481e55180d104064024815801c2c040920200f04c10815003444030400c030b0009000381700d140c40400282d0a8100c5455030261312881410b9010600c00810a407400c1c007506000c0352281e00e07440110140d5039207422081c1c802d502c1411030420158404899001004210f4040203c00785800c010240741c0000680036161089241d49151303200c444442115441400400b042005503580e600540c0f6074001c03c02040035840740500e1020396040c0420001024031660006c8521135540340e080000682026209e071124210340b5804640801c0d151191900841620350791454240386103000414011050b008144540d05000403c00103031a840c803094152503000185a2800062a00c4c0318000d182c10351002c01b5100b0307a0203101000c3c09503a80300300b0251070140160381c0d0313404190b20704100f040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 139901951 1250 139900701 139900703
    0x6010501031a0d0f02090a1a01050304050c04050c04050a0306050402210303010b0309150f040b160c020f0f0604230a0e0a0510050306070201020a080f01060e13180b04060e0604 77
    0x4034041e0400c440b07510300300d08850a082e1261004150500c0300d45c0200352032920440e00707140720b2a500c0b241171380200040c0564143d481c900f4a0030500e03618180c1d54040c0c41b91010440c031401551a480421440c80700c09007603501600c0087e00c418121036036030900341c0c054030f0182c0703080e8059201240355400e01030030b8803180e800414019009520390303440d05202e903074a5400188030b00c00754010560402c030204a40798005014890b49001c02e40c460800b81860340c0c54420181c6280350030802807015181c11904054040c0c2101d070103e400482401d12940460060f100720550746070b21460001e000714441c1081d11000d100d1000b8020f040740004138010a004107500e450003104c0c0d090510394001030081c01d01c2c1d0000d0382d0261444446480711996100440e291080549070382d00507035000301c0ca40404c40e40c410f940300d40c41035101d00c0e203400347d5240050140102036500185802900584490b19540308950840480e0554100102c003072114107090923a5440001d44048030b406081c83c8501a10160004583c0c0c012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 139903201 1250 139901951 139901981
    0x30f0e070b0901180504110912060609130606150c05070602060603100b0f0307060302091003110409020309160906061d1f2001050103050606030a0b0f0720010c020601050103 76
    0x2c601e00100654800e0955030300400c1e50b620a4502103000c0d02c072030041c1d500c801035440450b03444074240c03c20404205040c00d202c44803540444100300c115039401042c84d0308901d003918442c01c22901401c181000c1e110580140340300c0c1c4641250445d0041d440a00d480c60341d03001c0c505075040540c03a0030040ba00c4e543c09561131581a803002c107418108001c170ba07000300c481480c001e15454641001002003800c100540d401000880d5011800c05c02a083c008482e01d0080c0706461304000b40c6014081c01100ca02950040005c002d50100016140d10401c202081a070001c0c201c49421050343da075075001c05440140a21700c0040c8148040a080701c07503807200d08414002c010800038080c0c0c54010001c2058050f101e08204000049001500b20f401c3c02039800085c0a40c00000300d025810b60030542e240410160000340280e1042d04014086403079100300300d4111080d0254540a0b0322100740880e1140b03429003983d034030140c0c9c804252483c05d1056015007036050064080d980c450380d9641c015800c4607903e000b13503144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 139904451 1250 139903201 139903207
    0xa2606040b01060e040b09070e0f0f0105030406091a090703020103060b032a13030b0603010b01020a030c0f030c0206031f060207060c060b1908030304031202070c050d03020a05010c030f0e070b 84
    0x3c4078042d4640014010b000b80c00000c0c203818903030000e034000d082552070700701003500d4074204074640c00c0c52014503190380d200345c403688400707481c030b0000030113602c0000c0015040541d03458904082125082886401144c051483d4009003400f03034a154485c0c050348401c038003081c0b81440008020701408140ca204040154110f8000c2c40e00411103003848a0700c2d6000d0b0401d44e410420f1030094181c200d00708000c3d5004079284151868404141400c5620f00b201c2c203415035120501c940c0020354400401400d0507446090000c0e604002d00e01582d401d0f002170002035000c8004820840c0d80d4000b0210025403285030325a0403110f50740c1c1c41c1d0a03620b500c1a4000c6e076000958541c18000483d0b515044940b0794180a4400e406040d501800c05000301d2154000072640c2c0c1000041c441030560110508c40036843c4140d0444ca804680d90302c040400c5403a01c58940140142881d040526009202c80071701e554122000313010000d00190010000e05003400810805464120344d10301d1103500040f24000c2e030301c1c00403456103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 139905701 1250 139904451 139904459
    0x506011e05010f0f2a030e03011b110f0105130303051006090504150e04060e07080c0a15021e0102090118050303180604090905150f1311030109020a2606040b01 70
    0x681030102a400da00b0300103010000c3d902180d181c071783d60010a58184c4960701c400a03518000302070b05041183c03584261b041590b00c4110a00b030f2001d0507124420341c1080c2c0c070141031050b103507401c102c0c4400340c1c02000d510348410441d02e800d4072134505000600c42e070740420460b40c8000c60341c5a0700503c1c0c0140800289828400e0003c0e003400c0d803040b0001254518a201556500c40030748074402c0c0200c2d4116030a9440b4401c0580d80c500401518001d00140350280404210240116045548605c0f84841c0706449003800d00c0854002d10002c0c09201d49001400008405440581d020350b205076a41c0740000c01c040030301949501505482d005943e4020082c52070104106035801d10b015048000b140e100d8400c01000402c0c80441c40380030090b0340310310b018010541c400558030000c280000c1002101110200802c003280c2e0001c0c00d03045c5001c0e8000d12101d40d155000c070200b80103140d4540001e4200542660105042c8140010f0f81d01c80f0502e0b5004a10b4407021300702040d1504403c0e54028140700c2e4000040c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 139906951 1250 139905701 139905707
    0x30209100305010516140c030a0f030b0301020a18081906050a18030903120e030a02010804170d05040b18150417040b030603070501110a0b15030106030506011e05010f 73
    0x540204000c03249424140e1a41c8506007103d1081c1e54980342c4082041240510350b4100ea000c00c18070981103003503810b09881c0d0750000e1300c1c0e1042e071031400104084104840d850902a5000d18010040600210340f603249191011b4650700c1030314072840b501c6680450005409000044c410380c140600074030000f91046650340d60024003c0a13010385085030300c0c1e04031002c1450a4601191100d400b0355240244503245052980448c0c00d040e003a01c08002c480c12042486407030004001400c99130a103005402a80c4078103040c8100c05402031401c1c0e041c1400105504821183d4002e180614018100c4540a480e04c40200d00640004c9080c0ba07031a4000e500e01000307040032040803641c8540105410121071510301e54690341548603400607018558080244200c03400d003080a00044d001c00e00700015060201000e4603515052054000e140e0000070001a0aa515480390ba0341da4490241c0244a601e03100c0c503200d5182d100c2402120f20000340d040000c441d000d820051a000c03114180c46403224100d4000c412 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 139908201 1250 139906951 139906969
    0x6010c030e0a0803120a2405012f0a061406010903081303020409030926030301170106031703040201021605060307030902030c09160e1503060103090302100f06060e030607090302 78
    0x401d52100c254500010340f00400c1c0000c010483c066144442c003450403103000e0040707410310400d04407004025140203140680410502003511401d0030300c50000880b800e0041181d41281c034800b038503005034442d20403100b54001042c07400f1900c241c100f07200150b0200b00341c80480b0812210a030000d40120300c208086a01c0b8030042c82001e000c00b051100d400d07280c1e00882e0940340740301812030001d0b51280041102005040c10541002441c080e50016a8910004580d5a0006005142c0d810082c07001c1291a0301d4254441e500031a80300d510342200c1c0024000701c1e40c041e00219030503030142c096081e041044540c1d0341080e5054801c020300c0581142c403548000c4004001d401c03030480c2c0611580ea07061605070341301e0003a180300b4a03844400c41031400004000504040c201e02c0034078010305000302e031028000d6054069960240c404c1c03070005982c03c80742c14102d1401d85809520b11281e0328165000c0f45d06500740e0080c80941c3d01c261a2840840c42c0c680c14156103410481c0d0b1040011103007602800107103031081c26 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 139909451 1250 139908201 139908227
    0x41a0a0515070b010e04170703080402061b0a060f11030c0d09020a0302120601090b040b01091418010303050909010f05010c0204050601180f0e07020105041a0406020d0513061406010c03 81
    0x1402d040c041a90fa56414101c030a8101545a040c4401080100301654920800365400c84050034142802580c010780751180143c80248104804111a102c40001c014800c000c070304448100c99404025040c404003c05420204034501c60030110401c00c81c40703503641281d00a04000e0031040c81c0c884002000b00081ca005c40e41243c0c8181c21060000c0075039110a06204080d81c0c8002034038403540341110b0700045800300e00d4084d004506241056549a8011140404407085c803100742c000003183c140000c059000c3c04088403c0074180f1400801815030100207840100c10540ba8408107988400b90040c0604082c41224002403444103a2401420316230403040c2c0108060608001c921102c6002c541150708580005110b080751032410041c555074042c10b56089010b40c002080302e400d140e220728426110b101d47d262140d46605020030100a59903046600100144800b0805420584a640d500389085002540c8007400c0c1042801041c0e10b51124501a040585541c400748086580940d40c0510640e6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 139910701 1250 139909451 139909489
    0xf0903072006030a0c030627050c0903060702030d0c09030b0c0c07050a06030f06171507021f05010602060702010c0801060e03010b03030a05040f090b0f090c0d09030e041a0a05 77
    0x980281e4540b181c6001d98021003401401061074104ca410040480e4019409601d1206195050702403a64142000d1011080006004211940e0301030401e01d180c0300d60384240780c141c030891080101a60740400500840d06030250284100c480300102260032480c1b900000e0011855100420201e600d540c00808078600100c0c2500c000542e80c0002a41c0e290f4154071840c04242c0310f86902c1da0040b42c5106090240021042d0883c5103210102201d03640d0074044e109480e56814103012a05882c0200f01c8050014450303942d1240d42151800018082c000c28460700000d44541000b02d10301e01d00600500e5500c10096a424405030f18040d4115241c08803440110b415550742e40ea901603984042c0002c3c583d281c125120030740e071949440c5958202211650045a4142c40c00c3c1e409180780d5100d41c9049010102100c45407059110017040d040c2620650440d2011030303142000f00b500301504004e5061484004035000c0040041903440b03d03180242c0b030f07401e07264042d500f07480500407460091b03251101000085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 139911951 1250 139910701 139910753
    0x1902010e070602030408010b040e100b0a030f05030d06060201181e080708030f0c0705030f070305040e130302100b0f060d06080d0804120f1b0602090301060306140f090307 75
    0x100d8203506001c0c1c0e0350802c10041c2c10001e030622a1200900440505c054180c5040240c2c4000603042525407124040541203e600e0311a0003a00d5136503500d000c0044c54002108110b0a1118902075076264002e112803138000e41440c0f0006034031401071003164817000d0015540c0510070f0741551240e010080701e103408004454600d03c41008100b0a40c040c10805100f080c0a9a5a04041321a11302042c0001c0000c07002074420803603000021008010346181e082105282c540716a524903050392507020b2034200024a038130110810146003400320400c100d030340c0a41c0903101d010341c40203060000d442031011440d4021040382521151414007400a010b401251000003802c684c550f0700c25420701c509100a200012200d20500060100000200200c0041400c0c4015240d410010181c00202010b10103440450300c405a0410300110790101e80062000034020010261030340b500b01e00a0445503101c0f9100301d0740f40b000481480b081007446008809100c02941040302542c0c030244411030b102920001c490b504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 139913201 1250 139911951 139911971
    0x70905011e11010c03020403020a14030a0618020d03050702040f050c0403080d020d091407050a0609090903120e03181212070c0e010e010305010f2f130608091b06190201 74
    0x2132042c004040c2072583c0142c0e940d842c0d40108110142c8c01d070081d84443c955501501c400381e500040c4240c4103503100c1e03004640e800c1809400040e0100f110b0f4003941112034030030f100003003591200041005a00c02c03a020401d541168100f241120030071910110954010803040c80400c40d540c0150423503036100403015103003000c0400090103803a000f51044074250008011805c150406000540c0a007a060f15000703136662420704000d00c02000d900c1040d10944c1c6d5002038000b0b1600c0380c0e5000c94100c4604605101040f11080155a29031000203034031540300b40800c528032245030010030f039500b007600c0c02c0061049825420303020100e6800004216088540382000041c114400141035000b064442d030304007800e40c0b5506281342540e40b03440c001c2c1d01180c58029180348039915444444644414a4079031000ca03020724038101a1032090020f668110002140001080ca501040d010b00c903071071101c1036502c000e8060300440940b80341c0701c0d1440c0e0f01600911000400403241021600803049510010600503c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 139914451 1250 139913201 139913203
    0xf0209060d0504140303090307030e030321070e0a0302030c040b01121107060e06160e0303040b0d1d0d090b030604110a0804030206130b1308130b070b070905011e11 72
    0x8007080300712181d02d40d003c00091000440b455100640504082d510350f141002d091901c0f071141c1c0c0402401d00641c07012040b185d40b4200162401d10300d00082c0c1e44601e4008038812031007648111200c000040881c0814000c609000000404132580a0000e180d031840b920200000f0b0701e080c0750030504120b10310340031107c04809405078268640f0b1084000d036484129050541c140c559001f040300141d40240c4c14010302c0755800341402c040382c005103030441c0404120750000c2d00f50710483c1d0010700c03c098081102a00003407107030702a1038000a0840b21116041061092a0322400003896040100300d410104026000100005550001000704002a801404042000c07075400227003008001a1a1004000c100f580401001d60080d6242196564441807981c60040f0300d0b00c01000f0f0f01138881900405010040000d05440010041c4403c040c2d55945500d080c0d4141d811024065610000200105042c903029580d00800e07202c041e034031140007000040c950105c544158ad150010003101d0306840744c1c0110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 139915701 1250 139914451 139914457
    0x10c06180c06080723030a0b01030e070e010e062d010203070605010605031803090f0d020310060b12100501091211060d090203070902030f0624070b160207060f030f020906 75
    0x903a2103042903410101401020080740f22400090551806005c40c01c0601c0001a207038012081031011030045d107035000480280c0032250303c0000c203205840b40805e10004180005040ea41e0311a4100710a135115810800f00d010303921410340c140c2e41c140c40150503841040720040340010040c01202c0c503040e442d98400c02203800c01d0740064000340d404410310040504032111210600d002d00015410002843d0005042175003519180d4803612201a2040071510b060020369104400c484040000543c2c0701200d000944c80441130340c1c9042c000c0400103482c2c0c5100d44d150800c4d550107035208039401c0d08002c2c080710071f5031054200b915085c5030180c44080594642c2c0060954400c11480407076008082d10626203044000c1d0014000369005100b0840b4000000bc2d02c5940007504a40d0344400b60100355420001c21509440910281e100050031001c0c03000080200d80100a01406d08180e64084401203894584501600c000506000c030340d44003c41c440c0d001044100781d264001442c05003a04000f030f100e54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 139916951 1250 139915701 139915709
    0xd0c0b0a080a0b01180b07031101060303020c1f0905060306190803130b030f0601050304080c0d0f09050d0c0603050709080109060c080603060f0408070c0504090c050a050609010c06180c 81
    0x90300d01e004100d107098040c003840303c1c0c4242c00c2c2000328485034503911901a10801c0c0c0070f4000c2140300814040300303140c07140001d040c000d86000000c0040c01c4c0c40b810000d46480400031000d0113403030846660b003900c0c4245040004490b460f1ba5480030024240003c015142d0320203400703182e00400402c00c0d850103412201301c3c00014501c44009542e036400f002c0d040c5440c800c0710350055100100500401c040b64075aa95804e41c815401d181150303803a0344911b4158000d00602802004510804090360f142a8000100041d41891916a078085030703618170400130001070282e002803044214800400486000e50081908460603040c405102034940003094212141d420060300e2090b11079844d25551a040318591303810080941c040c007200c3c6000b000240200402800040610700300180e00010f206002000a0180600400a02c411607041c14006a22040341c003800d0b100d490702c03050003d120320f06802161601141078540e101c0891094a40d0802080c2d02100740d45400c0d80c11105500041e0000354181c060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 139918201 1250 139916951 139916957
    0x51c120c020c030601060903150504052401090b060304030c1202070801140a112a1207061406010305090d08060a030c06050c070609061202070c2304110909060d0c0b0a 73
    0x2c8082003054907043d4113034425014448884400d0000c1503070940038401d4010240c0012130342d61500d00e051444c00030003818010840c0b60100392014441010001141200d086a209100c46091842081003070b05c4292001000304080000c80d4002030308403803c941070140d450045d111419940c1405909444031208024280c0e04c0c0e803c2002086071851295201498103040c2090402c007650040030b84004601c200c040110102c00705010303200100300b00a004900c401400c40e5100c4d480b42c81c1c2140a030000c2448075101c2d48901000034000d5109102e00d41c8242009070080440540d100d0058600c01000751170b03e07400030b00440c80840410814110100249516a102c941e900300c1e581c002c501b400001d822420411407408420003205a000012400003821010010380e540f0092516207060303155640404034060300080786608403490141c21a50700c11044e0b405001030000c00110117154800c15001c140e201d0210404100c460804014021300c10307105000d01d8094a0720340da080c200d142c0041c5184000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 139919451 1250 139918201 139918213
    0x1506040801090b090307020a0611030c070b0315181308070c270605090a052707050307060216140d050a0b071106040203071802090604030c05010912051c120c02 70
    0x400ca041d950840c3d1107130742031003d5410148584d000031001d0626115000402c624a10a244000b405000b10f4002d000d0700e030f044039091903807181e0100d502e0304106c550468800b00c5000040301405c124601c070301c2d211602210310415544c0c01c007240c0c0c902044c3d00d1b0309848440c0705021940016210140420103042030503805055405002c410501100102071400011824500104101d4403101c94040c0c021000410204503555422244102406c0340b500a4910075038080d0f060712110b0002c1f80364400d480e81038056803400c5866403020381e651010340c400d00c8528040c08408001449401181c0c0011050042a4401813600303501c5444c078000c0030800030b40f1001200c0c1c0c140802c80d604592981070004680c0041c107110b11f043d40000b07803100654410320300702c600700002150340f14400fa4101e0f403000740020302d0f0b20b48441e228241415444542c0c05464040340c2001e802007403003160015030203146644803004100309118062080c1012103040d014400b480a460290300c1c02003081c0c0074024020104c0d50007401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 139920701 1250 139919451 139919453
    0x12040b040209090d080a0903110a03080105030106060e1c020609060a030204051009030302100e1c03090b0c040308070f0203010b060f0702030114090a030c0804030203010509031207020706050909150604080109 91
    0xc510018083c0e00965024818100e81150012002984448180000031b030300c07145420244d403aa40314100300b007054001c103a030030000c040c0c0080c55903068800c01d900030442a500c810080e5500c0341c0c0c030064075900440b8000710103002c1c4d11445401c02403030320140100d8140240e41000c03c201d03801a00d05000445c2e0040703014406401d1090300d0030000c22603480c2103566a071550720080d4680601409051040d43c031a03051a103510020002c09031410801c0788140c50340c45803010003c00030000c20a0880d0145d280d20b012591030000201034505681d0081403061501c2075582e034421000d00c11910807038141d5250340c80000b80765903000140101400f503e54450b6140003610402d400c4802c48a01e00c2a1840a071050016607840001c1e9a498203a2606000805100d40e0418412074001c1c2e0340000e42c19070a0104109030450048050500081800f20204154a40c0c12081e1780300ea003036011f0740c00015418840800c807490710042064220b03044200745000200c8031004100705074440c0d041498240e449000c014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 139921951 1250 139920701 139920709
    0x30615080c0303070b13050703020312120604050c091210050a060303110706080115020c10050403170304080a0311070f080c072312100203090109030e090f0703020f12040b0402 77
    0x740d4801100a50b00d041020b40c0e5a1000c0600504506507140e038800d40d5804116040080e02d024640080458822a0416200c40429401962007007520010203000c552a400d05003e440c2c094000300014508101880090055280034031084803800c0c0b01e58041400c40704024400c0500420030f012020903610300303504000c0c101c02484a0310f00706540c001d203410000b040d030142d0128191590100c402c42d5082200074100e2510800500c0d490388940081c060000c00d0b5044001082268031800704009010502130100b000b500044030064807440d000c010014001744a540081d1007464400900c0382003428503280d50000e0103e01c4022074610000045d0420402010801100100a140821401c2c21040f48500d502c0d030100e8a5042d02400d11074081c82552002485000500100d400d8110340300d01d491601d050180100380c0050300464050301c40001e06080c9400004d1188039004182c0d00da03610f6000c0c04400075030058180d00394248050000b58003a0020385042c40c0a140201c6051519040070300401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 139923201 1250 139921951 139921963
    0x3230f040227070f0f09061b0204061202030d1409040f1e09110307050307120303180c090b060f031321030203060307080a05070b030703060f120638060403061508 71
    0x304240194521000c4920f54406c100a0940780035142c55449105201a000307515440071000a60050902e080465030b500171000c138440650080b01101c03941c84d07000001b958100f403010301d02850b807481080f600c0c110742425041100100c451a000191407002c80480e81100c0c40c000340c1c00c1e00c070030b6190f00045091100c50004800604d1045015014442c5040002035984080d031241094901d0158905d40905000b94804c94490744611481581c151440ca00040000c0e01d5005170788407240303414450340590030101e090328146001e020140340b45031290800011100740500d0b0860b03000440c90320302c10031154010031410721000540c6000d40c880c01c240b070400d03080100c140c0044226511400422001c60000664002110f00d4032814a650751502078084025007072a4111100c062007020380080c0307511550000c06d00003070090804000001041c002500c984080580c445d0030844099584003d00e845906001c1c0311070001404940303400d689079031789010b8901811480d89041c61002042120314018400307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 139924451 1250 139923201 139923227
    0xc030c030608061e0405010209060301030311010608031e070f02100e040e03090607080a050405030a11030c011e050d020912060108060108070303050a05030718030b01050103230f04022707 82
    0x60319081c40c0401d0b07039240e14552440c074601d500044c20042024494294100c03015070401421942d40ca40e10ad0a002e0004031400100f0006d0358078240c0e0011380c00c030002c0b007a11814055060b051601d031204101a40340d40d040140c3c152400540401d005006a44801601d00488629124106820040070400040320407200038140e09400403c8071b00f0059071584121001035520001081c1c540c62009021106400350b900714540501c00c0b0039415051091213451009080030880c202e4a0b485104030045031078000380c41080b04020020014000154001d04c0034102c1c001d03074210011b04214108000a25031801a18101600d802080050207c0c00c801c1c420701d400341110300001c054040c510354000b03003d407107059003100c10000e0100220b10800d103c2c00101d1100b40501265030949500e90410203003c41080c810306021a00d00340500c0b04200306500d4603510f0354002594210290b951801801044100900c2240c0c04000402000425003a010111880c6000411642c8407072404d8a8042e004064800d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 139925701 1250 139924451 139924453
    0xe16020304031523090106170c1003020a0302090d081b03030408071704080f06010f090c05040b0703140a081f0311121c080a110c100504080702040c030c030608 70
    0x814004219140c81456004030301c5440042d4041d42d685043c8444c0402491004190f6000c00c103000c059041504a03500b6621500011760210315600340d240e907240f00820259411140c4c7e10f02441c0224001c4d0b000c2c10070070320141000b601d4a0080800908041d01c80001240c0204010506800c40380361210380b83c030300c04a070740015840d43c201a140c0a000d4081c0b2100285210302e00c0008038150811130b01950020080601101c0064000c10030300354032000c09000300c4030388050340800050041018050981d840e400ea0301c0c0d41e807074a41482c4e1310a0880c1d001840590622031005140500002c210004000fa20550790391840c550034032008100101d802031030b0050000c1009141880400e10501010b005074108554084082c94403040d0103080100b040c0b5800b10096840840c0118035820008043c81070190340d00c00c20404020104890ba00d001c0d8400b046016803040551512403213880e03011300e030060700070040700e818140994000360944485401140000313844005035001c40b9010f0148201411141c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 139926951 1250 139925701 139925707
    0x50d0516060504060914061605010e0d0801051011030915070b010504020f0409180507080106030302190c0b03040f1b0320030d0f09090c020304080601081504020d050f06010e160203 79
    0x40f802820642d0601921b01e10300c5901540d130300316686a008488811202180320700000308241421070090080d4080340f4418041d60b03171301e800180e2150300301740d05a690045ca20030315403013105003c46402c1c0c0c10391444000742c8410060b40103140e0b181c10140160199030b21305160f40b03500d10324040d248a641030748041d00680c01800540001e5003900113880c15581140030010750b440d203100a100794582040b2019019006114020601402c1900b08005590003a000c9520390b40030405121303601c62100502510300090782c83c0034480c40c80e102008680050042b44540c0b004805a02c0d02060240c0c1c008510110b0011020704004003c1c201000c000101120070071044901040c00210343c6402c2c10a606100700200f0401c01a5104d004000ca1800380c155480304020307440303000c1800380d0b49034058000c0da03181d80300c0d180000441d00c44c0010040e13524000000890302a03212682803106c1001840400c80700e50160614010880c40b0401a6a009001c040980340a40c00c0c2020403110a00702d0180580444d0030030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 139928057 1106 139926951 139926959
    0x40609020c2503030c021207080c040b060c060609070c0c0b03010303141813060801020c06060103110403390602030309070504050103030813030207050d0516060504 72
    0x24904441007251400501590000d401c02c00d104225411241480001d02c990b031039000d024405007a52601e40034aa45042c2132040b5500483c0440d0b00c4000d264180f440c00e4050054045800da4a00d0302c2c168040560b00e89505c001011b041c020006070010600042c403a02000b0807507038004078a00c0c450f075281e040000f660382c000c2c4420760000e102d0740440485c900010f002c40e0420039285a0002c440c0011070107103c28000c40d10081020950b440000144a440a00080c28106044006030015107044d4001404440f01769070701c00d8959000380710920014030301c01850310014850a041000001551131284032850540c0302c403c401c490341d904002480ea400102450040701410181d07140c0c80e8441040c00100e610034840540092100d402050408003000c055170002402481540c81d582c0e00c03030f00400d0310482d680d80d04603a154403007840c090300300701d00e8040100541160f1920f1881c003898 = true := by decide +kernel

theorem cover : BRFrame.Cov 139748201 139928057 := by
  have h0 := BRFrame.cov_init 139748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 139748201 ≤ n) (h2 : n < 139928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
