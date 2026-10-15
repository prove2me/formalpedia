-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4899
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:05:52.87698+00:00
-- url     : https://prove2.me/submissions/330622fd-03db-417e-89cf-49803269d8da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 880935251 ≤ n < 881115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 880936501 1250 880935251 880935271
    0x30a140108010527070b031e06010f050415090306050f0103050f150a0203070e0a03080a020c0405060607020d03020f0f0a1a101712030c120f07200a0f03090f0608 71
    0xd0002c515040c04140104e00140344800d03140119070b40d0081e91559402103641d035403800800704078001d400c08103210543d0005000e180003545030b10041e801070514426030040c5031002c3d44401800092501c641290000b4591040081c081410714104640f2110803c0c08220780c14040c9611484103000c00007007602002a0401000540340c0396071083c01b0080d03001920385070800101c2041880541c5900c40310100541c40360300710541e52080d0800082c2000080c8209611617800d0800b80034182c1d031404207450f02c80f901225030002458892030141e10380182c1d1810038515000c1d280291100940c0400c0c030310707002406280340c070005840e609456102c01d00100c82c00303c00760101c3c010901c95600303141c0c9941e00c100303030080803070713071f8010004100c040035400489586d0000c407800550710075443c04039260307181c0101c2c2c000c501c0700300b60600380c20141c0750b16007040404a60380829403268117804d5040112440e6240c00000845403a030503420014074910b030320b00a101036030218000004109108103444c51040caa11a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 880937751 1250 880936501 880936531
    0xa06080f33042d0c090b0d0e0c0406080106050906030303040b0103140a15020c0c0d02030d180b1207021903080402010c05101e0b010c080a05031902030a1401080105 72
    0x640021100042010707150019910f1a01c00d0010102090030154111034020076a25040380b040003030252480072228004000c0360a1042000d000d9100a84100c40d0b040800802c803038030000105481d0440d0400308c5507120b400c0148c00030341c615041d03102c20280c40c4241c0c0c0910466072140103050340c03888192001844641c840004101040c10600d00d04111081002600d81e06034040e05c604004051001034030640300e6001900c8000d400303003084690400360066610ba85c040c203541d0006521404506540c000340b103a1914410280c281c2d071400c00000c0c0c00a22295600c600d07080003450501d120403129000540b1a0344418400141900e03d142007203680f541c0c41034659074440e40112000c0c00f640394102d03401e00c11840c0b04113480030386000340354145900d03841701844c1d1448002c411082c0e07448116500e061006a040c500045450300d021a07040308290305000c0d80d81c6c1c03a0110b207003109442c00003180c0503a074030100600c40100415001200a50003001542003541d0325000784600322101035a140c16100314503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 880939001 1250 880937751 880937821
    0x1106012408060a2106090b0609180d0f0509041d07060809060415020f0d200a050d1802090c12280507030e010603110a240309020d020a06080f 62
    0x34102c00c4c5588031604281880c40540d03141420b40d01107100c1100c0002400040003c141400003003207911424241d9503240c88609841c83e01c0d1526117110402c0100300c060042045010301410440e0440c13a809002000040100e0090b41e10402d50b60814900c00d001d54600080c1c114450f603400c40c014081c0300007030011a1140c1e40d40100081c03008012401c0355400f813100070214844200a4490900110404903010301c40b00d0b49128117102c60240b01707004200c1840b107006443d6010303055918030928140000344164030b50750f1900da0900d0482d0001d6111210400700401d4003030100103000d0010401880d00c2703a6481da000a041144003a020030403070351400901e005890065500070300e410a4043c00c0004004440c0460582900c0c507c0c0c0085e1820800000305c40c00c40c0c10b00a0000380180f41103a0740040c111104200800a01c004117101810541c481450300d0642d6601c80c0603c1616a0040078104002c1c0d0b603200c080c0c0041003c640091001c1003c0d00001c0d143c0100c0395048001114443c181482d1700d0503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 880940251 1250 880939001 880939019
    0x3150f0f0c0a0302030423030c12190e0f06070302030a020d051c18171e1306050a02010e031602040c030902012a050307050c0a1e12031106012408060a 66
    0x3004006947e0351540d0451315004e605820742030b00c2210503810207165201a070108041c82c145400383c1000714007401300141c030301c00309195048480b6140c042c2f410f51882c0c141c00c40007035a00ca0704c8a0803180c0c010030000e01a401c154002005180c0b82445400703584182c500d29006503040c0c050780c0352500707482c0c40d043e2a01c04a43c8c01980040043d00803207489920002d0191034821010070740880030001d03124000b40c04a440c0303182c50280044660100c0101d49402007020f4101d00c440f0b82c501c241c1c8148000410801e00003030013074000081010508d01184e480300f49800056880c03132500101070b40102d00c2d14500304502403180c098020300ca5010303100c507810300341c1c5c1809500c1c0c540c5030145141e140540d01d0100700c00042d014001400c00ea03000e1070003010603a00c0a030402c507118401d540000300e091682500b40285041001285044603103500d0b800030410141c1c01c00f522410b11102e5503a4544c05180e0021800b521841e000401c3c1c2c14401d039050081c030852a07029130700b0300011fa03401540840c11200402010f20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 880941501 1250 880940251 880940257
    0x150403020a0f06410901120b0609060c1c020106030c170601051207090e0304060e09090606040b0a050405040c03052406130204031a041208190c020c03150f0f0c0a0302 73
    0xc1d45044d0454a941d429034122511203860720140c2040d0000c2d8501280da0700620040b401d003001c40c02040103410a20003d400307813084901981c096074010900e0402c0c6c08044c0400c40d020818240350b00340020349001c00900805144c04202ca400c1d51030360010440d4120211058400405500188220303400c140410800c02040d0362103000c148905040452444510b005406422403883c00131a00d850500801500086c02e1140c0d25010301c03d96810000a1100000c02e1074018801741c800098955404000c68913058454010642186c200003d210400000305410b10440340604140c80c582854030289402d10840c00c0a0451a8018032022510601d05040300300a0440e1041c801403520303650340e4402402c44118142e010f00740c040c0000704400c1c0200b0030701511300c0901b45d00e0915002c2c545100c61014000307408500d0076580d0356924030503c1050007000003c0d880c04000302142c604428000003032807000004c895460750102c00e880816000d1840c0340000d80580c900d181002d0401d04618000c40081d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 880942751 1250 880941501 880941557
    0x509010e12070602011505010e100e0105040b030f090f0106050a0308090d051603060c0504060503010e0a140a0c1b08072901030c080d2a0809150403020a0f06 69
    0x49a0100180300c0300d80c00b003241a000341880c3d000490680d4001d440b074025403185070310050501c0001d114100b065901e2803084001c0075814200014081141030040f078150055400c454410200001400708081c5113401840c4604143c00403640342d0020000341c11300741c0e01c061064541090b444981480000c142d10003414010501400700b44880c0c055850f614034002d540a0310b9000e03140420014018406540508054100d0078123005e0720706450035070700501511051240c078003403c501c1004038400381510303002a107014500c00c2001c0b01c4e42c141686000020f0032540c09070b1001c87c0918008010080d84000d4802c4280d4105a2403410606c01ea21075803022020180018074400141e1500c070000e03000c3c20a61406540100d0441c00e40c1d50400404520b4211b1014000c1c060010340c0c40714a012190140ca0140d034180802003100c8444c0880c41c05076158055500400d0f1301002030702c0502c00715160a409001164000c41e50b2840e029076a02134280400024060031000803602078200011980c0001040c00304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 880944001 1250 880942751 880942759
    0x6060d0c290301032103060e0a020703021f0209010909060e0606090117090c0a0819080901030f1d1911060304030c0b1603060602030c1b0114040b120c0a0509010e 71
    0x18001810301100781d030090300b044030001141403082d00803000e181c0020425044501702048040d0400e944890640e000801000783e4940000d00c01c0c080610a0040d00c46d00403101e048080c6a190069451010350024410300e800908210000103a103a424060308088803480c20048206844040c240400340d40715542e4641800046d00311110011120b203052881043c00c0e02c06402c560307010b01d04100c0700aa1a070301c82803040e0700010f00421703170a244808402c100e580c07003620140d80f8506000140c0160460322400d184162811403801d07069445581080d84007091030303090381c48d02040403002c01c5c1c0500004201400340800c08038110101c3c2052001542c0050007170401c607e0714060340e0f0754944844030484040200325004d420940d9103e41601445001e000c95002031401d0101000345156070b54154170807115811013500d60300e10142d005041984540020340c0c0140e941d16115052580640d001c802106e240c00f554100190f00d0825080c1030312182040d643d11545070240450045542c4051082d500f580 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 880945251 1250 880944001 880944059
    0xc0a1b140d020a020102010b0a081b040e010e0f011401061211040906080102070308010f08121b060103200d0c03062a0e01180501020d0807030608030a05030906060d0c 73
    0x25814100440071401c03400e6030003040e201891307100090039194680e489501401d41ea00d0140100c07500400c1781c00300d80e400c2c004c580781c0c0f110326840010042d081c0c01c413800d00700c0c1d40f03820030684004001040c0c010000e49110002d12449144d502070b541a050248500c1c0009001609111f5034004540c0002c0b688601d2800d500f4203164444a0840440c0d1890384400d0740c40c0c0d0f002400030109500324080e10300504240010354181490183e1050712603003d105129a80ca80001c2c01000d82c00b20340a9500006011101f00c0707000c0e60f128544403a011014014081c54000d034440c41c58183c2c80c11030b481c282c02e140e00416620803145107658190103450003143c0e002c2284a100c0c0c0d10084801760300c8800088907040d40e20400e68041450000d03051048440c58203d0b81408102d0602107030740c00090f5810704490a260080150703413411811001404150031251b07041c080003500003120355010000d1030003003880500f9100b0b1525507070104040c4c40300d0050000c0c0310410761101044190900414103a8207485030b035003280c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 880946501 1250 880945251 880945283
    0x30203010501090209130b030c06130305010e03040807150504090f020d050438040803060d080d02040e0a051b031e13260403021507050d03140c0a1b 65
    0x42507401c2604000076556000c21000058502040e1481103c80a85402c02621007903001003900d400000075240c0c003824001550354000b00400254800035034100d4000c006661101c42c00c01d17201e9020348152109442510000300d100c0011a1902218103126186c20385032a1030041440701400450302c2c50b144407030b402c3c0545850390303419010b2644120310131000c8005c2d10002c115603611006000c80700c0816401e4003075041503034000780d02c10160041d412401a64032960344500188070b00c40f1f005c1c0020703c0e070b000220711080a18440e802802c140c5081e907040554640e2400380c00c5040381c2c82181c44461a00d108140b5482082c0c3c0c800003590402952200e00d010b446980c110000c41c4001034540c24030054070750601074140198420340c0c2404000988889074690030b01c03640c000007401f0318040a80705098440c0112400c0e070795001120b21041c5c0c4030003920b22103002d0035000780c020b0041d40700855030400e41e0070002c0da41e0710030300301125500919502c03180481005000c01d040120b89980040f180005130501002c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 880947751 1250 880946501 880946503
    0xd02160f0312140d0605011b051005060a0f030803060f100e0904152301060c0f140c1f08010509090a06050612151051020703031b052104030203 63
    0x711003134421074004640103150000051100b101000703051280191000301c5000140301144082140311294008602a118200040c503203003e6640304001492034007000108110031078024621403803040340c60740c1d072002d80041800850000e4584580000b4502c40700c00b2183e24090442541103030040030240701c01c0b501c40342d40c0c400f1500001030710b15034801048905c1510f9140e4904103409400365117001c200c0701e18240d440241880c10814000d01422120300d4010b41040100104008144020030404032030030746810303650840a0740000440004e04a00011816042c05180e50303010b01d046400601c3c0440403919040000d21010f09055800904101146e1480004000f00c106001484940d83d0305818120740c40306400d9103d91140001c1110740d002c0b0590f510025030245401d003100c81010b0314440300a1041c0c0c44100c0000d0010612840316a0051281540091000240e03407103511840303c1c0000072080c0302d80d003500110000340154410b95040807440404440310b40302003044540d460629480b03500003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 880949001 1250 880947751 880947757
    0xd090209070c05010e0f0c0607031205180105060a030b180a0f0b0108061003030507081624140f0105100c0b010902030a0c050c0d0516080304050d02160f031214 70
    0x3000c00604015102d0061110038410030003e0f0035801c00500050b00e00180c000d407039003107010355188144000720342c0703c05160050803070000e0007822200412041c81d120f840c48408400348540c10a16600e02800221142881640242a20f80100d411a450750f221951081140003201c107000e0307a4010003961a00080750564031b524054801c481401143d03041207001450104010003182d904070030614104003007034212040740e440d5034000c0145503a6049411611103401078480d00241259100f44a14100c0c0525403481e01d503028000740c060042422111004280e40001e884140c0d9034180d000042085241110760340101c0b038854140181031461a4840b2440740380c01740c0c44002c50300d030000b003007190616130b600c41d030001c150003414903604059181030180c0d51036401080013010f00c80002140b100c000c00040d00d01d807146030301003281e139500d01d414642680c840000f806c030003000d8861000080364101e450b40d851401d0341c0d44a022000d800c1d245448200185500d42c00380c505210060041c609035140140c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 880950251 1250 880949001 880949011
    0x150507020121020c19061b3f0b130b010e10091e03030212040605030a0b06040810060f120b070e01140412030e03070f1a040e0106120b0d0c0b0d090209 66
    0x8410001c0982d8280079085d9151751400b8105d081c003440101000541020b09003480e00234000003030444002c15007070b002401d4025401d5000700044001e41c8079080c22660420340c0042000d4071402240c5005500c0c02090300c4004d44035501041c003400e14102c01d801c1280c821030307002d421481c156006a94400080120181138032503100111b5100b43c0500c28150100490004a400040090325181c60250000e02c43d00000e0800080642ca4201c5141c555488205540c043c1400d1010307039811040d861407500c01000350380f01b030450f40b804000300010504050010110400d40000c0d04441c83e0392112002c445e10304500011505115000c3d00f00c90b41c1c00c81c040c0150003d0900d003030f070b11612a403540c140582102805200c1c10710a82c405001441004280046102180d1489121102100f654140547c03907000b079030080c2e089900030000002e2402e40c0720780c41c0c40007001d94510800c54403102e001440103407505004050b00f04d074102003041003030702854402400005500140003542c10300c80e030b0000c4e85904058031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 880951501 1250 880950251 880950283
    0x70306111e04030c0807030201050315011e0215010e130f0501150927080a14071502120a0204080606060703030f0e030a14032203050c01050c04150507020121020c 71
    0x7800c0c0b007008200d20124000c0c2170600e00400300d5510b0340d40000c21500c4000c00758081c0049082c00041e07582d005003600200c41c2280050f1441d008000c40c4025583c1007600d614003584a81103000007040c3c18038031220390240e4040c400c015212403042d10707041d8151041003030441e5550f69503500ca0341540358101c1c0c058080c0c910510003244030a0114018192105d01c0e82900c11840d010400541c0000d6090088840d030b0340b141d0800c1170244186014941d914003c40501811450036036040041d41c5241ea801012136210703940d60040c16803580d04812049000d24040c0e9400c0d0f601c400003084052074040c010f01300c1c2030300c24076010503048003071111402510059020804280d01c041043c20714250400440c03c007480b0400106402c518201d15440100d410003001103084014118445042c94440c4080b2569160700300028401424480c4580c0d40b140e01501c03841010000c4d42c0c20991000b44113008941e40d0640595500030407981505a82220111f03a40751081d020782d0030404001d402100f84a54103210107591 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 880952751 1250 880951501 880951507
    0x307140327030a0c1101021212010801140403050d1d150109050601051201151b051b061207080a02251406130b07120e0a15020903070306111e 62
    0x5503491818203a0001d03480200d400074041035181c55400340c11820320603007003061014010303401300047c1d00380819042c2400d038503034000640701e01d04051306000300e0490780100020402242d0f41004007480d803900343c03401400510100011811003ca40d007028420703000550558000e0b0f0000d03100079140102c90b40340e1815036000704004005446242c440c99501a0080c02d010b4603010200700301b1022203005014401a8074200b2084d565194850740800048584039100c00000c580c56003009170351100280300c0043c1442d44162405c3c61800c018043c1c03007a0030b84240d42c1140d681c50f0140146c41400c8001c11021030654244802c6e0740d51760301c002029401020169081200340c1c500d0420707490300c104090840707086030310040c1404200e0000348581c0c1c07602d80c0c1100002180d52500d0108407044103c1895080c1c40c43e0405403500114040410100304080c481c0c810400d044400301514001da0184641e02c81e17040d0408a4100045121030300a152b40c107422440c198680440c1003242100510850802c000c185004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 880954001 1250 880952751 880952791
    0x30a061502061e10090e0106170a0c060c030c110d02062704060b0405012007090203010918031b0f14060103030f230d021308101d0d0503071403 63
    0x1803445070308044080115800303850140700318681300040d48030352401c850307a030101080c00309801c0d40818060200400249a485601d541e0b20b41e44001c642001d584650607510b001070a14040c80c80c00b4500380d41610b0b9034204441a40700c01441d01c200b10040398000c0040c40300040181d448000400001c00f148021515110b000740081c03207003000040006001c0c41c540401404100d0708101654100c0b0b009181030003002002914100d40c9080f80000c100d000e104444010940002030780141d41a02c480388020000d000c03d2451103850b2010000002d000300300310650340000c0c00310215081d400c0fa402000709446600310741c0d858031045c0000d0010b0382c9464001c90018002c050303014442a105e1300d840e103440a40816088004460803084203061000d01d071000910f80040c02140c0c0648400c02c2c1c0d0600068a9070703980b0515180c0f54800800c0f001c0701e00d450301d0000c00008001403181d0403070314880002040240201d001c2990162b01c0541000b05016001641740704111000000754032420a1108480c000320a07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 880955251 1250 880954001 880954021
    0xb040204020313050d0801140d150522030302310303030b010c08070c050102061e06060a21050103260f09182508090303040f060e0111181014030a06150206 68
    0x144814424860f4034001030200c0c01258ad58109047c008400141e25107611030010f40242d844040800b0010112040005054050380540024103401351481c1601c0c5501e0100d204480c074501408504030700075202440842d22130340c44041020780c18101081100c5a81d220907071203400926084900c02100c80044c402541d040c8090b64020301e6a82c04450040c190b500f024401e240c008090134000d14001c1040c103039151203004015420180c900402c503c3e040301001c0e540103072009010940300d6100c0083c0e6054600b020590b106d02030350304541362900b00300410401810235401102c5260340804459450070480314000c0c8000e0161b01e502d0038002c03002c40c40c8041741004481f02d107a030405002c40a41046454070b004402c499001d81c1c45808900043c0c214a8202e00034181c51012844079842c004a4480c01250a4000c00c2c0910400c0c0100424104c0003080000710581700c10b92030002500020303010126003141c0055600409220340106000e41c84981d91030111400301c000b040140d01040c24010308e404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 880956501 1250 880955251 880955279
    0x6021c020d0e03092803020d23030f0d050a0e0114090c031612140d0e03010b0303030709050d05390f0f1228150204030b040204020313050d0801 63
    0x1040d01440c201844070380040c5c103600f8000c0f1071001202c064020011500c00e44070400014560007007548084581c03500340b124580310000741081c4601c4500d100e0841014000080d9000c40035404051072034460401c0303002000d000040d00000d001030301c03114004410031007030050050707400040034070540502e860340c103036454000d807142010f00a40182584800e220000303d042c00950b0741c10b100e200c216521a103400c48001011001e291100d00440580041003540109504c0011400301d0007030184001c11802c240d100d11003512420040380707011394100001d0828642c00301440e402072082c5d4080042e095050a41c08140c600c4800807106400a40300c0007040c0c0901c8210141e40c155001d50011901c2404508031031201d40010b4803c0d040c1155a444c1d4400800446003581340081c1400040e14500000b51001c58004000320341011380c07220408500e051600c00e980840383c100103003d4403030300d4a4090100030340c000340c07030a1010041e0f01c00d01004148100304820034040f203561510400d6241602100b5541 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 880957751 1250 880956501 880956521
    0x9010605040806040204110c0f210f03070309050f030403080702090f16050c0109051501090c02030313080d020c160f06031107110102011e02070605010608040f030c06021c020d 77
    0x11100740301c14000d0000004440b548154160341c0001c00700640c0e00d5641080c01840020350140c42400b042c0d02c043c0401182c281c1182c610b5811810462a512800c90403600869a440002c1030302440001d140038448c1d00011062801403003030710f48002e00c21280901f1644176400940e1500000a50380003182001c0d0891a07020215541c02011404c08910302c80780d850314401c0d55810010085007900303840c00c3c20b40c86034040940c0141260b25810080700000c8041c0350920644121030300d00583d61190a001200304c070301c5100d216600c2c0280c514140d489189a401926560250b00d9082c0b01c011500c0d08108007002d000000c048134000070618080c0d101c9200c100c590001010142045094040c1da082041035845e03160b44416124007407031400c40100d00604100c242510240710b0b002c0d0910703943d800c035401843c41c00e01404090209a0700c0780025101c401c0f040c2e0300109680000c00044010a108040310310106201e000050303d041c00018400c46841e034804c0103981c24036400200d403109440c05105c1c0078080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 880959001 1250 880957751 880957757
    0xe2808010b01080a05100b1b3f13030c03060b090610050f0d0606020c0a140310050c0d182006070f050111030c0c070f0501141305040504080d050702120301150201060801060b0702090106 81
    0x201052920f9002148440c451185c0081e1070200d100e24290709804c2c0c3ea4241031000001d042c00341c3e41d04cc40383e4442003a1200303645551030880c403c4514140320000511400c00604180741000341240b00721241e0b40074027a00382c4000c40c24070410903800c409001e590000c1c2056801400c0300184401000004e02240c0d00100e90401c80c1c0a64010503140800c004040410b200130000307450b51504400141480351550307029410740342540100d02d40d8101541c1101140c0510440b4102500d5450101604c459011281d64000c038244080e00001d0100c0c611440340c184180000b1548800c00c0c92503400540003a1800d1500040c0403ca032440c9507000c05c250001001d1484845918500e0f000c0040d100001042c24010780140010b8407200121425502400a01c4060010419868242499075450b000100100f002606000105815034800100c2c0c0880c12a0508410310310b07481c00e13500a400e0012644c511096540b1000000341c54038080c03085078000c2c11104040e81c1d43e01024070402c00c0c07106058000d2400c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 880960251 1250 880959001 880959043
    0x906020d050f10081905072c1e0f15030708100e031303081e0706060f2903070908070b0a021e0a02060a0e2808010b01080a05100b1b 58
    0xd501c600040f901d80346204245d4280084005083c06418010b06800520400001d25095034064102d00315142d075400c40c1441180e080e4644d1074450300002602c2e0148980495004082041c0841d80c1080c0f580099403d48219800e20700c04001c41e09120041c0e0102d640354001f81d2082200580901a80250f440c0c0400518540b403540403000420815a02000c6d04440c0b01148510200815210b081c49540c0ca00c1540c60300c41105283c401c3c05422203011b0f18043e5091203000107284050b0948003a0843c0f405000c0d10f03c0040106041a00c60304010200ea042010350140056220b60034007041024285548595540390600c140103882c01d01568019040518001d80c0c0780120000440d034401c81d2513040322003079601c0c0001c80c03003156400e001c00c196541c4090b40c03817001c075884802080218407162007443c0e4000c00300e548817211801c0b1916201d0003404039141000203065134400e94002035000d13644030101c114003510f82a400c00250800c160940707022820b01c0365200400c004000d101641c004d51203401d85 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 880961501 1250 880960251 880960259
    0x909051c0201090c030b090a0b0a0507030f06060509040504170714010b0f060a21020301060c1506050105250b0408030f01050d03050715240e0f0114090a0906020d050f10 74
    0x2d0403071085c400a0100f04480011640c503600c20322041c0704240e00402074181d03506203031040000600042c1c9001c8013180c5000074414400a560290340c0803148130341c82d4581002c00e40c900703100107404000c20844234841e6010b02805c080a40030f0150401c0c50140300342c00071041c19010180d084030711501d21540b00380c00c2240b00281d540c0d80c16040359001006490942107841c004601490301003c100311171680740340040004070b01c460b0300c0044402694040d603102c00c5400c41302d50001c0102c51b040c1c010180010010001c9405030030203580341c030b0700007682c1400000c00c2d4111a140c201c201d00050342c2c11030740d41a0000c02d00501e000d05036140f1b07014140c101e401d0794080b00c042d0750140540c4241c0c980100943e405880ca180b0b03201d656404648080803480e102c0d030580c603048110a15080303241c05602245840d07c408100a10386010682d4103990300c14840d0303212202c3e100100310001030024102940036456070b00000000b11309002078100d10303032699804101c90800920891410800510303880d1486003c0364104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 880962751 1250 880961501 880961513
    0x40e070f0519061202160b04030f11120a050705060403090302120705090f060d0c031b0f0320030316080304020f030c0a030605070e1e030d0f080c130909051c020109 72
    0x11085850604001940302002d0000001031b001e0811110700e0b202040d00042c05129125450b5031240f072096a80c0c4a03940c0540310300307031804131480034848102d0740180e00700c012541441001b0100d0381c030726041c41414001c80740d40c2c1514110040303400b200040c134115410802c508210110404040c0e8041c044c00d801c0703051601040045c500109400d8120b030180011841d070341c45120f000c0512641201e41d0b010361503168100002001604103102070701403144840095034a4250000c6015130760311102c40c1d210034154015403402d042c807034a0b0f5144e1501040104502c00c1c80040103039016640300c0d41c08541c40f40783ca80100309400c0c2e080c03441213000e45c002c080c1090349640e03030300034080c1a02c1e03004000252540b2412002c6518a084041013500820000c1e14040303854400250f0715190302d000c030100d940c8880000c1b011541c1d0080f55200700007040640c00071800091461002e4003007c0c0b00304840040b03030381c0d8807000c2d1005d554400c0f809941d80d4008003030218461304e0400f00c0142c11002c6000900407911b003a5030701 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 880964001 1250 880962751 880962799
    0x19030203160804051002010e16080606060c0c0d030f08010504021c09030306170601050a0803090618011803060f0b090115030203150301023103171602040e070f05 71
    0x444040010207107000030408888240d60240001400303821a0740c0026074060300810071880303840d070248900035045c00c1325021036110b20f00350340c40c0c0c0e07002c0c008940b141001d00c1001d4110301000405801429015001604d03445500e00341d13036019950705a200120f841015019400607000b07140100d004200c5c2900409602c02d86005c604850000003034030045c6803c0460040c00340c1d400c03130b6014140261214019000c000341c503c5c141d87e0200c6642d5456503803805810f03903a1080005075500000103100c039040b060340464070302c0446003041c1000006161120150081d030759080c0c01c2154425507810715590083e40600c00c80029400030b0302c40c2c07092541040b1a000e0f54111a000c140d040540020002c0c6075480303588a000540b40c0301038025510341c415003103001c0d0041c00f110020303c0c0410490012000001d0081c0041048030b41100ba450314110751718a82202c2944039420b07000740145c030f0030141070058849218081011058402502d07441d4205807403a403010b40d0702e601c240d20980120080303c40c0d450300201c0ea = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 880965251 1250 880964001 880964017
    0x70615060804021c020303040b040504050a091e0c2103030b0306060f04111303060605010f02010203160f050c0706020f0706020c1f0c050a060504021c0b04110d050105160219030203 79
    0x83c1100300b0a001942d500503007004d04001d4240c00007050004404846001500c04e07a48101c809001c07541e030380360206044611444004d00000b4070103a2450300b2440481d5004c18031801003015116451b102c03103403a0814004030440f50841c0b2070b41208481816494458a000c0b020100c016020341d0908a0001710384d5201030f601d0074840c0d6a100780c40942036242d03204032000ca440240d12030940c2640c81c00d254004000a20846010400e43c40c01c22480c2807043c802c4901c66020918112441e101d00030b4200c8070000c68405c00e03014060200b0141e0182d8600b0000e090007070405074018030300d42c3e030022040303414401c0a510410543d4070400d10324041e946c40a50600e14103004c0c0e8154004d110414000700c0d803100340c0e10300c0500a030080c4100442801001d401c9903200368000d9038061580f080318004020761120109020b010054200007160000700e9520075100410801031030f08a1030042622680e084420a07690040b4426074a00a9030b2140d07014040810401c419102c894184c210685020b5106e21401796 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 880966501 1250 880965251 880965259
    0x1080f160503070327050f07180f020f0d0c0306060c1a13020a0602010522080a030506060904020c1513030815150304031d0907050409090501021e07061506080402 71
    0x400150228425407000b103001c1d51a00400a4803400c807003210145c0401048203640318064030000e14000240022003004407490f0000f82d1f85090001c0c2021001003461210803e0305035000c00c40d0700d8407082d0300406007100e01c02400c00010710110352140030f402c0341d5490f40302e941400391441c50640496030300354200640b0b24a030507801d00c8550b9602c005a13062100c01c003000358001c401e000c0205046505601061144400c9200b100e1481d03425601113120090741c180040020400700320100e42c05100307401050300440090070640c01d022200303001800780d81241142411a42c4081040c3d021032000d80d4580b9001144080ca85054240b00e8600030a0741d0002001d5180d8000041000358139600ca0f141805161003028000e55168101450020303c500201551000201180e03403111001d0700d0000c10a0780a90059114940b82a150074030005c05000c000300c00380e4a80d5424010075440044c0821084000c0c0d01c1550307199601d11944c0f50020840d81c0390600b0601122a00d282031014136004252245c0168040b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 880967751 1250 880966501 880966507
    0xc09033f050a180b1c140c160c0b0f070203010b0603091c0507050d030209030c0a180f091506030b07030c0207030f14070b0a0314040c0b071403120601080f1605 70
    0xb0b01050782c0c2043e6803010341505000944070b5422038401503400d05081a520007800284103c0d10300d001d040c90b0a99040b10450340070051f00b5950710360076801c00003141c412801d00703600036a00d024030310454112030808802582e00040c08011482c0a120f282100041184c20a066052212099544405416040c00d105206902c02020a400754096810003036014044030300300008a140203002c3e410a05005001c0c0c0f0816402c0d201c189400085002540d602144c95103a199140d20f040f0040c0c0901512030391740c150340d52010790206010310700e460001e4105440100b080d03071651400786081840140714508061410640c1d07078400c0d501080210440340c000c0800b180f240018284941030507140c140900440c445c18000080b4620550081c04110300240c5041060207041100d11503001c1048170000c00500e0184800c0c440003107002c001d03003c114000e5080142ca040b9001e400780c40c45e400381025400c2d0820400801c05d0704e60f4013910043e444651041da50040d410421030502c40000103c1007041400008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 880969001 1250 880967751 880967777
    0x200f070815011523040f2112030b0406030b061c050a0f1e06090506010503030705030d0f02120907090f0b0306184801050d0c09033f050a 60
    0x30f2040a042045800d09100c454101e04507881c2c0b40d42d02a2255120b0440f2500e4001580701482202c40c41d003071f501d1200d15003480e03200c2e0f44400c1c0311075061442a09141d581c00c43c8541395100d511810019621130303610070596003888020800303e1002320300d40c1e1049000030b04410000900c00300d01c2c601000d0303000c04000c07040c142074a00f10800c40c1043d42060f07070442d5900b425505001c1c084c0c000ca05140e000718160b912a1340c03900140350b21303031180650140c8907610821407502c00c1806a404180c428002480060519105450000f01a4010b0743c64070b4182e0311141c8240b0070310109200718085a40440810841d00b000e280200740c5980740213240e08443c0034005c14071001c0b03540c140040c0100c00ca0810300b20f500c440c01500d80582c039030312a04c3c0e007124884184040c0c1d0b80c031000c000240c590202d0144c4032541400c0a03940c4520190141c849000104400030f00000b0006088140604840c60001c0e4100030000c0c2d50310450560b03038160501e455018200764400c64500d40c020701204c1000c000c0d884d180e96040c150b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 880970251 1250 880969001 880969007
    0x1e0105180405102a0f23210f0108010b2b02060c030a020f010203040309030f15050c040503010c0c080301050f0402131e060201110904020a200f0708150115 68
    0x1203d0301c520201070030480000c1092600743c0700016002c0300010020500302c0c3d15202252000b104580280c0481c0203000e62585050700b080340c200d0040d0300100c1c180d14100f50384c110070070b844000041e400f00144071941400900240d2010003809800c410b0000c220320034000f400540d4840d02001d034002e5103200c030180c3e903061600f43e0250480803038003c0d010558603503c240010380c1c0e03a442184000014082d110354000b181c0030600071203000f643c00d9910381c12203900715202c0d04c0020703594007001c8400e02080c00501b40c444401d0f00038640b0401c040c07040caa45907490700d414142955064040b000c10419140300c680c00083d50380050f40d06503541a55984004040305020030001d1241b450204842c10b0640000101101c2e000303224461226240a0b00c12307001d81d00c7d0026800d0b01e20f4005100000744080c40032107428201b650280910f005035140542280300003000c2040070183d044c8140c10103800c16042981000d004000020081070401d0041c8041c01c0f200010160008041c007c8210241440418880881c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 880971501 1250 880970251 880970263
    0xc0307022b1202010e011104050109270e1623090708070e030a0215032205030315011b0c0614040803180a081b130c0507021908151e0105180405 63
    0x13440c02c000b088500d04141c01f00000781c10621a0500040f0900c0002c5840203d100307a01c90020b407498040d11034810b02c00703c4c2c4005400c1d08214130070980f06046168400503040784000d801000440004480400080c46501241d41040d5100c2e0040c040b81c000d10a00ca03a02a00059020180340340c015240d440c0440080e0604000290180d0311003410b05403040d00b0007003000154003507107800c00403a2090104000003642c00319030400c00f800c01d41040c40003440c00e0240542629140005140ca10005d98010080050048030390109844800001409104c0340f40c001d81101404140e40103418101490452100c0c4e0368414480e9403000820f00b420b154581d625200f00c0c0201818044c030a9503190481185c0d0143d100604254440c41440c60000c100503a582c0380c07003288160b500aa42e61840c0c10460b0f028004603c030710801043c581d521040c1c000807050000d0000d503825800c40340321440181000c0c15040c1040580c045803618103034481004002951b41d980c8441204400c540e086e0403160303514280141088 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 880972751 1250 880971501 880971521
    0x601061b2d031107240c0314030403020312060402042607030803180114040309030803060d120201021201050901050105090d060f020d060504230a090c05060c0307022b120201 76
    0x16035003204080406811050140350044502c0403a000c880c2c0c1c4140542003001118041070802c01724503485840d6074401e4844000f0340e800303810720f185150038242c88490642d00448081e4010703000031a20f1002106120740c00790700100e00300c80030740c2030908042c5001c0e8034243c800a03860300012070594080f01e2503014050b0b00001d41e00080403940380e15040b41d480c02800c030b032545004895403034030b07001c000b400404d00301c064001d03509552074032642c50a503501e01d0703520b0b4406404c0691209000741340c440013074440d00042c12940f0741d6a00142e282ca100700341e0312500303060680005124280c444010b0005980c40b00556071250012640520300f4812400c080004003510944046050700010b91013071140d6994006004454066804105125504030101100d84007204000b0041740600c5c013040c060a100d4000210352030013500b125401650f104c001504130b51005000b2446900f000c02d034103040d4503100a95071004100014007410840b1a44900308840b82843c000404044001408100041c0700b503210310054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 880974001 1250 880972751 880972823
    0x90f020315070f05041505030402040f0606091406120615073201050f010302210a060b150f03060415080d0206090c01020106080318180f07020601061b 66
    0x1001c41c20301100304030102d50410201c1c8014003d03088041c070800440b0115290012201002170070b016048031180c0c009407090b42e119407680304c940301080c440d00c01c1e07070300414042d110751005618006400781d1107140040c0140c4503140503c80c28822504241d00540d004504540d501003a00c0b4800c3ea01c2e6060190b840082c00307199465038841d40414112404902c810414005003103144102080c882c00e0300c501710340240d98040c1e40c00c010001418100c440003a091200052200c1e943d03000c00b01b151030806004425215641c540d80007000d1414401c42480300c0002c1090401e281c031003aa0f080b28000c3c44040c049900032541c582228003040c0c10fa010400c003626802094902411054900a59414041d02c0c18042805881c1c1d43c0049036005109800445900e00041d6003044111000249411400b080721341e0001c5c200000d640da407007451661288150807070101d0003503074142500020318002058001009201e22030781d071950041041414014803d504c08180b04145101c0c6150144000c7c0c002004002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 880975251 1250 880974001 880974013
    0x307120b181609031b08010f0911011101022704060503010b0108010b091f03020a12051009091103010903020a0611120c03060a0305010c05040503061f06140702130c1b0b0a090f0203 79
    0x41a192605d10011121200c0091040c41c1c1c10702c0d68107041710b007407040007480c1040d0b00e400100313154080c01d00a00039004890005040210380880300785030020401606040c0d1100c0680c1c2c03e150b01d0140704175800b1b0314050b4000c221030400d038400685450b806004100034200040340c60841542e59402c48055406d01c0340030086003401c0c3d20341c060b021350804082d16010481020f0384400d100158400c007403080c0355041141d4040f034035041e405401089664003d41ea01a0540885017aa4a0900501e07075128800d90042850301928181401103410808840300e07010b50400c1500e905008040c0e90640140740d00034040e0740e94842310300058190082d540000c3c807650900036549595500b040141045400c2a02524083d54030412500310310001e140c45014032000040c8184240c0740f02d07141034a070007101103402500d8010940c0008118010121291050944134400c840c14079900c541300202d400d51004000340c500700c4680d42c058035002c00074445030f4442d944114510a00600014540210340c01134147c0e05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 880976501 1250 880975251 880975283
    0x303080601111011121303091802040e010f08061005030a03051c0c03062310180807090219030e07060e0102010603140a05060f0f0103110a0b0307120b18160903 70
    0x2080e4020641420781a1010800148036507540446003c1841d03150341da5a2280c0d09048071269040d165427028540b05038244070116a00d005540700314082c0c4500d0a642048a2070400070038640000109140c40c01c0e075014400300002c2d200020084131865044c01c0581d07e4880e4044007440c140091000c0000a03410700b90700c02580d903055403045d4207540c2c813401c44001d0081904141000c031581080826080502c020351101180c0c8610081d42148000040d00141c065a0728862490f00607a500310344006a40000c03018a82001e850038800200d0141c00c040c0408a0810b008503250b15041c1310740000d001d4800d1040050303a00c03c0d0310000141d07900203a252190501000b40c581da40d58030603002c039458030030200440e03c0030b00c00340e0145214008100701000268203643d50010840c100250f4203401560508004c100c802007030019501c554060390341c842601e01041c210400f612481e002040c0104a440703442070744103d0b02500c9a61100c080e20014070084030041d0122000b000a5001a24030b070071300000c171a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 880977751 1250 880976501 880976531
    0x30304060f0c0206390307081b070807090b01021005042102340b1e0c010908030f070201060f18021c0c0203040602151302010806030a06150602060a0603030806011110 73
    0x682c0d074080400994940b545050221580c1c5d1203140c3c4060408d210900621a100114078041c0d08103011410175545c12942e2201c0382c41c50003480d900503c48a03901c6543c24461075a0401c081c900150181e841405541042c5e100c145010890f0680907151003e08058064194000c101c40c440b50030041c0b4143d04845040c4005500c0d01b0320100c284050b0700740c0780341c00040030400c2c00165491080d08240004545019101c412001e40c4515058a05952a0426403004c80c0503032028605c20901d0000c00c16251401000003421a62150412800ca091800b42401200103003440607540c481c001000680e21500203803c0c1d40809100311101030307010300708500c030004d080e800300162088840c1c0340c00300c55800e404020250200700003211000b070562042004c8402644c0300b080380c0f82e045000a1300741c4078046141d0b11100c0540307100c04c0c1d10b030381520700d19441000703100d0b8100710305a404004c0c89001c00066040d6075008082440191245040000a80c498200d010051101031068420004100500b0086060766 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 880979001 1250 880977751 880977817
    0x32127050a080c030303013f1421130506070c061d030309010c0f0b0a06290403030e150c1b0103140106031112010902090906030304060f0c0206 63
    0x8280120788011001072481c0c0c00140c1c681d411030000f400b035420b580c2851140c0b415445009100758114001c03030126001c14001c03020207025646d814040b1401c4160728141840202a80000003600343e20408030124a03408140c00d18102c00a1000c50695071104c102e6850400d2480c3e80185034001c0340060301d2402c00c81541b20b4401161001e449586000010032300d02d84080300380d9501c09405400130400c101981d0b215604c9a51424070880e0b201e13001502d140c4468800d03c1c000c4420703140003036445000f84551b5880c02d18004007240e903040040c030014103582c0c1c000c6181c0034a1200034184a11400b070300d00e4696480b0b8042c416000c4044140b038849034120b4921382e1b100820b852007420300741d12045000b5194424040c2101c2d848400d84115030503480c0940403801007207014044110050300f8008465901e1070f1000840c02010750190140c4c0380c4400c1010880829805444644a540108820808140c025010b402c010565082c02d03880c80409001046191080c10f60181503120005481da80c1c0e920017a9031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 880980251 1250 880979001 880979009
    0x1e190e0a052d0a03110126040c0e0105030a081902120313020a060809031b07050303070b0405240406050a180311120406020c0f0307030606030b070810032127 69
    0x1102ca01d80846040c0004046980800380c180100302d07403a809954080d0190b048605440480072084d10b004071844451924103075011030b110300c5150820000110f02030501340c0500303422006008114036030760b00c0000e01d208141032002c0c245038468071600094000e1004501c0321078040c038000e41e00d250044040250400c0200202d1041c1244100483c415204807a007a124000c0e2000451400d0800b210945040c4488148011300d481203100c0465151018000342001520640c490805410a45041414607981201201004007010444030203a00c10420740c9820640041c4000703441e03240c03101268003901900d08494540030840c03000d45c08040c3c3c0454182d81c07548c4030f8000c8d00c2d019079215070401203510403442a2401a4030000c0c1c80380461070614035642c4c06400040403681490f5480d590a4143d4850f82e00940b4605100c0b81007191198015501580c80803501012140780c50541d43c075581811284030400d401140d0040000300b580b8040d10401d001c00e81070005401c0b4a04081541002000081c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 880981501 1250 880980251 880980319
    0x60c011e0e070e0708060f0a121502031e0c1201140f010e1311090406090b010f0c050d032d0506010311030145021e190e0a05 55
    0x500765807488800724880090360303000e0f407200ca180c1e00c0f540b03000c80d480c0002030113142e48111407504a00d030507583c25140340c0041500d49917a5004081030b0900310f1800c9407800518402500401c00c10100030000040410084905c1c0c4201015855a0780c000300c890080c4c0d155901c07803100b907030000301d2003180c90195400d015008442c1030711170702e4002004562002807201e000d6004402d84010f1000d000154220018410030a08840c0c02e00000c3c2c3c0c000f6054440951186c5003a071742d24034a4075850350744081c3d40961b207138032818a00860201550744d03699481514031501d080659174080d01004140c1c0c016800c2c00e41608034000c0c8481c880c602500e10080000b55582c1d40441d180803070300801c128603d030640341220846c4044620384a54030704060f007522080b10a04800807260a1502940c0f2118030203142403190364880142c44880407014202240e68400220300003080034800c0600e1303021100000381d490381003032038040c40c4051003c3c086554080d1940101d9440402c50700d42c1ca40400c038070340c04031000303544140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 880982751 1250 880981501 880981511
    0x2303040302030904060b070309180b03060a061a0a0503160507060e0706030c0905060d050a0b0307032103110a0e0102010b2206050f0a090902011e020a0506150607060b060c011e 77
    0x1c09411120707c61020010301241e81a84100051103039000080801d040c800c03804941c031124440002e0070010100c2e2516003a40d0b80e164180030425030184001d007202d071001c1c01d407440c2c1b42c00524094070038003005040703182c24503000c0c851410040c81340b01581c3c180c0e80d20040a0101902c1d0744800740e10b50429008400000c0e01d00a000d0300e030b9500c180106e0040710005051030346001c2c1f1041c0000b015000007440d00c0000d81c1c035039803000d0342a141000114010f501a490f9480030080701c0748051150921046810308050810101680e684603010840380f50000505013440a40910700040c2d015104d54030800d90b0251b01c6034020405803214a0395028011080c42080000588075010040b0302020800c40b1600030303c0130981800b8102141e0300c0210410b0050403c1849403420a45062081401260324001a00000c2c030003c00c2207000c11502c3d411007034040002d44c1c80b5000314041405400384100241c80c3d00d858035409801c41d1543e43c22210401f07854402880248105810484090884440710494500e0701c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 880984001 1250 880982751 880982759
    0x7030c050a120203220818010216050d021807030605040609150b031317041d0702190303090c2705280e0703110315010e07230304030203090406 63
    0x100115400307440980c58040581c10302c2002c02c40250001418003480b12245480c4500f0180e1007242000007510400c40c0c1d07a42c8050380000d810108840403041415940500c41c641c2c007105804d440703002502c20650741440521361a000041100f000c036103443c020505460300b03104440d80d1680118007500d80554081c0700b2300356901c4214007109c80e2000c910300483e103003110900110b02810700843d000740424407042405405a280c9a210380311040002100c00d500040c00c1180256944060380070b01c5001e80c455405142a45021352240008640341c80300c418014000002c15020303901ca0070340285c00c00c032452200e94071560a030174400d4454000703a03218901150003000c1404140580c138400d116031030b0300d001c038003146c0c150074003c01d583c8000300d00c013481e11600c0c10400190300b0441c0c40000c5000d11410181d0491035001e050074501d1340d506000507400c02d080180040c4071055106338010825180c0002c44044003110401d118844040241c0903210020610042c0b41d4004007401101804990070400d00e566 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 880985251 1250 880984001 880984007
    0x40525020f0601090e0304030c060c020901060503100b03092415030f0c010807030b0907090509091902090709170604021008071d0102010e070612110301050d140705130507030c 77
    0x1000050700603603102d44010322901c01d0036007044202034410000c4a0030a80c49a50744039030166142c00c1701c030008485203501c00a518110011500501c41401d10510b1401e20000454100780280540d290b510000404112864010484012040c0d00e03141c0791510040c800e1070b18416500c007a10030740d2050041003030191651a0205940442046030070003890107615040066403440d400500034001e1650b2440440c4c0b803601d070210410710454042d6140302c0f045040200b00020088003401c6040c90394800200da5000813282c075030940d07146070111103503480c3e40d075001c008481601c02ca0b00701c0601d001441c0d070001c0044034001400c84c0280d100b26105c0800c521400011182c0010403100400010100d0380d1403443c1e250540003d04020301c06200100e0901307081c000382451300045034461030005500001d0b01da06a0300c0380c803501814800301100c0c0741c40d65141c0000245160115000680544000500d018002e501003002034000c040c050f00e1120585a8000e00c1d000070070f4200c51110100c1d0404207840c0b50944 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 880986501 1250 880985251 880985263
    0x80316021204030f0309030f06020309210706090c03021804031b11060a090f0612201b07091803080610050a050c03040509010825030b0f09030904052502 67
    0x1041014078201071843d04ca0041c21140036400f078051001a21000c40411400204501c1090040b0000342e5a802c15641e031034680031840d19600038441d6000603080c449201072080310b49603500306801141c2c0380013030b007000440c0102a500003544460280762b00304d400085548080d2055000341c41d034500a40c0c02c00014041020419002819145071030a2040d0303e1a040d009050069080d00c1c02142440d102c12500003540801c1d040383c3c01041d42094101c45a8100d801401800f048241c140030601d081c1c503c42c0728460207001e08100c06c80c00707001d550808d0b100c402c0110100500c903101080c054000400180d6044005a110990000b4080c80c0000c0c590300b029006510712410382d5960a1401d0b6001808440035044842c1c2d054060104020000b0156107000845000c0c0840d40701401c110004003140404943e0110020907131070306d440000308003154030b00f0316007940b092070a60b8001c0569502c4000fa41075115208515501520302018007401490280c0e20103100f01c1841d040c60a40c4e0702c1804143d035504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 880987751 1250 880986501 880986523
    0x406020631030302031312020610060c170f070b010f05040b030c0108040602180a180c110d030b0d0609030801050a06090e131a010603050f061516020a050402040308031602 75
    0xc0d205440e076000280c40380d030082d54405030361015070381c26283d01c0e0390752081d84a9181c07520006034809000e01440400d0741014100604490400780341200090f07031070500015044061040c0e01e90081000d001c8010301c2c1c01201d060740d0b0300101c5920070f0344c0c460780085120a50340c000c0b50b00803403138024045082d00700000e05104070380d0161215502551303540c0e280c2e800f0b0750105030314005c04a4802d40e03901013610f4003040d2001078030b52840b007000840c681079000001c40380380038402420044070819044a241e000310700c42044448601d8080340075084440812910b00d03654030001c02461600d00703580f0034160702402c0141600e804541002c1078564071074080340c0c02152400781025113071400c0f000c555182801080e2070002441111607001e90354518141140c0c44070240c0c00b0b040802c0c0c442003002806031040c900d8562250040303410851a1503d4101103c160007014204402c2c0404200d0841c250742c1e075003c600f0300920b4024015541c43c1c0c3c07030b842c2c10320540c1c00584001e400c110b41d03160007101c4c4500100e000c0c0e141c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 880989001 1250 880987751 880987831
    0x120a0606140910050c10050604150e070e04060b0408030705070b0f121506161e0c0b210a0b03060a0501030218071202070b09061303020d0509120304060206 68
    0x30000c41000c009014100680075004d20008000300d0b600c00100340250044003405a100045e14540302c0c061000740c54202c070815052403400c0405100d4072014940d00f60300140b1610b003000000e0b003810007150040090380c01c00301035140041000144440000700500ba1380340300e5000ea07039086680b0800c01400e0700460321404100c2d0000c2c0941003484034071400300e59015201c18089645030072144081380450340600d14410301c1a442000c03070720a20041e004c40400283d151246034100301d14a440d4240f52081c03d0040100101000030008503680361054980c0c0c01102210700c151150034500b00500040c403580064500038040c80c80007810003072461250300e0480750098803024802240340656042a00001d01100500101010340800026984060454a03101302c1d40000b590034820380302803401000815808000c0140d4200c2c40000340d02040d00421500c2074201542c42d0001c00c5c0c0001d14034904070064a1180c07001040004200c0d6000401c40d00402c2000d01c0f5065148075184546417a04d128901d007010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 880990251 1250 880989001 880989007
    0x50a0b04022701051e13051f0b03061e0a0b0a030e010b060708090a18021c05041211010b0d051c0516030c020d02060c0607030b0316051203040506120a060614 69
    0x82403c20380d001d034140c04441c60305c01d1400603c0200180d851400710700c0b02d0312096543c0e8104200c2d800c4203282c440da082440c113403c0c03e030246009482c500e648030007000c040c0103125140604000441d4a0f03801c4a00d10303402410b011401e51260f60f44011500040c0040e00060b081c5600d40c10b03041410310a80304800e6001d4442440e00b4000e03181e2a0050380007442072608103010300700c0001c000003262301c1084601c412000142c1e58245203071510400075400040d40304018541b00c00d0000084011128a45645040c00c0c490080780081451500426015002e00e4114a035000800200309000c5440b03c220f510340c1217003101320038480c04211080e0040b19401e840079521460003001082c054044001d0261008000021800785075001c90126000b203840858076031311072810301c0034264160061050492080e0300601074a00b4a03107960244800511a1a02800310002c1c0c502c01c0e00d8051013254090400500791998031520801756070b011480803144000c013545031000210341e0718455026107407204030242241e81 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 880991501 1250 880990251 880990259
    0x606010504030519020619020c0301060f05011d121b09130c0306050c16061a15070b06031009030203040e06060f0414011e020a0302101107080f07050a0b04022701 71
    0x80c0d6240d0914050381e001a051011603582107c07a07000c3d100c81c0442d035026100000c8504107040c00d5490f01d400284032200303000c20910060340d00c0500c3c0101001011248042c654104010540c460b01d580b41c2000e05002e001590030315030f10002c1c2c00d032a0890050f0f6610305113580d03941c110085004e504000401000d01c010b41040454100d0f00041d41042c1d83e0049c1d140340110340c1c1c40c205620f181406003111500c1d25103940180314050020001c0c0f0301074007958a4070f003c0301298402c481611500100925012844010400c1500c0c00c0200d01c10700c030380e0030000700110003060402a682c1d420510511041c00025400101c490030301d4402ea03030303145084002003802c080c2480c20340354210b880c0c544903138100b04420482c5460301464a00d4407a094801d40c0103050031106a003070080c1400d0710040c61950305030500ca444c1d010119200b080300c40c500e400c0012580c441d4100c9540c5e6032244a6408080d02a00c104150300d030500000341d1005005600c22906981c1e02c04030b00759070003106201c11009841007140c4400401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 880992751 1250 880991501 880991533
    0x1801051507030203040e070f0305091615050d110c191a1503160602100203060a03032703150b190519080a11011116090902040e1009030206060105040305 67
    0x404920b00c030f801568102a200d400503d0240c10071506d0100203020719034401c0e261038061040b03941120700b01000d85034109628200ea501c01019204040c0e04001816070160811702ca074068501d05107000009200c10500c107004082d4a810103660300300b80b8000e046564141c00811129101030a6100c5010798508500d014500d841820042c010446055040300c4041c160794103200d0079010088010305178640f2400d0a10007450880e070761300c01c051424410405d0100550f40e17800d10b042120351500d0b10f5124000d03044021203c00c2d41052040356a22450f43c004000c0004000070001d46080c010310401000703580b8410080682c134511820b40307039040c0101050146003000d42c14204400030300040c0c1d034045550341040da494000f40c000207803800701446102d11129a801300305d0351140400507000b050424045103903c400101075125014545542d02030b04021515240c002c0c0c8514040b0300c042c0c5519040c04411403003c0c040380201200180140c20018810b5800365007650140e0360410020700b01042c020042da = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 880994001 1250 880992751 880992757
    0x30d0533010810050405041b060c0206030f09030408030a030e15010b18030127050f0328140409022101080d0302070816121803150216020303040f0518010515 69
    0x440c0c0d5524040404180c54451b40101401184a00d84024943c00007049501d528440c5400101c02c2048440104015903078200c01d07250407140d504a151070741d881e007005d418610b02c61a03001004030300000c100401020f0b0035620070900c502440042c0c0704d070703612203019400c07064000340203c1c1581ca100340204105100c4102c2c00d110a00c1c005000040d8810f145c420540d90320784068007603071280c0d1840780c1c11004c03c003060101e0120741c0c030914021803d1001c000c0403901e81c030080c00703140300e4091003141034406403e1007074815101100c4044e03541c0b0754681c1c40e55580c6010394810002518821074085d640e81907001c10051490498007850702074140c0c00d410200480182d0f000c9c1b4819216980244110422100a0082550018400e4003019914040c40380c0103805803503400514180c0a00b40074040010500080d03408102122407a40181d0700c0c001100c1811281080d51800b035010310001c600030440d001010200804e0792000c07104103140294510106508080074001d6541024005003911140ca1250b406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 880995251 1250 880994001 880994011
    0x10f2d060b0417070815060d1b0609030b060306070f0c0f060e0c010921020d021809010227030d050708042420060c090111030d05330108 60
    0x4045032032552000d80c1825600250401105080e842c1000740c6200e20801c40c841c01030a5043c041c1c00d8410706c5120310f26140100a10150041441c1300340f0390100110b072101c00c01520f00540148500c036072aa900204011901d00045030381c0c0300ba840100e40781d45400102207101d11000d5903171214101e2103400c00c442c0d509100d08201e512103a40c3c2c00d000f0000340d45020ba4240e0713205240040c85541020b01c0010308101e119440104d282c5108061020041020003030005d40300d07010748440401c9651440440c9048406c86603d0f44480317121400d01030000c2d410340080c11781c5203c1c80d0044010110442145c01e0622544110b56407640c4045015102c150041d4040e104c1c0502581019003840e9441088014505401e018120b0f03d519030b000d03686110b5040508031407542c3c01915071580428000345840d82d188405003000440000120b00365080d41e01c0740e404c041c0c0203810320095a80322402c016025011744016101540900480b5a000141000442692114003c40f5076809204805200190f541800c0900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 880996501 1250 880995251 880995341
    0x2405011b12090f030f02040b0d03050409110409020c0120120a1808070606030c121e05032214010203130e0601020c060a0f090b0a090522050c070302010f 67
    0x10300080c0000f000c80010300114000c20002c208105288104811141071815407481076021003030003800300741d2140c1030f1810b0f1111484006100c000301224030342940070717550001c0303841400000c11030001d25040d0006e02c80102c0c804c5045044044903c840c07041d034001d4000b8481940c9400c00010a090001c0e0005e901c0e44006100e07403540b001e040e858820059001c201d00f81d400c503486040401c10024241513520050490401080540320b8036541c00b007601c0b049214401061240f03061071028000144100c4090100c100400c0426105ca041d40002c400c181784110182001d0140b060441c0354008400c49000301046404640301505185941e80780301d40160100781107100d0700228034000d848420040c50f800110340c5428205050000005081c400960410102d510b000c1c024411120f1f00483d040c0c0940340c04541507801e071482284c0e0750b0340c042a00741c0ea2078109030511050054030050003006047d07043c020ba0013031014012111520040d00e00b00031313044881e03200d082c45080480188000c10860b54028070b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 880997751 1250 880996501 880996517
    0x60115050f090a030507030f2a0509040c0b0c010b040506120a03080c1306030f0c0306050306190e030a030902010809030c1b01030e060a021902070812030405102405011b12 75
    0x61503a524001b540d800c1120400140c80268003400120942030050900908083d00c00c900991a007441b400403074401e547c014040c20002c1420807d141140d14054040d50078204c0c2c840d00c04035140c60207090280090340c080c2d031070100440c40c982015188280711000e10401086260080c1c0c0d0115883c580c0100000e0700d40c0c4041c0400841000740e400c0b41c50080407955004103464010019003803c035401c03210b4240c10316181000c20000c0b901c0203c0d055602010400e8851841220300c024a40600f5903201c41c10998040010002000d1750103502014030349000382c0e1001159074900820903904d200b10340c0805c0303c0f680160b1501442c250010780800d02d2140601d40490f0009890085c186828800da82d400e00e61500446c144000200817144916400a1f80c070007014030616100301d1030303151b5503000b008000740d2f0030000c0086d050100c1000718030385035040358101b089030744074040c46081c810f40c0c0340440b40e01d403c5038444002210b40c46032a4001c0c00e1800b0307290f02409800547d581544403042d001144050110341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 880999001 1250 880997751 880997753
    0xe041703040b0105010e060307090b03180a05060f010f080a02100509040f092f09040c0807030312051b0307211802030d050c0607030e01020d09030e03060115050f090a03 74
    0x10001035401144030342d4119000d5410100054580b0030980c8050380208000e1007000061a40405d42c84216910b0001e11a42c0783c903104480c8801c0b0141952945a91140c050241c04211000178501e00c500c204c0e5480a505980303507418004003510b00c1c4525480ca900001c402400342c03a0603000f201c103411003410410f14085401c00410180c51200c414109081c1e961141e1805021107031503000740c1585c0c0d41c8004c201c0f8003950788880d80c0030048015094010440d55001a04100300b0104502c060703e030400859100f1507030f80c9802450b000300f000b2120199401d0001281d21800e0604030001d05110b920f9249045564404040b200344007107403105d01034065101400c0c8501c80d420304c2859030503441d115401d074448c00d0718018103113005480306804040000411105586440c04120b8a801c48464907000c25a15a03d84019000e030040c10a002da80c5403814501030f08140c0c20a80040c3c56287c10707015108241e0340c80d22150030182540c0a900d001c00c208001c1c100d8402c0c020b10082c03422140040ca0b8409850712 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 881000251 1250 880999001 880999043
    0x108041511130305060702010e191b0306050405160f0b03060103090314030109061703041d04030201110307050a17010b0a050d1104170f060126031b011a0603100e04 72
    0x8941c2c001e81c2d00c5e8010340d00b0311000d60307030a00880440606100080403601c035100e072641e60a00440c10090807080303642284269035942a101c50004642000d01030005040501381540c85401c024045c0c62403142d0440002910000070030510211410900c51a045030303105801074004c4d1030b130a0b400f1801c0194000840e10604d42500140d40a40300d10b0200180640c18940703042a800000c0e0076030501340d88140410051405508416030320180c00d004890010380720ba1506a0160001103103600d1000300100030810003580c490045c0c6400c074903907a2013905020090604504d02c3c5020700a200b410a020013a0022540c0110020200402d903403400242d2625105641350084d0400d411820200710525181079016a081004103038800b89007014000c10351600c0d9403c0088400e0344580480e65284c21a0403260510038416900302108005481c1a15410b00d0081d03802000e120502e0080354800c4158104a41492010781c2d101d04825070a200c4000c2c28905108020315005004943c081c00110400b03036540c10b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 881001501 1250 881000251 881000287
    0x3030f0c1015090b0a1212050c0a050d1205070f0315051e090c040b0d0b0d060c020c01021b0105071b03020a1d1e0402100e06040b0c0c0108041511 64
    0x1a6400404405030038403003ca4141c0300c08001c814414880551705000c20748412018050700b50b442840382c4050214450f00342c2d024040d211440701c141c019240745c00203107c0085956440705500d5031b100c5d002c0c09562400b402c100c2d54203549400000d66800c40080c16a1b01035400160140442680348950342c2c0e83c2e10002d003200c0c00e0440000349000c40c0c0080140a4145456040d411281c3e001680c0d0505081c20900d5000740210440c500341c2a40302c1d03284031282d4594400614005401c088140072a41220354040d44c0c4410684c110390062160032001d101098040381145998403050750b843d031502e0103030f40364030119400040002d4400c407116000000140d60b8100c4010083c051145180e03070883c0f4500c4c04d2900510018032441d81081d031007005003180303103c60866550195045a095410310b5140500f03c5280003625011500180005000f0414800403000380040b200d41c5422141c02d50701050044881a00503100200b0304640c0c041645920b0001f504083e817034000410945052101d00142035604034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 881002751 1250 881001501 881001521
    0x5031303030903090810060f080c150a0311070602030612010b100509180907030507060f1b0f080414130903050406050a051e071b1a0a0903020d030f08130203030f0c10 73
    0x6d82d48a004004c01d201c0000350100030000034014000840005000c034040d002c080d039000c06e00e103100040400381c040c00791348402414400301120503103074411031a000d00250b00070741e0031501c124028061188001014003039102905000303894003d03201d2501074161000d03007246403c1e950110244158036564500f07801c02500c104105401030503824950b09149080070140e80001c4204101d1550000c14917800210904015802c1c1030418607003281410500e0280710b035000000d00da04000a800988140990b14024601c90110364000c980800e03800854100e444034400140840d005020421410380900050505c0f00400e00342146402101107078a115840540d10302010102c011520b4002d10080034404c504c1c007100e440a80d80c0c12803c0181c4441140b00b005030140404e00300140c2c69020070720401141d40110f6000d40749030804060b0307150140c2140d02000b03440e00000c2c2070100050f0f00d9240d0060301070201d50081c1c0078510b4203103210300d2550b040e40b00d10340513549485291030780420400907124a50400d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 881004001 1250 881002751 881002783
    0x51e2806052e080c060705030d0501080309120c09042315041a1b0c0a08030f01030b060105070f020d020109030807050607120204050a09150f03060603050d050313030309030908 77
    0x203035040401c841c8001020502c50350070100d0100511401c1400a101d18149004841480e1a80c80300d10f400c601d140310b450f8025001508190000507201c4000024122601e0103c612244103c15000f94581e10b02c20340e030400307030310503813235000300e40440c0c1c014140e45078402410102041389081e80c071000d840d145900315000c0d980174019040000b40a0f0100707201c500c2213540d42000907181040103450701c07100ea060010b03400c00f01000813001443c40d01003146450b902d130301c04141e40c4caa01d00343d0030310106400244026140040c0a40000e021503209070119011140d001c014180c1c0c80c0660380900078135846107541203041c40404080800401c0390342000d000d07200c0c40b81e80105410b10705504010b00d8014000002c4000c60b006000900c21541d4070111141901d070040070009103802218458940d00e1842c0c4c6c0001e134284054000070040c00b00d680c018005680c00340044645102040b4011200303444110384034107480b0256986c07400042d1107504401a80b0740240740074218981c5a8110754204402d4401112301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 881005251 1250 881004001 881004031
    0xb1e09060f0a0b1e030402030a02090c04270b061911070b190f0201110f0304061b020a060c0503010e06100215070e15160803191404051e280605 63
    0x400d0801100d03000d240700c0d0b454404c0d07085051503030109543e20468a0002c1c8516010000542c4054001c0d0903200140945092206207031640300c05092150700c110000c400950901c040d49060b414100300f10b415020080442003001441d0700d0085a0590b000c4c0705c038007014050006e002691442c0b03040039120440ca088a02860b04005020241030095200008400e6905000d4840100710011081d0380042c4031034060140c1c3d07582d4030b1900400400c0d003c06111040d100507810b0000040e0b000401e0004a0301c04c0c81c04001e0300a024034150f07031034002449400411485040040d8041c14040080c06502001e80125020000c282007182030020007210240000f8204840d41c0c00e123858030003e0180320040c0340c1d01d0329160550345200250700600c000000303491030200002082c0d40554070304520108403404078040082c0c0342c90484940c6520300c141d909a0b400e100e101c2111000d241d035500410345008002008121190488000d0078032850b940c0351b0f03605101c000c0d41e0340d1000300300d650007960320600300c1c1a041c001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 881006501 1250 881005251 881005267
    0x3181e03031801120b01050301060c02010504050a060c02030f0610050f030a15051f14010f020f0703060f050f15040c050f03090303010303090e0c07032d120b1e09060f0a0b 75
    0xc80300c0e007207841310030300b05082240010203640c1080487c1e0640d50b00e440c00d600041e400780010395141c421640501d801009010740020b40550080020300c500784203c003958030200c041a4004d691b4007003074944940d4000401340400480c03400d20459204101d001d415150041c6181e1200445124820065020140c488081100b090070b014908519010708d101c8006c030039810103050518550711005031505100c03c1490540010b0f0003008a0a402020401281d40041d101d00d401000740140d03030040740c102400c10300860301d071080c0e0007100303842030a01c00c110105040700d50b000c020107010b8010381d20013841010000c018491005100441c81860010001c40da2545546801482c0440c0e075405081844554030601c05802030b102e00f00c41c066901880d001480b0707184080070000842807100140512101c07214400d0b25650085824071240441030010810080030109005501029150a8608031170720b40d0344010074a030520225420100107000c1c92000484100030900400342e603046007040c8480803420740 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 881007751 1250 881006501 881006507
    0xe060402040b011d0d140607050703090e07020c040f1506050414010201061d060307180c090501091811040305011d0705010315140111010216020a0803181e03031801 72
    0x400040d0084c038002080300281c070500405091689040e5118078600d008100502803440e00003034900001c80155001428900c0002e0300c1c0c0e501c941000c90104000400c0010a0424078400364400c10b12900605001001182040024098410040d080a13642c481c8118000c44052114014200648031255528200324402c88820038240e4240d04580c100ba000703021100000303a00c04080c038407000b0f283c0c0f41926a040020700f0280c3c1c0b6000050002180c2c0c036440c40c500c409410800388000c00340c640c05042e03500e0781300440724562203004850601c2c21a05d16081c00588543c001100484101300b090b040c240c49a42d0300d42900c02c80300300c0c2120403041603004521000f05206010003800d0174202000300d50b18040000404058911841c0071005c10445003000741d9001d411400440c4420343c0085683e107507141084686201c4d40302e400c6e4098184803c02050340750000080ba131712256141d1413201c46000c00410401c1544c4104405c168146403004081941e8404202410840c0a0b9804511010410304001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 881009001 1250 881007751 881007761
    0x708010f050108030f1b1203060909010e0d05070203070b0c030703090602030a0905090606120906011d04080d05071e03050a0506040b0d11010c0503190807110d080612010e06040204 79
    0x4500c50074035000c01081043d600100b16031040c000381909985654002c4c900c5d140c00c0c6115220388400c0d0244c0c1660a4131030081700300031031040400300ca081503d5240d0401d50b60885030940840007581e8060303122a000903000d1006001040e10040403150010b846101000d00c81d080100752614a61001c18204109504400d11502030300551008508004000d0070042038a805846190f02441418000c10704640301d52084407080f500c004000c00050070400b002542c0c64209111384032010340040c45400d000304d0741003441d5018540240703a1a0070803031040c0d0340c8001003070050f18035800c0c0821001482e41d40440d010250002003000d8400190328a8032950030400d0381c3c0c1c02071404d40704a01e001201e0b1501c0c2d4a81602540c03250b00b0042010203080301e000181e425002c030010240c454480428107000669000500c003000b90513580d03c02603161600a02504d498842c5a404101c40d0051301130006010b214000380b0b580001c008107003511101200c10303a0f9084442450000380c841d00709104000540c2060f001b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 881010251 1250 881009001 881009021
    0x40905011b081303120b0603130c0906300b040b060f010c02100f02030906070f0c0506070c120503090604060f0e09010f09050604020c01060f0611010b060406111e070801 74
    0x2000c0d5464001031110010700c0911000f800d01210300405c810300d2000350300c040c0c0c3c10103000d00800e90b82d0910703401c803803940310f104402101c444840700b00106d011902d030300644007201c0541d10740c020f542e00425120108031405515800540868002c400c000c581408406801180280003400c141d08101d018006038640c407802c11818000300e6015040181c9507102c82024800c41c510744424004071042c4201d04502c18008142c0c1c8c00000410740c0410700c040c0d00901010703c1d20500411000341d42c2c070014001c4c107014040c400380c41d10005a00c02c020700c1500b0f80c60300c06028407074429039240141000000f41290084d17000704000032841114290015001030340d80c9603017a42103c25011070740c0341000b0b44000c0045070003411010380e00c031400b03d1300503110368040e14240c00412009220003034031040d80d800e5205036441520b0000f210300f42c80800e00c540611804844181c05062986040d0401d031060b60f01405400b209000c40c80307200ca101d40c0c2c025a5200b000e650203110b0740605540c1303280001c407500392408001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 881011501 1250 881010251 881010257
    0x100e01090c1407230d0314060a0b18150901121506111207080309061602030307031e052e1202210d0206010303170402100e0f040905011b 60
    0xd80c10501c1d0341c0000c9045089008070300750700e41e14042458006000700c04180b5410101d110b0301941e9a1001c40444c81d05400f00b44c070360707080181140c80110507504090035a207064004d07464103800c1c006981210010230103107140b094075194150307410002c100f2010304135940242d00f100100e4000740359a40701d51380c0030250a09240902655071802c0c1180c2003465144079803800e1280c190104070b031540060000448400c1e801d0116900d40e8850300b000910f940c000c640f01500da00515000440040c0e01c410b42442c4111a98011810740d545c84606400500b03a255007120240140400b035103848040e400b500d07214180315803403001031300380510155045036200c1011314525072810f9005d0110000c00c034040f00304190112891440000f00780007128440c004801c02c02c1c6103000e600b09402c4101d800040c0360341200d2103a038980010390080d00800040750010384000354004004241010382600c81c6014001e10f03c03009260b500c44809203400a411160501c20454945c4d45500c2c40000c2c680c48810348043e108080d003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 881012751 1250 881011501 881011511
    0x507110f03131d1602071805100b0a0207150c1217060103020c0a02060d090b0a0603020f01090806062214041103121209070312021c0f021207020409060203100e0109 72
    0x83c1d5000d0440c04002c2660718800c00d41e00882d10954400c02c1503000805010900b008400380e45c200300c6d40541421902004020b0000e800014028502801c40c0c9006426501400c092810448030483d40d501d48801101007109d100341101c04152160008240700e4505e44648460940e0390108809006006041a041c14810700070401d00703080c00b003091902c95a04413141a500c03003044860300010510510040c120007060010085030140552044050303d008586283c0c0d0390f0802e1004644403044c40c052500d8036006a80030550500300003140356403040c0d07400382003400e640800315000c040310048450642442590000e0109003e52038010342e030781d0903065001d001d5081100c11400a10701ca1458030b101052106400626403000c10300101028590101c0103ca14100040000703598100c49031342208419045090031070054018090000c030284943c01034140d801c124118083d241d003190f0b0301660420348a440010004507035100541c402c00810400500d60740c2000c103007445080c0305801c4400c80a240c0b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 881014001 1250 881012751 881012789
    0x90c0315010e031b0a17030a090e0408040311010908010e070f1509210506150102010c0815010f14030a020304170711121501090209011713060507110f0313 68
    0x316050800040c00b016444204d01000c0128010310f100b58000c000c9452645865010740c80c01200030800808140d403450502d989445101c8000700c1d06032001000f03007404000800c0020b9046209405070301c4141003918030f0980d0b903e8420f0940300070307205d440c000d07401c00f110601c902c03001c032503484015141c0e0034030030520341c00101005007080009010700380103010120344404c0340700d10030300302e484100303070711000303480480c20107041c4091a001c032880f00c2c03805542131200c0c112031248030343e079000d01c40c408800300c800d11a415000192110b00e02403110038108448400000403484600c002140035526000f00180e40740b03454104a031000d5842c80200d41034080401482c0045144c48010b5840400103c60345040050f8220142d0b00d040505140c0d08000000d400000035101d4055002d0249401c0a80702c503120021a500000c00c0c51604503120b1281e44407102014000c684140e1025502c0074581c01c0802d00c944400400c946001d2030101d165510340c1c80000c544490045451407007004208844140c001c0c0500c0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 881015251 1250 881014001 881014003
    0x5030709110d1109011d1e030c0604120308010e041505070e091311040b03070b07060b1e0a14060d1a0a180501150f0e0f090c0315010e03 60
    0x11500c60312880c0c545074a4041c0e00140380e0400c41e030680c20000001c020700b02d044806851190801c0400034080b0780382c141c0c80300007002022505500000c0040c42d0a1940203404d0780014036030f451040c1d2581501c204003800025880740b07002480a031003d0b44101580e102d962400501504050300002c0e40c0c10001d4003403000150321100030702c9813001010343c08251a0740e50b6400320f81c0d15440c1180740d039003c1c60750b1050140046995405c580014000c410b00d103036403414030040c44103513803d0b8a0f07031541541c06100700f004540007000240c8100c922a031004140c030450304001610308130115000c0311681c514074511864038039010031140000e2504010b07859104000100181c0380d030103560001009143c651000c00c1c5001c0e88501e04540030700008081c0c4509649030f02e1010500c6200c900914400d0f071510001180c60801c038943d42c440942213a513042d421404070380084488003c0e8000c0150048000300090701c1c6543c845080c0751007180300101240c2c513403900086800740a074042c05154140302000b40080343e6520 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 881016501 1250 881015251 881015263
    0x6220506040b060f04020703200304051513080d080a181a070903061814070b04051c0204050a1a0a08070501180b0d0603031e05120c16150c05040503 65
    0x2400011042d101e0b9100070100e207a44d6401011103074801e10000c0c405007011f40110313031442d0204444507108641104400290358078402c90140d070703034000c40901100d0100e029070401040d8a0080c41180b40002c0d0381c8807541d40c5011580311502020490700401c0003d842414440d1f8110701c80c9000032400165115125110304c0d20000c1041707130001c2c8010b4006600307907004d040ea007002150f0080c82082a40d00342c1c245841400b140300700441d0384060400e81e418010700000b6660381a02da000e402030340b17043c1c509003c1214079059440000c00c403c0e544040312016a03280e10802d4031034070b260000407c1040d041301d10300f00c508100031641da100b01400c4005104002c4002207000a0710740a0a051541c0380344011701e200040c255600082400b00000707070750f074030503801034101c0c0040381c0c840c0d115004200342070100c501c00c42460520050004809114100b4502010940c6503007018411106034540388400900f40e0700342d100742d003059840c03031481c100b561240315440c4507240400e8950f00d003107030406082c2000261950 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 881017751 1250 881016501 881016503
    0x70c0c06052802010606020f01050903090405060a15020307150207110f040222091104180c09051e09070201020c030706051806160f090b1b030d0e0622050604 69
    0x1c00442d2050a5203140b09038000800d98000e50b04030300140103580207002c0c000d540100c0005001e015407511549134140074150007004200c01440c100340c1c2071410300004100090105031301000d258000110610f51046103010781906a01465130b801d628100506240c610003104103100d40304104140204030090030400c0c40300401c46030505013013581c00000d4080d02a83c80c2a000742c50b0040002114008503501c120700b211000c1038140403000c2a503840c3d128901452141c511a241d00c1500085001180e0f0b001141001603801c0c000f0190740ca90004c141d9403040303580c11441c3d050480c01c003610146046600740768822803c0c402580b0705104400c02544034042c00c84000d00030350f181d4021404550160b00c01c0da003030305081d00441e0313001c0c4ed200c4103241d810714003040210045010011409a510701c9051840191011608143d207002c10020ba0f440c0302c60000d803080c1c8110301051001075a000341c45e00a444031451000020034040c200a56219408102905120f010303aa10210000c0000c5010550590103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 881019001 1250 881017751 881017757
    0x150207060806100c23120301050907090503060c0901170c0c010e010c0c020d050705030a080d0b011407021e03030f070203070b03220302010902210c01020a0308241f08070c0c06 77
    0x104144170f514944004000c10300c1c03400d004c4d811045070710540070300203075049070004c540c08450340d15805015a12480ca034041d003a0141c2240e40052996012031000b000035510600d08000010b8140c400840030101c15602c080e0260000600e00b44966000d000f610159104070008200e488403168001d400300c944020028010381100c0305075800d1100604c40c02000705009001d94805803d6403800304040c0d0b120541701c481c62486d01c0f2289010b0f52062080e591048080f800c4c4501c3c10069400308288112503602d64103114100284056454800b03001400348914506a1180c455907030307104050074480503410556010000b07004000c1020300d8400c1e065603900c028900e148003032041c0e007400ca000d00804007029410a440a01031180400d0700f4200c445100d100d942922803500c1d05000481e1230b0105140d006e4000b403214000720b00e001c154108646103240b00443e90480c0221200e010505074011801e815003041100311400e4034094015103010381c4010549001c40c80481d150751031680b594050b0058a0030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 881020251 1250 881019001 881019023
    0x301110a030c0201060e0109050105011d0f120309182a0f0a091a030411121b180c0a0f05030c0f071a090c030705031501090b0a150207060806100c 64
    0x2c1c0707070003984502c0141c2444100c01e0019a11810084060302c020f00c280703400100000141680c05680c88403620070120000c1c48a03a0542c0c0c0401007140b124201c0845281e00d000402c407403200d940d9115a00015030f214609070001e18942401f94002401c0026801c80c50100c001400403d100c9541c02150201d8002c640026210107145c5401c9036004448c0e0042030003d4449400c041d2098100005503201e14491000341c1400d40303a12007880801d01c4c1041c1d201d40e182d40b002031910340d550b09189643c03607080350283c510240084001c4044c0c207140010b4510500403038002484040803940461b002d001d41c243d03403c00c1495401d001c01e00031500e102c0c10341c0303c480184000c528001001420441c998041250003001c040d20305007030310745948603000700c00414403e11400400003000d090104031150b42d9196044900c05980c078202030400a804041c0e15150b00c031841c2c003000314100c944d25048081184260740106000c0c0c0c20840040d01c60035000c0c0243d4402c5201a1843c154658010358086a50b580050100b603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 881021501 1250 881020251 881020271
    0x50c060a081801021e07020a050117060d061b2a02061605070b07150c081302060705070510020d0f08010e04140106170f0c04141b120106110c0301110a03 67
    0x1009001d80c00380c940b51584071001d03440c0c071585e2510103030a80500885040e220720317903144011751f0f10344244042e00d8203521000b400903007245010182c8207169800358070b022a144c03400600912000640d0f4400c080400e150b444c01c03000c1185c01128100100140d46140d00d0040030369000200300d40500300c07205d25010180920030040040511550000700510300c1803035242c902c541b0301088060030307001402400500e018940052584106034803405441c44400c3c0c22034080d825002d02000341c0c49000c080d211841b41c020000340035116034081d50916072041c2e024005058000d00d004180c02d45400307842040040501c0180039030b5000008860300b25a00511030112122800070302800750009502100c2510000d10959015500c0820490004020302080e13400c4400550104412901c8001c82d4440001e900030000b15148a001d442c02200b202c1c5081141c10404422000d5031001c800740c00075000660540341510750500100a54000c48108070000e10488104102d00d016500814544904040e190502e001d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 881022751 1250 881021501 881021503
    0x30e0402070f08210403080601170c180a0510030605100806030d1d0909030c070b0f0a0c030c060905030a0e010302181512040501020309191515150903050c060a0818 72
    0x8810036041d13440d0108146010f080140072000c04035502404907600b114804803100307800899910854803900d00301e0411141c1e04d01050310407202c44042e500301e000b4000c0420682d807031001c1200d41150503940070903401c3c00d00d000d022014401d42c240000340b00d00203090018030f40e00401d414550080c9458681114100c1202d801c15030544c440402d60043c0b044410300181105c044018668250700e001142c544545c4c89040002510800a0128941030140401d41c001403094242034040b5001c0d24021107552919101d040455101440c1110503601c00170704d50f0900c0350000407102881c042402c04600340720900b05645032281602000c948074066449002540c000c0341c0c001c0c0c900c800300c8104400c4451400b4030f040e40c002e40c01074401c00c52501c2034190190b08491211301000d800c80c1c0c07080f4082007400c0310300b48401c058040845a521104c69901c2d011440d00c140400488020340203584000109156080040c103000f18004900d0262070308004012219800201290b002070341c15800d0702c1d100500100386 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 881024001 1250 881022751 881022787
    0x602030a02072a0602070812030c12070c020f09010e0412120f061d0c1905070f05030a030506092a0702121c090f05090603010621030e0402070f08 64
    0x3004903070405030700c400d5030600201c5045503143c1100840c04040d12400203907500c86181c414489203500c01c49030399071800b03844400385800c80011250181049a000000d41c03c000301143d0540004605140010551030181400302484c0015076100c240c80d4102803e404002c00020406420111075200400000b4030601420103041c04080c8100700c003040503501e10b4058101031003400251b100e50809100d600c0100340000380100c42c07507002c0500d421045030030704070701e0303495016014288407080c8883c1d408606101603521741c5d944500081e65072016000000b0f811144050074880c01521403604204500c4010207009160105450070b00100714040107846c4494410280c00a4000e000f0803030191001c9000101d2a00d15036840c4e181204c1015080c40842c3c014003240b048420503075406804204505040120542111020b0004500d1b65151125900b41450520401001856450109040c99802030540e020180c2c11602549050955107072295140071008014110440c0060f200860701019179007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 881025251 1250 881024001 881024003
    0x70f0c0203190b0a0b010c12030e06010b0307030c08160509040204180504051b0607020f0f0d0b0106030b18060105220f0e07020303090d1b3f0c0602030a0207 69
    0x4503841618601d10a4144040b100d5080320350a4418000c00c241c505140911803c605040c1d44e080070144031603c41c10403801030745031004289030f52506110042e04c2d06000c8107000c0c003400f00d02a5a64100540020101e68121021104000501d01803107a80b01c0500642220352602d407524584410035235000400034030aa038009064100f000d9030424180c0c1e410340200b4800c81c0981c2c2524500c1c072400300c4034154000840d81c40750340040b04100a0380140380c0061285100d03c8003070130081200c4100d4000c140c01607541c0d10b0036204800d15000402c00142d00d8010b0035841507080d40c1e1116440c980001c0d2031007815000e440a810300c40042a1740846070b1581485c00c80315507080811503100c030ba0319a080080750045000314212a0400303400a000c072400003040300d0140c0d11840062440f40708002040300d080d10a084045181109048114046014039070103180654001d920704080398101c1d4203107a00c41040410181842028110b80f031181600242e244d4403e03074110102596070784d00c881c02ca000034810900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 881026501 1250 881025251 881025253
    0x1017030d150311030a080d0f0e01090f050d090501140f07020616060614060d0f0b131d010501061d0a0f030812010e1504180b04080a030c17070f0c0203 66
    0x41c200c2026882601c461003200d0045090b80078a0344400140b58840300020300181c0b0f100e038100084440704a1540c007024102c2c2540d00700060300f60445049c40e081d54405001511100e100d40c0202051040500c46002c8081c950309020312480c3c40e04001030310080c00d031401068000e80214402c1e1a0f045210211030703140b0b40c000c080726030303172a000e80580345480088a070664440e440c0030008602c01500c1d540311410980000c16060038805000c5041e001307414000c40d0324500c0d50701d0710b01e0709400351180c405450514142040c04540065040003001c220b02d407080c84e008403a1306010040203c2c98100030440050551798041c103404e074100b40041842d050702030380954003e41a40800005004403000a80f244104028101c145640c0e540741c04884c102055462024001840341c0380740240c507003035218515452841401a814440944481120200c04c07602900d01d080001400b4403265854498045446010300344004010304541001c02c0441005203190b05010095058141c0e0034080d81d03400e409140d0040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 881027751 1250 881026501 881026511
    0x8030304121202090f0d030225080606060a2016170610030309090903030b060d0b0916081305010e16140405010b0a08130b07050901080901051017030d 66
    0x100c0c00c1c6a0034021600c244000640084030300c21500000e000300c0d200c12400412115000051404111469500041c01ca0a6104400041045686540d44107405521184011a07150314100143d41003400c0104210301c60401089030300d0003a60406100c0103200701c59000e0015107094140c03020b1508490803000b603445140d0303200c0081e140511191805500311602d041d1049501c1d102443c1c0b0a0b201c80f400010003003650808188102d4007035070f0000700c045009142c00300b104c441030000315406520a00c00c510b5204d84a0604983e0303400c012b5a400c2c0c1044421410600c8100b0889005200c2c0d01d000e0198200309a400d4400d0f02408000d41040700e114408005481850111000000903503041d4030800301340050245440055107080d110300741c102c550390040c141ca0880c05103c116050034004101440007150601900c010482102c1d42500c100c1c1c181d169903554112200014150550041504200c2d07070424040000481d0300e8400c03d0212018100c80303e40c40313034000c0f40c028114054000500701344c510304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 881029001 1250 881027751 881027753
    0x10b2b0504030e09040b0109020a020106030206040e072a080a051c1d0a110d050109080d291305060102030d091a0702010209060412080d0203010b0714060105011b0c08030304 76
    0x940d00041c040ca1007a01d8842041079010180210035a08840161000e00d4050041100c1314140d0010801e0704540d00c0006255070322640024010340003604509801c00c2d00f0000c0008454005e00c148481e1194001080040c1c448030781581030038071100c0b03802080200d000c142d400303086004100340c94040384c111014400400356818424000c1004402008048498000c00f0a4084c07000c079190100d01c0e040512603d49a0307010080c00301442422104460a640e01d01d48100810b400501070001208440d501003000310302119040030031010405404661014580d0f50710761940c840180c592001440a0041282da4907079005134150302800700085080303030401c003204041042c01040002e01408007410000c01d0384414030124203c0c02190715058104c03104000030f11a08105440b490710851080d903089141605112158050360420703072040c00d01b10008a510020404440001c01d00c9441c89001480103602d03200009151441448614411100100c1c0840c280080603601001038600c2e04120b0f9901d05003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 881030251 1250 881029001 881029087
    0x6090a0b1c0c051e0d05010f08060109021801030c110106060c050f070e01050613031221050402090a0b150703170f04030801181407020d090509040b010b 67
    0x180107600191803080034054101103880c0325601c1c5286160b600c035401c2580f40300c80b601c80b01d0490750b1310010f080003d00c242d5406900781c0c081c0f18080d141024450300d6003850b01c103d9510301034040e0010b0380100e0040c07004415083d0340c60396440c208034091802085c1401008ca00742c0b6501d0304025a02007070f50902401050b01508000c0120b612442501180c0104081142490310307051a8003550ba80440447c00420045c03910001800f0340c3c1c0d8000c001244030b20b580c1c0d038a20a107140070078202c00108150340c8000000f0181e0784021455401244401d0180385402c1c0e00041e540d1000030400f038429603035241235070140d8032171620380d074451a000038029640c0d009901740685400c41604566599440300c9000540d4500746102e00c6020b0741e419180c080315079080503c00c03d0556440c0180407586030b40c0b80d00c541c0640101c100d109018504c40d4014002406141c040108410b645802c0107028011840a11000810070b070181e6045500b2080800c0e2950502d02402c3c010082c0c5211580804000b0480c12744a051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 881031501 1250 881030251 881030257
    0xd03020a030e1b0f010801080601092c06041a0f1f0b13050406080304030f03030903050c0a0c03053016080a030509100506011b06110a0309060506120a0f0206090a0b 72
    0xe8102c500c50b41c480d05038130044410070805d000708400d58200d80010011480c0e01d4202c41d949136822121640d6030707100c0444240b0100fa29005c0d2441c50b5100900340000c3c4420786155400100c50b12041303600501e401c00780e141c211440540300c034840300c0b800c481150046c1c58500d00040680250340a16070b036800c001a059910355003c0c00f4452103286000ca00280d8040700004690850b603100c00b81000061983d1025001056601000d809100c0700b080304000d08a814070a0f60380140c03042d00748034140c2d03045040c40d600d440304e80140d12031044164551800c0d0f6040701c1203450200e4805104140d80d85080c07860036504584030070402001700d40e010641f985480e80540010744035000440854440c8035080200c1e106461041e20007a0120b07034203d10b8083d6141d400407070b90041c28041c50000c0390400c1100e954903000c0e8040e40c400c8000030f0340c54003e001009414003402d40c0003141100c0049042c1042d42103203031280c6000b00000c1c01900d41401c0181103480c0c032816194958401040076804c2d50b81d0300c803074003590741c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 881032751 1250 881031501 881031553
    0x10c020a09020a021b0a03031d0a12051b24070f060c020303010914190e12190e0901140d21030c020118080415031e150602060105030d03020a030e 64
    0x2150700c2170b208014204242642c041b02c0c2c065440400741075142c002c80c4200d1048004164200c81d10a60200f8035041000030074007a01d110748018003d20700707026604801c403200a03c540c0c0c81001000700e1054200340b00d8240300d20f441102000c440e81d900c2d152070419042400c160006000300d0810028070803064020001e94100d41c4881024000f4a400d02c0f0701500d0500708a030413003c9210045024100c2170034035441900c410642c8000c0358040c6440d000720724040c2d04010305003546144d2031041040303590380c40300c0b003003081d940162104c09095060030311503500a00e001403014043c110200c2000c0610211202402c9985505200d0b20310f920a4008010050079400402801560130705124500c481c0e04030500c041c041ea0807050703190800341001c0600b010004441c0d00c800c100354859420b003010141d2a10401c10360807070070000013524100c06107110082c2e50150302c00030a40d0400c0f80104201d0314081030300d41c003a8155240046c0d541500e04003d800502121140415902c0703503c00d071842095956403c40014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 881034001 1250 881032751 881032783
    0x1b0b0403080c070804231806120c0904141c0503070f020d09091e06240c1a040204180b1f061413120b07080109090f02010c020a09020a02 60
    0x2640d01c401140c042c03481038040040411204200c10410410500600c81c401c0c03a507007100025007609034002551003c10250311400700407010003807042a14021101c4400c04000c80301418101040b5000110b84c07441c01007018018180d20380c541104904248540b03098100d03090f8020b0b900c0400740314000c1ca9038008807081c501241c4425000740390103000044658000385640d441c082001c0c1031031002e001070682081040c2c4e544034110705000d003000640c0a91005041c4500040ea00c149190000400c0c0c140560800800c0c089030b00e41321400314a000c1404030300c0844004c010a15915544040b034000d040650301d000e10141d01850000802c40300b103099030700484031020600742c1440341503420701c1c0d0214144540c00100e05128900980c00c04400050408030f11801c1c0042a85aa140705c03c52041480120032140c100032102000318107908084050f0142c0f41c00f9004010300c3d00b150761780314030884903070030041c0c10720031400d052404560b42c921100000c0d052015041d0349902d600c00c006503481422003405001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 881035251 1250 881034001 881034017
    0x7051515040924021b011a10020703030302090f060a080709060e1c050309040612060513080403150e030f0a030612020108190b0607030f121415011b0b0403 68
    0x180349042e00600c03840503040b504020600c0a10450100e54004126070b450846400b48911103480403a80f07090091901d4100000c40c80502c5510307035400100f00003110b240305030754400c800301c6215800503100042c0c903418200142e0311406000065001d8003840c0d20154002c400241863715154081300d01d5006141c943c440040c05501ca54003611400e24041c0310940080140a070500300c82560b4500b900c8460041c42603d15140d51000440c0644080360404402486a158280204083c0c0c0c4201540001146003030580000c81d5580c0b4603417071080d031201900e203040304260519240c4155104021400350403040708d6440da00780c80040503070340184c07074a500444e04d8071100107910f010904090010980c160343d1034401b0b50360503c14a0b89150420f00d0410100d95400c990b008603100c0100404081c1d00949850348104500345004100344c50495500e41002d0030080d400340c0c205801407140760001c44080c0f06028018546004894010085551a0f07499910880d69000e02c0520000140118040e98507010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 881036501 1250 881035251 881035291
    0x5010f061508130816020d0b0c0c0708060903070210030b03010f0e1002040503060c16050f070e071e050906160b01090b0603070912020d080a120b040c080f040206070515 74
    0x14a203000703030783c015201c41e10400074150b4511031498040302c250b01c0100403545580007900d452200c84011108144010303c0051101c1e01d1044c1082180014441e01000b000c1620f00007d1650b100d0040701c10090040380080308000e800c078042d80040c68980c1c4d0280080002c94400c400205c0030f4444215004034900488042d0b511b45c1450b40200c0b4140d8001030010201c40d100d205000915a00480030143d64401c4200c0c9003001038814416640240301d41e40c0284140ca0034144903000c41e42014040c18244045600482190320300394a10341d04110180c117050b0f0700c1d403d410002c1007442c400c214480507080341c5039005004000300544518140c50941c1740c1002155581c006200e40b03032005072440000701d894858100b241030342c40c040c00141181301600c04c8014034140d903641000e40d000410b01c4000300d41840d901c0c0c0346800c124403500c0d240f12170488040c4800ca085420249c90729001500e8030b569800c0c5d050001d0159240c030001c0f50540d42e44101281c00e900211002c81941d903d0948034180404401c0038402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 881037751 1250 881036501 881036521
    0x1050708060f241e07030815040903121e0c02010e0606030c010503040b06060f030f0a110901142a03180d0b220804060207051f170405010f061508 64
    0x112001011070070251401e403c07080d0342c21942c20100310b504009414180b540d81044240003d40346051080e200d02c403050900401240d04000880140703801207240201a40c0400d50140c3c42442c400c1d00008001002031101c020890903540c031500216142d804d044000081d80d505501c100c0e4200450001c0c0e8495440714810503440e8202d09040f140080d03006e00110f0301003104451001c0d002030303008114915241c5404042c5440b9002254a80022003080d001c10030007101a00441e04240401c0800030b25203415840041d204541510702c075a20700c1d40224038400c4501044511203000b00c18080d0050300301e0820002c681e0381354000c94192030b043d41002070031040d504084564640440d8072003048074840c0d0f03c6091100a4007141e6408144502c130f1041003030040b4035071030000c10241002d640036080003414202400300108100e02000b080020701d15015038000e601009100410701206840764050300c86081c5540507022008100601d60315040c2c0000c0c808940305c942d01c04c580c51a03101c010b40784d5140da04d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 881039001 1250 881037751 881037769
    0xc1512050108070501140705010c0309060506030604081b0c061b0f010b01090311040b18010603180b0106031e020f04090606050703021c05040b120405061f0b030a02070501050708060f 80
    0x64400d9001c1c1a00303114960042216607524141b1120312030900c04e16032203103804e64194071050004280e9811403642441541d0040c6540f01400394000e00312402c00d5560380c070451203540074401c1102c000c5485c800311000c0902820121a03070050485848180340d1076420a14041d203240140644540f204107141c2440602170004418416103030511124510340b60742c070140c80d40740144d942c461b130f03070381c0d080005551080d0b654680c5c0e000600700100c542d0b05005000c1e0032103a03868000725a130140d8500010000d0708400360b150640d64280780100304500400180d8281541c40b20311101241c0c000b01d990001e00709802c0240041341c1e6010000d1050980e16803054401d40f00c3c4510140c01600300d00d89000040070b500c502d500d01d4107200d00d040d80c94036a40d45e805200540100d0203403034400c0d102e0750511040c002c0030000590854443c0e5408050f036005020340c0c2d035020509100f01e8188007008800144a9403d55042d5000c0760381100007408036103411403000340740ca90200d030964030809010070081180e0601e0070074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 881040251 1250 881039001 881039009
    0xe030109143901080a0e01090614070201060302090411030f060a02030f10030503220b0c1b060310090e0c06160302060a051b030603190b150f0d02040c0c0c15120501 72
    0x803002d52520198011140c01d00028602a00c0310340750f00c0340e50500d600c24400c03a43c1c55401031400181c141c040440440301c07440060850f01c1103a0619000b40301595410314000d820a40c0420850954914000480d09181045491907001d000b00410000f84d415640c00451107085405007550715550b4804020301140624040500306a0050140f2482c08800420014035420790407806040e403035440900011950200321007840580103100030b40e5041c44001c8031440500001c58000f821403500e078401c500c07103045500c120b901303107070f141c01c02170280c0718081c01803040048000c0c002a5490320384000c042d942c1081080d04500510070b20001502c001c01900c140d034014806e40d1064408130b0500c641c040c03200c0c4c00140805605004040d4031384940c811b0810940122403049039444858070b0005c02c0d0301c50000d4580e40c1d16000303000e498110780c010765520a0880c011a41181c00003240c080203182161000c04010300107202c01c0400030b010401c003c0c105400e5114031490382e82d85d0032170040c403c4040140c5e1310030302c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 881041501 1250 881040251 881040343
    0x4060f030506190902040806060f0f1003180609030e030d0f1116030605010519081207081b01061e08060414101803090509070903030e03010914 63
    0x14041100611076003140790003040081c00743d1050074180c49000b0000080d07510542045034001420450030809100302c07507006030202c5410054140110102c2c07581404000c44920580d1b00541d07104070705020780c1c8282c02d080036803818494010154038090b40145401c0c00c0940110b038418034510300500c0c0000c3d038130342c3d401419030741c240d4503000c002800c0e079a001038844d41c00218001c0e1040c09404034100c0b80004000d5004e050003103141c1d490803050042114494941070b051209510050245100c001080201c8000100c0c0d255074440d03103420020715900540c46607200f00307440351210700c00c0d8600c1500f020054620900c0000110002c4903074000c0003403940d203d401c41e9a005000050301150444180300302501c03182080e00c0310310341c02031640d0b0100e41046842130690317502f01d907241c410305610030402c00c05040300307a03580007050414000107407003550a440020100444e0050049880d2820341204104d1544030b4606e1541d13056a0440079164485480c0c003c13800c1c9000700032618111715850a25001c1d000d881 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 881042751 1250 881041501 881041517
    0x804080c0316033c0e090a090318030b0118020f0703021f1811060903060109150902040803031602030f13051302070201090b0903010612080a02010e06060616110306100f05060406 78
    0x8130b284103000a01c840c90090015640020341143c462003910b43c421007020800059041702440d000c0c01c00e00400c0d9400a641440c000140001480000c1030742c1541d52010034408000040040c1c003020b4801c0b508003071000080410f11004154000620340707414106440301084100d10100e080040300c4c0351600100281c00030a8101001c0b0325442000005071102500080c5007007941808685408403c0c0c2c403e2190681d2240d2503c1100203015441e4050614500194940f03460709981a50701e002c06044020b000d8407181c1000321180c001c200700e48038050707090800c589501001ea5a0100c5004600c0b41c2030051100c14800450750f01c0620840b140c4075030586800340d4607810301101460580050441c95015075892a003c54000211048000d46038854245142d80e12449000242581c8142c0300002c5103a002d1414014030b99194400c0d564100b5244485440902c41030804c0852100500c01d00c1e60140900c005020a000f424629031050b100c60b4100b0300c0d180c581d00c0c81400b0442c8168494800090010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 881044001 1250 881042751 881042837
    0x201110708090301090209090a051b1813060c051314010203120a140a051608040209011413140108070f030506191b020309040b01020a11010804080c031603 68
    0x8107018115a400240c000120014198007081c181b080a4801a4090740204201e104200d410030008a07c2c0213440d00f000740390010341011603038050005180040c1c020200c00005c1c1e08448455048074070640200042c80f06408004015205502c40800c0040070003100c2008220034858001041200300c0c1a4000d515150342c0c1920029102d038050210114280c441400e40345100070000300d2402000d0069001540f410310100d08810503000030000d1050050100420025943d0034480d103044806aa8218001451000000e484840d0500c8000b280702d10f000150500640000c01c3c440c142c420540880d50f9544c1c8401c00d00340107600500c00145213034000700000715514a0100855038041070407002159a82d6683c0140e00d002c0c804500a00050340003007000001450b0602400b11900400e002910b0b8550f01a21030500b400c00d41c5400790305010f40301c00480c3c20040240d0441d18402002001c1d40d80700d0250301c2031481020306007a0168000703105031001500e2200f074107118492081301102070f14012003d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 881045251 1250 881044001 881044013
    0xc020c0f1e150c0312070c020904030503180304080105040b0108061b090d050118150e0a0204022a0a1a090c0d05070902070b1b0a0f05090a0b0a0f0f02011107 69
    0x101200c1c0b6003107400603001d010500e650344090f01841402601442d1111700c4150030301c1001d807000702941c08208400e9410009625032501d416007142e01450156680c4e5640c0c021b0b00c4a405080e2010b0102c1e2100180004400006600c401c0c001e91040640040c01d9030b0b02c103c2c01d44d0301c1d44295058100980c41d110300c1000401e44000600c1c0c1c03030b04060300b801441401502c890782141d014040d8503a2401101640c4010012500043d202c01010418208008007480841e280c5d19424850000c0c01954005461301d6116460a850040b11070820f002c104180c00c081030403604c0d0303602e454040313450b046c1220140c20800a0720001604c2240d080004000c403030441c0080210b5601415419155806201c0d400704a1002ca070008000072805480c001e2124140840c4071080360880030f400580305082031107010800c50b40030341c0d0490b0b0440249041c0c0d840342c142e140040c9010580790700c14000c503800003468000c029001201011240069200c1c1c0b80900c0854109900f45d90b800700c08400d444204221031400121 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 881046501 1250 881045251 881045299
    0xe06060a031e05091509030c0304140607021026010e071808100c090504061d04080d0501151106010506030a0c0201020405060c0f060c0a0903020d060906050a0c020c0f 73
    0x700400e00442c1540404114400c8800554601c2460b80001103880401104080742c1d80d0400c00d00802107140180c94559180c50340120300610f844045004485c3e580796a415054a8805400800c072000f0000071074070281050b0400290016000b00301c0220750410140d814825048a07526a013140a9580e011411101c80381c140301c0c1040760350394101c0c4c0460588001c0056200752428590009468401d014026150480c0755100701e128600340b035801e11510705003451485443e642d9443c135101035212840c00302d5050149035456559640380c44000a95003a5100007950038130070b00e44807411000e0304140001e80300e0609000303894029504102080700c20b0b103154003420b035428007440018205612074000848a40c01040207003682da0020354800f1000320f0501195401c0110503a10b43d00e45091141e010703024840911019200f040c0d850288800c0c80302d00e0b00045001030f4004020410b81c900903600740018900a455100144103040c131441944c2082e40c41c41d903180380024101e80d035107540601c203c0d507988 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 881047751 1250 881046501 881046521
    0x120c0c060e221401080106140a080d0e121005060411070c0b0d090501150602121602100c05030a030f1a011e09050907052203080d0c360e06060a03 64
    0x6940b520f00d681032504046005010740262000461081c1c986850001c40803036850b4140e00c076a10816040014440005403038004205d541426841c0b0050440083d507208200d0440207410700514500681d51407899006c240700c1d1608540404c41072010580d111280e0242d2a0b004189905848051251041c842c0150003020211240420b0b140003590b141030030344040380741da2607541810700002c1c89010340601c207604441c00e5006003d800c010300002613440c11340306218064015680140d078103030501c3c82407802200c01030b0450100ca6a0b01e0031403038010000e10b0018a40c082440c41c200a00000014500d0f03024800c3c4070503034a00b80407000c3c5d6106450705810708024003090003c00b0380f00042c90303295012081d120f000540c85054a400409071407010003c104115a20928805213091001851460a58400c5008481c3c00100c80c11405403c1d10090500d00d50300800c9003800708003d409203e00002500840307a802484445c3c1656060600d00050040c0d9001d82e0000091090509a0744698000c046d04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 881049001 1250 881047751 881047819
    0x7031a090c0f161203050405250b04080a030e010801080a0b0a022b180f0807110a090b0a050913080a02031612030b0a0e070e03010207120c0c060e 64
    0x180309001c58142d100800d444003407150b603401c0310203201c904c03000d2801c1c620003410700f44010b282664400d0f0b01e81485140c54181d52640c0841000012030780642c0e50301810b81c0b640304503980e5072039828255480b07100c281c04400150440890605951003420074070b0480f41c00c1ea0041508000c0e982d1820300840004003c1d00f0103560900c1404040c02165940c015001040706406030003803040440081a030b9030f03600601c0c04d4881c100e101080090013488124064541104003d9191481c0d071a1600d0b11850b600e00155206c06088004075a0f14003560041c40040b1049401c41c81d829501c0051200c0280308032400e40e181b110030b41d8190045091840101074041481c41600c0ca80780c10030354030450440c0311030300503542c080e000700010184a0f013503c509039100038101c071f200541e180f03402c00a041e40310b4020b021408004600b800c1c061540c0303007501543e0071070754000d16429000b1090803009200c4611083d090368580c0c0846000a00c441c022003010040c0000580340300048045030003904134900c0e132100000c03a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 881050251 1250 881049001 881049007
    0x9060f11030f040611060606070201080604091b05130e030901030b011e050d2711040902030307080307020c0109032f041b030e01020c1020120a0507031a090c 69
    0xe0346424030003454081280b240894540b03040100062a00021086070b40d0280d100000380162540c0325021740d4031103982464281090ba44400201c0c0c0680b0b840c0750001c0248020401c00c520403003403401a1020b5440a0b02c2c02c012074040001003206541c4c0c821101d08182d00f041040e40b0307c1d54400e40005802c820181030603040300c443c000000c2201c0e4000f5408200203000400c0024112109002c0d69448805d26400481c02e6929107071070803042d9021010061074140401544066501c0707035042103007416002410343e070719004542072558440d4400c0b034503030005001d00c1841c1013132980a040c90009480c0c0000140d8140d201114104440e080b04403400003050015001c480030b0307640c80c0e005051021907140125280c091480300e000c0c041c0c800840000a6903401409400c5280d2000204241620074805c000306a141c504481c5641c03001d620994480200c000180e114200d140a0449038050340c003181d0304000c0307560b03111001ca040707512441001d81200c903ca1640d00381450a20340154108000324041c5103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 881051501 1250 881050251 881050277
    0x16020909011e0b0102010606030623030715020c1201050408040b0f0f0a030b152106040603021008010f3c0807060c021c0c2616150f09060f 61
    0x41000340c2010300742c98161160000302c0e0360359082c000c2d00020310503800c00f0f001041c2410004082e00c0351102d0102c110902d02010030050395010460782c0d0042070840c41d03482d240560604001d40b40d402c1c0c11020fa01603d05940c0e90341000905210b098462038119100703500309401c00058103d103502c4420b180400380010701405801d42c9000008140500f203940740007586aa11009200d148102d80d180c00707102003002c0c0f15070052030344038808c0c8200c80c40118a428140740c0c0c442d400200104601d4201a401c03c2c40c03a445003200a40003101c40e4141d480c4018070f0884540c6c0c60032104071488000c06c14228a5150105c6036072071804080140c031071100060200d00d1055221600640b40011541c000301c0010081c8428006500740707203501840c5013120100ca6603240c0c140b078513201d4000c02540b081076031000b1420200c180001411000348110305904095a802c1c2e205c600c45203d10001b50301410090a4a00c0700e0103a903a8001c1d0a40000103844d5194008410300d4108152507100e00307140504184086109212 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 881052751 1250 881051501 881051531
    0x506150a0804080c1f050702060c180a1206050405161406070302011407020303100803180105090102100906060513051e07050c0109080c0f1227040906060303141602090901 75
    0x403c1c4500c201c43d07a880c0713400d017030038040080c0c2d5009441c44056400c400309012840705400b0840300324807500c011150580c0480008190440c0450340f0203860b0b58032501452041002d0394024a00450080b0104c03000103501841580300550544a80081c580d004440c00c040c50410b50082d040b601e00a00001a42e50390088418201610403a40e00b001a0000002c108034042d911040002a01c000c1e0015801e0580000d000004200380c1402941400004a44040c4580c03007080f8031440c06000c00c0c02403204d001c40c0c1c0703003620180119001c2c03e403280c4111403003581c1025282c454184141258003410181902d492a800501d54014040b00204101000440c4942d0006d0080c0c00d410762040c0031181e5508080b4009600b8450342080581064008022a10f000314010095401d81c0c00307246070700e014001c00b04084803010a590280c1070b410a0600050500f0b1210552180d41180e000e40c80f0804d082c0d07151000b000851017169920b0302136654041c00c820140c20711540c801e43c00042c503c0002801d8803014200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 881054001 1250 881052751 881052763
    0xe0d0c050d0f020a080c01050301090f060f08370b04081e1902060705031f090c020d020c19260102191106100b0a02010603240506150a0804080c 63
    0x1560030b186518419011410048020300007801c1c0305002d40040c1c2184d80008040d488188103003602a901c4640300080507080754402c80090200c0d40e40412a01c0d41c891103540c071000c524150a1003e5515000070651180c10b0000b407410080d002c07040001194581d86903420000050301c10395102070184069880280034100c07909140203060002c54442c44500d101070740000d42d0003650700464003c40107220500b50820103407500305521400791414000780210900d01841241e1110481358144803001304026000f00308006104a40e5003510740d4810386200703202850b0350643d001e00700001c07041020043e401a802003004258044001c2c440c92000752800642640c0144420300604699540143c4105030001c4207207011a4040d4064450b900c6d2a040d2005045094403030f21042c030500051428030396201f94090001b80d580540440100200a40745580002d641d1401070382e094501000f1802c103140255900014030001a0b440e450513583c0002183c0d42403000e00103c035018028894003907403e02c24000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 881055251 1250 881054001 881054003
    0x80612101d01180209040212122a01150605091801170d020609030a210618062108070804081c030c180506032a07050d0504060e0d0c050d 60
    0x4100c06007441c07001201e08440e0107072809091504030109140058031002d22856105404440162940070107440c80ea003403943c40c044101490a00040480d0544000c88a2a881ca842d81100d5456002c10302c80d10380c00ca4040039100d4800e04510f0f40c08000e2140b00c2e034000c00d280d490140226840590140760000700e0502078001290210400d00b00e008048001c101c150301c1c00405200900050a2004815469110f400c00308010000080801c003060201000410a43c1a00740801c2009035559000031160b40014100428a682032180003d50548401c000d00d42c0c002504803a5150b0883c42d07901c011245c0e000c002c0c1210740442c02e010000e420f4405011200031121100d03116a0340d1101c48a000f4100c5a200e81214244040016140c3c2c003183c1c5442294180c58040da039159a030785660008182030000300940300c0c045004048100800444400900f070f1040c441c1045402d54041400241c2c1e00e80a54020000010003d0500c070f005440c0c80c401c40c03d070140c00b9148950fa0baa8070303034010071114001400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 881056501 1250 881055251 881055281
    0x81509061306120f060b010503010e011802040305150a05090307030512070c0c0905040302010507110309010e0316121703091b0d0213020901090b0f0409020702040b0414011e0608061210 81
    0x48031310700b401407030b006900342e01c8024030380607186604150b2140f0809006000c0c0140c1040c0c80b04251050304015411900a1608001242d2241800c200340c12580c10003110b544a40c81c1c14040419102c4d80f00000303440301994140c503054140f500440850800d038200802c88810082e4107500100402c0c1508a440007070080b0314004103140c07030242030190030340c0c4c030280c4001d04026418005060305480402600c1c5100340900c0c2400e400102003000914005200c03402c24261781803008001903c65940c4001070040d44034069403100094200131001c16400301b01c4101c4000d030400c444000300110810582049030500929207114841071390041034456402a41981c0d5880e80060084480d60300903940d40020004400d2240c50190005c080701c000c0c0c015481140b050b2600072603508110751310b039045030070003801c013610400070003400002c0301400600a02c611041054031311089101c60300c88030040c406482c44c40e101d641082e02c55a081c003901000c466000d503110300541e00c8241302942107014003c90503995203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 881057751 1250 881056501 881056523
    0x20d080a080705030c07080304060b0424050d0b07140c06040c0e0a0902061e070204050a09031101050f070c050a0c0b0a1409030a061e050f0708150906130612 69
    0x3a02034203002000c0d01880501109208014131800403400320380465a10100880d1a915207144c001c01a00c2440207041e80282040b05140003996501182000054a181c40c5154030baa500140402003100c0c00000e0000300d5213034005a2058000e4084500e54070200178050710b00000d0140303070b9081c40340940e4100d5500703090082c2004065002c01840e0303013110700700104000125080c0d0005134148610701d03611130050307166a408111400e03070000b590036003500900140800e18083c10244001e1510040031004560084116442c448051080503c51011540f22568607120704070280c4481c11204000c58903442060346900000349420f004200070240d40790156110112142e025001c0c40d40d00a0420074103c0c02d004aa205681c0004c0c54040c054000708000340341c00a030700d260030b20001017100c6d101640d030030034080c089124084401c11744a00c3c0c09a031303400020780700c15039640f102c1c122402c64640d2000785034020444903c0d14082808445181c080d00183e484e0341d030b01070151400c1c03030107409480348004a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 881059001 1250 881057751 881057767
    0x10605010305061c1202070f030b1e01080303070c110616050c061c020c0102160506191404122a3c02031006090209100e100516020d08 59
    0x903004460304a001284c40300090030000e600f00c0d0110485810241c1a00412080a11054000e01115004d0f1640a40294000f40c5a007041130640409840c6020203050b0f50070820600c031300c00c0440728161620032010310700d5902c0d400401c84800f4402141941c541100e910540d000d0740da184c0c000c0903481905241080c2030952414610304044000003030343e004030001c1080030b070b580c9074103c6042801101c01740010384401e07860744510300a01815074524504030b0382c00d1104092000024099100b40c1c41c98800300100c55004564805446031091444034a940c0306012800082c8070807201151207255113071202c40c2c02e1560611119184204003500404441c3c0c1c02c2800501c0710b0500110000d07540201c50500b56048a41c49040c02d4010391070071456031803040024004c543d42802306044461041a040c00882d448089560007588400c0021303104812030003142070000e01980f401d0300f80020040102d1516541e0030010780e280da00000e1600b284a07400752070040180d507500c264042180c0500c81c515258100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 881060251 1250 881059001 881059007
    0x609170102090904061b050f0703030e03040509011d10050105180d15060603140f1609080303151305010807060309061b0c031706030d110f0a1b0509010506120403050d090501060501 79
    0xa900384806c104081000b910171700342c40c848100c8200702e505180000b2414881d01e141030031401190800f0b64030107090300000424862003001d061188252110032000c40e01e82601000a0143c18420580816810721400742c400841078442980d01d080645040c1c0811010343d16921001c504090309161255290414000b00d94140303d00b0f440d101195002c1c200c981022030754a201094018001c2d03a0b860300354601c407002d06210340c400c44c0c02060000100e94807402d140045803103020b4543c0b00c2a000308400f500500301c40c2c3e000e02500b8102c50452000d03100040c1054000c40241004a00c01d82e000c0783c45205402d42d05d4999015000a80c5840e80c443c6d1068500b442c000b8181e400c6482520f40c0d42c0c0d4050b0a001c00307070380e010503652008202410002d100301c5404500a09100d031203498120203001d100032001c2808030a0004607200d451000c0c206182a4580c000c0104819083c018283c21110900003a4100e50a41e81060b400c58064241a4104030090043c0c009a80003c0c074201c80d1079448003020001c43d60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 881061501 1250 881060251 881060291
    0x140901050d06030b073b030f0304080d080603010207032a0c0308090a050a03080d050a060e0f060111031810020a0203070f0e06040c050306010e010917060103050607030501060917010209090406 84
    0x5202c517810303440c1c400a080181d00e002410340b04c105540e071546c000796105d07030301080706158140001058940302d56a030780f18a030b2500000171016010421a9000544901c0c06208642910343d064a0340d40c02e842d1403284140d03484c0050202c041041d03003101503c4021510040760000218450602581d840041d00248584243d080e44410302880e01c4600c2840011a440140d4030b050036507440005c0c01c1d42d900d000f5140600905d510041070007030340c00c0511050791102500b89100300c6003070321102c0c2000100c9940c0e0755640702e011200801880455121003151070700c9000c046e600d1820f0f01c102c1d8548610303134000034140a0b01d40d000d600c10b82030034034040200d4400b13055150303845102128100a0007140715009021880010181030400c0000d54440e902d5038040c02203007024110b48404400315002014000d40d80c0c00007800207650501c150700029141d01e11a0003040e060b20420b59420007603610700509201c1302c0003080240c1da610f54017030044400549a805107140b040d40143c0002c181071b10500d100d519004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 881062751 1250 881061501 881061527
    0xd0f1502040e06041a010c03030b01120912270314031308030a0e010f050306010e0a090507021f0b150c101a0108150a2120030601060906140901050d06030b07 69
    0x890f414a0f900d80c2e070007002c4407e56a42509010440001c454012115418401d1005418510f01031480c020f0000c454156074000450741c44948a01103108500446154100303d02101820072910500010f00e55414840000c0040f10850342420075400040b055920780c1c1c3c02071107242d80045030300141568420f00c050803812003800c1c0100c020250708401051440020700303046c1072020101450a0544980c0140703401482e048000b084503060120303000352075045414418410722041103d200300044c80b48500e4503c5500240714000c0700340c00c4031a2500d280c1081c040c446107409240d401c000e0355403440c00340d40d0305841d516041c0580c00011b1000504800d201402c00e0007070404048000000c3d8541000301d030140c8000111503820484072002c1c2d050000800d600003010a60681c5901c2640103c05080b2171100c002101660041c1c1c1c4c175000300711201209803084c000010140442d0001e800700320300c014012400c040c50254500b517446460201600c0308d55004644801144081003011903010b8203d402036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 881064001 1250 881062751 881062781
    0x9150a110618060a0506060909070225140d03090801180c15090b0c070302130603260f130e0709091503081b1603080c07050904020d0f1502040e0604 65
    0x303103148030510790380d80001010003d03c0385d560001315419030798810a58404580003000c62446103405071000b91106460b92442c6104445084c0c1071003e5808080307000e00b5141c07803d555407c0c801152080200d42307101c0e801d049e014030503034140114075841d0078041c540301065001c00c2180c0011503854101e8244055074894640040c00d01c0d13003429000c1c1c0c883c51072801c4401c00c201158a4140100049041900640c0001d60111a11100d10440e100d1904040c1c122030246001700450703840c0e90a8103151139100a81c208040100b04104001e600c0f00401038485520704581220b2075641340d0f0300440d580f920079105c510100342c0c050300410400e9124002c4c01083d40842d0b00240310545035580d0480c903400f58041010741074000c40c0c0e51761144101000406d0304400c401080709940e6903039082400c51503110340000003150103090000304044c00c040b140f0300e000b541d014010b100d0114050700c0d82801c0b9489003500301c8c0c0724001200421503424890000c1c2c07001d0626204000003070304092041001b192040311415683c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 881065251 1250 881064001 881064031
    0xe131409010b2b110102120408010501090e0106050303030103031215030b060a05040b03031c0f05071d0130110a09050f030a051e2806050a0902130209150a1106 70
    0xc1e4503140f828502e9580c002d03640f021492240c401030b4200703142841341c1c503d144000b1400042100c41504040d048640c1c00d442000207442c4801c00a00340c40040c0111a05a4410401080001d110b51440022146440000224403078403202043d241402c0b0b43c0190303121200703d030500c40c2601c0c200081c40d0050074205e0341040048600004a038481c0164000c0180c0d20509403040286440c103504255070403018004200711524003002c0103004c018150400300801035500d840c00c007055016203c80180b03c07040001c0c000002540d240c03000105203407480c0410b005038603244558400440580a806480c41703d0b240c1c20280e80c1000c0c140400100c504080c0c5109503c403182070b4001c180d001c1690041d025600c0800c000000401c40010b00d0b103a8507040413a2011015040040840c003600d20000ca5180301e50301c140304549902c803030901699000400658130036029030840ba441040c99006144d80300c005800006118004620101250050000f900c01f0625a203e9945017280605c55181d12401503210350300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 881066501 1250 881065251 881065309
    0x914010302030c0d0521070c08010c2c040c031d010207170702010c050709020406140a020d0809150405010c08011e0312050c100b0f0d030e131409010b 66
    0xc1e45010003c10240511445401501803042c140300c044113801d843c00c40407a0a054010136102d040d40042d400b40c0d5101c44042002c1024501030181e200141030326903030303064508200807030035000e0300e0140507001200781c024248152640b660702501c41d480e92070380ca00154032100d1110300c203000e08030066081e4050f4410417258000440304046141803003168100a911440343d4401601c215405001c003030130a104441c000a440800da030001c1045e40e810340e80f440c9240f0310040a41e000b038040e040030b400258024084912316075106881455108000408507003035410800c0c10040400d00585041c1c501d80d450344010002260004403050040801c110410040e44160b542000c07008801e000003480d8048070343d2203100c264401c9003a15646d203032950a41d00500c01c031184800c000e0000702820f50103180c40203061101440d21100340d61100d0380607100d10b00c801100c1070401c80d41c0d803041c1c1c1072402301550b25000c0019140300803003140c3c0301e00074081c00040c00c00c2031b0804004801c170b001400900400590006c0c03007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 881067751 1250 881066501 881066503
    0x60504030b0c0f040513090c15050a0305041e03123206040912020a060606050c120c0703081908130c0603051803030703150503060903270306070504091401030203 71
    0x564002c680c85034403521024603030a080c2251080b9440213600c407500850314201c1500940c404030510341309100c0c1260596803400160809804001e48401082c0c040c488003030201d01913000550320600c1400410080188070200c0c003200b046071142070340041d0003251142203041543c410001d41c1c10b01684040c4d1410703d100d0341c61001905a0070100d01555a400104001c0d032a6034100554190b800b111003109101d81c183e0003556843d4032201603504500f0043c5c0055a0b0b805101100c1d074410068001d8119504440740394003040c1d000d4000d0002341c1c86100400008030b02d60030054a20710340e00c1050183d04540c0c48100400c1c480c0042c0c28076401c1440d1101850028141d405004211001400c01049540e07400328210b11002141202c101c080c0800010007000b02d0381640180c2c1340b0482900711f4504d241d255804c1c9a59400202c1c0d0541c06540204007203118501c00c444254131700420090940402200300011130705002060302e40c000032400114040c003004ca601e000d902d1161401400c03003003075580f440d0002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 881069001 1250 881067751 881067773
    0x60f0303091a04210b010b19170604020a140a0809070608090c0d02030a0606180c03180209181b040b06090f100302040918060b0604140118181506050403 67
    0x45411004050f103d40301300c3c0c09055110a03e541c012400a881d50f940344403561140d480042c1515800841e510030303445840c021000b0360195004804222150345d10780e0300380310003544080c070305400307011422100e030049442103801030036007160556940c91315082914800c0d2902d00c154010005100c00d135410050b10313150004210070307130880c111a0450620341174000b00741030103070345980508030034288280410042c00c4402a2400340480103405c104803012140c04034221511003240c9503490300003000e480c01520b02544d0741a00b0240d0300d08580c0c44014150a801d1400300c42c11400c02c2041400e0038540d80c5c52030a48184c3c81000d1003900c22614045d5400002070307030a4070b000c140f0b03403082840010719280144280c0c140c40103044a1482003001c4119042541c481c860a584121215800c2c008001420300b00349003074034102c1700c22058025915000e1801510550685500030641480c0098005440e910402ea803500e4003099080014080300105003000290680760007440500c02c04010402c0011102410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 881070251 1250 881069001 881069009
    0xf060a0b0a060c11090a0608010e0f06010b09010903022704050709050c0a120c02011b0309060c03090c0603020c0312070c0b0703020c0d0507020a0e0709170c060d0e10060f0303091a04 80
    0x85d01009503510030084004000e03e8024007074640c6041001d014501d070014028005c545000111903840c1c1e0f80e03102e83c200c18840c6802c042e00191001504100500f0f144094102a80010200a036035000107032904440090446003500d030b071342c007040d41000f108070240708141d0040001d00d101482c010b51200090102c40c3d1408564482c91b95402140254038400c1d0300003036244040084503a603601e6008001400b0b0201c1420541d54503142031300c07003050307140248a006043c035031004080d000b81e4036002c400e80094001540b08580381c0020000c1144c08c0b4462861940300b010142c0b134110301e13010703141880710035020b004126005041c0304001c220036140002801000c0c0300c0d500d00d40741d55601050b00c0401c4170000f55920240301c40d40070b01d0500c6030180e007002c004005e490103001440c031304220802c40280d40d26000141c2c0c0c2d4011104100b1824041a6508035a81070305680b030032030303110324590003131981240d00551080c24030b00c2c0c0002050041642c4200c998004151a108041441148030402c1100c0d01c92842 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 881071501 1250 881070251 881070259
    0xf09090402030703050f100b0f0d0222060b0a080601080903190c02060d02250b1303031812142703070807090f060803031501110f060a0b0a060c11 64
    0x1400310b650401100d030255900906480380120f0040030309a588034000d110302c10980c00c01049440303500700030354618440c0341c1c000c090302c90f101010340922698807801e142c280e00284640c0a41805c0c1c1ca868003138480141501c0500c01d580701700700c40000780a41da01401d01d030304000c041424044410000010b540a14245100c00b2a107450550703001c1d6032405e03480c0c800075081030700450028800c282990280905521413030202c2c25006048010301d400da0740740000100348034054804a10b0100142c02d10100803031107030800207058041070344886401840d800c4110f480c221900443c407407155001201e1948038808990302802c000c8405560845002c86241601c0284000b0104403c160390402120b00149108820b40b24160f80312101c1d0005030100300304982180d410000002074040f000400c880c410304881e946800c0442c40003004403080848e251002c00716204004621803c4076080c1310007809000d00c00400100005c0b01c00c140a1055581c0c1e0022041c85503203c003810103d0308000b40e120f81d03240119 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 881072751 1250 881071501 881071519
    0xa090b0a0c02010f1404020f010c0b07050d09230c0105070804030b0c070b09010605091308090118051008061c0215030403050403060618060b0405210c0306071e02030f09 74
    0x1c40308a0050030000d1a1180700c03800c04841d03000c1880c17082c1d0843d0045009585141c1c1c100006401518408503000c001040c0040000014204501c604050440c05040c800040b450810350344840c050f0301c100420004c0081a0741c4122107000b4410454801d01000c2824402d040002d2078585111502440c44068241140c2000080710046524104c40140364080e88802640c207180c02c0b114000c100e14080d00d4007400c1c00c0d00101d0103001c0e02e00811580c4651092020b490000b84270f00468548008890142842c104480040354035621042d42400d14036040c2e560342810f180640400225054560303001f240d02c0110800000945c8a005165049903100387c40266252140d280880b014455980080c103510310301180800d01214680348103c41401d21241800300c03d071a2111032070f4920551207072aa001d1402030f421490141c188a0321003d40c6444800d8401d294441e201184c00cac2001140e1480001d81d0151000b041c0601082036200a10b00301e10080d4281590b400103e0303d04c0c8102001207125490b50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 881074001 1250 881072751 881072771
    0x15140703232a0418090c14030f0609010c090b070c0623030f010612050106091406040308042612180d050d030c171303050c03041a120a090b0a 62
    0x41100e0082508a0042800100d4146407100300e503041070003601041d810a03940784904400c1340c0a40c0c5403e5030001e11aa05461410b4088180a0041004980c00d030180703a06c0c00400c41820310a96100b100c03501d00124180300b540100810200c80d5401142c11013005000303902c0441c590445c1c08099900782c1c02c01c001c8070700144004900410f10f00301c0049034540004104a01c0c011070403a100e040781d60307584420102c05046d52001090b00c1303090107a00b0005101100420174040c0001108111038000ba14aa1815490340c41d15101684130760040b03580000e400b000014040102240400881c11300c4000d000c0c1c0780504254140719100e2920310100404010008800302ea0300d554100142d544d0042c02c80e0310703020500d10064068001d5124000c007041c688910b0000c400140d076036031885120746490010f1449103903035041e90b55402181030340009110522010540745207400e000b203000e0000180d0f10345c8034581d0000a401070000100643c1440c0d041c4205480025034a07050141c02001e00540401d0700020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 881075251 1250 881074001 881074021
    0x42030a2004150c0807080d060b07020904080901050c0313170f06010b0a03020f030f04060f0e07170a020d08121506191b0804050307060f0c03030f091514070323 70
    0x1907200107400e031500024171008028210008003851110712100740059036895200705218040c009000c0e4001149000040c0020185c13401400c00344030504049040c46220b0b003803189950805646424903d54010b001d001c58116003030840000d680490003803e030940c80035403154a4090602c11448207480100304040058080d030182c60715843c5100f900ca80324035041003403444000042d6000d485a42c5810315280170103501d4003405640294507030080c02c09600c0d044a0912240c6010442c041500803001d1160041e0f489041c88038116004548030783c2c44481d0102074200d0140060560008284010b000c03038610303110001500d118002c0412211048203e19500750f9035112402e0000c18104500081d2004108403d0040c00640d10144e0440e45465186d9206540400210f21110040b54400e00e00000080c401e802c06005c0341102e0a0109007519165691440c4000c0540600d81c0e064947c3c00d02c0301a60700203d0255030003030381858288044006483d101000d1411004054001c1140318001030384c00700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 881076501 1250 881075251 881075267
    0x5060607080703030b040b100918060806010f03150b010c120c06050702011a04150b0304140d05030718050105030718050901140111070542030a200415 66
    0xa040581c0556810062600034002d14024084622445c0307071640400c81ca00b41017803020241412911040341550070046090f1105c102c40c044941026200c40d008603001109000e02d600074882803101e448160304616124200c0072030f6000c90a400d92614946012680e07203d9043c4e025035400203c98400c0454695085441400d0404068501030804040c05030b5580d056200086881c070603c4d5203001d0340d06490420094400708a0018649a5003c0003805a0108030000b190803a200d81e403240c800640c0102d0550034130031701000c24000b0840c040108440550041da08102248414007a08412810000040c24900014285d5010040c203680341420340d610740c0c04040050040106a03111560b5036007684000b040c114900307203001408604403980754810014606c0280c0d1401406041491004000c1817002c240100d1840303082522644041c0380040c40c0c581c110020024004d442d927883c94200301c0b0500b0b035082c0304840035620000d115450900d0500c48107a405507500c0080e041c500c0c404075001198036007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 881077751 1250 881076501 881076503
    0x90b09070804021f180506192703061e020703140d060509090313080f070614121e060d030c140c120105070e040e0a02012f0c030f060601050d05060607 66
    0x250b160119030803141d08400d110046540f14924203c54540781c46c203016590145d0310400540d1701101021f851031034040e1810301281001420180c508410300808915130101d254070a82c1c0b00380c0c0e01d045643c4440f42d45210030300701219800040d0300d081d038160340090001003100400304926070041041d140803c601e4000e40001c110003410000300b42002032501e82c03070b5400010b80100c0c4074505100010114030100e4131200224003140540686883d081c02910403a10b008041c0f1002081080030603405500713038045501404907012074191904044850b140000e40180c46144104c0d40d1404010010ba4410380300c86150703030300c00c850420799000507014078a00300060702c0c00740d4486901e1500380b607d12415032190b4410002c42c0d40f03200c4c01021207003e020072074800342000240c2da04182803070b00c00b5501501e00310704200c0101016004d0740700c0d0700b885c0b100700840400b03074280c50341c00280c11a0814a0208900500201060082d104034200600041c0c82072140804400c0f50f41d4480c000a48c540c0e0310f48007511103003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 881079001 1250 881077751 881077789
    0x2210f03040815010602060705030915250306122009040f06150b0403080a090906180e0105130b13080304080306041a0604170109050703060204050901090b0907080402 73
    0x1244110180c036a0882d0007281c102e4400c1a24078015a00c01c0303060300e0b0480d505900942002d0721807150840341503200418140441c4149101c6402150003a8882441a80503e0101100c0454210f0000d404222000c240041600702081401225044c0070a8090070354030803824040c1c07030402c603241002460a10210340d0700480c220204024000c5004003001c005100d244100040b0034414510034080d2818011180d04400a11042c40020095802401121303001d05201008541d2040b20b9000d8a0a0350004810701c3d0240d1440d0b00c45040320b0145443e4422110001e02072417070003140c9504e00030000700024251040b0301d80072401c1c2000f109201d40d146504501c0e02503030b03071805042000d0f0713a501c1505c0d12401980b800103000910b0500103118030020200804082c581031506410b01016a650f0500c040349c6c0d540e88010b14001901004a44c000390b202d407602503100da2901081121f01d21050340501303c101e090603103042083d0794129640341e2203d0103013055443c0c0d48840c00807400c500400041c4981c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 881080251 1250 881079001 881079013
    0x60305030919260a02121c021209010e061201091b080603060406020c0106050a0e0a060f080d03020d0f0e0c09070e0d140a050604110312160221 63
    0x50010100051400311419210a804442c10749900d020000c40b0344100000e405140700801c0700040c404200c90b0505030404116032484040d900002c107016203907035080c5915408540d00902c4c9070038032182019144e240e400500303031600301c401201751644104c29209040140f90088201e0300e82c0c03080141c8070303203286441d161010780d070712447c1c90360080420710100f40c2c512102d078068005592190103694455540540a0000c1d03848aa403040065000a510105155280c100105a50325900e008900810b0720a0b54000310741400c0143c44100c0c0c0494100c01030310144400144a209800110602506d84510300141d5405061011000500281103241c100c1c1d41080140d4110181c00201240c181e001202c009404d515941000e50b04120441c2a15400020700300c3d0100108000100e0f0260040c000410303101e254055030740b9641051001c031001c45204184001c42c10090038100304078091208241222890181c070001c103111000c20010000344a10304020076514a51000030030b012160b2030b80e4045a00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 881081501 1250 881080251 881080253
    0xf0b07050a05062e050102190203071815060e030304060f020c0a060e09060f180901020f070305031f1214100e07080c0d02060307050d1e06030b070f0e06070203100603 73
    0x50500c24400c03503044c505424058040070825640c102c0d41241d5058000b440341000d0701d418101220f825910070790b418000c90b4400103030402105c0700c03521800b142c4800050311101824012202c0d5113503401001c2000000d41604200d0345000040f10103841302c60505036041a5080d408900c1c22160041ca41d401c440d010b040042d92a41240116401c2242100c00b243c05684a00500c641d19072004802540b05207150000680440c00404942d04035609a0001d803820f10359a4144129a21080c1c2c220001840001000b204004c96600025491883c8442000c8207180890403803042d8416500a000d08008208500c030110003003190b041e0a41d50454140081c0c0c4400c0c2109440f25103034465003c06001310071480c0303120302d04100719847c801c0d4000c101d18116102d108082303d10760008013440c4c2c0015692420041580394142d10f030021f114807084085109805c6140441c000c9901030208010301a41880c19185942c00041d09040144259906d0340c4070045d500001c0d141c02c3c1401d00101c1344502e0010080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 881082751 1250 881081501 881081521
    0xf101a09042406150f030b060f07080d060e040c08010b0303031611070f090e01050c180d080301150f030207020a090e10020f0a020d140301060e18090c010f090f0b07050a0506 76
    0x13121880407500c41e401c9028407100d040d01520100d0403001c0e4001e4080120824400001c0041c0500c02d02504005041401c0520202c003110300ca600038050400c2c0a0040104006100d030012020b0b04080c4000d20043c0d15032000309640c4d0001500c5200840800394461076101c1c0b042c0e00100040485404840c0183d80d5594102060301c4680104c1d206181000810958a4014002d1501507083e4480031440c1c0403980140401c0351000e4805640e00006001c0200c000c1040740020314007802d0b01300c411036a40c000c01c11018140c5444800e1090030305005110241c09642d488146030304689801c0f40c08901850f6960943c5e040007030017001c00454610203d03e01c200f03807034040d025007240c00035902140e1140851030801c0c1ea415507090300241400000b0001404100e104803100e201e41741019103600b0480408407802800e1140441b2076107a5948440c140c02d140e90390080c000503c07215107041903544503050a00006001085014104c0509000581941000401c00a24401ca03400c40c0558005060803103800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 881084001 1250 881082751 881082779
    0x16030c0b0d0e030a080610110a120203040e0405010606030b0a12020d021c1b06050c120c070b0c010b010801140d020d080d090309031502030f0f0907080f101a09042406 73
    0x150040c019210b0140c48036000b02320f43c02403070440380000c1450554a641e0540d09005600034a03046000a210000c0e11100614449010f0b512074400418580c0c101840241111510040140702e58006030080001e140e00d0841104c0143d01034400244000490010901c948414060621001d810098a109004410b04003c00300b4144a001402d107030303a01c0508035100c1c069400b84860940000f440d2500b10501c0c070004120352052102038500c01566401c3c0c00c107031a001521702401c40e94588003101d030320750307070040d1050b001d40340070319641d1404045000490038000e18117000034014107044a50000380051403050303840160840030306100d031803400d1030001d040d030070684400c440c01c90b003c0d581c0c0b103d071400358020359104040000b00821320390740b80c1154030f16070b0700c000d868000341e40503040011032008014003455452030b01e100b0003041501c8045401d50b0032681126003c0414040c0c641c00340076242e846903034080e003050300186d602006d4031403004007207040705031075071030750b83c280d241500c0099203107004444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 881085251 1250 881084001 881084011
    0xf030902030a0b10091a10110c1504030b070305071416021e130b06030403030504030e03010c1107081b060a05041d071b03080103080d0f02030f040516030c0b0d0e030a08 74
    0x42401555119103166842c1c820006c0915801074100c42001602c0b403080036906088000386088070241c0901700c010541c0c0c3c5014a45200d406280001e0a10520444a060541105407407400300000e1614500c0103003004e81f141d00101c1c01d800c0013740643c490402d514140c108036002049540074455007045e03150701c0e001096110340034003004030418030315000a1140d000038200c00f4120310314507921550100d0080400800031024000316501040076520244103040c0c10100c1c81e1524220001214071583c6442030a81c00b6442691000004072031000da500015400b014055a441e9200d40255030103850901503070300400c0d03402c1c0d101c0240685088110040c28000c07459900e6618000e10507094200707a4100c1040090042070b41c510040000410b1000100172000c07000e12f00040211000702118260b0b4001e0310710b003107004a10380502052007000d0141c070081c04903c0510a8220307103155120031140503d0304c9100e03114480400c50008811321900300e5101c0503070000030ba943d514400c8602600804050714 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 881086501 1250 881085251 881085269
    0x80309040e03070b0610031b08040302190c1811070615062d0323060306010602070e0c1813090c080c06040306092901030312020a0f030902030a0b10 65
    0x104078622001c1c00701c100c5800039000009104207903120024083c0c0b094848030180304055444034481c80303603280211840881031580e600e19030f1a04080c14024900050000b0500e0080c3c0f910800c100040c240300840d02c200c40701c140a00300350301103812111000307103013030781031800882c0000519008000c0d05501600861010320107089403d89c40d03a0040b12110440100cec580c06550300f0000c64480350780b09801c3d82c0a0406441c1c003082c4510162464401025400b032000340f000390322001c1c402d9910b428041103015040600c0100005ca2500900140040c00038010466481c00002e01040e80c0000d07072250541a81e0192440c1c01e034108031356820000340480c807400d5070000c590400114440c0004903659182c0000148554200b90a43d02c0d02d000400c45408102c51210700c062010310301c0700d90060b070304101030806181c9500662450a000d440903030017040d2800d1242c41000320350b81d6a5088012422026210310700010036094900c042850300143d008007a200c008403104104424405041140c1034400080c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 881087751 1250 881086501 881086511
    0x50f06041a0c03010605121017011e0e03040e070905040c05030601081f0515210108061003030c0b0c0c1b0f040e0c01030506060d050c0315011b060c110708030904 71
    0x2c03a4207001c2c0030a0040c0c9001501c10011403010340600110980c0040c0c009159444032983c0da200045501c42518030143d0070b94661007140003c1e941c4100a0403203000d550001d1010007421070240da00c1e84110b010720000b6901c150049441c03d1311800c044000340001405c02c10444007640009001c40d0000c860440c0014075040005d00c00060404843c0324812440072059a51428036003000b010f05110012544140c2091101481146104040f404003618410f90000030354101604141007a41c01440080382038084c100810001e64000d00c800344480d00045201d17255111a03a9800700303845501c1200c130703c6e481a03411980c060140c45155031403220040b6246020220580240005e80741c6003146d540041e00a0040b060265001c0e400c4154003810045c40503290005401005c0101c1d0820349203c248120040308011203045600c80c850350310202420580c8010362001c0c125032501345aa43c004001c00d8a8184c5420168081d1001098120b0118250350308039480ba4001ca90341d80000d015148224107003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 881089001 1250 881087751 881087761
    0xb03010e161101050f10060c211b0b09010b09040c06032019090801110f0d110d050411041119020309030d110d090f030602180405010905150f030c0409050f06041a 71
    0x82e108d01202c0365101d000c00b5900d2126070f40750130030050030440000900045020381c440041a0724440c060440c4a50115180c44c10038600003801c440444e0074484c010310400c01800082403454080e01c040701c09130314012910000000c01b41c80302a4414624198500011070b40f116284440c4104210305240c907590340c40c402c0c1d5036400c070078242c03828043ca0383d0101100300b00c0c03c855a1201c030001d040035844d1000105880014108400b041c0d84003019101080d585c850601003004030a0b40752120089049400348040031400241440b140f14441c0b8005168001d000710200c0c59000f0300c151640c0a0300203094850144540c0700c041c20a10704e60200501c640180c040000748540289040c800b0381d1140110180c0d050f00310381c3c8110080d13024205403191008440c46c12000c6613103c6c01100c1c087c20300d4020214190a120400c010b218029840c01846124a107100500a0b20001410060818101d03800300f00b13040386040107800e02d070b41d1180010081c0601c4003003005002d010105c05494240020500c1c1c0242d4032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 881090251 1250 881089001 881089007
    0x100e16030b390a0509220b0402030c0d150e07090602100c0f050304060605040f092901120c080d030c030b0d0b06010c1b14011112030a050c1b0706090b03010e161101050f1006 76
    0x30032035a2a04a02f000e10201c078100065a104039000c112100341004410740f581d082c100003040440b40500002c14807401809103540c180031601d2164520035041c81220388200f4054585110917400204000700440042c0503c189608210002c0c02c025100700841c800500c04000030701010542a288070081d04243d0703102020620007207058200500c400b1240740d007082d03130b541c40d40c03521940169045c9054480101d0b01e440d01f4031180014552a07180020308031b00582c4081d06840c00d84400c0b03446aa105c00c00c01c000301c0c030b01d44901940b024003407801407802c840c1c0386080f00c0049140584180701c0a288203000c1000c11075075141c0000d10a090329a001010481c0404d240d0b2480700000c00c040c00d22050010903114003198010715000074804c10402d0a001b00750910000020130b400481000d42d000f030f1000c00101d03401010355405801e0344204240743d0f6052820050800034060f242c80c44606040c2810040c071032288024030301c2605070900074071080c100300d54030404500081e1001ea0086110b0768000441e940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 881091501 1250 881090251 881090257
    0x1603050c010c170a0c020a060e1b0607031d01020703170304140303010605070f030e040c0e21060402150f03070c0c060c0203100e16030b390a0509220b0402 68
    0x82a00c07104259a40d90528002808005c40c01c4810f43c46000f0503a0009400d40c002e841e01d00d19000001c0000103251141e031881d140804954a006880410402d4082035101c0004243d10000c20f1001d00103d90f001d0040b032402d0101c0d4006414441c148a0381203c01d103011000f58043da004540301c0d2111003840144a8480c4800c0c4504030220350304010601c001500d100c61500581e01038149112150300310404031b026180081c12240015048108034540c51902e0107a1241c807820a60040000300c17400707645165600c0c80908081d115807028441c4c041c007a0806402c03108000c500340520760310303414072520141035a902590100c410341503500c00415158030030b810894825400030000c00010300035020320300c02010314110800d01c038050450410000b1034100d00081c001c0d8820300d08034400d0f14295483c01c5030f02c85c44941d415207502040c0031190007030115250f5001041d8410100568603000408147d0b00303481154a1190021030350a902000380c55180340d00310380191407110610000e903040c41000100e02c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 881092751 1250 881091501 881091527
    0x13050105091f0c12050c0f0c030a020d081b1606021b0910170c0f041104150513090b0405151c02010302040509100f080703030914061603050c010c 64
    0x51611a40b40908003040a8082c2d60016070814140c41d0b5000c3e198030850b84a01c11103400030030b400280305006500308006200030142a02d01500c140d00380701000a46961500c003000c3e00c58125480d2081c10710079000120b0342810180c10104059402d40c0500f541c403010598007042d41c00c1e203940400101540041030b40d007002c3c090f100c44000110b078003000700a000f05001e07044191400a140d004255a080d000c00c0040b0f107041d502c0180780840c50711007000b03a2940c5a00e2800c1c0100d081451070345d04200d00c5800e5800b96078072411a03ca0105440d40201c540b4011400c2c16070544000c048005004003d03075010341c091480540c2c051001d86d8403148070025814130740d0105034220007035846201d58020b20341c40202c03041d441454054500707660f5100081181c0e10540b0025140d5414a00401c0500310b0200c009000740200300141562034507589024007000320600c160100000710744012460b540d905011180010400691400601d10a0a0060154000104031035a07580b03045c400c9031040d8050081d0200d10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 881094001 1250 881092751 881092759
    0x106020d021609090f02090f2406030c07050a051f0c0206151e090124020d020a06020915030403090f06030603020f040f14040f0201030b09090d030507050c121305010509 74
    0x10310f18154501c002854a00003c1d2051824074881ca0b0050b40e911008a01480501c49410303102c0c1072a0303c0480c42c80c018151080c0c1d1840781c4102c0300d0515200d10083e00e0b4080405034503d07403660301e40c0c1001070030f28000e45c100074034900440e80e0402c03a03004251010581c0c82c3d503602f400c202c1c0005004090740e85a90130766202000c0e003512846030b80b80d4941400010050076402030380710720580300d80f00411008542038012000c18283c1414640a02e104c61110110900c99480140704040c14484041d40751075078264094003032500054859501d4075080990b8070011030140307410350b50b8505414010007a100c01d000d080000007000e8000034045100b4061102a0b81d00240041580000c800404c8001d00e01902e0002c452911740c902c0718071240e540382d03405108500940d0f00a003410380910004048584a00c046445503040e40241300101000040d82d405901c414180041c032611000010707103071405803182500ca944201c44005d000000714001801c080040c0300e4070b44020b1911040150b44d1405103c400a0704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 881095251 1250 881094001 881094043
    0x3020d050c1509010e070608060418031403090102130806100e16201e06070201020a050f0c2503021219171306090e13020f13020c0102040602060106020d02 68
    0x1405a60b0260305420000d1000002041c0722000000f03800c29425510280220b001601045524141400740580c4980c04c032045641d4051180e8001e4074444001c0880c09182501100040344520250f040302c04000c0b6488041031919510713880d060381c07541c0855600702101c00400740013603403601e07481543d40608804246090100d25001040301c86081030803d6060304d901d001219845901c080c00300007501c0c4c61324003c42c40790040a4101514044010300010116841000511110f80e0710000391a0507040e0005410f580710b40076402645012002500180300c3c00440b00c071060383c031041c10052000c59109441403c0038100a02600d9196074003440c0d2111a40703580f041d0321000a01c1f002d8810000c08004803924200201c0b107011181c2d1400315040800800d805060901041c1e01030b2890300ea011301c1d9107101504940095000c2510b0492030100d01d8042c100e41e03504c09103003400c9601a280c40030701d007900840d1030390359800d0001e5941c0b400380306080150143c891030b0090703c0c2c40458855922124250440c076 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 881096501 1250 881095251 881095273
    0x41b0503130f0204090c0501080c0309070b2b02180402030103080a18120309061116030b06011739191b0507051011060c0307090302060a0503010303020d050c 69
    0x241c41c610410403584090040c0b0314600582e0703944501510320f4050045c01d06818104000501301450113016048501c07400d10030040603050000300503060b04c12100200e5183c0441e0314501820b8500100009840b01001900da900c28075541e0103401c0580e80808441e10050007001030001301d01c4280800f1701042c0d0200300004403180540d00c110519a078070904c40c141c0c1e69030354641d4207000c48544802c400060034010200011603210440c02d205062413800741a01e80c1820041210402103480020310780c102c441d002590030380c000c500110040010b68690340f200e1170004070480714040108812590716a01612850703000498041040342c1d050110744051500d40000241d20442400d4041b000803c114041d010f484102501035850f911441403004069084c1008100141504105100c81c00c000d40000781c0d0141c0ca000046442e0850420301a6968a850380c900c1243e4542003070708040e401a80018005400591240c01035040300d0003036003911030004866030201c9083c440c0c1e9000c10a81d03888501c1c020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881097751 1250 881096501 881096521
    0x9120b060f03070315090b06010305150103270c051f0804080309010603020607060b09070203160b1801021603091e2606070e010e04020301030c1208040503150402041b0503 75
    0x75850040040071a2a103d65070740c0e034413134030003811400d0604c426180c1d80030a040240c10340c2c0180e003044090905000e1882e0600c0d6130b100e5040303296869410507498500741e18030012041d04508040490140d2548107148900300424100d1503841054003425600d071000040e05a002548011008165580c48881c1c5070758072143d03450340000d8080d0801e03540c0d625000005a580800078204140701d41c60100e4180ca0b6402007103580c0c44000d10840540d0001c22003e079a60128407040ca00c080d920001400040e190a02041c0225090068640c02588002128961005510300c0503052600c42c0d503c02410545070003400c59101140140048000a000c01c180125000b10340b910407a4000340707006006614072280c60911f004401d60f00200805e0781e481d400d90003540e0041c1a0840464256019499035146549040b00540075101d001c20001d80046510304005240085900802000303080b24292510702c40c0d800d030041d6003958101e205a25003d0780b5215828100010340c0d40d40303ea911800c1c11595624405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 881099001 1250 881097751 881097769
    0xc0306060306060d020c15010e06220e011b03020c0d0f0f050309030909190b1504060c0503040b040806180a0b04020411160503030604150e06010e06250309120b06 71
    0x4d6040c0a400348074011b110380041000c456400d81805096090b0f51601001007a001800352840740500c01d44015484d061901c1c4031200c940a01c05280010a45802c00190340108540c081c1045105c212030440501940e1540103000316420500c01d035040b6013000201540e200d0b0707074030403648041140b0345070f000f100e0750040300503562040702c0500780e0f4170700000e03200000c03030306001200c0c00710104c2d02d49408005541d5592290516550040c1d9201c031440b034a06810403810b008505c03526080248410313010081180500a4070014010082116152030301c4659a0b610740004540111451108102d0918081d80000d20701003810341049061003240c0342c41d000d000190070141804c0c20090800c000c40c606034207a900c5201c9000313008001540e1a8107100007000f0544002064000d01d101c0341801c18070030540720301022500180242800b8500b04410300100e0003d0140b01c0c00309103240203002c080c44e40d4103020b2014004d001e12031b50b18804d00e151101e0140300c10a0488201802c04100d200c0001c80e070741004004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 881100251 1250 881099001 881099017
    0x412030c08041a310b06010914040507171006083909060406020102270306071209020429030105090c0409021c030203180616060207060e1606080c030606030606 70
    0x682444806800c103031340448410302d5028101d444004000c481409810456160091800d10f0240411441d107102d02c01e0448070240002c0c82030b079450300422002d80c05032441c2c0a000c20424136200491a1009040e441805c00348960b00116811800250658240b2003000d0340b039021032039005403070400300c100c1078040e03002d840c00707046030200d00304038a206556800b8080d0005000d1a40050381d03031000c1074990b00700c290b0540c10403090b60040b5103d144c0380f55130100740c41d54800e550307292134000c0c5074840f414400034005011000e0341081c50300c692186600240d095107240a80001004a168459042403508035003040320000400d81000c4908003203460305130009805507000400c07681c129090054198148815044201c0240e800003400b02c0050b4070282101030801c10440b4003e060940d202c442c42c2189100c0c0100805260340000e45800b0488144d1121080e01424011652035001c00c220391180b8088600070070010440820004a21b03086078402ca030300c10f40000e4200c1341140c5418082c06555040114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 881101501 1250 881100251 881100271
    0x71419031221051e0a20180307030203070605130f090e1b0f0f19090b0a0b070b040602070813060f03110304020f060714030a020a060f0b090f0c070b0412030c08041a 72
    0x65410030b048031441b0035800e000c00a160039941c0c1c076004039100c2e401d0301c840d1582400791700424410005681d020a07210116115410101e41c0c0d2801c00b81407401d00066500851700c07440f070f50341011520b584258083e5039116407403000c84a099518603031942e4003400800040d540000703d524a050340c0d050092a42658400c06000d0788890600c020a44c04800602e4004100840c0c2e00c2c00c050010341f9283c1150070040403216049440d044c4540c640610480c00204090300c901d400140e02020000745004a46484407525552010191603210080c02440c0c401d04000c0002d00700005904040c4041044034061070b8020182200f5000040512413690407103441a1200800c141c4d038030300100005c6c0020300a006003640034103403e04451805400301c82c50041c406102510703001d402003a0351505807a6075007010700c2c1701d0144035a0b6101c07182800b15100d400030090450640c041440104000d90005540512513030305c0620810b070134440c4c00c8441c06011140034000c00b4452003d42140045c8003513607500441801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 881102751 1250 881101501 881101511
    0xf2202070510230405030406030b010509031c090b270f06030103030807090b030f0a0b1f051b0303060603070309080d0603140f071419031221051e0a 65
    0x1071a814100074402d42d0326200700e5215408580b2001c0c045880e040c26500110710b00200d0f09003601c855540340240d0240c00103042e555188406035a0180c401c1d21001c540080c01c90b40c001084074185071407240b12001202c041110514040b404035004425500034a009030481d14000d4800b1030a01380c2588a0101c0a8000c1d105403200d045a84455005601031802a03d4441250400c03100040c4500074552010521003010b00074016561502901c00b508172805030004107500700d40400140d40d0503640201d08141c4043c200104a156400074007800e800c0301031000c4240000c001d104115100e11003120340950141007040054070044c0a60f208400c1c1c103000d24811410300c0390b00380d0804100c484d590000e0361181800f10000711044020000d100c0184003240140c240545000e178041c8582030014002403041c9406150f50b43c00c1c1034004009001907800c003c24940c801c140c00006441c00004100f0b00301c1800c05118442c80e00c603d58041d10340030343c20509407006106001800301010f00800781181041035161 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 881104001 1250 881102751 881102753
    0x703091e0512160809040213170f010b0109120c05100207080c06190807090308040e060f1905060c010f0f05010f06030603050606040e0102192001050114040e0f0d0306140f220207 78
    0x84400c15016000703590100c0c00c9c0152004559162900c0700d819184181c0c103021156031141d90244171002214000c2c4904030200050b49001160544950409600032072a0419960038540c0040d1940840d105907050300c1104032100706101c5c0d40d2103440385c2c40e5090011410101202c900c50580b5a60040c1d062500c840855100c2c1d13101e0b00b05a20641c04000105401c0d000d018240c6044078801181c144110380c640e4800109200007003215041d0721485210300380208640d0200103080d00503000042d03000c403040010881484d400801003200703015004070f106802c50041103c60007482680c0c150398000c00200000e0b5550400c010107005900c08400e0603540074881080207805003582460a1030264403180c0d5145006c0c400041905008501c030611a0f040c14010003610074aa507845144550903100407c140c2c101407006480c2052544c0030304020b11900c41c481a1103585580a4020354404075524ae6910380e10000708007205100040042d48a1030603031901035200950001c000b40207402020242c01d140741 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 881105251 1250 881104001 881104027
    0x80a0803341b0f0312090605010e040b130c290313020913021804020102070e090f10050702061306061d1e0106170703091e05121608090402 61
    0x120955115000d03108988501120b81150580d110745000300300c14400046140c40e9101c801c481280c001d014005880e00c000b44004440e0030140c0f0580e04803100340a607507900c6030702c0e80507510116002d85544c0c0c00d14000c25020001180340c0707000550041c2d0519a054100307140624140b690003d0788248140d013601ea071030503070811009141304107140148036403141003d00500590242c0148242d03603000c0c501c04948010783e41c07144005016100807240b98500e641e42e00c0180d02e03001030b0350081018900d4010800500d01030000313848070010500030642d03d1281d9450402415100300f0b42c2c2040240e0090b40000300c211403041e0b450826540183c0005c01c015586105030340072044008403000d007040e0a01c080000c0c505681d040d045d920840008000b1596149c2310009101c0001d010440940154407000301c0c4502d4440d07000001444c0d0404240c0111403030803800c81c50700b09001d9800300d480b0f002d42400c44018504410550381c80d010003d1007141640ca407581c480e00140d02c2454100e40c4a503080c8144030302480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 881106501 1250 881105251 881105311
    0x8240c0717090102010e01020a1b020a120f030318110603061503131707050d0c080c0712050105150f0111033108060c1b0c03010c05190504080a0803 65
    0x101c12041980d560542d000020f01b0360b182c0010310142a0700400241c190198000c070a0302d00062081450700c2000902c1c400603240f4840b5601403564030507450445c0e024402e8040300e0307c1102d40709440821040e040e9125003512546403c0c0050940010014015030700c0c01c01c03000a650000c0c00522244084070314403401c418a801c19143c403c1c203501018014401c208500d40c04d0404010081d80942c10058560f032103680ea00081000c030002c0060780980300007040108020748a240280b0404e6030905516017044421801d001e003802d039080d40c2002c1c003185c1160400130500c1003d400281250030011030340340c010b5030081c4000254010601c81080945a04107150301e110b140160640401200c40c10620103102d01d00e1b000c1e420010b05070b0405024130500d140441c1c00c5807020b8140300e480c4003810f03003444003c90510300159000c613055405c00301c02c0c00c034042e03011008185030000722001403000300a407042244c0340d0249001c0c6131744a41c00745036044041111351000d10380c000f944030002d4070707aa031080c4401d081c219 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 881107751 1250 881106501 881106533
    0xb09060d090f030f0f020a0b2206050a1e05060a05010810051c0204050115020c0409060225060507030b010503180f16140d1a0406181b08240c07 63
    0x910322140c05400d103544170170780c070b40d441d6030520040602030b080b51500d16084601410200b2464070750305180030500c110b14440380c19503030420070403c06071030030171100c0d0007900c404040c00200c0000102158011059442020300662014080071820390420300150344180000c0e0142c0204d00c400c0d00001b81d00d035545100446070800c0d44940071200d1034944140016150706811941c580070895010705c0007541c0c005070350f0055107411a80031a4a40c05410104000c0c442c040310030b04041442c00344155030700e00210801301014820700d402c10917039544030300480484510001c0d070b9000079400c0001c0f9a012a00d402c501840c48480000d48003030940d100400c6190210080c51b00c0c1d00345552080401c040c1c8107015003090590302c00d44203032070200b00c070b43e0703c007a0702030740c00c60101c00f004640301c01040c01d104055204c4a10307410107148441000c0b81a003411004050800c1030800030040d5540c1c0400d047c900824a07203103c0c400310822030b082001071512444881001040d00103150b50074002c0c030001c2074005030306910003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 881109001 1250 881107751 881107757
    0x121d060406090e0705070302250e0a02091008100b07290a2d0c0314090f06130b0115020a080a0c1208070f110a0c0602010e160b09060d090f03 62
    0x1850700c600c802e43c85900510300010300c01c042c4034043c0800e401081c42080b56030403002d00080c0141e64031202c60020116002540d05601100070020100c100b5401000f210000321030f09003011045050446200108550b10307215098900010020040300d60003421040c0e1040508042c0701e11014036402c900428a60458045903016040c007040c50800d1107000c0a20b0f0703403d03455603e00da2003038541c0f0200c060880c0490085030360341d28040c68043c1c800d502a803459072201d03d047c485400d0481e0390340d550303108004251401d40a00350224600341500119180580d40c450007540841e0320700a81b440250900400b11002c2d8010050048005a0000001c09001501351160010031483c0d040010304003400620840c02d01c03903908280500c098001e0001580700405140072103110014189450521042c1640106058840c00c070200d241501074200741e81c3d41e94000300300c40586500024002c07071043c042c030480d41c0405007001240011300b001002480000290300020171344401d0f6654003900d070110000d0603400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 881110251 1250 881109001 881109017
    0xe010b0d06140109020c151f180c1809090503041d0a06091a041a0901090504331127033306030a120201060918121d060406 54
    0x1c03030002141100e0151510102c210300300508804a03d94a11240d104100d040081f50700180034203218242c0265190401e83c202c289888d03441016511104140d10310b40d415504241042d03007c2d0f40320700c604d00c0404840c44c500d5401245000840781c020801144180d07901d000070000440d220301c900710b01012690813a24000707a5031501104200443c3c22640100b500300d420700c10142d040b0000c480100c040c059003103038006454044094001160746610b201d041d0451152000028400456030040b8429801740382c030910860381020215003102c9201090b11002e50304040310307495081c0306510103120020240601890800750440c22a10880801224022005c80124800140c2410b000f11824140c0200c2070b44210340b0f500012124518580148544800b020000038010755400c001854550341c0007a140c615030018040c00901915240c001c8540c02030034032040c00c1003401140e1030b013010305400030181d80000c8030400c0220b52a807d1050b042d114216201d0784100d80c1d642d541d0061005007070a44072204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 881111501 1250 881110251 881110271
    0x420a1b171207140306010c150b031506030c041112071808030a0f03050105011202030c22080f030307080f070c0c0906030c090204080304061b0812090c0306010b09040e010b0d06 77
    0x1119280f02c45a102100c9003d00034055240d0b000351580c1c40da40c0e4442400e9181528081c1c01c03070010412424059410710a00101c403405078102c1c411240500002d40a440e0f014502c88140310580e202c10044851140007007281390109030311002c0098010080f0716200d05004c1e01100d00100a05154002442d503420015404200c40e4002c0c0d1104403c0020303040c1407000d90315141c0080c111028041070220201e8001001556543c0e60104a91182005544000b4040e00c641e0030010990210f02a038001407043e2482d60014000c004103403071040f4031980d66080156a0b100580e94640005400302051040030040c0c0d20000e03c0414011024110366031000482a14505118031910403aa000d501c881740704110a02850b03030044102c0f400e030340031400d00048566100c0369400d0348882c0400060804100441d507004e40b04a03068a0f28040e81106045680c07803d810010940c45180a00c00c03e0501c40007042551510700b070607001915000c0c036000c000280390f1240c1c4003003841030f404d03803c0c1101c00715030f209603401e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 881112751 1250 881111501 881111507
    0x3030512090714010309020114040b07021c050c010309031b05100b0915010c0c0320040c211107050f07150216090b420a1b171207 57
    0x15501921260041000b507103030009121864540b151150704140d2a03e5801c000d69000b43c25804200f1941c041c1156201e0783c0e4251000c85e900032082c204d105441120407100341c102e00040070b28a85400101511111230020015401420b40c204110b0030301008110100c13000e84040442c000e010b0090780601440581c00720108120351004c040c8600c00c404641c18455503180c401000040350800b070074210300c01c045a09120f2039905035940001c046079800202e00f000030b602994282590302c03080d5020700c10706406102c2510310741c03d451242100307981c1c0d800c90b03410749640c2908001c640301000019a1316120462300c5640c140783d11000603150a50180703004000d9041802d540c580403410b41d1028210b011000c0307100c0305510000d4800c04d04500c0d21505121041d40d0b412a0040070100d001c0200109806821035100385c40480810419540340303507420059582c8001e00c211800c220444c0d541404603400c10300102054600320509580b84030200a1110f20850104001c00344c04407084c00d414418a071224000b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 881114001 1250 881112751 881112787
    0xf02030f1c0509010f24030b070504050904140606220903050418021b06060105041703090607061b030b03120304060f240504020f040e040219300f080d15030305 70
    0x1001d104500100c10b00d00c0f188035841c0c110547c0d61055002003140c40710340044480340100e41115030b11142c500700780000c00c6010700007107640701010310030341d03003183e4400042200f0100019000c0d0b402512903c5000803840c1207501c15001144030b17080040c2000d848056400140020b1100c1106169002441d6030040c110304da80d007a50b58080c034008100038581400024114082c034401c1d1981c410460710301c60b522030828002e84040d21005010bc90300d8040d01c3c01c2c2507015285500c00f182030445415260807610f4441e004905140902500800e0040c460140300035050f0700003042503c0450b60741c00c0000480b007450141e1403400030f442c4204440c040144280e0401140c0c10b40c0464455441080307142215150142902d017101e0f807811040314503656a00100b550f6640116070000da442c950000464a050310049415a102614031000708604264203c0710060f450f041d80a0000441030341c41c0000500d000c0c0040000c1c0030311901c04100844403280e01e42200d04039400440c0400ca0114408454503010052 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 881115107 1106 881114001 881114021
    0x509060c0109290906010803090d152a0f0e090619030c0801060801150e04030521071b110111010608061003030f0f02030f1c0509010f 59
    0x2c603d07150f008410540700e4000090000c02d5280d4400544641038445d030000541c40c01c4000000c000300791216040031148030300390341c00004445109009498012031031600341c0001289000345281181a00c20f8490308110004d0420b000c819409082008030b644182c03406166500c50201080d000306080007200f0b08821401000010001555064030444110f98000c011280c0c5079a4154241c0d08804104180114043c034140030940d42000300d56001446810542d213061030483d8030014011600b04124204640310003048069600409200001c1405d07040d11a0b65200b035682354150180111003141c100184800c41c82444802548410042c00c4000b049a600340340a4000d0700c2c0d5094036010480004950001100342e09000d90901082107075541c01035400c1c40c0010601011a800017007800890b040f541004400c070f0012072203214000c07041c820000c03902c901c4207081c0b80b003a590501e103 = true := by decide +kernel

theorem cover : BRFrame.Cov 880935251 881115107 := by
  have h0 := BRFrame.cov_init 880935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 880935251 ≤ n) (h2 : n < 881115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
