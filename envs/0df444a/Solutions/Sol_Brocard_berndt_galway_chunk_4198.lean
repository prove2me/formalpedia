-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4198
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:25.053434+00:00
-- url     : https://prove2.me/submissions/9ba5f3ab-5c8f-468e-9690-97d34f568d66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 754856115 ≤ n < 755035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 754857365 1250 754856115 754856119
    0x3131401090503061825030201020708150a0f0e0f1c1707035013080901020a060f0b0f10020a0305030a0e01020a0c02030c010c020f0f0d0c0806070806 66
    0x141d00342441c001c0fa031100c001620b68038041410300340a820001d401d0210345800f07001c0400a1041d03e40e040b5425401c4900c0d440145c0c0076002d1410702143c0c3c0384000c40c0e00c0c03841d104a0040088251100c1070740b20b004140300c0e503ca0b8425551020031080ba03000038004849150107140003880c02c401d60180c1c0140760090b075102e9500307004d1403090084140c03003805c800c154428650304000136805e11b4022050380c00000d5501c0c501030400040303e41c1d04e040880d4143c080481d0341150030010403400c0c59407860036810082d42c594411a42510b95540000c503940010410300f281072043d40c5201d600f0380e843d1001d94449190f1001400c0d00c030420010303181400f0240d078040403411180b209070356200c3e0b40003a44503045aa0080d040010000001d50f48600306c1d0414542140000c001b1590f80650032030081c41c0e044107001c124404e002c0c451118110398814004100510b4004020308950381c0030400f004003000700100445e4010306e107000c1c003501190f040c203042002840c8940103003210b440c0c5000c0051030391900800c0c480c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 754858615 1250 754857365 754857377
    0x3090b0a0209010c29010b120c0a0203070210120906050a05060f01050d0f0612030206070e010525060f180308061804140c030303011806120b190207020303131401 71
    0x9005607074061304900d10705401050050000300c2030909448035440790403000c8041e10041d80001003c034018001444900000602020103441c0c05111a25070300c0351140620041c0d01c1401040701510b405040103d00c1003032070501c5180c80b42e40051010640d41118010f81c1c41559450800c8a6030b40c0602501e54007004c1180c1d154112018980060824012160a4a9000c0c0c0d2100c00141c3e0465a9000d50007030200b045c09080e4241c02c51400954403d01101c0309800980000344821095024209440c4d00320740780b4001d140d1080d07400070400d041344001c180540307149440313054019000b0701910070902d5503502c0f60b040707100003580c0d4103025203504000340000e0701071000881440d01c500b801c036000d82d81082c0d00200003020b02c40181402850300b2401120103502d80400800090940c9000c0d0f40d241c0701c1d0164000a008041e5260010241003400807005040001c0c4240020644950001c031661170040202d0014100358441d00420300d503800007401761219425055082c407100c0584095010150002d107044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 754859865 1250 754858615 754858627
    0xf05101403030313030c1e06050603190321270302070b120a020a020a02100302041a03040209010b0309030f04090504060b0d15020a0c0503120708090a030807140f070303090b0a02 78
    0x350044d07040710501504100324110329004101180c081c00d0051030410003000b048a035141420b5000b000c0584100740b280c442c030741c0729810b15290700d00c50f0740515425496414041100803031070045480c0c072000d1703405540d40e01e8001e1300c0040c0104064180d90b00b004010a0309000262401900c2c26542e5081544000010300c40c1c0340043d5500264a40d020000c02c0003d6192031503240160301d440d002400081d800b5106032030080445515034090411905004660b4050024500c1d150721688400da40c041d42080111005110741e2641000954004c6a03541c02c8070720f8042506450491038001c0d40100d091390b40c43d0024041800003034014501c0c565022100f0f5549000c440c0e581090251080584c043d405802290fa02001809008400001d94108051b45d81d600300e510010084040100d030f1107000700c1d82c2c040115080c088006030702200c456058451201c00d403114031090350400805191075440c80c81c10809080c50310f078110b0107040810b00c60f032008184904240791001c0c07070000086c00000e03818418000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 754861115 1250 754859865 754859881
    0x607031a150703200703111f0804050715020a0209100312090e060406080a0f150204030501020d06080609100506031c1e030b060706050a020403050105190b0102031e0306040f051014030303 82
    0x1720800700c9511007408124000b42e40c0102c0c030009000014840b4000440d89241103061300b20840d103100798810340c01c1d5141c90351540300c00560418440d81c10700042e88032041103001400c0c00c2c6000c13a001150350711100c40f8580d6a54901c0521400003584a00080307102d002048500501d1a140350130040454003071003400d0900d81502d43d41d44100300040d084240401303140c42172241490364031494104140b0300303541c0da42d142d0801c42d010354081c075070501d8410315103c000034241318081001d50140b240c1e00c001e404d12070034000054000c1c0c0800b400745580b6020b0312816092541101ca1000d50040242c1c4400500e0711422240340c03c081d4100079020141403c01c0c481d001190317103c20403501c00c20f60248000503662540ae032014000e01950b007000b0f06640c03a100610071090385d1030342034400911b0400014042c515802004903180d01440c0380b0f05224901800ca50b0300208030010203198018005000004c0e1030030b08401010030744070b058540e071074401ca04140500c0310202c0d40c400764580e040305130700541ca58204050703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 754862365 1250 754861115 754861123
    0x3050c0714130906060b04081f061410120504030807020f0703080406180f0308072006030604020904090c060e0f042c10020a02031315020607031a15070320 68
    0x400b840c0b4103655200c40300420400e5440840980482e4840c140c0f0313175854481156681002d860001a181400254814000090700034842903c04810581107520303503d0042c0300d01c80d40c01900e403006010010f2984010f5842d0352142a2190340a982d40a105003001c1d40c0180c10940c6043c00c205c03468200340d006001140b0180d04a0707040312a689015000002c0516a0080308042a081540710a070a007500001f8040300707501422019000d082401c40d01c0302c00840500000f000300010303540049041c00003c0d814030b41903001c1e010b00307e4041d0000c1500207080d560107008085075004040810200350f01c090f2170341000c00780345404040580f400c01002c180c2281c4050122030704007070f510300101c00c441c14a66a0728240401a859441c0450541d110b0a500002a41302d030021302c41500280030080c400103481e030b4940000a048032171500500f8650302c5200088015151644418175060309440c3e0f5110107880d0107100d1140101800c403010340361085494000d0802e0418030391860300f03010012040c0d4510320045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 754863615 1250 754862365 754862389
    0x9060e090a0b0612070b1306050c1002070303022a0f0321070e0a0609142b11030a0308041a0631020a030c02011d0a0b060a09020703050c0714 62
    0x80b00701010307940c0d01d50000d4841084030b140e00466024201002511415282c00742c4101542c4040304a107094980104032014003035400007100640c000d11241425a1040c0d0007845000c1c01782c98054542482c20b050503c1100c420003924a0468605041c00c0c500320041c09841c2503c44410051890990340510740b8544178000c2032114a120340f4500866400303400b549680203242e00c040c2c80c1080e0195200c0000d040b606041c800e000d8504803402201c0c4542c03609010054074110060450a02c1200480b14982c0342200310034110b62070480c10448078403035038003000402c0318141300359500c260701d1420749070812000040000842d003008405050101a540781e80f07581898241c8800c89044901490311200142400c6121011000b03200040840040d60325800440c0585803640003840012040d04208104880303030b0011018980180110710009080c01208a8102c40300030001903c80b0b85400d4180101d80c4a00303021008103c00140c10903c1c010b041c000a8028601c0105d00486003d800022034100172044c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 754864865 1250 754863615 754863623
    0x4170c09090d0e1c02040905060f09070e04031d2101060b1612120207060b010e121c0903060608010c0809030a09062a03121416050c0703061509060e090a 67
    0x15130307100c042d03406510309400c0e040d0002e0090121007900d0400342d840300b4050310041c07100740300c13800007800074400020840125240361280035102c3c2e07501c1d1001c8a003031120b2201c250b181300d542103410059a480b0798846a03009200507000701c41042607110325007103d40540c81054001c50034003192444503802402d0020710b54109014001c0e2001c00320080b03c12003294400645030314404201e100c2408800d80c0807004241f07080c0c80308810303880e044c420050301080003404d0084a522080c0170001d80c00511404001880c03990511440c0642c90340c1d100010f5850036000400182e559100d00028164040902500010078001840c580110030000414480c8240214002e0040881c1803072110300900c1040343c030400500300b211444100b80d1a0040c688083c84140f039002d10b04008041d00d0b02998114418001e4205136500500d4444410055400b13812400d000400c5018142e000000f189050040300e54081e103800c050710b0307010305040300c0c40202d8105400140030310450001300580301c000080c50040f50303904 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 754866115 1250 754864865 754864879
    0xb0406080c01030216171b01090b0604110405060403060b2b08030c190f080703060609030b0a150602060a060608092a03120c010b03060408030c0c0304170c09090d0e 72
    0x100340b216008417082480300030710058800480d0402c81396203602800c200040380440b680d0152007000c16900740d8010380005045000002c1c003103580361609a0004ea03944c402c410035603041c40c2ea04d8000600a401c0b07036009581c1c0c581c450004109a19201004c10381c0c0390820390066281c40c03071070001e6844100401c20001e04a442c00030106d05c4c20041c6a0690380202c1c0100e4582e08100301e44240108428600c14034000460311050100302030500a0151000b6544d45545145140386142c60b040c0d45031707201401c10041035560f4643d8004054030003525001401d1940c00603e82428050300a1048602943c86802040a164144006500d01003039075241c0c480b5100012484e10410b0008008441c01040e8441d81482503240f00380a41e000d4030050064104080000c006125509081c16224101150010111281040050200d101c01009410303900c0c14801164106500c80b00f0403002c0710320709180707042e041e402803001924501d084880e00d40e00003520350140c17000640c1c010016080724003003e1440d2141d25 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 754867365 1250 754866115 754866127
    0xb04110316090e0c040209031b1c030c0308010605120c0307350a060609030f0303061d06040c031509020a0509030d08160507020105030f04050c0a08100b0406080c010302 74
    0x1a0401c0a03501068200d001c0c031081d103540301d10050042030089240d0a80c2d0240f01d111002600d03045c400e81d19140d1001d8080c006c6000c41d0180000054000400c3d103500c01408a80442600110307807032060030612903220340002c50607a0a018003980c1c0140d10031402c0003c1005150640c45010740f149800c031100107123890b12901ca140040d5044501924516030b25000b0480405401e00c40b8140d40d0240d040b00480441503485c0c0118441c2613603041c4c0140e002107071607003008000084c0c02c041070b9407040d40039140c0010340d65158040c1c2155044c100c80300c4d0a1402c041418400381e071070984a0031a003501d107401c003000454001c17410754688031040d1003036000459020641c81100c40c0614212440030000406030b4140500c1014090710100050342c240d1005811a1440806070b80108201c074480e9070142c460b681940d5aa600c4194000d800800448650240036034402031925004040805882c60802a00c000450321600d24122130a42d0030541c8664240202000907240108401c60000300a01c1c0141c1c0d03440b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 754868615 1250 754867365 754867369
    0x70e0403050d090c090b1509010f050d29040212011413020309010501082e180f03120b030732030a030216060314190e0f060f0c070b0411 60
    0x801000450b100c0107040c1002c0344204009921203100740d0340b440c0c1003049042c403035100740461001c15420340304084070204a80b403c80e42c003403000c1d013200c0d2403989842c2e8541603c1074048020b441c3c0f0240981d8000c040034000744442c80300080514000c11055400f1401d02a4a42c0921141c2c5410f100703401c004680402c0804060701d440c2008588035250000a558074106641d11038004d103c24800c04019000d04440c00401c070a40d948540b04800340107056040c1c10b00d2481e204030081402c03907280880c8510b5031030124006801640826280d81c000d0703c40299204140b001e080075a0301110b940d6220350018181844907090140d915105a50b003107500351008280d4691820051000070b40499051207904811010198001000401a0a901d92880320300b50707110303801c0c0c007078800302140c00e211540e034980020f803a11a44010240a0071a0030004100c0a110505441c00c10480b807010180c2a00b01004201c2d0040039550001d4001c3e0051201514200094803000320200c00904010413441214403d01815 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 754869865 1250 754868615 754868617
    0xf0d060b03030d09030c050c03070806071b06052e050105040e04060e0a0f1502040b0904090c03150f060e0603060f070c02031e0c0301050103150f060b040e01050a08030309070e040305 80
    0x195283c200801141c0d05a080142111146010490307403482060706030075650401060190455010306c0c020901510381d00c0b015141000c11203003204420300b0703502290010401701d02419000c1e41c0c45017200b40c002c256040c1c8021210742d09010724561050300780700c00c04c440e0741d002084a00300d80b00d800e141595503d0754038060f4041d041c0800e0091161113150406401c0c8040c0d44c002d40e002d03070302c83d4042c081080400458a801c1e80954891000b43d6502440b40d07050030b0800d50050b00311144141c8107401314903100e03038072707881c1180c1c5501c001c10046544d070a00e110165031920641000d01951090449186011800240e0b5800020010720508031a400810301ca0b6020f88460424241d00909441c010b00714a1042c5d0420044d00044103154801c03c9101500c6007010712840f811781e0b42158010300c5070190b807412a030160400035207000803141c1d1008005540301c801070140c8041e00000c1000100d55240508000c022600d0350015141900f0810a0084002000602404844100307007141c4030341d0380f0780c103043d00c00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 754871115 1250 754869865 754869877
    0xb040c080a020708040f26060906130503190504180b0d03030b03030c0102030c07030305070c02010e04110c03040b040306061a04090f0902030114041b08060a150f0806090c0f0d060b0303 81
    0x44003030000b0204014080003000029032400303031041040c010549914556408c42035031400c440b40c020700042032402031103607020041d040c01070b01168502500803180c2005140000c0000300010000310781808402c140c2e2000307417240c200c0c0f60028005100d82c4c2000601015448000400341a910f40c03807204591018001d844018113610000c54581c0360000441c01a948070340804c50019250000040c1081e025044152040303070181c4d50410141748d820140030043c0b0311200c6002d410902400603e6240b00200000d00240a20401c16034030340d4a10f10f0070030b00740c070141d03000044040d038080c2030709484084010544040300c0603d900815420f42004c940001040c58400294155007086488612642c0c130b2030103540109c1c0324080508074051401031307240341d002050243d0085900050042120b0a0264002403800561502203a4260fa541ca2010502c01016440528140c0200d0208a40c1d40e0041c494409140001d4580307814030855240002c4408840906c0188400e0341d0f000081c009440820a46403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 754872365 1250 754871115 754871129
    0xb030a060f060e132c160b1e0307020303070516080d1e1b0e04240602010506090730110c0c0607050a170705030417010b040c080a02070804 61
    0x12450b03181d041c02007042001002540c054080484d521007400302501c6800a000c48107129007060321101e820742001d086007420283c01c1c512403080910340001c03204040354011309111140d142d556031740103038510784014440010401c44105000300310500e84c01008503544070320035240c01a0340d42c21921703d118100000e540041d25120313010440e0401e002c8264010941540d03044007100c80700c4030304011803040c1d4010b0b89040c01c03600c03446070704186654021980308616050003040841c5112665940141c0c0440ca4404c45034450342010b030030044540c0a00c039031600040b0680300c1c04200c4ca40310f00d024143c0300400c55503c2820a81c6001d01d9004100c0d0110f03140f1001342ca100074030602e08132807041c0c81541c00680110303e55003d200740400e039918082d801c641583da03000d405820050380f41c0d142c501c500640c400540200d10340421254002032410320061024208401d81003c4055039502003501b183c546a242d140034a14080e07056005a0700265125400561450056940c82c16071409040324000c540c0104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 754873615 1250 754872365 754872389
    0x120a02070c0b1c050703060302030f060709061b0605040803061306030c030b071b050f0c09100311060403120c110108130b060103020403060e070623040501051e180901080a0c0b030a06 80
    0x1c4a5a60b06d07030081011640202c04441510901440041d1111010785815010030b61004040041074066115001580003106c01c26071846a10380312070080c1d40e4101e6045418890010401405252024641001c069035940c104046421070b40c3d01500741410f808082d0102c41c0c50400190306500c0f0390701501d00359243c8440c56060040e2450429a6007443c0c0c491003038140940781342c0464030700f469811580318044c020a03440140340345484420340400c0da0030043e50800010000880459103c1401005005699070751031880c50309810003440718100303801031a0402c501a0305002d1801b00040c91003011035003149039580305448010060b0000e210b940c0c0b00600c4903041001001c200f071070229090301140c5064481c1101282e43e05480e02015100c6120310500710350a0005008651048014003040c0048461030103101c651906060f089401c5070320078407000d000001d01078455003071202d200b40c010600f0304002c018080c4107548a40800107075009a00c602080800001d980a0301500081d0041501440314 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 754874865 1250 754873615 754873621
    0x3040b240d0321111b0c09040b0907050603090a020f01030605190305070801110f21010b090a050303180114130b12060607080708030a091403120a02070c0b1c05 70
    0x2034485a62400e54507402400042241e500480f240a40c00e100e0000a103014500114a84900c012003071600c1180300d188110311403c1740b55101c41c030040b40240c1c024005048180381150300e0b540b5100603904100d000c2c100c14000c1c0440805d0000d0b04403030080d41151704441c4445280012802000c0700d03030105a01c103031401035072480381c0c40c091600d10030307a03014a046e20a01911a03203024240c4044c9905d640c40c0203410450392102041c00e001400310100c4501e421100703143d181156400311802030300414001d50001800d2003140c40c14961610050100f54040d5007007000e060a0051000c1108180070b050080151200d000b09421500300e40d002c4080b4000100b5403034451001d480a504242480d4a0040c2040c012903500d2600c2415070b00000e074040862450400c1c1ca642c0c040d200d8002801c07203002c458507100f080b0006590f5140c5103c91072490001180c54480c40b017a5900b82210145c01748407102d00c10082400400d0318100802c06640c5145c81c120384ea4540e10404528140c1d0400109a901d8a80018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 754876115 1250 754874865 754874867
    0x40f05010203070f020105090a05060c0f120103031d01030c091e030b1503160305030d020a030213181a09061018060201140705030702060105011b0b0406060f0b03040b240d03 76
    0x900d244c0144a03170080140c0d43c0c52902d0580d40e2620403c000c5c0c0320b03500100003d0822191100205401c00a40c3d0710784d41030920383c1034a03480703070362007038000710086500007909179003c07205a286225452002d20302030200c90102000a0803006c402e000d01c4640104006021410751483e200031070055070300510080a0b45040c11070344288540e01a4418400c0c00f90f1075604445036515891f04080e07036000000b0310302d0210740c424220003d40c8644a18401c2c1034003031080786000003036042c02d4002080f03040507482c1070410600402d13044842d8050303000680d0904100300c0c89107456525001c1c1d40840280c0300030001e400049004d840190f030b80c00e64006203102c402008186958107400501500c0d0f03100c44225040e40300c1d0081a5158041190440c0041e484070004200e03d622032000b01141c90307400040054440481d883d560744050040324103581c2c65407104402c0144000c54202d0000402e07501d6006800c50078942c0e21010419800f9202c81e041400b080c00d84414410070219100741e8800c001d02c01d98814101c2e01d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 754877365 1250 754876115 754876127
    0xf061c0c180c021b1c0b0f07020c03010621110901080a0c0918170f0d050f090f0604030f1205190507050c0d111006180c0e09010608040f0501020307 65
    0x1440c201c99500b4941441441030000584290314694580c4290845140b00b05002e08041c109118919001200f1900804540700626450080340080044151484d010784043d2506043c81c00c0b42c0d0003030b03141c89000c0146444d403400c401900d9801003840c000c010040d050100e103105500d00405d07803000020380001500c0c0f40000307030000798500c90b1400d00c0c2d000fa522420394003214020300281a4400713611621100044807000d0108400c110003054a06049025003403a5580c3c03ca08020b4110507559024041c40350255142142e000c58800c00802282c00c0841100c0e45030a80504010b0034418070500d12156a4040d503d4001c0803941c0101c10841494007001a18084082c0d40a0f1801d0300c1c50b14011074070003441130341155480d1283d00024100030911b01001c55075003403460840c1c400f82c01140c1d070141c9202a00d016040003440c000c20136501403000c0c001c006044a41f032126800901106004580d40b54031419030081c1115114102481203648a0400d84255001c400d00206254400010060303c140c00035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 754878615 1250 754877365 754877399
    0x903030f07030e04090c0513110a030b0a1a1b121204030e0103110f0f070609030305070f0206041109040501180b150d0b010302040506031504080706050f0f061c0c 71
    0x9a101e802c185002010704c011540c0031040038000d15a4040140701c0c2d42000386590b00c40f6000d10320001142c1c43c1c001c00a6100341c02c01900d102c0086c2d110608040186400304140700540412507103960810030071640340b5254131407416040d80c404900c3d0907001d402a400e101404900c1c8905074a960790301001c94804000c12412101280403a16030000220154403d00c84e10300a540d80c412402d10784880e00440ca00c150304110b83c0c0003000d50007007040c04e000a503240200382000c0d00ca0b480c0801e05092680c0060a001103103400c9000315445081040045900d0303140380d02e40b14200761460042510b440c18260b000d841119400c0311052101a120406c008a000000d4840c8002e001c040d07a80c510080100810b49498400107018559003100600c05450070b0752060340c02407070007401c036442c480f000e5a003404441000c6800b507402c0f0601203000428007045000c0c00c6c2c0e00c0403e500461140389401013260020080141c4528002c016031158802d0818040da07180101a42141f921032900d03903150920720038107001e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 754879865 1250 754878615 754878617
    0xb0102120a1808160506090d08070f020901060503040c1e0b03100501030b01020102040308030615160b0a050f1e040201030e01140a0b04050720031312030305010f0810110903030f0703 80
    0xa0001143c82c0086035030140e0407016003126602c18508010007000b504101d11950340300c80c000740d0700c2c000180e24000600a90740b04488895100c1000d0040200b8a05c059115101340315080042000045190402d00c064400f0031075940d030182c07001800e50043c0b200d01d401284241400006001d804066051036a046500c245da00384a01030050b0012420f03400b03544402086d4002c203001181c03041c509502c0c08503c00015503e1542082800500307280c0d20481c4100c147d40d05400e110600900040754040c00703a000c041310500c0c405600b885103212140e0010a10b2001481c21000042411a80b0a42103010242218402403003081d5402c070f082e0034103c00c141c441d0505586800001d1081d4109406000d100e9005074684d100c007694604440024596080c550b00c00e0350200300007202c54a000c0c8030100016200072828401e2019041c9000340c200c0e2010b8004401007803c40300208078128000074081d501001c2c5050104000500c0011000c0d1800f604507001c0d40b600000c9000080809404050b041e01802 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 754881115 1250 754879865 754879907
    0x191103130605150a061409060a050406030c0801150804111e1f02030a0c08071a01031b240219120f03050112060c0e0a0611010b011b060b0102120a 64
    0x910f510050700316400340000c0c0d400070101d140c10001180181841802c8905d5401c0603843d0045081c000b0700e2680c00b11200c08007040c0003060510905a05100d068841d00190030880120f504103000181e003017003007100c0d0a04002c07031540001d0404c122032558499081c00030308090840f0b48c00e80c5000406064880341c050148a46410f15051321003148211824980a900558a4108126412034401e04040c00544400404010a01c005010540f1107600c20f0280d0305028119410340c43c108865044000d0407507003000724950180303d442c440b502141d0200d10034101c40c0c403103159460320580c21b06200703051907102100f80484030414440c83c80708070910089242d40b40301d0b91041407071082d800c6074400e00410504c00ea051083d8400140160700400d400b06850621511002a03100000c0960549801180015030b04030300403510020240a1611045403d090078400c110b84800300b8102424101006414241c0b190251800c69000307002c140c5281c40d008000950340c619010780034018010300026003042d044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 754882365 1250 754881115 754881121
    0x31b0303040c030b060d0b0a0c091e06030c03090c03050f012a0507080c030a020703020a15120525030b031b030a03030e16060905090601050a08191103130605 69
    0x401204880c031842d8803120092000c0c0c11031300c4408401c1001090b00e504a0071050008010a0601b00c602340304e40785081002c6204ca074503020041004141e540540303940c038154100348d4a1240410191800d45295141c0050f0488000c5030840c0a44003001d0064200b403c2c1010100504c500410441091034000000784500e440c5d510540a0307402d0000e01c0c90051407c0c10019401d80c43c40341c0010441c01d40134030030030703030800108846003819a80400405409030f4084a0200214107041e07401400030300f103420302d0f14100e40740e000c4040c0c10031460300c881304035040e42d44001039181c2c00c08500c2c15040c01400d0103c1e41c2c04404205002e0024034103500090b10134410117200071101ea0448270000100c48000e03002d04220754065034158090141d0502001355030041c0b01d000d9100c03101c10448800140301582c1c5107034155183c902032041c4604050300b4070b81003010412200c0e10086d08010910780041c0a064001300048043c01d01c1b42c01803403c3c00140c85036000007c00d000303680b82482c17403401c4840e018501c1002661 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 754883615 1250 754882365 754882417
    0x10608071d07030c1701170d031a0f0d2406050316030b040309081b1503010e01060f0c050303010b0c01141b0d0e07081608030705030f09040b0a0803 65
    0x8032900c00c48504901e1850006444648a41c11412032000141400315442c0108100b004110ba400d030050350615200300098418140304100c03038030078103140b800e0411000b0b049403004100d2400b180801030045c0c8500ca98443d240d01c0c2e2003888495540c00008403921000d410a84240450207070f0340c400c010310700f000000f2030b16203008951082d9140c1011045450360389140d407100b405210003441502444089100018140d40900400c0318580c5c42112001201c07a50394100100c000c8170368a078107102d580610041c0060040401c01a0641d4600e061029040c148070340300301c0303503400301d03420003046404048000030f05000520080e06025000d04002e0090041c90604140d0500d070840c0c80d01d40f261040fa1000c1902d04090009165403505a04007080140078845090b00d848203c1c1d00102e020741c400884101c078001707400c5c0b881c005400c0f0103029628040e500d4603559524040c8890104450000103000301c0d0716582c0c0d9000002c02040602608026a078440c9059141e8000d001012419160080712140030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 754884865 1250 754883615 754883639
    0x510020f01060e060916020d0804060b1203030a0e03070c060c0c09060801020415050304050d030e100501120303052413060509070c120903150b0d080f0c0c121b1f0201060807 76
    0x1b601c1298000e103000304a00c01d04070760705480074000350303840c60b6900043c00c05a01c4201d404a1241e0340d52001315540e00740590301c2c3c8215100306a041a0701c1d00f051000000141d000c5404000710b61031464118048100750510320400d081076404000d003d403505200141c40d00064026008440b29003c0300c0072600e1038140d00b0345061000701da0040403070b000ba107660070280b030180e846031040c40038860403144042030702580304089034000e80000900d0035140c20840e04040c0d145c010154401030329907249402801c070310300d40319582e45a1600c1c2c911802042000c3c1011a210341c0c07244c8010100186800281e00304847c000d0400390b908001529070a6954040c6071b212400f921031501141d5002e000c540318400050000c4004002e680021507018084400440c0411840c4000d0500086030120b400d40d0340d40c03550f4040d46003001864030035000d1f560083d000c19141c2c1c80400c1c6598103210031501c4501080c02c41300002c0800c0300d4211351050151000f6614070210794154455002d07207010b082100c07000e0391254190156 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 754886115 1250 754884865 754884901
    0x40b070314070315080f060a0b06360d080909011a0f090f191707050105070b0703091506030311012703020a08030411040b04150510020f01060e0609 65
    0x79218600400c407502e210b588540222208101061340658855002c01c2c04c2c1944080d000705660312500c00e0205070345d1070b44192402c6883c110b41542c6400050305041802410681654116072101c004a6a90b0805615840303a005002090040d403180285030103609038101e000c0e607038041c030701000021070304400ca0421a01d4002c0e0b003d82c414140b100e079036540314141d07001039105a0407030301c010004895501c424041c0b05480701204c40d42240c007824943c0c40340310b861035141ca10050307512540c02000241d0300001221341c4950003041441c60f40c0d41d0044142e01420210174000d060320365410803508045103650100d400d0781c0c400e0f84e46003a030300810f440781c40c01e8424043c445a24101007014906004107442500380b0303818807900546034000700035128922150400c40b015901704161040710b041620345803084d0b40d03110070115010001602c141ca8040c05810f040d0003900e004600c42c9071144407040c0200311800f00348580000a001180e1030f507101b10042c4500303440e01e82c0200384030780208041200d90440050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 754887365 1250 754886115 754886141
    0x50106021b0a0b2d0703080103080f0702030d2601050303040b071e03020109020f0904030903080a17190b01020303070f1b061802150903060c0a020f0312040b0703 71
    0x1229421240003103140400305501941c030849884001a4052614014000041a04c01c44000c100b14030080c03403a94480510b9040c1c1180c2d0100001c000194020070300606407034200400c42c0e21007000c4824920309118184c2e020b5418461211342000310365018004280c07401c0c1f10040030040d903a5903440c0c4e03551910280919030740750300180400d0042d401008003405a05001d002c045640341210041c040343d561100e081a001030b51107400c031030190305045e01c10995804055800420514080d10000c1181246002c010a0010700058a41445102d0a4282d98039540d00d540c1144a0402460400364855040c0b0008105418509604160760001c425244601d00039190b010700c4030000031040351900c0c200810300200810348619000030540a1180050318001f10082c4620a00344d401005401c000b01e014134568650300300304804840c3c5000c00d00c1d50700a0240e92002d80c44003c111007d900b0102e190014054034800401c807410301a061580550003280581d294410079114420110161a01948590 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 754888615 1250 754887365 754887373
    0x6030c050904020103061508040c0f050f12010e0118060b090609190627050c0406020703020103180b0c04140306070e011d100f02070902040f0315060e07081905010602 73
    0x668184211a9030b031041c814500000c05a80741c0c4c0030300000700e40d0320b4401400200410700300810030113a1554000070b004242598040346140030009400600201440c0c4d001c5c0c0c0e40303c5052a1403d400f5041020007002e044024401800500010a141e0b03102c0901950b03550308201d407005450070f2407840ac40c010306000c0d120071000d40e9074000c5442243c0b161866481110381d901f0002a0aa0102203c42080c80000065800301012001c1c900142c40d4090002d6601c908104410030182e03400066020481350b085c2408520403002d41452074076503c0c0080c003c3c10310981030b4108005c8100520040c810b584a280b4440c2000e0008428540d032041c0031102c1c500810340c0b2100f1401c0325070243c41030b11407804038401002e241e02140030104500c0483c076002000451914155400c01680500c1030030094081c4c1e001c21030a181c075180d05840300d40123521019005030f0380301d45640985c00c40b40d00301d1005030164450850310f90400c500012304200c822258000080081c01240c0320005103800f07018122071980e4024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 754889865 1250 754888615 754888619
    0xc1712070b0708130204060b0304140706020705130204150302070506010b040e06091302120102090f01020f03040608130c2403050f01090c0c1b030506070c1203050c091305150406030c 80
    0x1d940140c0d000e41120b04801004e0020300059445005400203800ba20011070303140c1c00c2070302d02210f4403d40480084da03190421101841456400100760089403801c0b503100d00101a40c0d103a8100900c2950402258500c0391064007010340e406800410103e8418400c40fa50f903179840040d12010302413805076045010f020703000b2402501e00080c08a400205c880d07031541e20301d500740e4009030601c0c1c20070b942c59030300380d4002c20850710310320f4001c002c500440c00a00150640c0d010b50760006850b0f10880c0034000a100d0f0140214100d61b0700c04510b0516107900c4203030100303402e4031801100c2006a0290611901c60000810300325010310a0203424000c502001162042c3d03401c0c000d00300040c0481c001c011007008503810240c80450300c40c8410901002c0c1c48000e889003103066003019401e001c4010810b805200390050440000f0b001c5100310503c0003124500041c2c142c0315022001000e00c9000f12076544001c08072030081e132403312684054068200c4201d50b4503804980030a010a0324203520014006081620003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 754891115 1250 754889865 754889867
    0xa110f120a050d051503100603020112020a202a030c04240f0e13021c0309030c0b09010201050703110f090a0905040804090c0201090b130501090c1712070b07 69
    0x1070592005181405800d100c40c030f0b00c1c08011210200c802024102c0d0501c042d410606082c0000600030502c9003040c0181c80c190380010f1f01c5000c034250b0021030594002003e0505510075002c0d0003e040b510595501c1c4020805041c659849028011401c0030658182c52021030760031100c5540c0010002d00544080c41c0904100001404c02102d584118042c000d502001100090300c2040500081000d0008803424021000540d40700100351070254402c5812142c01b580d5000d5101c400020321149a88501e02c1c24034003207900e03141c281e20040c4031084850020a07034000c454080c00039001c0a034000c024950300c80500328140e60324082c00b403140040400056400c0315108001f061031440c003910042000e0384c0e689410040b0380b01250180c450900120301403203641d0041c01200c203d512a88002d102e01d0149840d0769050040180c04100406151005a81007003000e42295824503001440403442e01d40d680030005e10003841c51400b501c1c9014042106c40c10120b101c056455081d004400d0900982e03403884 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 754892365 1250 754891115 754891117
    0xd0b15040902130f0605030706030f0f02070c03140f0303070309050d020c010f12090f110a09050123010e0d06150512190203030403060501060c06051e0604111e0a110f12 74
    0x600b109098031030001059071f880821010b4024000c0d69800900031050380c08030b03c01c640d0410311000400b4010080781c0041240300e03074180c0950382c1003080182c81c04110303020580707422000000c41d03031030740400b00400081c0c03909036200305100c50150040d584040088102241c8400b40d140c00b40d4081420b01d200c0140181c85814403403030803990000000ba840100c6d07240c080000d00715520884c1d4015510700d8500003401c001c600030004000b007450500255040c280e81500e21070055041c2e0540d681d251450038204da1141601484106001d441000e0015807800c00c4000b030420161010405101e08200040c18244003100301d00c2412810081c150354070040c4540310b840302860006070307850700c0b040c8808004251b19100301d50081c00d0f070b902c030300b1a29884d51401e03c0503610020300c8045071142e25101614100f010450305a4041401c640004025000d446144200d0148458042d0403944e02554040b541b0a041c004084003401603c4902c040c80040b50850b60302c02103000b00441d160000c1e1400007030102c07114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 754893615 1250 754892365 754892381
    0x100b270c0d09050703120f05030c0a08040204021c0501062303160203070203030a050c011808030601080712022a0606150703020a060f1b03020a0c0f020409020d0b1504090213 76
    0x4500420b80311129195039107425883e400c01ea5418410280300f03a409600609100001c00c40c9080183c1941b03010080015a8058810580c051112880000c0c08540d0341c0c3d41140c3e040074914040d2919928821711007001008240589404295224410b4101d000340340340928460081600c44c13450b540e5001ea400034402d401c0d4000c102580320502022006036014009400200e01d641d0f07509848500055006094401c01000c0c014800c0300c1b40c640720041608242241d920a0080c248500607440e2102c1c2142d8007501050882126840070421401140e1703c01c260611a603200d2600e0b040c18031004444648410013691059803140030040949401c11110b005040070358000d005440e82c20b41151140d01c20303980c1600074241201e660300034241c814103540448685000c0b042c84c0441c24030340c4034a005898034999180103000d0716800305450b011561aa040804207130360142034207041c50141d2601400945065460662002c000c107911034084c2080c0c03045245541d001800203a00740010000280141000313 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 754894865 1250 754893615 754893637
    0xa36080702030316030215010f050619120f020c07050910060c1b060809160f120507050d0b010f0801020a050f0702030a0501240605040b0306041d100b270c 68
    0x9001e1484d902844003640c407802d502a40180c0445200350805514454058000c91101c0f100400d06102c241c0700d0f00e0640744104406c2010007060010410280d0b6800c8a00c1042c040ba18140540b1440d00c882c80c1d005480d1301c2c1c40b0502180c5845132511308110103d40300b00c680b010b200c49911030801080388200c81991a40e0300444690100030401110404041c0464200707401151000040c0003040004000344410b0358201c0c0e074400b4515003089070703c0c0f800c11b001d441000a02c0c2603c00e1f28006110080c80700c4002420001e040c0c0d01d120200b0f02c0d0101d48510b0034402c0d0790305159000070015040b501030007180c00580195036a540307440042581401c1a0f04040f000341c2e0188038403410400050403d100d9091668002811131200c001e5448400c1c00c440015000042044810311080100100080c00e480e0001c004a40105031440410303c0c80e816541c42c1904034407140b1614020a1903401640e01c051301e007040a44000740c1d0b500124000c032403842c88a290104450401c1c800080600d00c039003010344950810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 754896115 1250 754894865 754894867
    0x1260c1612091403060103030e180f07090f08251508150a05032d070e070201060905010b090d0203070510051305220519050a360807020303 61
    0x108805181691055060441d0320341040c4120420700c0c2e070081e00c540010b0441035107642c000c0c41c541d000300e41c07900e20621008040c0b04441401d00764076999135010446002c682c1004105d5031501e91540b0500d40c0c41035401001040320a00003264000c0e00e02c0300a0107540c420002031600c1e000c4150780c10300c10380103841d0001c1e102484c1c00d008204241071400c504058905560f402d4041d007000d184400c480703440c50802e6842241d08030b0003080707587c40100f88441120084807a0407104102c115001c015500d131214001740038001c2010100740341840c0901035000300b5881c2e00070031403036882d642100101d40302805180c0303c0500501071084549080c6001d00030361417024090ba841e00d6518404200c1e00b4070344050800100b030021541c462721110090122004000864280710b401021100303003000c000141100c203007102d03190f0002543c0e6405400c1054480407600380d04201d00d10300100341c900103001d04081214080c0b840081e100d40d188100e502d4000c0b030400d503441c80100a0040c4c0d584000c90340000d00407601800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 754897365 1250 754896115 754896127
    0x5161e0c0804080a1208060a0603090503090901030f11012109020d14010b0108060d0b041502091009080609011a0f0f060703080405150c07150b09070908010b01260c 72
    0x40c0c52020740001c0c44460000e1078490090316101246800c000411700811400008021181d540d01100d201185c095040c000382c1b400080c01e00c603086d44070350342c1d413944c00c95040e2000108000d0440302d13080070b06011b410100c2c4c46901d040c0046600d0070020009852514440c2c00101c140c030400c1e4010007107a031000300071140c410002d81e6400c1440350102c240c841c26964075607030500a540c200503003a900c842c044501c0c408801c9256104001d0480c0540081d100d0a004c1341d46484a400c2c580c115551123034010100c0c6585144010000c10010b80c2d4000d2801d40c1c007900d0086031484005019110200030030520f15108503086800380f146180102010607400020039160f03d0150301e07040e0003803803181e02a0b07031031202d18581401d245240048100420724551015010000d40003400015600b0243d4040c5800014031a0b110701280500f42e00401643d01201a07800d2107252a0003190050448144500a10035554207000544084440100185111894101e01a03550364821300312548440040c4545083c05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 754898615 1250 754897365 754897373
    0x15020c090403050406030b0607020310020313080304061b03090203060c0307031e1d070305070905060f030f0f0c010c080409020304031806030606080f04020612100b0a021005161e0c 79
    0x520151000e4000c690001024480c1c50780c140268080c00302d003943c40c5849c3c4000369011986e03c001c00e14620180c1580400030542144e50072040c80c54094200194540b07905090500e1002070406050120b04810b0410f94114954024000da030b800e55002030113050300f40e43e41017500c0030301e0b400140f01408060703030355025904000304003d010b8041c0046200001d0191504d266201c001c0c2c0000c5c0103640560300290003000000c0700018114140c031860000894951281e40c042102c1c549a88160355060050501140c240c03840007404412015501c001c03158240d040300c1c01524114000440039181c000208014403203c09150000c5030401d11a00c2e00440d50100c031902000b449005070031400000352503034010002180e1050860f508064104100c01060921341d001035403520600104541c00003000c400074129070489102c0e10001c14840d6801c55079441c11240c02510303144070499800c00280f03404041800c950404c0484059500b641d182c0c2c0c03009002d2168a900300301d40d1201110704105551803110005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 754899865 1250 754898615 754898629
    0x313020103020f0d1b03140c0c151906090b060a03180b010611060c0f160309080d030b040e0604020306060d1403130303110a080d0c2a0203120c0715020c 67
    0x84903203048001048440305e40040c610b0707800210364104243c10591600c84000c1c1910001c0e80009040c2c182c56911b4102566403410008100381844000880c001009812903840026040c1c1c11010300f0702b040742d5512041c013a81164444a009600300d2418032503120014043d501210240300c010320b0290f50101255103e1181240076081070000a4580f480d40383d100104100858110703203e0b42c0702a05012030080e0303500c4e0310301039020800380b00d2241c410307581c040c135020340c803010003400300da1080d155030400700e030406001392074044111401a4508548021581400304205006641c0140030b041c580d122031080007241c08030700350203480301c42c0764083c15031144030200020720801040c5650030030064910b080180c442d030002d5009444603006034400000250400c4211150f031340400350001390031034001c1407c440d9400c112071002106140c01341448134007651405900c2c10750b8401c4007110050641165071100a010310a0171640580c0440e1040c41100407007803002080511510443d01064080c100103458 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 754901115 1250 754899865 754899877
    0x90206040b07030206090105040f151d0d020c1203030703050405161401090501020d0e060a020f030d24240e090a050114030708060a0b2202030108060105090105060313020103020f 78
    0x11107000140d0720205501070240c01d030705c1400c5400800841c503007034655006981d0031980007000050200d00c94401c2401c2c1b0340c085400894440f410380c5250002d030002c299625092500d1001520170328200603050703c0c00140078911204840040c0d03095494292054010b802d02810881e0140150f501414641801d810300c10010300c07451180d0120044c1120000d003441d0880d412041c115000741d40100856900140c000e041a2000d039007156481449840890401a09651200c014000060083d20011b070701d4010703042c084115010943c490384900013000c1c003007445120784a00c1c0701c0304030703101e2090904820022420b04541d00f44024030846030000240105421a0703064406640d4200511140e4151203c2404801c01500200b40583c01c181000c1d6481c08001c0041d07110a0300c544850000351140c040e00719202064030f03070307410050001c0c4585002a4200f405555541d00c140c00002446141c134040403812102e000e0010b0f891a00c0741d89414402c414009026030505d41c00f000b4903002d02000700002e00d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 754902365 1250 754901115 754901129
    0x90204020405060a120510060e0d02030f010e250806070e04063804050f12070305030a1d1e040203060a0b040b0702041b0503180a05061e160503060d030309020604 71
    0x480e1150617606401183c001801c2c0030919840345009009090300a6415040228112020b08030980c0d10300c0024030b016950340980b03181d5400c0040c0c1502c048400500d403c00300d1020302440d071441a5451402e0500102403041ca0ed0a520070001b2032170303203401110500000000604045002c80d1504000c003204201c520904a0b80640074a0341c001c543c04c02414100ca0b0000304110342d1500d0b02d020005101d65004810162040d140700f410090388a008000900c01903070311009603501c8000421000e00404c500c00b05101d00e0003259040c005240c540f6080040d00700b05182d01210041b2603440921000b508005e04032034001d050504007141064441016000a007180c40146645031480c0c8144001d88111901c80c0380b00050841600d655950420300340d07a030214410010201d81800900d243d0300e013013859000500b09004550078004550f00c403810300c18110090b501c5650380c60b03c0702c20b503901c126200500030100284050011400d0351404241040245010346070104040f007203600003c0c0c2036030145e0b215038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 754903615 1250 754902365 754902377
    0xd08011e0806330901061407060e03281b0302160f0603181a0603031e21060a090509160e010504050c0c10090303180b0105121f090204020405060a 64
    0x401d4469640c50044041aa81401da490184490300810130200d01801600240040c0303030200e18184111300142c0d034803960010002d011404048034007588076403241c1250220070004441504020440c10782802480c80036544031611020182c032000140759081900310b08500989042150790f000004024001c0c06262030201100d81c50103e010b0103c80070822106801e110145009020804405540002c4000c00980c3d55450765102c00082c1980b140c0450303840049401c01100510080e014007400c003410480744540a201580700c6021824141240c00c65802024510144022102c580001e6001036019080303503a1440c00030b2542d0001a441c0e0418008200a440100302d10714050084076080680c140c481840d141c0b403d9a0280c48080c1501e14100b21500c072a00801010b01c241e0104422100b1280307075109107120751a004c07411117000c0c402d1510404000988146880021500380b0650b0046911140030010310000107010703006056059900c640e09100c00141903c0310001030910b0050b603550b01c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 754904865 1250 754903615 754903651
    0x10030b0f071e080c160b0408090405071b020d060e07081b04092a0b1c321302060f03100b07030807180918060e0d08011e0806 55
    0x4244954215034020b625880b11000b98a4542141560b40c104d41c078960256a5056581040c0c0702c990a428001452500e50358100001d00c40790201910b1380403022181803000b86c85404040760f82140c0c1007102107107650b440c00c15000601d0b211720700404181c4201004100c0d501901d1001d4200b01007a402036001da001002034502c00400c2480c14001010b040b1010001528161610202c40c1c9040c094114002140b4154400c400401080f0000034213103418010ba8902e2039a0540781c0c0c403030701c51411030392490500384001400d0b0401424401c0a4040440080078041200201051000040c03c1591003401c00d088200140e203800004140050078034040e6690313810450401d0090b5500c0360720071030b0309400500c14880000da110004640009491070021080b0000722800003d00c03029030310800010345070003090711007400d8100140e221039016041c200a10200c81481d9610b0300c0fa01d541090010782c19100500c2514803481030803000030034a1300003482c0161075500c62803804000744e9070340c84080028030007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 754906115 1250 754904865 754904867
    0xf090c140a08011406010807110d030b090a112208010c0201020408210d0f021603020c041805072d0e060901050102011b050a020a0203030d020304300810030b0f07 71
    0x501c000410811000300700700662605401421000581010b0402c404600400c00c414481d4480da9512801c1100740d490030740715500058020440f00310000e000c0c05c284000180003101c00e1040850320307410710340d13014500003484001c4104422012140e02046020050210b0300000c24481c0b81c0741006650001640e4500b4200c0f07841ca800803840d000302c01c50311000b681c0c00e61507440000703075079071180403038030200722000c1907581c45004e4028104610319001e03602f6040010b0603800110111a89425035042203043d6030404120741c820000c81001d0310b02c2e44415400c2020040780e041d07490b5603840c07600d00d002d100d8000103000e00400101c2e90040303840300f404105000d030b540b0303100102d41c0c01400240001c00507000840c886002114841540000307102c0e000c40e426140c54000d00550301c2d15940103007680c0d038860f050304203c0000d401c19a0291003000d4805e400301c3c1101c2042c44801d1000c82d1031890b18135004142d90003115130a40003455002c0090301141c0000000d4100d071601401804c001081e14128900000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 754907365 1250 754906115 754906129
    0xc091a070b061509100c051005190207020d1b230a060f0f140f0406080a0501050d030504120c0504050c090f0108100501080c0c07060206040507080303010f05040f090c14 74
    0x4100b520591003d51607030800c11038003084407490201540c8628036008580800c0c0c40d01e0030b4442001c1c200b40140310300400c0111082c1d00043c41a0b08c40b816814492001c58400001c83c016928003e40203620f41c42d0070310214807002500000c42d5281005a40b10300d4541c0c200038000e101c91052100c0c0c1303003070800101416141895040300505101d107800e40c8045207480700100380f9140c0031115030512081d010a5200d40143c6011200c1284c500c41007207568030740c0d801d001800b0b0803088032400d807158600300000c522464040074170590260565030b204c3c02d20341440d114440652030f09404842950f2103800004d0b058556008a510400180d0000341c3c40f56002c0043c040b40c400d001e440d65041000000400c002c81004e040341c401500c03c00c0c070348251181d0f038441c1201c00364440e0704d18181d580c1c41048000600300d5030010756284124416010b890205a50741e000940d640000c0c06040004c082c2c0d040d003400f260919901c03045603031089883c013060003085c41d2210003215046402c0003031140d803080c884001c1420114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 754908615 1250 754907365 754907371
    0x51002070f0b071e1401020c071a031b03070c0f0b040b100320010309021c0c2c071e0806150414010e03071a03060918070501030c091a070b 61
    0x2c00d60a140c030803a03a4440c240b50040ca0524103000c0750481c003d80030720440e003410110303101c89030300211b50380c40d0030035051a48c4071264841c850b051210a0703010301d8641c103420282d80c01100360a1160311000c12800000500c0e8000a00384020480e85d81c529401140303140f444001990b0082e828a0b24070300b4a0701344805503040051201090101700c56040002803d034824070010700400181c039900700350444004030042d019003031000e0740c00303141e40140c201d801c4100340040d84504d1180607401201503880545c0031440b9900100100140005130400d81215480c020003980925280761484600d00304001170b0810f81d42c10101140058003c100b04001410041c01c0b100c0c0f0094858001c074101441c0040a110f03038602c00041710b042001d228070901107a10104030316800350501172181c28002070300c214140c903590400c46070248104030460101c1e0440d400006d00f82d0b481140607000e021000d05041c01500a081c03c901241c0800000e07903000a40711a001d000242800e94074031419580c3c113541d09020705900405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 754909865 1250 754908615 754908629
    0x1b030b071116052404030b06120d0806040b06070f05070e060a0305191a0408071a06011b081b060103060c03060b0714010204030b0f040219050102030d020f04051002070f 74
    0x81200d2180941c0340300c6031504a900403207049108002e80c1380500700000782c1d440302110058001c1004000c00c002c03200d450703110710410b5500704a8514198541a91390515080700310106140b14040b86d11418107802200559202030405403403d0416595182001c80c032a00540e90398010800c00d0200e405104201c6800400454103203591900719120562030702040d40001020401420161082108081d1a10025408601a2601ca1400f4105504075a01058044607038104030a5101044406091902c3c004c02c0b041c0e4070106c1d943c0000c8030038481d58000c0f59040d01c4815091000c45d080d400b2a1440200050100c2e0160880e540345203000000d0b1040c5486000506041800902840c0076100c00e950b2420b130800c4544000c400140c00041c0280f1841e0406442d040700c00d0b0402861081d540d0005009078802d444007200a042c1c410899040c03541802400d005820820140e140700386640c025101c20030300504503524003a503030030010700046c103031a00d02c0000d41c01002b0200040320680c3c02040040c04d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 754911115 1250 754909865 754909873
    0x30d11040807090f0b03031b120708070f0203100e0a020f0405010e06010c080405040609021216051905090d0506060901090e100c0c0b010b03180309030d0c1b030b0711 73
    0x20126440e4035090070f0301600e0841030750f13107902c400015010703040304a035501e02070306072a500c580e40d001070752488400040380030082c4102d60100d458070f080c0c04220380c14030f40c10520341c0e8240b030b041c5d45c1c5040308918100f009980c1441000c80e9030304042007510400420341c00700c400524282e4554070511071014020808103100d50b1030080100080c000e0100050780c0102c0034a80407a05050601c3c2c09050750040f600615002482d00101003507040c420b0340149805580300790b2540039551002059001c43d10b20904400010b4810700c40ca203040c3c1c141a401040c00003443c10818100f103094408518600881c04e01665590f010381c0c248007650030903040311400751030072043c140403110040040c1e50362044a05e824000559070b034540100294401c541084011741d1080c1d8100c80c46d40d40c2e1a27080a41c2d0001c0d5080d001d002003240304410b2000c6d000045130740c030781000780107000079001c1d000007074a0a040300d0500340ca90310641904c3d01c46807000641500e01840c800c0002c0c1940341843d8000818550884c40c2e290080c1d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 754912365 1250 754911115 754911119
    0x807060c0c0519031202010b040506040c0c080306010e1f1707020a0308060a0e161413050f0409080c0609010b041e1104120c09110f12070201020f0705030d1104 70
    0xd038001c403100980390103a652900c100c50403075040303a030342e0703451340c0043d01200d854051129850303819041844904800c49082c440d40d21400108004c03562200003040225840e45000400250000c0c051030b0300c0300c0141441d40188158001090412581d0449441d01d09048449034001c1500811800318034041e02c0801c0d01341346001c0c0e50182d60703404a99000790901200c10000380080d81c0b1442c402002d08401d0301c0000142c00c029143c400e003000c10955180110f00590700440352428044107446800d032070304240c02d54151501c8248202903002041607a040fa8580020b01c02194820005040000d0100e009007650320703001c1071150031100d00f0700f0010b00c91400c101103075452510442c10400c1950485100082c03d030400c0070280040c0c070982d80111780c686100b0303d0765000e12416130038140031201d41150a2042c0304076010345180c94402d000f69489040014000c50f8404098034031060783c40566400010302d0103803810142089508103441c01c0760039610001e0241c80708221801217411443d0700c02034190901e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 754913615 1250 754912365 754912373
    0xe0d0912060f0f2405091e1803030906100b07030905091812041802040b030c07050a022214010e0c0706150605070506090a0c0303050c1e070807060c 65
    0x1109102030050340e100c141c2c0318401c0c90140e00418a807004080c00b009407002001200700001061902d100d0310f61540c1c10001000d05001d01d559100b145800900c40420100d0305542000c140080c055907144d10011480b80c1c00030034100001d5014034507900040070309140811142d41e402020317400c001030040d07081c0100400031390002080001d1350003c0310460003581e81e800e04101d080148520422051051201c2040100c3c0801c00420036a84d06007070b007004d0101825075039016482a4460200a01401c100003010f0940f51009401c100340b2490a451240c003240d00010062142444075084901c0c0080308864048100d2051610764840031516086541c9040c01c0e2000e403680042c00715000010002d4007070200982680214824036941e042503002c19142d1600415940050b01c0071907545c030a40000c6107900310001181d02a0a038040181540d8bd403c60340e048401c0e0708540203100a610072114554801021090320304102c11200c03004013100e5107004038240c1b403c81c0c9640024180074071000030354082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 754914865 1250 754913615 754913639
    0xf090607090513020306060d050a0b040b04090f170c030408010f14060f0f0418050606190807030602070311011b0e190b090d0b160801060f0c140c03030a030e0d09 71
    0xf40004180044c1c5aa65004c086441c030b1042440c0d1000c00b07480d040030440c1d0500b00794090f0502d1071050b68200070f042106014001140e2418902600e020880c8511a00203012981d800c00c60141d00d1203e1800c014515044600c1c542050300580481d94446280c005101d5443c8204c404d65040c40c8022003590030414013007400148005091402110300c019980800d407182d810400300c00403041c40d09410780c1c10b5420300c140ca9076401c0c1c80c034038490460b00c4c8030010070b070f80c50364000c0080e1040b141c09003010b40e107195201c3d4000d5000101c101c081c001031041314004618203214940409072040e114140e5440b0303001000b0560002009050f105419090200f05540084000c46041e00d10b040345040e40d903012400015403090360340c00000c0403203182108100700d00b0741680c48843e9005498484074016600c404050310144c604d01a040e000a20202e094000300b040304c0f6a01683c0048603003503559107070802c0c000c40e0559004800e10008640c030780f401030310030ba0020090140400d640d40703003101c5101c2c1441c500c1404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 754916115 1250 754914865 754914889
    0x809060a0c0e0907021c1d030f070b1309051f0e0c0d0905010605030109152901121104081b030a05030702090a022205010f0305101a0408060f0906070905 67
    0x103c4403180040c002500800250310842415190129045c200840042818544000781011101c1541800303006090005680c0008a02c1c28050301180d400d1803160359664109071701010260740c01e40c60001d40015644140380c02000b90714200d006501d210f2058100b4000302c0c0d80704621b4502e040042107865045d00c01540c40c0201107100104050070b0300e01308039001d000580c01048e81946881c101000300116124488c4220030846e8007804484100301840900d4900306441910180007540280200d6205480340000c00c1403080f0005003e01c44026030711040e070095040081d00754014101e0328003100d042c14130000c10440413070060414082c00e55a568881c0a480d000a02544100d0041000380055405844042035405032641d41c8243c0e071000310410f401c2c07921855011681041484c94124401c0c01094840c03200c0821009541d0310b0038101940c840b090b0000585501000d00006c11401414848240210a4981c0300c841906103a4422420704001404500500030b03a040b040000784c07910400307808 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 754917365 1250 754916115 754916119
    0xf020606181501140d0501030212010e0a020105210106031a1c0803280204050a120b06060d0204051306060306051002121602030a031d0a0b04030803250809060a0c0e 72
    0x6000c2c55804016200d440070280c940001034800704041c9503510055025504a0b4001c071003900351803e580440354200e0b08880d0381c41c081134200480300360165010306c0003403031f21310f020440901920031850f20842c6078190a03048580007e8442000d4450400c45500010590104031040200c180d000c54420035036403e048401072000c5801310000d4441c2c2000b2007110b03001401444048803041140a40d140254014041c0780c0c031503502c1100118480c0440b4030b0300ca1109a204100f0b208a40ba00340c00c003c0c1c0307078104100b9088529002c01c804038031600d505846035104400c100000c00d20b141000405810385070583c02103402100170482c035400c02540000c907854050b085111965561101107051009000c40b820040d400d0b103d000500010550710508041c80111280d20102e45600348004220f948002071240c02120303c801e100510108440000560300108116491498040c00386200c6042c42c40c44406480418202e00410600313100502000d94405240e05041003500611180a09001d0442e07e41754 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 754918615 1250 754917365 754917391
    0x2220b040e0f2523091b03060103092a09050a02031b0a030b0619030b120312090c1210060e0408030a09020a0504020c07060e040c02071211100f02060618 67
    0x40c9001c0d00b60950500a0701064807010409074604810320f132200015080c1c54014540d00300051160004e4510a03d1405080e011451940d1104801180070b000c6201050340e2100d100c1e00c5e8000030f01c03d00f40b012804141181040c0f00c10511b480c40d45c1c03044034001003503141114010410048408000840070009081403410251070303111400e4110000c20002c054150064400143c11130002070700c548115080c01c0c1550107100341648a024002c0aa2030005001500d61043c440e00b01c007512414a50380d4401e40f180c0440c1d4501241400045020b64800001d0f5100d400c00480d078107444800d405104080d2949070301101032400d080d0342d00030280c4801042c1104640c6d5901050702156036001c40c003402882c0050040d9200d4420002150300d0b08580c1c429040400c40742d4402261509090041200303c08282d0007a000141c42c003240d5488203820051700315000c00c0d0003a903440660f520044a02c4401c40c9075541c10704800000c03500603141000107041030340300e21600404610021042c040d110703804145480c00d0303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 754919865 1250 754918615 754918663
    0xe071d030303090d0c0c0902030a0e010b04060e010524181309020a1205010f1406210a060c180803090a140d0201050d1e05091509030f030402220b040e0f 67
    0x1d60071b4180260010602a400017041c0212020160050700000f4004002003180d02c1d05e440400c0202c4030548602d005154801004116501e015101c80c2046070b1103051618020909200782d5120ba484400c50400015000c046400360741400c009072905079034091010040001c040e00012a10310340b40c841c44000341540c46661003008001c0d0061892146101d20911070007084c61082c82c020002114150701444200d1514594420000c0c1c16030342c4043c0800207010042c3c1c0c1d940307401028000704101039083c802e800a45a103600300c00031800d40200004405180ca40000c202000700d05401540104035281c0403008080540d6030310503810b0744a03903090900d181c4c0c45018044240180005900d4030242250020710b81041049030740026104407414001d540e041c52194041303002514003990000c00719071090240703d01103c504002140c100303000805c2c091454540d418014041130100000d404010b8569884807960708090045e00e012844800203030501214841d1055a03d00442c001448258854060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 754921115 1250 754919865 754919873
    0x12020d021f060e04150f0b0609040c090b04230f0f220f0e191e0812011706150117130c06022b0f050a090e071d030303090d0c 55
    0x110b50014045070b00c10b06820715080c284000c00b0403a002242c04c13180e042c4440020000581d11500c3c225075001801c503402c040302981031000604000c08010244507041e280428100114409400240f403440e8120035001c0c120419803030b44030200040303607015807603900b00c41d9940d65410401c0803005000359103091842d410b0740864108141307440300966400780342135000010042c95410049a01e1920b00c11502600c0d09001b030702529000c42c000150640f8403900c207030f03c42030004024a0701458021180a82403e06060154500140030380c010f0702c030310091444d00300440c01b00303020300f03a807107081c000600740140c02000001e00070a88003040005411100c10028480600800781d080415030440a40141c0684504001e51f1b1503440c81d60080c0d0300c0744101020342000320000c101d07140c030984503503481c214240301d000203030390a40220210030140310707981001041210002e0b401521401d01c3e076030358031420780e50030344601c042d84464001c2e24040c0d0020810002c42c0040062480c041d008549400d00800a050074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 754922365 1250 754921115 754921121
    0x30f0312020a05040815100515092205130b0c0a052709150a050f0103020d1415062502060c0303040501020a09081c080601050c0604080712020d021f 65
    0x40540c00d284041003544407554040c01038000c0e95141c0040300e4003010303048444400880120790311510070100300c405000600382007050440612401c0c108a00f855000e5000414181160000b01c10060500c003d203108000e442c0600c0e0b401004400035003041a80584407a205944c0081041d00d090070006921030f01d00d8480c40850b06080e500c080307019041c0785800320340d100159000140303500c90600440803c2c2118a290040201007a0043c03022798482c0c9400e06210101d020b034603505060540c00d200540024400d400b503400460600e62074040796203800c00315006032481c0d030701483d409031105000b036114401d00382e901c1d05100c108007280d1250240c414800a02588545080c940e42c500020041c40100141500542180280c982b24410f0341031320b550320580da07040250082c00c100800804507030700c0e03240150701c203640142041c0360007450f1041d203a04040c0f0380708003503800701c8207403200240100902244801c1026030007104d06c0603000e08031110b04020b5541616074580040344c2c04501003c500c00000368 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 754923615 1250 754922365 754922387
    0x903021801060f050a022e0912030e0d080f0903071a0f18060415180b060312040f030b0c19050307020f07270f05010e10050d02060301030f03 62
    0xc14101921103a0016441200d40c00e10510001c12541d1220550842c00740042d00c051180c15070080074140c8500c0003c51090046580550701c05020303d070005151900c5000c1c0e082c030117004009c042c5860159020080845400b50410105a04840440850710758484022900309000d107681d40500c1e21102061401c500c9a820010b00001c1a003019035420030003200807500c04c00e01d040344030f41079a50b21726280d4010a0612038082e040e0b04641d000800040310280b002d201c0c1589a81c0004560341203071000c4000c4060444141c49001c01c200403c031007841c041003110b98500110182e9804d01d4176064034414190120300000b0102c04507c00002c0c0313000061030a5590040c80ca805083c8400d10400018000398002c0e03901c00014000c07402660165800081c0801c121014100445030016006d08071240203005540e114a10321b460300b4a04030081c502d402594064154140c1150150034680342512390302d83c866020b14021381b08188900050382d60b80c000e9078112904040e1080002040341b800f2a0202048 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 754924865 1250 754923615 754923619
    0x904051005070c030f022d121605072c0705090603010f0e07020105190e19110117070206070e031608060a140118021e0d20160b0601090302 61
    0xc0100b01e041980308078124080707402a10303040c0300c03080c0c1c2d0030080341c403180130090300c0e103039004820003600c200ca00000c01007403402c04004c282c8000c6030b00400504544c1d4041c40d0340d40c0c2807118011100003445020f0104a0041c040840b0120802d0050526854441d403410171200d6043c550000007001031380194111910350b000101301d41d6a960311030007545111511400b684c150b28414000042c03c403401445030a0140703d416401c03c610711016013006015010000403200d1a01485910200a000c00c07202c00798014855000022009246000108842c107540003d00c00c0f001e128007840407103a000300d1040d0b0803503c5031414030a018019400300c0e1a00c0f80303c00c1400d1941c2c000c4203000685202c00708001d8044e0580c0141445113503403240c0f03c00281c160030b00030048540168030580f0340762840c07540101101d4031210021810146043c0302c5110030b80200303205110880d282c48070040024811407500710018440800135007002954501c0d40106030418100400208504010402031380c0504139150041d940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 754926115 1250 754924865 754924871
    0x2a0306060909030e0d0203061501050d0623100806040f020c031308060c2a011e0f0606030507080433020d050f0103030c060906020f0c21160209040510 66
    0x9101d1800c0300510808a041d400034003103401d05403052800005041445400030014200d0b07483e121004a400c0e00e1300c880c0d5031305000382002840554940f0740a000300400701018004140c80c40c040c60740d04a00102c80d21742d44501100c05880e09026044070089802c00415103000402d080208005c0d0004e2040015078020ba110100f54200c42459100260081c0c0f280c1c08155040e070b403514039160050740101502d46910080008034916100d040150042c0c040c8018400070982c480306603600302c2c1d40d13860511080101134a038002c11411054a006035070041081d07103420021461701e10780c010134900b00540b008048010f06054030058400390a030b144030b140c0260701c01a04a40216a03c1402580844c42d0540e0309810701c80000d01c00010141464120307038258070741c1a84540b482e0307034090040400c000c01b2550030f41c1c20300601c1d26900c100c802070000d25030020300078401d40840458a1904031403c0c09070030b501101c100220326a03070069080b100705082e03058407804025200e41c904103082100b0303402c6009000345 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 754927365 1250 754926115 754926119
    0x1512030f05040b0f0703140f07061a040905060711071512110301150801090c140a09080105040c03051516030b1201110322020607080703030b0909012003042a030606 72
    0x4c0c08000a040d018444d0f00d400700561800300d04411a801001505880d00a090110310301043c40d03a04040a6404210140d038540010b1034002821520846e01c103441543c402002c00c1042500704008410000d400001411240e180030110742c000c02c280c00307480040100c01070030010102880e41088080c1420f040c1c03221384944e121414500010f001d103142c00005607103030300000b80d03e02d0b661007254400440d80d0b0b83c013100c0600c844049201030b0b1254520b00c013007040c04c52000440c048203207e42e9001d148146000589a450340c01c6c01c81c41c0141074407913583ea940558040c0000491045100c9680e62000d080c0401ca03078450500040084c41320744581c000c80d50a1084440e402c0c04024000c6110303000c01c1c1c04a002c1c450742da11400e903030091101f0000350049000c00680010401c640081c1048031310a2802041041d0a400402c1200c10705481c40c59460b0345640310145004142c106007442850405507a604502d010340303582003022207615581300b0060490005044a201425202000d15000380d01400216 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 754928615 1250 754927365 754927387
    0x14030d0c0f0614150103090b0708040c080303130605070807090e0702030c03040906051c03080415021603180501022103090705060c0f0c1c060b030f1603061512030f05040b 75
    0x204003200d2640d1586070403215180a5070107841140c884c01c8d044480c12509036950207040c1c860803c09002521081c054000c0011364130b00400c021882403145180185c1c00c4d1000d40382c03403030a0303c00107800f480c03d0050358400c00c590a503008100d481110710780a0305442588403c40140d0441c0306800f9008640d000004000c5800c640d1a040f40d4201c0b0360603194001920740304000b074800b00450000050000b03074480d011a020840c1844104206004800010701d4016404205c044a500c000800c40100c0c8450010004000342d909196001f0642070000d00b00c1220281000384080c0c4000860f02c4e03c005000c030110b4480d140c10002d0401900c0040c1000d5507036942001e070315903a40c0c0d80c40d17800030301c510420540c0451414915103404240c0c026005404800d101030751100b001c0c2904000c00c83d0544543c0d460001000790800030480d240140004c040380c039604504040d010f90307007159040740c0740340680300741008001c420040394a4481d405140000e101042d054040340e007440703a940403008504020403818580 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 754929865 1250 754928615 754928651
    0x150306060d060e1020040b1602040b060301060215090c0a0e0c09102d08010501120e030a0c06150305061906050d060204170601080c01050c01020d0f02031014030d0c0f06 74
    0x2016482441c0384003446880d010b80e840c0c8107c1c024818440030034006145101001c81c40000140d20003000482c801100308003180c3c554009038407090069224809100762000131503c01a0098107610181200d440340030041000c0f0760311f6126907080044050300184040500310143e0f0a0900300404403404506681802040b207807010742c512100f010400c01411b1019441480c040c01008952503012060707103003d0040d240d520030070011b0036107a62140070b800f52007c424002052910a51380300c0e4030003d81c3c541020310440e1500d405900c03071580510814000b00700000f4031141e01080c0b00b0f2402c04d01540028100b409003d003030b805150031014010702c11301080380e0398000e8000d842c0c065200540d491551850f107507403000c0a104a040e1a0416010703034005501c01c0700203006002440d00094940700400300300c0800c0f200d6003020740e500240c0c04402d1140f88241324502400070100502500c0041034244002a01c0712941d030001000c0c82a08003ca00400810b41400c580b4641c0100b01040b0310b0088888d00d40c44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 754931115 1250 754929865 754929881
    0xa1a1b10051f031208071211250507090203040c031e1109040c05190f1508010602030a08010e07030905160312090b0f090a03050708070e150306060d060e10 68
    0x502c04220000041c0c0c02156075824045075004001c50750711160003c416294800c01511500810a1b00641403100e40b48070301078503403000c10300d880c815628070750105400d480b184005010340611b01ca03258440045540042c800c0180e0300c8842005989031a035180460396901564030040549082a00e1980360340410b892481c0d241e4040d0b80035401c2c103ca10700400040701d83c102c80003842d0325042d4100f40014206404001c14500303544486d102066252050740000800c0d1340c0c010f031044034184040c0010660700066003801044503000850030030140c02009098500b05014003081c44540100049000e4807a401010355203401506407001c01144502646044855000075640d010120f0b00000c0c0da01c3c46448140101ea07407400200307060900c51910101c641e800420720951128103440084040b0f402400100d009140843c0100305032031400c2c4040c03600d0240201164400c51100f248007009440110310350b58403102c101c50074100110716140c41001000c2070900500c0a01c00e280c0710001d03003441c691151032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 754932365 1250 754931115 754931131
    0x2090a0b03010e0114030d0305070201061e03060f1107110406050a0b0c060108120a030504050f031204120224190510050a140f090912190e0a1a1b1005 66
    0x3d26a200c584100c4103184036082140c06038000340f507480605209903c03a0350403008520004c01c030566242e007120620135541400d80160150810100308001241c403e0a4502241c8001842500b1105880750090f0003010006072041c034204101d16075a40c0c0e640c0c800320240c54001c2c1a101601e80380c0800c2d800c560403c01402e0510721400001080740b01c000a1500c82c2c40b00030306001c600e86810351408a01600000d441102c0d28841d00c10418030780b100c1030001e0201c1e1816403601c0610307480e00d410204080540030030204155041040c16400c04650b41444604414200d4002d0300240c40b0040c0c4100b040c42030604410086191205010324a031401c00c1c00d2045a0046850901c159103500c0b0320018481003521481c0d104148980080031401c10b24030103a40501801c098941c12402030044c1c50b1141c2c402d0074840040a031038900318900340d810040e0b034141c4030001d0740c02c03040c1241031505154500d968180702d2101c40d0700218490480b0206400703518134289070032060303c24003130f6502c05442c0642000c1c1c0d1109 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 754933615 1250 754932365 754932389
    0x60504050f0405091902060720100f05030708090c041b031109090a09030c0b0c07140604052a04180c12050c0418060e06010302010f0903030504170102090a0b0301 71
    0x1ea0300d000c0c010306009403040b0010707084920320f01000300c2e040100701c07004a070010000e029a9001c20003180034018810208180c015400303628508100306840f0400001d02408461000224156030003001d803079120215040c60807840d01d61003003081c90210351707898941d4082e083c40600c001c03002d602425211180d0441d20140b20f2100c1c04904090f0500901c24039075000741c04000043c80d82c0c041501b1481086009041c00900c0300515160940c84100454240f070001400266040420882c8068503100b90024805424141815070b10162200241400711001d0300c00d41c0d0b4407143d4480060302100310120000e100300030205804c00340c01c408030390880040d0b80c151140e42d40000d81103418407440004960050141101c1c0b03049600b000000e20b401a1089511200d5004610001e60a8811804130b1000306008010b01d40c03640c4001444000325040c6a81080342c6a01d040001a0b00002982d00f6902480c00a007851010042114024011040451b502c40181000040c250400d18002c605a5820605035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 754934865 1250 754933615 754933639
    0x411010f050405031902010e0a091410050d0f050f0a14011407050a0507030e04050103060e010c0f021b1c21020319080718230405060a05100c0c06050405 67
    0x41c1d07294000d5108003905500120f038082c03142e1a031040310000152050500380c02d100c80d648086080075402e9003140010968135900704201312101c110b403540c0891840c01c01050f041c105808a05940b440c000010845841000c0741c1040001c18081c400a04002404840b014031160070086010784400043c034500303501e080c150040450400e544948140d10070307254285421804001221a9400940103500300041c2c078a240209540d10700450f070085001e85408542140642121070840301d04001c21820b00c0a135544000c1c0c00d540110783d01460b26070035030014003d980f011011680d02c41400900c0036440c10104881c20401003201e280d60218041384651040000c01140c09036660310034110790181c158040280403600390f1240210319070046092600c2e01d107005055074842c002c885950003814003010406580c048109485404101c041c204907400d000e181800f501103420320443d07004040c028081d880c03140c08860b00488440039410341c80904240d015548104c02002504240034030751154118480b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 754936115 1250 754934865 754934867
    0x90b240d0201481b030320070306140106110708120a0c0210120b0402031b03060111030307170c070308010b0c01181209050307080c010f170411010f 65
    0x180c045100e506840d0102a20948800c0300030000fa1840c9044061103151640100354001032030007841e2030103074030740c4400c8014546010842d280038240d010203114411407040020a5016800c03030040002500a0343d0341e4003000c034606090400c140c00c05413649007031040c009804058820024102c40c00f035912011401380d150502500d842652040c03500507480340c032000c8806020074000380322604460501c1942d800142d03020494100084060b0f10220320b920680d00c6102c8101c3c06060342c903040865045165103070103114100108851307112a51121000310000d074180c0d003d803100c1d81d490b1600c002125100d00e050b10004201802d0040e80d4040b80e594100031407103030710000c0c6c01d650000d54551981000380e0300f003d02c512000c0e007040700100d03c25922501e5020050003100030020102d03028070030040c03600019000182c18000383e6070003940680c1c40a0300400c01c01001062080c0c2d0074809180204840c401020222a5110003000200f0000015010300c0100401e044103503400b050282c07a032451040b54440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 754937365 1250 754936115 754936129
    0x1020913020c1510030c1a0306040f0e1510050105161202011d0d0923090411060f0d0b030708060a0c0c080316020114010f050d1a28020702012001090b24 67
    0x21f074425110f400303101280039807800b508044940703100032000207400900c0b48a41840c011200c00c0050341303800f0300c42c00d03c50482252031580c0080c20080c240503240207464455020304007409240a80040c0080f11800041c1c0e2007034020410a00c1c04811001d0b00613080c1290540715400d00c1400e02c045a44500001007840c113159250910500b4000c549020380391040c180015814014811182040700c4542d415196803083c014242c09070f0351f0a0469255031000402004860f071038807500d4800d61110008002c854800598680e01a040d2400491a0311000303006880014140c01c00408904012040110008824040704020111035000f400400c2c8a00030000695000f070040400f5141e520000303010a007480c0402403101071283d1020315100c0c0401000d1001c03100162256240c181d00000f0010340d0a60a2111314200780128000318502002940040c04510180d01400600841440041c1e0030081c00e50020080e01d0300444002d41c6d0b49400a14804541d031130781d210100328039521001c4200c2e030400301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 754938615 1250 754937365 754937399
    0xf030415120b0a03020d03020c060a020d030e06090a120c050d05091801140103110c03070b0f0a06061d01050715050601121107030311070c0f051201020913020c1510030c 74
    0x50300c10f40c011400c640920242c0862418207405501c81e1619030119901c80d030008080071043c6501510300c0c42c40c02500102074484091900c04140d1011003400803d176004100c0040440c2d000c0303920161841c0c8050705449c402c0410030094060b010300f1512041d0f450300038000b020b001030101c076126101c0750480d281c8000040280603131201122224a224020350196120300201420001c0050a00010384001880c0d45d001c42003c803000c0c8100f60074090a007510088940e00300e071a5200a0001c0c07410500014900d02500103461000c3d0105488100c240c0d001d04121020140c100340032000c0800e900000380041e0606032127450004149a8000305e03442114840e2003405601c00d50501d04d000c9482d142100a0000505581c40301d0340c003000398400198418807060010005541000c28240c03800b41002a03e92a88000f900581d004120201d010342d103001a1140c01150381500584801c1c100b050366240642c021006414043d0110511540c1806078003400d0480b441811b15058081e250003003180049408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 754939865 1250 754938615 754938619
    0x3071b050c040c0306090e39010309020d0b0907150918090204020c030315011803050c2817010606030209010801171603110103050601020c0102100e0f030415120b 71
    0x4408071221854a60080609074041c2d181c08204151510207400442d509019003464640c41007000d803418601000401e013040020700030031b4007840302c1076403804981945040e59504040d43c80042808660310380d42039402460b004403c4c1d9400746040d00c3c10b6640c45010f401034a908030704141c4a100070b94801d81540050720080360380d00d0881c40400340f5100143c2200750b82264416000d00610611910420143d072240520781c0b100c920b4152483c0c005014000160b03a07038a91882800341c2407005c6100003035020345120703040e180e507105080200c1d996035840d003440d00c060012003004500010b0390701600412116400e50200200320940e52034109804038812002c1903404101c64400410000852041701c82c1e4a44030641075402c046409030608135202d409030070482e580301c549182c4800f5542d1610074241e001c1d50038002803100c050f43c08000b030350310210560046501500c80042103d141014050b000c000450041141d480f41c0d00d0b403074200e1052203040090000101c3e0001c0c900d089480310f000c0c0d02803007240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 754941115 1250 754939865 754939873
    0xb0408030706180503070506011e05090705032502010905070f0602120d110301030305040603140708060f0d0203010c0c1a0c040504240303030f0f020309030307050310150503071b05 79
    0xba0780d11009071105210340b081c042c500c804203c3c003040e0144001c24a240c480c101812156040c0301c000d5140208084040b034001042040900c49912084269030f084559810059242d50f00d002d180404a0f1a03074151003d199080344160500580542051102c0d622680607118a070340c907044c980f619403640384207400059000c1035034254030f0443d0b036004201d8480034420101d0080c00500d000750b0740340e10070b031310440018500240400c020b0758540700e50039560017000c0c2500c1042c28480c2c0c006280d01d4001c0e000d03d1159583e0149400e45680d40081e030100b42ea80a80280700144201c20060701c40c2058110a85803285903a0521034840100e01803c6d200b680d078124404d040074140410700004100c040960342c0c80c0d1400029003000a500b494040004611a0380c0201e007a0001c03040b558140c4044402070b00105005000b4840d00030008400e50b81e000c1c4075894020b490365a81110f0b1f02507900260321203012034111520082e030096000300258880c0b291034480030700818481d00c0d040c001901d11007000d03100d504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 754942365 1250 754941115 754941127
    0x1b021204050d080c010c0504150e0a05040203100807170c190b07020607060f150b04060804110418052d0604030810081009140706091205031903020901090b040803 71
    0x9000b0a0102c4100e0180e04840d060480451819003141c00c0b502001010a00c0810100040c01c0b20304402d4803100c1c03280c90200a28075100c000314070760115034080c00e40b2031500480047c028030070348143c5500034a0b5a504441c8400d40c0e039039030400804261310408002c0e000e034041c1c1508078144040c004000c2c6001c0400464580c0c500740d802d511076000701c002240d010798104800408140180101c8006891000c0006028161240c43e40400e03000c07070b071259a11010503c810850305030001c02c080d03801500580300d100d0760800540010000c16030820169510a000440001070100c0002c450401250440000e1552210b41001803426007500120310a59400700300043c1c0003a1144400c05d8109000400c458492501c48000e5803d10800c0c0501f80d102d1030351244020144044107503480d020300f81c1c0001405126003400c600400c140240d000d1707061071646c01d10050f01000010070071150107002046144088508102008000c0d5219001c2940043c42c02c104c0800c2030550903084400300c0d21003038002c628140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 754943615 1250 754942365 754942369
    0x40e0103022e0c050111071a2511070b2706030f0114010905120d02011d07030f240504060f2a0e090c22051e221b02120405 54
    0x24908003411130703035552240040004101802c001e019090b21440a190881f540540700000807000100880d2422015800c48403000c45814242090351a80b85071145800042e1b881c40351518030181c2c080118000d00003047c4501070401c2c42c0121440106031400344c070000d008001c0008074001a14000000250305d4010404201c410200d007a40e04c03411704002026565640001d6906001000014040e422062a00c4c00165080c803e103980d0401c54106044c0c4202d10401c49030b91004240001002c0342c403140007850a0000b10702c500504a4035407411019081915601440507101c1601c003114100e04040b0113100a10082c040d401c400e0052100605011072100040d11210700400e0f4444103003d40d040c40c210b52a01c603014003901c00c1d080281d805540d1001001c034800303568003038482c5100c07540d45040c0911507641e816100400c0d544110f00c0b00e40031100c400c00001d0032500b000d4007803482c007110345a00c0035202260350440400340c20a90969140760b54070020030b82e207400c5104204040180200b1050200d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 754944865 1250 754943615 754943627
    0xb0705070221030c010b010306120b06010507123903080a0207140f070e07050a03020f09091503060705070809100e0306040f290a0b0f0402040e0103022e 67
    0x52800146031200c1449050038261000d0720b2401441590b0f0400229030324240700c24000c84800c03100a18082020500d490340c280c0a02d01c1e819801440762010a0100c0c0a9070301c12010345203103c0d007050216000000c00c0501501d4540b00d40b4001484501514080c62002c080001d200903108540a050a12000c0303960100c03480301b0010480d51005031300703010076800301d8904000c04400d480754400805040314802107051401319290310403490452180c0801004c0d41c0e100c0e068980300b4025040150b11000061501c0b03010340a403007501504000c401c0204082e083c2c18400c2140349110940548415864043c800c503142c0c80b5a003009440c1c140200407501e000c0c203000840802c0307040c6c0c0d0324050075100350202c0000e05208081e40d0130b54840c14000001d00600c40c10f941d090101c021984600410524502ca6005c00303080c0c003c1c60803a000350f480308016455240c9001140703e400004204564035a150b150542c3c01090a010590180000019400d00d110380c43d001100541c2410259480c40140002c049482c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 754946115 1250 754944865 754944877
    0x5160f03110711040f020a091e150507140105101703040f0303090e01150c02012607050d0e030a0905090c091c02040b090f07111c08220b0705 62
    0x10556900031800d079000248014001451240d00148080d4403d14104819107001c602000029441006034004050f048a1302000715900800000021080c04c10f600c19074420540c800c905100440c8060b80409600100400186110b8110303175204031034110703249088a46c1190309241070b08800740e041c4107400c8450110601c010020003101c1c0b0b859184e403140941c02a10b030380202d001ca0300d000070074000d40701d03c1d45030301d80581240b90b110880841d00420060404055180103418800d5610702c007510074000c070303080380440c0d40c00c0c8101c1407035820400402041c660140c4200e065840c41d045182421700004003c84528207074658039a03003220b0602080100484001e092148811020843d080d010744823204181e40258041800e44c1c04203102d40144000da40c40d10218503c05c03960a8100300f4814080102107030000240d1400c0c14074426042d42c0c0f10301e0702c024407000201016010300c205241ca50300c605c102d4400c0c000100040c83c0700450b90301e144202208140c00030301e50480748001030340041c420000fa02c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 754947365 1250 754946115 754946117
    0x10050109140a030c080304051309170d1508030d060806011203050a0909050a090b16091a04030602030c071407060c060b22090302071d010e0a090b01080708070905160f 73
    0x109143e60390b5900d19402c02150300841840e0004138080105107000c50014040200c1404144819866940d078811400100310755210504808030345000c03007880d03c0e4403c5403065440741081200c0c5446e505802d9494200b5621300c2000d5003081004a10400082030050481e8078640072a00103544a0341c0035111034103c03204c000e00304a899040090004024002c082c000c003408140000d00c0da41c2e42c05c0003000500e005110a070a803005441e90203265900598801c2142c1c0004090301070201c071764021001e0351007540c0c409004c1e54004070034462004c0c5480010302c6030b00d200760390014404d04245c000c1a1202107510580300428042e404100c003041c950341102d4a407440c001e058007501d4a00502c0e03104c943d5410511f0020b1245d0740c0044004041c5c04004810291200100d81c08040c6041d001e03843d0788a41c14000c00603028110700205100b030343d80d40c020605565100d4000b045540c0c6038560079940c0c51140c0706240707441c403e480001505d0b524a12416018601300300c1e007001540d440c8142555207080b0211018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 754948615 1250 754947365 754947379
    0x909070803190225090c090b22050a091a0a24090e070c03021513060906060504020c1005150108010603050711010e1e010605090708070e0310141005010914 68
    0x890410600e070034250710181060002520b130782c00e24402408881d120701c81e8000b0f11148400a01c1b04e0400c40b426240088a1543d000b00441d200310705180642c6030075445075400c554010004a0940c0581d00700d51003e050040301c241c2d12007034403010003800c02c50900c02d1020583c0e40101c040002d02c45180e204541c4402030822001a079652159010400c82c125041e10000e4015514007040581c1440141401c200e038a030700001c54102a40c1100030700e5a042c5000b4030055076251110104491500000003c180041c421515201c40c00d4166880d074100340801c910551038000058684d000440e24000c100006944000700e5a09241068006010203407402041c00010b110581070501d090160780010078289014181c0300309031001c050340307407000105412056410100c044c001619602034040d404142450b01540c55116690140c0348101d20701840e0b87c05000d125810109100c0c0307500301415400500303400143c141c0d2051808403070b20005001e86070000d86a01c1080290300c450524400d52840014034903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 754949865 1250 754948615 754948633
    0xb010b0c0a150212070e060f0706150306060503120f04171f020d20071214040303090311220203090f0a0f1e080a0c0320060609090708031902 62
    0x320721219880942c0201940000e204010032180200e40381c0c20240508004058404500010307001e400790001c1c00702611000700b090030a0043d00d03007210000790800d41c500c150941d03c0c0e05018024051a0081d140640b0034080c002c4040040c5004545080130300c001c9482c1054140503007015000421011002c0c14401c0c940c0b010501c0307038160540043c0b8605004016a680603000e442810754401003072124011075640d20118490880d002110245d03503005d0b0001d0b02d05001400b064429003129800c00881c044041404801c044c3c0042000090303900031409006810415020412b0402e40c5c8500c0c40002c10300492240b110307a40c03d401464100074010103407004031800e24545481c0c10b5040703c0c16070b003149001604034140181441e006507407801082c0d11400c10201c0c3d80301c6805902c0f0b8007881804000000c030000d4289442564160300720294241e0f11203c070001d20880680d00c90058403051300c980360340e001050003100001104401c5540d0003001d03609194504640f48041554101680c080d40916458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 754951115 1250 754949865 754949873
    0x907110601261b04050a0905060a0b1206100612020a0f08091e060f01050907050a140405041b0f0509030a0206090a03020402030c04030b070305040308160306030b2701090b010b0c0a 79
    0x1d0f420300800e12003c00c3c2560318802084103494003d017920400d60314102502010a4010800c260300c000c0503080030500440c44004103110703414051000c000ca020b0300082c80b045284141c82a41113446036503a0343c09004003013024200324810610b1030004281c400d032000d0420741c081e00c031171170780021060141c8001c00c217010069410305501003800300c5544c01910400070000c03510119140500401ea640b40014a01058064240d1050b80c040100780700d0380a000030007140d00301c0d044501070100034001380449074441c13600800d0326913a1010a00420411003503016010f00c01c4003500c0800300c4c010010100a212902402120b40c411851560403000b420801b201580741d40c0003c40c040e4010404c034a80d110310798203104d01180f001030030420403d410601884080b82d803040e1415001125001615952070900304e0590040500742d000501c044004c00811081e030804060412b8503003d8980d08503082d0f100340f00707098201c0d0051000201801248001449124103100107460240e044500319a42040c050311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 754952365 1250 754951115 754951123
    0x120a0e010f020408070e010b07081b0a0b01030204051f14040603060204030318140303040b0f0c100b180910020715090c09062408060d0b0114090711060126 68
    0x220381c1d06490340000381000320490802c504001000c2d407207100f0142d54100030840049100781d56000e00401400328a8101c5484c0c100740302810702000200311180d14019203808208002e0902c02a8801d82c901000260000300c01c081d8003a80760800c0740d0542400d03042c40410300004214500e07050f00a42d50710400f000080180c4010f2010314002c0e1200d00301c2d07550052905c84407000c00c2c7c124844890301c038401070031036850001c15501070754444840140c407418601400100c1380142903000c113103071051a00e984264400b40c0c0c4900100390060301c3c003000c61509002e410900400c113603003094490f030002c1d450181400c0254003900300c062103030307544820f0030699545400580c1d41c200010b49406035848002c0103030240701d10511000703020300c085000080b10060004005900e050304032009005598001600030f694900794202c07240e40c450444880c0703584031804c03200580c88600c010742c01281c2010108a0107801030b40083e200841c120011714983e03082241d2241310b01e4508048950704003140320b0401101c04d00340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 754953615 1250 754952365 754952381
    0x6020c22141003050f030c0c0904080d0f0603020907110304150c0506011e27050718140f0a05031b0102010618020903070e060333131a0c120a0e01 64
    0x1c2c00080007075045040c69410400340d001c110a1943c400c0001d8045454041002c040f9203030201d1341c024195507142400305880c41242d04424007940340080540300150680d00c203009403070081d5921903050362842e109840c0924a010b90350b419900074001003010742610004070303140303140525040900302d1301580c1d0349142110a810180101000c0c5441c0c9190501d4040010010301c1c89880218100c0c10184030b456040c1e40c040180e40d191070b00c540000d0031080c000c00341d0407100320381704661030030095503103d82c081d00b10b0380b01502510510f41c0c0074041c0900d00d02205c100307054481c014090b00507000300c90701400c1e100292101c2207040d9501d614000500f6800c00403101c00759519400050b035504510300030075051015a4010200c0d00c280b410501101d41c0f000516840c078418211a202d418005050801d1000344490f4820740082901008003d40707101190640010603205100d031081c480400d42005075201c104484816001d030b0300b484071b800c40030307156080d00e50001a005070001e504810120028207540440c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 754954865 1250 754953615 754953631
    0x2702040e03030c0a0f05090a0b2206030e120702060412060b040f1e1a040c14030c09011404030506040b0705160b2a0f070311010c1806020c2214 63
    0x4102d0141041d0020b0307451720160070710319106203040301100000312a1007450169828504000c80c0308580b0304042988020619a8900c02480703c81da40c0074020060248001c02c0341b0580580e2000c80c0c0d10001031070641321415401800c030b50900e41001c2c1190a442d00e0a08160703159915050700709020317143d03803141c540b603055440d00105060141c1c0c0741c00c882e8198440020340140b4603103120550500800d202001d1041002c032000301d10450004000c88402c21000c2100d449640000f0901c6047c4540320007c05560700280c86070505800750700c2400c013007405140b00240041e0007810000c3c0029165240c16a44140301d0b080c000e0800c0b030b21100780a0403030501441103441c11f01450034025090140004002d00300503140c0700303261040c64100c100d1640e010f13108a05c642d0b0040442d5150030140100c1c98140c1c0015184000c0146407aa003200608002404000c8412048040c2011911a102207030f4000d40101c0600445100c0c0030565800040c41c1c0c5030308640e400d840da58117000072425100704d80c40b80160340d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 754956115 1250 754954865 754954867
    0x3010305070501080603060402010f1803050f0f011d03092e02010e1006050d080921030304030e0d020d02010e03100e062205060c0c0c060a1e032702040e03030c 70
    0x1041c1c0050038551300a06820300c81e9004408100060381d21100001100d242480d240b103161010208002200384180c100070b20354064020004081100000c4000c541740c1140000e01c003091b8403000c008125400515210081e4004101100f101e041a10081515008680c071480c04220405140e0f04801d444a46000040c0d4403003056151000d401c00c03000034851200282008510b180c2000034403042c0c0c030a0002060300030080783c00380455441e50400900740a10201c02c0d2800700219240548a90003207804501060303000b00c4d42141800e000c0c0c9455442d83c1c0c040d028171041032050300156420302000c0c440503810320540181c0ca58080c0725010740c40311003803000002c00741804e14403080c5035180e00840b099400f0041720b5803a100400d500003002a04160001601542c42a40700c4926040441c0c1c280301c21341200c0700203030a500890b032182c0d0359aa1000c40529004207505081e00403003e46025000c80e0340441e00c0b440110741c1c958080000072188a10040000034030115055070182103130022102201c4402e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 754957365 1250 754956115 754956119
    0xc030a1a121f0209030316020609040c020619060e010e0a090c0f060801170316050703050d3203060f220917030c0f0304061d031b0a020f12030d020301030507 69
    0x102038032001ea00700400441c15030600361320310042681c0e40182030807521042c11604c540030070754a820040703420015014009010a030b0407440085d64030107003500c688410300e611175012007061945201c3e01c001c2c0c80c050768001c2400c1e481c2c94040f5111741c1d03018100c1c0d948540d807a0380c07000015843c10b00210061031002d400ca4003042c501071000d001008142c1c000704280c0034856400b183c200000c400c45001b80780c82083c0d500c0c0d141136400c00514140c40754100500d144600592044010741000f5015080c84c08807034000b0602071600890940407071510341c0202001c4051010070410720309021510590a0040c0480b014011114584180c0c983c106502c0340c0c40950716181081802440c01c44102441c146880d180d26500303000d1a10044c5118280207003441c042c1c044003050030481c0c150002078051806807a2844001c011141782074403030f0b0100d0092110003400441d81000080c0102d64440c109400800100030f007036a4a050062044c0754034000202400108442d003000105480914080d601410003401c2041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 754958615 1250 754957365 754957393
    0xb073b0a061d0604080606060a050c120409050903090a18090501021b01140403050d02070f0812060316080613050f06041a010b0f030a0b040b040e03120705030c030a1a12 74
    0xb250940914007490042009120310b0000040064001c1c50985a145d507a15080608860034000d0803035214150240c40c5d01c0100e010580400b0b07100b0b0f80c000c3c030410031098032240c00b00f075924410a800203170042160001049a261084200c0040c88100040402c00800707503624942264040b007082e40404c503420f890398505c00e100b40305052481c001503403010694181510090641d005d201d03a00541680c0008240041040780038140c0101d980c012510783e03c581c10117006e402c40200841e5058024030072109070841c602ca101441404547d4298040c1034142c9441d60b850013000106001919248520030001e18008020402544541c2c054a400c600074942c0102c18540050306900101003000180841c00d00c46032a0012a50000e0012100040744614400030502400813664010751151400c0864244504088000d00c904840969407001e00d680300365003501d080c042135840f07108401d0144009042000d01f42d000c40d26656405100240000611000545041240204400a0300480040341c0c0e04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 754959865 1250 754958615 754958657
    0x4051309031b140f2a010201020f07060b0414100302060304020d12050304030f08150d05251403030a0206040212010b211606020c010302090a090204090501030b073b0a06 74
    0x21140e0701c05015903017414008401e109600c181d02c1d40105110800082182e8000d41c11603040c611b2040c03000d5101c904900f040c0000380a14124940180d081600c0d0101400c1005503592243c84041c855480d1a41190203105440d08020401ca811800c03101211010407088a103030300c0810034613038030556a80f80518000f0724803543c02c60b82c001030042034410b11000610400420740054000d4880c50b082403c581006850090761400501022043c0840420b103040000f0000c2c054070544030303400000c02c204c08141680ca201e07004000b001078020101090043c64100c900140d41000d00e000807485001c0580082c124401c84220b40030340040c000b407650300c0740105102186040b244806d81408080c40e00c00040d4481180540c000c0c10540e00003a44141da81e02c0d0003201000e0301c1c08c03802c00c54039991651115002001d00b0700098507070441c020001003c052040500710044043d1994445030840c01d64048004c440d0302002000340c101c000341c91404991a43c002c07480042015a4410384c040401e201d031100c103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 754961115 1250 754959865 754959883
    0x6130803070309030c060612120207142806120614090406090807080d0c03060e090a08030a022203051c0c0b040201050c0613060b03121806070f1202100204051309031b14 74
    0x554124074810400d91085103081c8a00700c10a46080cde05485513140e0030810560441a41ca5001920480c0468a51351142c0204d0500c50304030001c21069840e0340c401c16648e244520a65031042e00d01d0002800520942c11040c8064420000f15082184581e22048250421100080e040c1d68801041c081c0075814001c00c0c005086041404001d401c01c04001c644884000c0d00c0076041201c0080807418400d0643c1c111a103c42c19001c0e9a41c500003140c501c0d07109000e840c4019581d51042c11400449a484c03040701403030140032511002c4d004205a40c07880003004c00140b06905000c030a110500300b280c01400894840c002600f208034640b000c0b031a00104440403502c006d4060b0f480342885c0305245207417030b0807074922801400004c41c00302d2902c0c0008402c0d10904100820b00303501c600f515000c100104007030203400c00c0b1a8080d00c032003030f0b4100d4211049000d2032164641c030003845a2004442c0d100c5a002000c2d040c02481c204001034002440103030300600c0034000b20b50b41c0c820f1031200d2082c00d03070a00081c82 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 754962365 1250 754961115 754961117
    0x1c021b06060a0911032e0608040203160f030f020a050901090b0301060801200903010608070e04060605010507031b030903082d07020f191203050c06130803070309030c06061212 77
    0x6940260b0200f8401408010100801c07038451210582c00d55130010f26140954140e1480b00d0006e54440308020300422090340c0403406485944d2261003410880221070094031143c50901400078030f95219020140301852050742c1100900e0710200b003503100d55141c03134082d01c01014041607100d6a102030500b110080e5104051503403400040404010b100c600050340c050f054200251100d074081c00007801090380b07900552083c4a1400001002524282c446e4440c43c0908420031001756035000664440c4a2144000c00103078529842d0050f0480b5441d44001c418000e00e840c0b42c000c0e880369a8480913602600340300300c01c1645001100344845646040c040c00424070800142091010380c0840c003101c00480f01a44a04410b0400303004040203089000001c001611040c10301511509000e0401d9000070b030641c00501648000070340d00040044802c00c101d0b4420100381c5155a0711710118010090030b682102000720041c522004115140074a0014100150031200003040c0303454804d10f85405e1407280c038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 754963615 1250 754962365 754962371
    0xb13150e0318150304030e09010e0402030a02060705100507020c0a05031b040b3712030903170c070306020307032f0319050a0b010e12031c021b06060a09 67
    0x1442504080142d580701c0184030380e0101c984040400081041d00d00661001c0c0c0802d000c41000145640402013140000d000d031940c4820b6626480b40d501e5881040782c1c040c0d0164004124440103003807440042581038003640580740b13203c07101c0700300000780c481c190b0b900700060380400d01d1030030b0500d000058103000309400c400074136251440000365480c0d01d1b00d0b081c0130b0b803040e43c0c0c801c0800c0702c07a280d041d402448204080100b282081445003c0000c0025502ca000780c58801c81c5000318515101000504ad070310340548890803030900e556511040c401c000000050356400c00e010715010f81c14100554005944544c50140c2c50f4684664024111448418141801041b1a078002c01d204c0482c4480c0d8801042e29120f1541d80e580e07544a018640d0b00c400c1420303a2540742100300410910aa88928a011001da94400004100600b081070540da001006079507904201700309203680310241d41d04003149406031000341c10445551494800c42d01945401280c58000c2010000c5501c4e0002d8440040d00752a0010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 754964865 1250 754963615 754963631
    0x21e010209091f030203100204140d03020307112107181107030e0117090c0301050702010e030406081003050604051f0606091517010f090b0319030c0f0b1315 69
    0xa008800d02600031042c1c00c0c20310a4010340f802081c9119000785402500f160b4006070001c250700000e600c90b10810710403c00410303030780c0c566207401000310292542645c021410100c117511030f01460320280c41050b1340f00186000e1440e10103400300e8218071002459000c1d1601501e401c401c40c800314840880c1031000352401e01c284030340801040075039a40c140c0600d00408020030850040c2c1c0d8603103100750019140c5640d1403c000c0090030003d880b0a0520303040d402801030b901e41c40d80c00d90913a080c0f943c448045401c00e10050202c01c2c4581d400a03888003966100564141e0f80b515228140348050340c0c140c820390000c0040e001036021940b441443c558083c13000700802031820300001d200f030480d40910001e070900c0280c48001e03507104010f00f00004280340303906030513540c0d500d8140c500300ca0903105244000b81042d0300201039140102d8118000b50a02c240000b18030b6403598215035500304a1300848400e6030b8008054042002d03011741c144114550022646c50444a04204051110761006070b48018180652 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 754966115 1250 754964865 754964869
    0x1140a180b0118030f141515011e0e06070201120e1c05030621030702210d080903040501081801051e0a0c21020c0a050102031512030a080a020910021e010209 69
    0x10110860340003201b451500b011401c60328240031810383c030000341000190600c00d296140302da81d2041c50400340c81d09003541321000b0060a01040c0440000c012800b6841c00700b900381091002081c907148149010812100e542c9140380481d0005800c3c40899444000c860355580d1885408409007042401c0c484d007107141c528000349a07001c242000700031180015030062010304040066801c0594000c0103400c10101420380d18007505e0451411032410710801e400c45402034081c1c8542c50040e00c4080195103024146130041d1038051016001050401540c602650b11400a104c3c40340603042c00000d074043c19038100016032091a018050012461924860060258001c1140d00880081e00240801207a140d101709d002802440415681c4e4041d0807100010080c0640c000c620901d242a810807108020806100840016010585882c0c0c1308004020b504c6e0700880c0100d078000c2c134024015181c00b0301c24000c0348a141c212a10070025034004130b00103210443d035100c51290f080c10362008602749030071600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 754967365 1250 754966115 754966133
    0xf1506070309030b0712050c13090e0c130b031216020d021201150806010f031203020304020a050a0801020d0e01020c0d05090a1a0414061201140a180b011803 69
    0x41128421040051248109070042c10440300441d00030004481c80d00c0d00e0f205c050030b8003c200240c400e259140c2000140c04460440940d58049200340c04003080508000c801001400300320790020301442804008111540c5800c2c150b4008402110007044a15035207050600d8000c8200c0c40c0309960000b44000c0ea2204d200c0d5940c0c4c802d8540440e540b00359541c4900215510b441c41050005242d400c03c0703162807540300150041c9080b12085412500076a1b42d4010f90070220049001c000d080c0c0c400c1c400b40282d0780b0b00c290007440d0007a000400710000c080d40c1d00001460160f840d407140100383d40203d107250f400c0b14207114844003810041c0003580f510f01c40b00802516407110390025420310501007040c140c42d44504803100054800d06d03841c160312207030100c16030029410903c00c58078000000640b141c00382c00c1100c1582d0450125402d0b02c7d1699080107281c0300c515030200b001d6600200c422200044280842d032000c101e40c0c041d018009404261000010070060400c20443c1440c18072503020000241c07104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 754968615 1250 754967365 754967401
    0x8070603092d02040507020705010e0604030302030a0f030b06070c14150a1b300302070c090902060c061006090b0316030506010207080a080a031b09061b05060f040204050f 75
    0x300090101009880c500c0785058110b00c1c0203034116103040300f0420025000540305003038031000d0301c904007000c080350200205031050b4000140182c00c14454000b00d00d01550b020f212480550501140070325400b40460510b4028060030750304504500c4040010b08440818800c6000040e90042d900303000c20480b4034030b0ba10481079039404015110300511003107041e804951403030551140241e294401c2400101c511032440c0a05500da00c00d00780152480c59010703201702c42c0361a034442c4242c0751301403404010100a00100c2c00a903003004d410081c2543d446800c0c000d85200d00110403541c50343d1814504000c10220094010307525102003001840900d06035504206c62039006480c010403207a80310b00040382000c90365072054100d032054400040130000204042e24a02c1c40310781e000c200303081092543d225201806540b1801190b41da0000b405500d100d10091515208501c030325002c40c08207941c8040c40c240007141c41c00215000031080c00210b18240c082c480c1c0091003e45609100d00342041103070443d041c80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 754969865 1250 754968615 754968653
    0xc0201090c1707050909010c0e0132210709081204090b040608030408100f2d150b03061c020102072d12030f0305011413240807060309 59
    0xca50b89040000c014000240c140030701300c8031741810a600309034081c00e0f44451100c049290b896a0140c103510443d020203409150710900b00e4500b9800303405100000e65501c1c3d528071210704104090182c0e4580c1c3c05d404003044110101c403814985560f0003011844681c100d02d80d03d401101d092409406080181c03130541e044070b2400901070040f20000782c000e01a0380d0041d00c03140030104000405903000705009880482c4c08405000b0140b50700410307011100100c440d9144031000400d0030341050a900d1403803440140440d00000d09105440c0320703982401c001e90200500510001c100b001600380050002d00c02c400d4480d0700001c002d020303030020f034417108140104c450030b62180c40104c4402c194120480c0c114000b81000301401c0c5c0c1c580c0c03920074658644c01001d0700403802c80130558907010320031b1140c0303070407907090040b11150302000c5020030403081f41441d048000280c5941040701c0d00201c41000c40003e442c060b07000ea04052410504a042ca1030540c01501410703d0040d4180100f4000c9240c80d450000c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 754971115 1250 754969865 754969889
    0x2206020d02070c03030207060905010305060d0b130519020f04091a100e010f1403061006030f150611061b0412031101060f1806180b0a180f0c0201090c 66
    0x200140c180080c0a01400580000510b0800000349a000716071082912015501c1c0000b20340c4900c0150255042611290b400a80e60355201700440d528506031500940608824140507099440e05491b0440b403400b064052888203107a5021440c00203031480b03002d0700555081c40b1419440e1a40100c1c0e4540ca038040c845948030b40300090781025102220b0014100540b903040c0c4a50311800042681d2919000b482210117640081c0c010710b240c0001c8152281e060302501051359410701004a000d045440c0d900d0a00c1038031940c01c1d2607503060b0010341e20003070040c0b0341e50000500c64215003d031404401524052070340c41d080c46040d954100410448095a61854502c4008121032a085071031402d402c8440425501e442004180701c4c1c1200340c0881101c0c04140300314402e081a100f88002c94140c0c1c404d2801e000403104507a0030655481d046648400f40c01082031030010b503508d001c00303070b080f4030031045501e566070310141d440c40801300d44500021100307588020064543d050341c810421018500414080c004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 754972365 1250 754971115 754971127
    0x507030f0c090903030209100e031f0b0607140114011202150f0c010f060510091404020403140d03150b0a1218080d0b010c08031303090902160605220602 67
    0x120051401000b070400032030400000e155802c009000390004410320f44607c1d100003003152820b10174035072a05d001030000d01401c5180d442c1141c1c00074a9640f86035400c5569200d08404503180e407500301802956000344000b030b11040a0810b100d00315501328003080080c0b8803820041c44410b00380741c031984505505a070818031051a410000c185401070006d0143c0046000688084650064104200e1900080000e01545031518204100543c46000010000341d010004026000c40c9030002c03400c0b00005003006107016102c2d2550198003082044017242540030701030303400e8000d606105245450082c41400701c0300d0f604007031400b81c6510403600071104104925a200c1034050242e40950780c003020210781402c42078401e18200c007082c3c210009580c0c009240404035105175004070540e2003060343c003041c6a4610350328145820700c2034071510415420480c1d80d03000410642060b10040c015011014070b0010035040070300d04a016500002c00d4401d54000d4031140100004581c4031084203c0d601081c0943c40350 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 754973615 1250 754972365 754972373
    0x207030c0204050411010f02030a0e0603040c050604030c0f05041103041220070611060f060d03050f070309080d0306080303240901060f021606050f0703120e0105060109050301090507030f 82
    0x1440c088040d502c0340c9007a013407004004007809620b640d24401e0b210403920710400d0000340e84a0003540c03500004500104c6407072159142c250010740c0d10522852540ea152500c900100340360b508a40c03c21100404120414002e90641c0d680d1580100011a818026a00304480340e180900003d04010440601e21001c8005d4078020410303070441540d50000503502111074504070382d0b44c221511446000c039810750b80314444001c0201d01310748104103981a607103080c0c4584051040d0442112000d800f0041c0501190b4a482080c0004200711030007540c8012410f42001c1c1d005042003955038091050600d404010803d07404040305403a480090300e18000c0b40000c10f1014101c804264000c141da02c00270481c00810003d4000c0032107180c01c4660350031565000c416607030b41d0380c00307510a01401c0c01080b4103226034178102da00c2400078103046210b85001216148a09010015139183c03101d042c003107035110420020340e9680071894000500302280280115030543c0c03211a00c545881c00b0140103260001004001c1c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 754974865 1250 754973615 754973627
    0x50a0309060f0b040c0e03060f0405030c100507121506140d02030109090506161403100e160807050a0c06020714060a09061506050d0c11010c0201051608040b0a020703 73
    0x8640000c1c090140414881400009200004a0318442d41c549000540782a129003402014010007030000d00e0280c842c20640040d0705001041222640f0003001118104401405000a4203014020100c1c6505042801800281051040803035141c90080940c810300200b12040c0c04941d19814555400c44081c00c800d1340c14407410040714040d900010001526010325400300341c40900400c1619120b480d827a40202280d101004d8810000300c4040c2e030300204803401c04c0156080003141c034540100c607540b00d084003c1c2100407100c0c0d100510318040c0c84030019400002e205e0f03211006280c80f521f031030980030380506495000c81000d021107074003048041c10040e101805540c00c0300034104070f231410726055456002404807401e0456040b82081c0b2303840d01814030424941e0690300c0f55144c00342030040c0403441000416000011004100d0303005904c900480702071242c03401224907503002140360318040342c0d1020a1350030404800100310f903680c200408200f6030086190030802020000d6a24201800c0031205 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 754976115 1250 754974865 754974881
    0x1b08090c190b040e060906030a02090415090f080d0c050322050109050111031603020307080606160209090703060b0a0f12170f0c10052412120408060a021306050a03 72
    0xb00900008011440020905581384251002c4690344116034a480915880b1012844025046800c40c400305001516000c940d0360300d9251403400103280100c684540c14541100c460580300d12030000354000c8000c245005d0229490700c2800c00c2071075803c02001d524481e200450403503400909424010f070400c031b000c0d0059110280c0101c028007043e80b00c00c4818059902c151002d0000995801c00c01d401c46000340213803480303040c0e29100d4503a035540300030511090b9400340c2c52210805000c6000c03a401a030341e005d000380c003541010f03000700311190862500602301c1c2c140c0c02d0b50b184280300c41301c800c00501800c0902d800684140b812501082d45440c60148030742d060406940262103000708907020700c0c0d000040a024a250302d44200c4141201041c811411540d0a859003210390b24820b045590004044c480c400c104030000d0072004000c8a561051030038200c020508054a0400160401a4100c2001160703044410160304525150251241c142c120700c01c0d03c100c03c180300002c5041c44d0346074066845406 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 754977365 1250 754976115 754976129
    0xa0306020f0c2103040f15060303020c0f0108060604090e12040b130506130308030705070602120907080706020619090f0c0911071109060402070c03061b08090c19 71
    0x51a141d5004181c151a002807841150503c51880e0249016049100c00d072050803030740509520315121030711211500c45411000381e940d801c6025141c6c40201441c441e080c010340c06075000c3d0000c001480104803044004052140c10484500240205540c440048070101c802c2a0300014001030310100c00745c100105a107000301500c03000f04000903100d0844006180c58a050044643c1440c1c0350420061035002d260303003400000d005071b139050000a506000640c1c11044038200076003085042d0b80ca5105980c40440d1110120300040244401d00c1800c00c2070b200030b0140e01010300134160030844020351303540e0020454501c0c1448040c0003c0407030700326030003040c0450300001084d03800440d0741850900900c4a118068a80740340030804189050300500390341300d01b41e004042070a2000104200450980c000e8129580b01d5801c0002c040003492070040d1500440c402c0d040032803a00d82041240f400080c07640d002109110402c8100920031001081048180b10100c500d4000b0702141460000c80032808e1b04514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 754978615 1250 754977365 754977367
    0x90d08220b04080a080c04080303160908160509010b03070f080a1803020d090603020307170c0405041b0807030c170702100c02152203080a0b0418020f030705010813020a030602 77
    0x2c0140b060300780c02401801c81e00d45880f902070301d44040c51043d5205600c5505400d40090020912400d4041540031208070907140251440340c5554080342454613211528031035080041c420042c5040075403000d8010246402c026007185800304000d0542a90042000100048080010004251130340f000e2065032480780028402a01454003940d25a46c012030b0001043c06a007000030000d109000300e0388212990340d207460388a949603600c1d034403203040030f041080b00b000140800704543e1207620501591030748150340300c030b040460850051700908000d000d550425040c80704081c010794103c0d2000a00041000c0400965034810000b2401d10070070f00c3d0401801d600780100303000c4159001030310b0304018a02003161070240d21400c3c45502900d80010a03012891044140d200100340035000403503028401070300104031061501d00040803581a44601d50646803c1c1c05c1c16025400c1051104030050010b800500b6480d0a00002a143c040c00a010754000703910940c83c04115140c0c9001000215403084c025 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 754979865 1250 754978615 754978621
    0xf05030406080702160819062901090b04050d0209070c0b0a0204091d0616021c120b09090604080901140c071d040c051306080d0c0b090d08220b 63
    0x10030003201920104010700c10100c2c40c2c006200549150030441e0b00c1040100314110900c800021904410341080c8c2d6801e54929000c500e8600070b00c02d020000407200074182034000c41800252030348100341c111201c500740600c01404262901d5141c42420340d0111030b0031a1903950040103d4554000b030310001d028800c0c081c2030098030140e6401500a440d8101c07801c1c00a140c034913406080c03108000705881c541d86e101902141103540c0701540e80d040c0911034030541d00a0b00020300441500c5030f00866075400920419001061111a4450b1401c1107404942c00c08160078555001d41d525940544050303c03240d4001460145c0e6070040100022111040c80042d849030206080d054a42903a48034083e2207040c4070802c502000d061001c000c4c410b82d88810440d5000d410b180a2200039140c0303582c2c00449982d10100451090020400740f14013610350340e9424024101391510500c00c41c0041d01004080d407000c0b4100000b02d8114200c03551003110018a00300280107180c0d000000d00e04250060041d00a51040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 754981115 1250 754979865 754979867
    0x30f02090303070f2904230a08032a18130e060105091506121005060408010e0c04024f030b0f01030f030f140307020f010b18060d0f05030406 62
    0x740b03424140504c1503409002d040501d241200b92080c0501c10394075802c85d0000e8002440281802c680c080711008a5040c180301c61000c910744055000f090360304010100400031807050440020000805040030303104070407020340916005002e07070301c0310a0282c48070b0700032142c40303886404d4941c0d0f501603102c00600c810291030602c251101800e01800b0b00902400e800120240e2000c4404028948090f20035480c040341c448110b52241d070040c00e120b0154148090029007596524080e00140c14030000000b025a04110307854604000850001c0c01680107000c200100c08a41c800c02540304201c49058a040d0882440111003a002ea84911411041c814418182c020b08100d54801c0c2c9203d0b00c9885215210300c031000310a0542440010b0044a1032152031001030b20407a4420700451107410305980c40083c0056014068004590410040c0c0c400d000c0328004110074060740250031020f031800202c131156a01d1b0361200c10360040c4058000d0100c49001ca0401060100e204281c1e038022040d661144c0e21160 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 754982365 1250 754981115 754981133
    0x52206091502040f030b0604091e0305302514090301090c0f09020f0406110307020a0816120b07110a320c0a05130204050a08030702010818060601030f0209030307 71
    0xc21b82d40c4503000e000041a030f003060703c50b0050894000554100c07204c0d40b10186600180c41c50000c40411100340131284440703c00348000c0f54601e0b0102c403809031100e00081100c61410009010b1042d1291101000c06120100000340d5116002d61900d038034000c100103c20061440340f010640d40540c030b8103c944092000c91107011068440341003641d00710a60316110071082e4016800e0340b01c00700d0000c000420480d40038000000c91102013101b524205007043c1c000a00c40071882d0f00051041d0015030303513121642404440c000c041c001144109042501a441720354036400002c00d030b6014048105030444018404101c0c003030070164400c090010103140300700c4600c119410020309038022542e460100a10840100c0c100c0074285c1e0160100c1d00151806082003207030704580c00c0909c6115400c0001141d20f0300e400050501500500c002160344584901c001811408001c101d2031480354402e00e41c050881000c0344a0740c105c1c0c82441c000c01c091000301d49440017441942406a410300c0001038580400003200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 754983615 1250 754982365 754982369
    0x305210118060e39030405010c120e0325050d02030d06050f060d050705040513020c12090315040c0f120c0e0c070611090402040e0a052206091502040f 66
    0xe8401d2009503a100741c0200307006400d550202c07a064140004007184200044c201e025040880e040c0c110710520b00070002c85562081e1025101c1d81d455268101d141307508400f8084454148440400c5000c0501140944a00400c001e0000000910000410412100410960b0641c100081d500f001442c024003940e0303030703200061b2004c283e030401c10002420320f09400203520895018100d40c0c42c081c0c26005050042c0030003032110040c08424080460641c491060319104030f95080c3c40181c0e0f5050010b0911700d0084510565000745c0010130141d4895100400e0704a40c5120300306140c0e10355291441c288060040a8010007006480c501e00020807072110034803110900d01503a0070307454140c0ca8840d0020743c15411078140d00340887c00c02003a00010325940c0301072406c0b0059810035040912400015013170760f10603070001c1d103400100d20910500342454444d40d40c010000402185181020041d20b0300c240202e0b05010341215030302d0199809000c00640d408031002d00c21001155039603280c4541d11482c10141c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 754984865 1250 754983615 754983659
    0xc040806130c0803122701020d0905010609051b0304150903030b09070306060503070507020303071704031a040f020103051323122a030f04030b0f071b03052101 70
    0x4080001d032080c030110807201c40558160702040956510340c07200c10007029031003401d03e206ca0710401e645450345081c030140c83d11003c04200840c00100c82d081c468203541081c0c1060b042c492501c0d0038040d480c01018079a40c007403801c1a81c0700d6101d0f03603076061020710340710690b503169802030a10560008041d4103038024203250404440003c02611307101b000300d007120042d00480010501c100003142c482c3e4001c1c4094201c40d480101120310b0298039a0b1018803903000c50f10409860b10010500703100b041a96040854590045c020284c40c5140540b01c2c1c03280d11405c408060305042e541e60100d551480d00c10114142150071841c011000b4005000c10380440e01c054081070320f28001e400203059100110300c226048040e800f6034103c030100c5a8000943d150304916011543c03440100041050301100001800c0114091400900240341c00040c520803120000c02441c1002204000c070210041030b001030b04a0b0070b07010320740161130b498494130b40705041030740046080342541000c000050386000807201b5010720410f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 754986115 1250 754984865 754984883
    0x100c1202040b09120d080402041e0204090c0201112704180308040512040f0b090402071502090a0b0a0507060506041d0f150601020d11030904110a030506270c04080613 73
    0x10300313455251140007000d01480040c000d40045005460180c00c95510401800c44000c500d40d44010190201e0340107a020034001a114520f142c0b0b5942c0a1007445920810030300d00c00e1030040c2c070700728070841c20000912a482c404d07120810040d541d02d40c0c0d8000c0441e29240d203504420000142000b82145a048900f21682d1041407001c04020b00302a06a4088a43e00e110b001d481909000b122500342e044480c000b6003041e400d014490100e00a902d4101d02c04d110350344016070361804602800b2001c5402d4008940d41c0b141080b0064000750310100700c0300d929422006c0000c1c10340301e0000050141c02455400360b051000180058000040802c4c0072001c0d4404201b00c0b540740c00c0f03800d0100c0c44040300300c40d103c0c056001140100c50181c002e182c51904075a401080d81e240010400020b41100c104604e5410700070408106100f84a4040c420650030560845444009500e55142d0400080030301001040136807446002c25a0b5120381c10603038000d40300c541e0039610700b880c0200c0c04881d039400340103007502c400e18 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 754987365 1250 754986115 754986139
    0xa0507050c0a080a081c051014010306030b060927010c1b0f02060c01060905070c020102010f050108100915020706020705190206091002192f03100c1202040b09 70
    0x25042e0040d0b003c858892020300020001500d41000c103411801d00c04444030711051180b4031343d20741d51044510400810540072005814422000020245003003140d050600d054014808200c1207030b2003503807187c002c9038100000d036030b03140000c00f11011b81c00b03000d20309520065010a80d0207040d00300881503402c6503070700244480c1c4038009100b01d5500c014081c040807902c41e410700150806800030410003805c80000308005950703418803821240219070650000702c1c1c2a040a08540c6c2c20300401d00295103541060016504081c1c4450700c949070341c46c0f04519655100074410810504141444d50408402c0d01192140e4480c10960301a40c001c803011562400b03000c212584001103002140070a40d0003800e21400c15510740d00307000c9413140401082041d032240a50320b001c3c406a40c451194a18441c034550104035403403900440c0300711803c28644a80010011070280191030002d01c040c01800c800030045101a929401070340c6448424080c0312200340002004680c4c0d224035001800c50101c241c603076101940d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 754988615 1250 754987365 754987369
    0x906180b06093c0108070c030e09060301110f0717041a130b0a020d1e080f0411100903120e01051b030d020a08100605040807090c020a080a0507050c 65
    0x150035116040d600c06001c2c40300501c6030815494082c50b50092205011891804401805409450165601d1400d0020050040710b5902001c02d030703005180c43c2005203c45049941c0580038801284081d4000c420000019032940d0f800d411010030201202985a40d601119515a820f6404000192110000281d90084007010b800440f4100c03801c1e000500b443d40e40c8a4503808065000d0000c1c02044d9681520216004600000034000c1112036001801d01d0171142401030102043c0c00d078200b01568072010101c454540001442d82c2c1b060360600c0c2054140d0f218a0168100103419811a801001441701c1c030500c250064032041c141e03805850000c031542d0007000200c40280304034904a001800c00c0c01000021610b203400741c0105031080042d02d0402d02d4096122003281c11820180000900403c18003d407161011010800380501e440c0843c40c09052990b00d03035580210f0310826901035566020700c0b0f0000e10031f00204103410b82c40107000d07a5501080c000144507400140c41551180201004803a00c2c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 754989865 1250 754988615 754988621
    0x1d04031b26190311120a05060f09010b1b03041703030405070f14040b0f060a051201050406080c010f020a021c03030b0406050310090609140f1b030601090902010c0c090618 75
    0x11075840ca945a01d00c001200080300070f0540c56114004c1c0440610990308010781c20b0070407910501c2d114900040740c2c9081e008000c00b000c10305400c01e02900d48000180b0102d000c0d14101d40441ca005810303104030040340c04800b45140f04651100017001c43d02c1540b8064044084005c2d8001d500880c110707000540c851414500c00d40b403610504c4140c0b41d99024501150505802000b4486401405100b018a08001003483c0350312119107580005c6001410300c4000c2c3c85644150b02501e0140c5017048214200b4403800d41d6081c0e00c81c0e00782c1c14422005080300810348200030766024168041d18080f03032100c4402c00001c58408900040b400701e4200b003140070082c02c25100700401c51714010300030005c480481e0006401822035280558165031102d03001d0340400d4402410f0380d0030030820f00041c84001c00c44005641880340003041c0d070b803d0b00d60201c503407541c0760340c00550181074a0305076038001170071100ba200603510703a41401c5004005521a0343c000a0310031907903000b0000c64041010f10600703505010860f42c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 754991115 1250 754989865 754989877
    0x40e0c0c06010302130e070b0a090603060503061f081009020906190e0903130308040801050c030c070809011218050d050c0312060402070c0f050103060e011d04031b26 73
    0x1050740401d00400141c50000914402030f0050100050184d46000c04641400c010f908001084100042d601151641c0200342100a0010346000c104130784c00c1c030340000c2d01c5440103016401c00e117002414014140c1600800c0d6002800c0071000c031003208203401414006890780003170580c480e2050100007009070038408410080144601407007800c20b0f04040d2000000320001d4003085083c07100740704142800d003002c1d03c80ca01640c002d11106403101d180800290130358200601081b203c106c140300340058683c00409950050b540000c0c0c103516800e0f54401281d51400740010250742d14142202e9080801d105a1910305d880d006070300355100d80541c1c8400786c40d10300ca003e8862800e64000c00c130302da4000318007101031a0041c1c00140b000d403030b151494898070a50202a04083ca01c022032110405c00c1d5a014440c0f84010128007072400c40301c0d1f160052071a04c213254410005a1a401240020201403003001d01c1d10003000040e00030ba800e4101e07400d000754980e124600801c4854001d0164407400c11905c41520b070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 754992365 1250 754991115 754991137
    0x161d071701092325050d240915170132060f0d0201030f090506010f09240b0a090504180203010608011122090f0b0405060d1e0224040e0c 60
    0x103a2142c40403421158401d00c05140b1304100c01441826000003250041c148408000b8070f9100c114071441c10405410807881d4404142d0901d0a200c440051501c503c51030100d030a08441c44500c44400d00ca001d000d090280c6041481107585821342c42d4124030020503408608900101000e1a038610080c00319010280c0f95480d40884454101c60040d0b00c07a801030001c401d0700110104030301416640c4c7d00e141003401c0c0c200001c0740c0480581400226403910801200f12001a5020140c82034040300d1802d08055010f00e414100002500107a4103008504a0006000c00740080265641078903241d000705c0b40000003203210b9400e0500c0020b910105010b1145045000210381d881c100303192401700301811110100401c0c202c2e001030009014611481000c070320584941d0041039003d80001040708480c1c005100c0f501c6041c134196000c01080480ca80303454030041c00c0d081030090001c28000101c48440350314401c0d40c0e03003100180c1a600c410400000d0012035200b900b20144544680400080c94081c081d4105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 754993615 1250 754992365 754992391
    0x60303090b16020901141903020907050c011d01020d0b031501140310050906100b03160f0e060c0f062206090807080c010905161d0717010923 62
    0x88095010680101814140c10101c00614502e550200b15801c509034804032808420602c03140303860801d96080d03030240368100c0096218034250380c0040c1506202600c440300300000414660080303003003540809951001c800c21190072184100856020354800520100f449041c50f56210301c41c1000a00e05818000001100c03503260f08089a6102c0c80c60a01d0400b0343c0740c82881101681c00406214030b07409503038408090078603403410014034104c009190307001d5000110200104842e0700460030410450a5061500042d203a0f10008102e9aa44094507540d90254001840d00301400d00002c401c04024200030585515540c2c0a005241c02d0007000000c545810550054400140c1079500a0321030f01d20074104681001d02a49900c1d01942001580000a80d5205450014000208a0f41c0c9445524661490105051024070369103040b1803081a010307480454089031030640180101c0189239940c0c5d4401c07040d9a034407007403003016001303060030025008403003401c4441d5508840c0741d007445039042440032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 754994865 1250 754993615 754993619
    0x11271503030f030c0304020f010c0510050601090f08030423130b06120a410c07020402030408192d11060a023001151218140106030309 59
    0xa2400402180505a4180810858508030480810255024158070a025500c0e03103400e105001596407140c0341c2ca41071007901c0c0c130040300107072001420601f006500d800101c1c990300d0703810050307413469200c3d0400080d820036950007041540340000035000b1200e0001c4040c04010f05901400111280703404510b0b0040d0b0301d90603e0381e6910003900100c4061201415061074910003c00701c840204e82030302d0340000c8603140c1c0345400b0303c11821480000c2c4071280307a1210758002800b140007c803217500ca0104500e003544980019500c403145900761801d854000d08155600d190921300044a80e200070049401030030a0010140b129100720304505003d508200b009984800000c00101c1c01b150090510003044a081480e405010040c0314450140417104009602c56005034070070001841c0b070b4220702100d0725100000c402d1340260b07040c2c0a41101c9503800c102201c1c5610354001c0b02c2d04000e40e0b07030343d512081c20b2907101e40c140c2004000a0300054010000b518044140001d294240c0d5658400500092203404023 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 754996115 1250 754994865 754994881
    0x90c0f03070203040e013b19020f07060c08150114030a0b030a030e01030c180501030518030c0601030317160305100305010908120f04080403081b0a1127 67
    0x15074101100b4012a400c1564480340c0b40000c81c0240c025441241241d03c00200c0c1c1c0e882c29841b41e03018106c0d41c100f9160380d211042030390500c1c0341c02080035120721028903c5003512035007981100c54101d000030b40c041d82c40140d0b00b440e4010b0030f0344541d14000100d00000107804800c0c800381842005105a6170011044e020740064006031b00040c2c03016420b1941c131402c2c2030301c42c0e400300554100c003440782e1281d01c523041c000000582214210340030103050158201c5c0000071101da50f4440750648909080000c0c1544418005102c185d14040320401d440c0302c00500c0c03246104000513094101c030b10035525286494542c41a1010310541694030032084107210841028480c02600207562061010400100e400c2c0d0f40e441d61801d40d614040113545800c0f002988002200d0001800c03036003d14001100340755828282e4440b50540300d1840044c001a00100e8002000b201c2580c1c000c85402092088030300c140c4484c205000d1600c18000300c1031207007140c4507020030900c10f603580d120089004012104029610815 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 754997365 1250 754996115 754996117
    0x150105160809040e250506070203150406140c070209072109140a06140c090d170702040615020105060a060e240c0f010b01090308090622080109020f090c0f 68
    0x721182c0c0c01610b43c4c20156a50b44104030101044581d406101039000d1400c00e02079510596030815801803004000400141e200017420440c1094450190350701e80d510340c00c0400060000440058000300040c0500c0004840e030f41c0a411601c8c000c480418098898400940350401004800d10380c0305140c4601e810501200c0d440b900d00503000c1e90f650b04030030203000396050078240d5412085456a0703035145401105800840300b80d901540c0061042d00d400c170303240c0011701550610180281514007101180308500856015a0b51303541d4058421300410381c5031304141c0603600c40c1510800041d071902c0000780807860412010b100b192055110f0b01050301c020806e000496140d02045d101c05208000502e62511800c0020481e5002c8200078120320030681030207900b56404021524104880c80e0b42c03e0012440180842d072030340301c04032500d55551920344050310400c540d8060400782c403003804200084010064112a9215108841c580b01c504091020020112810784034044200d405011103594071000030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 754998615 1250 754997365 754997377
    0x806060a0e13020307053007060c081e0706020406030b150901030f0e03120106020d03091104050a0b03010e01050a11071a040804030b01060210140f2403030d051501051608 75
    0x1606076504d45d40c40e540444e80006c8105042d003801040b02012080c1c0c040902041005c800c000c101030122a072914000a00a18081c00e000e4030150000130191100c011444643d8001c4005035001038456010b81083c000a411521404010a007410000d1140d482d140401c0071480e6060790005003818100d0380114000c1c1250384203c1c1001e40d4502069003e5501000a48103604130000c0344c004039814100000c1c208241e44207030f001450b04005105001404884482a503241300f502c0002c0c0c00d981d00078449024111508002d40c01d546440c3d050202d80c8019000f143c41002e00c0803040c0031807160305a6500681c4100380c1d02034030309902190200324802c500f8030780941140c000c070162400c054407603d41ca002e00d00c080c0d010102590149052007203401d140c1c0961a050030520110700300343d141c01c0d50007505029000b8040c0328150b91407080007103942c1000700c2c101c4076580d0150482e601c030644110410002c1006841c14170b40c88071103003100c124030344c401e0741200d0740d0320002481c0780000501c9580c1c1081640081e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 754999865 1250 754998615 754998619
    0xa03050a02210c01060602060906010909080f03040308010932040c0e0705120a0b0d0b0714041202030f070305100207020f04020a051206030c101d04020406090806060a0e1302 76
    0x41e084010410100c900c0000d100c0b0201c20b5643d80d0654a600d107003100e102c1d501200640d00324000b00708e0110804600e650441d0805080419418481c3c0381441c2c0c5485802d22a102c0c44001100f0320003415030104000d03042e900f40301e8041101481784c000c0094596002184a14200e00c4800074076000c40030008083d0f0414414010183c0c030540310340c00050300c040221b0354000003540104084150f404080e03c06a040036121030304201d10804200414500080910003a20141207400800c0c8014800d050241000d110075100b203403603039164083e0400d40d042100d001d074407074800c0b201c0c4d542613550003040402c00c585d03200005140203003005042e80c0186d04a9002aa400243c144440700303540c03078600041008000940d6410303603038410820740a10f5048080c1040c2c3c000c3c1d008085d00c0300d040c0c4680013403280c10105801e0003245202d8144a42502100e00c0703100a400c1400070400148031500411036205950f0304100b6100241c3c0c1d148103018216205104640405d00e082011038440d810407a2658401800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 755001115 1250 754999865 754999873
    0x120406020a080f132303040308030a0f15030209041103101d010203010b09011101090803010605030423030904151a030610110c010c050a050601350309101110091509050a03050a02 78
    0x3208805c03a0640e0010391090710150800820400c0c0700382030784102c0460342e11a500800946d03020450909414080d400001c4c00351204401080c14403620302e0780d0714400341005085805003024500100003a0282c400d00f80303e00d0340001921140c0d0001802075074141c03403074901c696040c642c40704011101d403c100304d06070b0260b560303503051940410a0320340258080e10742a281c0320303541d00b810310380f04100e88002150143c4100400c00441060040402204e891040c2100e01103480301001d6525070358429654002c0c06100c00c074070b07a1199000e43c0b1901031440354004948005202150130400d0310071542e900c02103401501321210b90000f56004000181c2640e000740210394031244156185813604000f0380005501100016540c0c185081c00b2008404501501140116606030558001d03a24000e10505078843c450000240f80c0c11441030003806445200a81140c444200f045078100040840e49000da03009040d9108044c05100c80e4090a40f00340d030b105000780310b82c0c507298808030340c0c9070482c1100c9011809 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 755002365 1250 755001115 755001173
    0x8150424151a0a020601060e01120504050f06071d13061e090f020906030a02160506070810050103060501050a0807020c060403080405030d032906120406020a080f13 72
    0xd4184100c00c454107000700000300311401d00d010070075151042000c541d5054001c2200b42c0700e9030381c00f048090440e009800c0c05110002d031440140c43c0400c1d03104090f07a40c589840204014814002a59802d00c4040810b80381e4903101d6000886078808042d0078500d10092542c1e0b80e102a05054400c408041c1c2e03084000100103488040f00d0214450542e014250040f48601c2032001e849244603032205541110001c500e009000c0001c605d4070700005042c8200d00b9030108000110307080e4484500c40460b0b00000742c1c0c0f51803074101400303020494182c41c4285e0303001c0c0300304020400b075000344600001e0b40c0050f10340e01d090140e0030000300c0b000000209034038110f00400070300000350307291400908080c521860000761185d0030b000515141034540e014180030941089104111030500029114440003011071a1400440080214a280c4115010000d100c0300080c1017209005041c0d0152669685550b104000c6031905440c846000318181c54030b0690070000d480810000746840310522145041c540107400300a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 755003615 1250 755002365 755002433
    0x2904140a150b0f0306011d04150509030d050105090f040b040c081b0301051e130c0f03110f030601051e03010b1003022206140f0715060609081504 64
    0x203004800218810758980d41c000c0c4183ca03000003549041501900289002d603d40140d00b50340c12920f6000820107652003010a0910001132074a5034002034142c014070003410f014000e00c0d982c0d8030240402c115540f07004000310f01460400141c82c0201d6807240c50340c1d07035910303a0346810001d0b01c005001290b101c040681c0005402000380202a41860880900d0321181850390601d425200c2c0180b01900e08020f079030380020100400008070383c2251081e50041b906d010705203004503200d200b03508400d21102900340004100024a0071081c10b0b142e09441158500d40384c0001d140c0e03600c50030300602d50b0000c5400c0d12082c032411400c4c0c261001c0c0e44010004128001d41a002c0340b00c54902d11b80490000f81c001404d00080400075600c0da00c01c0d600c94041914591810342c0040c009411520003084000f0000781402034100d0440660300c5460300310b88101c0b400e600140420006208601c42c4d180400c01005000031050408260301882103c0340112991541c1e40c0c0d80e800502c80b04025900b0082d91822075211201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 755004865 1250 755003615 755003633
    0x5030604022707020706141e0c15130210020105090c04020d020d09050109020301060806010b04050927150601090b092b050a1a06060703030c0e1207032904140a 70
    0x850f025005001c406040101c014512030034070007a07400c1040100801d010404504025500340c0d406d038a402522341c425a542c003400c0c80320311881d0100c2c520350f03142404010080c5d00c0312950424821980003091580d06038080e070986400711016031142e00706003180c610300e0a203500100000c0d124000c0051901d183c058445003111030340101a98941e64540c140000c50a0910424025064403070041a8661400d81e074460b151042e402014080c5013402c002c190354002e003240005441e9051401c08801d0803a8505450b952030241c00b11000081e40300002c58025406440000d065620140706a4078091400090103c4083d02c2d40c0b988000000c690070791401d260101e0781440c4124031581c081d0440300c11600380500d00780c965018103100c419911091100f6a682e48086400595150a01050711506c5070780613140c5c2018075030301e40d40140d25040f6140240b10041140700c180d92142100f12403907800c0008054007031503040f80c84041c032095100400d02242050000d20500e2040302c0c100c88026000345c6e101c03494 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 755006115 1250 755004865 755004871
    0xe13060602060f0a0207020d080702030a0c031202010518070b0c0a230d0314040201030b15030711331906090c0206150f01030c17040812010f050306040227 68
    0x507006501030043c4401124096070300032480440640c104181500043c0411061610091031400009411401c54406101410806030851024507066542e41072040050641541400055207480000b580c500c610000c0c3c45a4001928010a04e850520178000304941c4030032610391091007100003c000013029140f0145841c0003007410240720030242c000013850300350b01c028078809040c01c3c8503d200602e00c1c0442e40b150310907024600810562498404a0070b0040310003581145180c1c000b00300046507802c2140c0c2600d0a08035001c803598440c500003440300c0e03421780c14440f48078466000181c0294910700110160030000104460500b01001e03104c44088840d03990240d00c01c180c46816090045806000041e4012444d41c07484107601e40e1140001d0985400b484928149a0340341c80a03080c80e07206950006a012018807c000341d0b05041c00d00407041c0c3c001ca00036000d4405400000b0071941c064007404802c8440113030051071151515420400c010311049c00481c40c01c0b00d151000c2860080001c14140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 755007365 1250 755006115 755006117
    0x1410020f10020a090b0f030f04020612040b15090c07060914030703170705030615180d0c14121002031302060a18050406030818040e0304090605010e09160e130606 71
    0x207a600010b043c05403400712180d0160101400500c4640c02082e45032045917840503090914507115174481c8005055801028041980c00000c9010042005000e445c01802155000b0a40104105100070000e401004803004950b00700d05000c2080021030a400c1013080034495040d0804c000780c2183d0f802c0c50f642162105a000030100b000c2450510030442c403140d0031851038074121f85140b41c0140411540100c0004414000d28009203001d10403180003c200b041020041031038003110044d0600004207406030050008810340701040e808646000004071000c10010710203411241240241b10000750002002c210024075000d070180016903c000003403a241ca0b403901c07100525140d100c2a020107040340d03000750740154a00300090000c50384050a5070104995a41d03104001207001c03000c2800b4007003641810301d40d84400309010a06072201d800610598000382d0f07034100da0025900410a05a405407807401100d514907c440d0800c078840c00b1110b5002c4409032285841400507003580003254001c0c1c2c0060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 755008615 1250 755007365 755007367
    0x20307021008011d090613020f0d0b09060705030f04080306010c0f080c160b0405045717070c08041502060c07020102060c0d0609090b010303181410020f1002 69
    0x8411440e001c0c042041600800340e13101c1c85840c15800352035403840301030301e00907030b20000811010031903a82009001c90018040e0030603414505030b20f0301c50305200080ea040c0c1c4c070030f01425000900081c484c0c800d4130302c01c60108065840300e1300c580d03ca41002d070340050400350400c000e1845c90004102c0b000320008080d4130072528295101e44007104141000b00c80c803812519260103180030440e00c05540300741c3d410707190101e0700003800e8940078406582c00d100c240303446550742441c101103840903800390018108411040e208002c8101071034010380034810881880001085510703103442c0503107611400c00c070383c04082030601004504003519003020700d0300702e54030140a030903682405061b06541440207d0f0800200302950f82002210b1340081c0d10b442005003a00c1071000c000c0f81d03907169203400d904440d0041115200c1002100c6160a00d41d50309002400305401041d0b50a81c400102c0d9200400f060869003207030081d013000d0030070408100307100d02c00c000f080703086201c1c0c0f4a003040008020b0060004802900d1001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 755009865 1250 755008615 755008619
    0x1308010204171903120c030b030706020a02030708010536160602070e040c0b03130c061d06071101030b150c06040209090718020a0908030a0801050f030a020d060504020102030702100801 81
    0xb1031070f01c120201d000e161070700400074034000680c2042400352201e0300900045910030395034070118001d142c5c0200709541032040460019000c2c2d0086131040030720307009a0aa40b00c030ba84506203076090b102d0a80701c2c1c40000c1a4000812685605540c0407418000d410480c582d8401600115074a0802004081f484c003441800c070400034150100040c2c0010079552030603400525103038460301034400b030501c510a5400d40010004501d000054941c0415960058444404607100c0c8002070000705d03161008c04441203141428265490403105035591541d10411000c0043d03102801103015120340307504070703806c14445403445000340c80a030003502c500071204000b45000d15144c010000820406171000c11182c0044000f0b009007006016080303c50100200050f030740b4102003c080f6804102ca500c524031600010516175807603940004040d04036102101e0324260b0312508010141c07200541d181c002d40c05481a1000000980e0a410544e0f000d801401900c0c02d0070550740204072082700103050240081c00d00401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 755011115 1250 755009865 755009909
    0x204030501091b050a03110f0a1d0f0f150d050106180902090106030506030a030e0a05060304111e01120f0b0a060906020d023c01020a05040603060803130b1308010204 73
    0x70800040808580180902c4d1564541d00340000307002c8540c0780150140990213010303441e40040c60004000124400050306c54030010b002e00d40c402030b14541d503034502f050042280440f01c90401070151840c440080c4e03041141c0e104104901183c0c03902200c265480e541e001610340e0300c508401150f0780345080085a6500300303104000740c90700141c200b0018145270005001380c5840c0000c0d0340000c1503260070300340c1d0f4005500000a8a0070794603400f141e0300017400400c100400111181b480074030b1400b0340301070203518072880a0f80001c0380104040360000d03c0c2581e844d000420f045d08600700312803892000260840b4002e0100e4070a0146400c89004243d1003d0700b00480c99040000c0f048a192a2024100842820602e5040c40c0310100075443c00350300090342c0045160f90a000480074014140085580d07600c4100003070200d401921400b0003003458010b000445480100c21200c01d810725550b11400c1034140180d03101c064000701c208941115102c50040740e6482c0c02d100410181caa140d2450501c1060090703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 755012365 1250 755011115 755011163
    0x201e0c0a150509090901060e0a02190c120e0406050d0b0f1e06010507031b03021b09010e0a050415050405071703090a0e13051221130f020103020403050109 68
    0x4441005510155200d4141c2079000040d81c400304030880304540107450342c003001030142c83c180d041000c2148074101800742c0b42c462a030080407a50001d501209800d40078410a840c03400b407802000c0d0910031014401405030740310303492030412030900400004640344c50b04003258408080050440e0081584020700c00c00c4841d11014039800119030300c050020711029003101290344005452681407240c081800020540611f141c09046252000c01e05500e4442d81002980d071000703203d01011010b540726580c840d40c00c04465030760503210f8058a000b01c68690780c003020000e18000f413094030341042c002c0d68101c048640c0d02850b80038a001c1d20050803641c3c20803803003601e01500c440704d0004030781c403c00c1f80c4015516080071100468600304e003c40416070b41c1c43d00c000002005010000d150303011b443c1c0030180d0140c032a03010b0000c4c1c40039124000e901c001152003c0e00700040c242e48402031801e4041c02c3c040040c0c081146182154810f150150405640399202400d4560054003150707080c41c1e1080c50101414410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 755013615 1250 755012365 755012369
    0x30612100e06010b040f05010302090a120b01060807050c191b0303090f0506180405041704090f11030702120f070b01060c020315100b0903011b0206040311010606201e0c0a 75
    0x1262501d001e04c1d2006d04d0b000925140300b01c41c18075402080030030444c0e59001792000104040c2c8800c80d0900f40c01d00d480e0302c4160003406200046903000f80458034051160b400e440710141d151000380014074040850010210308004112603481c4107001c0001d61a501803c1d103001103100340c41d0414030030304044502d0a060030030707001640148802d209841c0390f103a0010841614a03816140000c6507200d030b0800483c040002851001141400074000914050581c8466400c07402a40c6c10403414284248841d524441903c5040069025008101810000ca00101600c01c01182490300c2c0c00c42c0c0390b0715951141d5099108401240b00f142ca1041541070a00c0b850720711a5400207040000c0c54003e0110200c100280208100da4002043e000c0e04c9407000d40c1301c1a0200c101c0e21070510a00e0030070030000e50b0750400f128101e00145503d20728040c04041400b40f0b8054030340c1629403000705108850ba003a042c080c01c6030445d60603c500f0003141400c100040d500c0d20280d05080180c03168005400c1071042001a075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 755014865 1250 755013615 755013629
    0xa0801060311031b09030a05120a0e060304230a060612030210050c16020103140a0b010924120b04060f06030c02030f180102030c19060612030e06030612100e0601 71
    0x10010440b540180f01d003280c0020301804c0c00c00343c4440f0b480340400d207080400703440206507110ba296500d00c00241d8070040c084601c9156580070030010781100784070090000381e400515005034070a049012550f143e0360407501c0e80c07086c0d00b00c0c0c3c01d40001d07488020684020f136000840800c1502284d00c140b590501030340d000e00c00191403c2c4610f00f4206880e15091295094a131482c201091000007168030907042010410500c03618503000f4108945044001c1c8210394000d80480e002c040006007200c120314000f41c200c8480c0c0001c03180c0069100e0255200d410b42000c846030196180007000756071380c4a200d0304026007071b004080001681450800703022591180240d00c25980184000c41306903000360121242d88a50140c440218889140140e1031400b90003084200c078091048440542507482d851b6044680c01843c0500c001a03440350364202c0000f13081c2000e070004207406490406800c0560055411240241c141c40f000340c0c100e00c0a90800102501400c102a140d80c04030084540800565001d0800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 755016115 1250 755014865 755014867
    0x13060b03042f040b0117010314160f060e060f0d05040b070509090402130e030f1e0a0815220f0f0b010c15060f1814010513150306020a0801060311 64
    0x481580c2040301c0341c0045a5100f19100d0405624a904c13070240705299981321480d110003035842e803900e401c5515035024401210303c41d100e8203001040c481c09900b011902c2e4080c241445070704000d0111210005035520b00d82040b81000301c5000c03c00b5900040c940d035440c40a0000c1c10341070924044801c250050030240400505000503122541d510a11a400582c11504440c600109400302c1e400340c41d0409246c1c2403404041540310454000000810314071910100a2000001c0c5048015207400742100050000751000c0002e14001c952181c0400709500081c10600c000041c0f14030102c41d00c01e101d440c0d990b100d881e000004414985801010b420451460b41804a80406000200040200f03000504032000d0300840030002505076212002070100c90003d140010349481e12803d074420040d101440c51450521516084d50b04d0441540c161070006000c060550030074600c032006400000140e03000d841c1009800400161f0501c020b1101d400c0c0c40d102c105440d89011005000c03a10982002c040c00d0344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 755017365 1250 755016115 755016173
    0xa020a090509030d02090f04020304030f0806100905012f01060608090a121d150903060f060a12020a0521060a051509040516092f07030c0213060b0304 66
    0x20080f0603203001c40044900161200070070310000b01d444190a06440c0c00a00c0007050006143e0f00406948840249407120802c6480d12024003180b2103010303226000046c039448013884150b1107655170f41280c8500301703507515410a40343c406507884a154810400142c0d50384104201c0250030a91081d030140702e2102902c2034140c15250301ca88083c081600c1d000b0008010448010048905040d5401da00c0180c188071428180c9520071009621080d000c5100748034400024084140c4002d21a2150001038540e12402d0702d0711140442500d84420101ea0061503144045a41e4940504d1145520104c04007051001094204036050035000f03407910030518109000c010385a4600d510108614000ba00c504a06558508005040c80d1401620b6000081710170760002e4511019049a07201d0800c1c90701c89a0301c038100540300c448480a15403c80180c403000d00441000c00c2c01078145040300f0b40090448150040035002000444001b03420152210101100303010901403120300712240d1030f00d002515a8215 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 755018615 1250 755017365 755017381
    0x1806010e0609101b0c0e06011d031c03020c0303100906080a0807030c0606090c080919020901030f0c0e25090b22091107110906091501031d0a020a0905 66
    0x83c400e80c5180d0511604130110380343d10318100d2002d5141500070340e02c1c420040e00c41e84100075515041e203085d4006816800651050445610800c200010082c0102000d001079602090445040035601c401d050b070900c0080d8060100380300031441174511410004010f814001513100b10340340750300491060b80c8080050303c0020240c20841e2000c40c2c044c180805042e443e0f14090000e40200d4210000440c101281c095219410086a5014640400a9030301c40200a40e60503508407682a020354009a001c00401c080f9284c2410805034900039004801019111181c0714070303001003507c41c3c00c1400e20a120300f1031403d25411007140f54150ba468544091403511003403d0705402620841c82d0344a162601056480e45000e2001c401044801070601000c08030012611507508603d8080d1114440c8074014100c600c0c1408400c3d00c02c2500518107191900c8620b00f03509100f000d6031005050550b0743e10303414420a0000046107220362610010085940303940305108c0e0b41d1040ba40480b0105080c0410b110b209 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 755019865 1250 755018615 755018629
    0xe0d0207081207020a05040608160b0a0903021c060603080703020d0212030406020901170a020403051605031903090305150106110604020a121e0501290a0918021806010e0609 76
    0x20884081400d600d802d601d00008059a021b0b0b406507a00a11b02000001c00c045c011555158500420306490310742c03695256001101e10a11052100050303085500381b00601d0301140540c1d003001101c000f00b40b13040c015981c480c03c031070b1707560000c1e121603101081d4101059410401044080c0c00352020b881000b2946030701c11032600001d0401050540c0129034043c03d64410300d0004101d00c13085404e5080c03400c001680c000294801d02081d125801000c20045034031071000e02000031510041c3c01488d440001510202243d422721100310204641c460300000414020000c6a14401c1c016541c4d000070351500c80c000e44492038a02848003950000020070025983d0b03109901c0882e07104080001c203034840c5180c5400c1811a10914117123034030410b040d00d01840415804030301d2000d1900003a8079400e2103040103000d01200307408080e81c4100070080a00a0b4455508440320041810031301c1140243c1c00d900151448520f44000d07007204000d45d040121543e840011400d07050019242c0e54a06104840882c0f00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 755021115 1250 755019865 755019883
    0xd230a02070e09010930050319091410020a120e070911090306010906150c0b04021e0405040b07142d041701050405010c030203160f051306030e0d020708 67
    0x800c40382c100050084500f034001030500c50b03001a0198003081442c00803040d044800159003140362240311401c41d00b90045007142c1c001d0b685c00c403070101031122005801c4041c100c0b100341100c150000090818a03807004018001c4058030961016803205264400140581410702c181c4030014101010070980071004950a82602c81101c03011804800445200d0050710984c04800d80500c07030750000184e01c2d0050b60041c426104810610041400d2421341200e46181000b00582995040c40c040380c01440c0c80d400314044c030114503100108031429080080c0c11a8000c071825105080d13043c0402074825880002c10500d41c0860003c24100740740c400300b0104102e1484401128407922400d01c48003000c1400607a170082c03104018494500e00c0c0000d03c10301800d4180c5085403150309013000c41d00c0150107070007900d101e94020041c002e00700b542c0700c0040350040c1100003640c0500408001040340b04c40c2c004681d9001d0403541d1000b240c60300043c5400b900d03000c1001c45c500f085400c048010701581c800403a00f01c2c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 755022365 1250 755021115 755021129
    0x5151c0b1e040b150c0d0503330907180602060106121503170403060605030705100509010309020901080d0e0f090403080702030d230711060c0f09030d230a0207 70
    0x208a00e07191010400a01070b0b00f01e004d610000480c0c008409070050001084c1074155a025a0344042e001041924240025103000310f04418a010711144582e6134120590711240000321b1206042e10301c4c0120b1031510040d145400015070a400ca80021091000324000030403e62008200c6036151081c01411422504180031036203882d05c3c007000424080e04000380144da08914800f00c02408106280b003e5806840f0071a07a80c3e0428000150524022500404441015000b0038040c0001c82c011901c951244001e13606141da6403c3c1c107030158449500b142e01070703d11040100954840c07428003070209541294004e10074000028456015121285010f80041d45401d01800903101c0c9641a03045014055002034031a203080326592000341c1c07891140e02e00900d0300003441410340b1550001c80c0c00961030b86400000d581b0080100c0c5005002c07100901603480070300e80540c10a070380c2c0000203040812400755500000d08641010105a44011000061080903d031f01460444600c0c0042e4542e0842d106100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 755023615 1250 755022365 755022409
    0xc010b120c19090507020a050f010c020307020402030a1d010c0e060f0415020f0d0e1c020108010b0901030e10020909011d07050306060d0c08070206011a2205151c0b 72
    0x70b0705034805015600074000840c003d1001d460110f400a41c0ca081c2c8010654042c4141c880c00c0300b4184040c800c03d100410107901545c41c206803a020311000c1c0d44094140a0701e542d41d01200343c10351180c8034101500030100400071511841081008000c42c2c000c0c0c40c11446050100700d20b050314008801100c0481d00106503c2180b0f401c00f240a0b41000310035200100302d8058241d5a5800c0b5600113021560075100700c910324083e000e14403080f000540101e40c000d010a0035100140400700700d11010b006040014540440e1031220030302018140040349410500d042d03008500a00325240c9004454050309404181d00074240d000407407400b5100001e01980244071001001c41d806403170b9041117400741100d5032014041500c0001c4003c2a58804840c03241c0140203000c000700f034031032404000f40d20240c4105d100c03508200800c000c42a0f007940c4915090361003800c0c0724002900b074071690340080d10b00c4002440191030b50310921820304c03240750b0403826101d6603140100742281940c640064450344190040f01c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 755024865 1250 755023615 755023639
    0x91b1507020d030c060609110a0305042108090705010201091e1509080702030124170708160906060f0909020d0b0405150103180b0c0f07060f020c010b120c 68
    0x1220300c11410040d40022104040c4410305070480c0380e10003258895030f000c00c202683c0340340ca101102c45160031340c40926010070078445901d100c0d0308840c1d0824001c03088100224004e81c0007403c0e040b82c01420f1000304400f07900300402d843c01884110010942800207220501c4596038251050003240020044541200c80700000d2003044590820812501c601c00c0103018243e0811031281e400940d0304034801c0d030030a0b4040c68061090460101c048100e200d240c14000e0800825503150b40320880b10034458858031400007101e010030010b991187e034455650081c410b00b407501460680d0065080101030004400c1c0001145034819113010442e0054200181c8990203d00014081c1040c081407640c41802c00c0c0c144a60709015061600100000362804c1021051500c52043d00721300200c4c000d04500d00d00c100051902e5001d8008100c1c0c034401c40c500514003005a5114400c9820200d0b800344000d5020648408141d024405c1c215070340320403242c00c02c0070803004024642c0d038041201d000b0302418101e200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 755026115 1250 755024865 755024899
    0x131d010507091e0b03070509100f121d1501030201020f1501150507060c080a06090605180601020a05070e0610030516030e010905010608101103090a0b0c070209041109091b 75
    0x4a4405084c0148a081e81c0e824030b03110082660300407510b56449160700075904071400e0b004e00511986003203c1e88071120750090100d0508000c0006060701012003109400d00030410000703010522a851000301e040c8499410f50000a00d002045006040664011812034410740301d110a02811140030f03d91003076806008041c1100c1c1806131013001046039080c10001a84c00d40c000c1d2070b4900c999034110007001481e5407015444240c403040e00c50b56400102200d425100c112542e24895400071045c01103a012244a50310285011850ba100010303062105050100c24541401406118091442c3c140320605002d4818500359006074181d009044d5165050462000290011f5a00c2d94010000708041741d42c1e10341e880c0c0c0b0341c40c08071030402d2000c1c0b4180641460102c0902030340d00407240c0780c0c000c0c03004440b10b640c1c0315400031000c0c06510814100740080b0005950340c4c00002d12652007010b00550b8400b034030b0140028032070050805402a000f40070450070302050170071030f080910380442d034030342001c408a21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 755027365 1250 755026115 755026169
    0x30c031302030f010606080c0426030423030c10021020070b06040608150106050f040909030c1506210215301303030e0c131d01050709 59
    0x12000350540242841a081201c041d17001c0c5007100d100341c491004035940c0519464861040d4014030143c07000282800104c4814185051568890782048916103902c8a503c003900207411801e0411a514048025015060501c1200d0200b4010348846036081405540a5103949242107114141580c070342803a81c0c0440115048074910b0b03c0401c545940b50541d05100c00503400031684907010741c2c14420009a04100021155444d0401804a0229900308401251281d209200403202c101d03043c0070104095031b0a00c0748004c010702c65280c4429249403450b14103490083d000300e81c55a10f180c0b4404001410350104842801e507051410154811401d00c0000c655003800b0241d82060240460a5001c1c07440751002203402100c5669600c101155034030541920302412540c15128804e001e00040001c3d0080d044041442d820f0015909401c00384d9010841c2c81d8541c0342d0600304162550b500c01d8104c18081b404d100c003c1180b5000384114900321740b018000000c1d0b40304200c2444a0b50030700b0902440598 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 755028615 1250 755027365 755027401
    0x306090e0102040e15090408031506040b0a0f090b0f0c0a0506070c0b0c03160509040b04142a090108070512091014060102070501050c1f1d070b030c03 66
    0x200100182039000360340d54000c2d0002d0054a02c40310086020400b84d0907400311840c900360000300500c400ea81ca659902903680c02c00781020074081c51b8131400c25180c2d514040500041d11400d100307036840702c0000700b0041100800d0b815070380910914080611202d48004101c45e040512120300658910180010a1030001500006001c5000b5802440007075035101551920345400b50300f14904503202c2000301d501c14407007030303a1202e1003d2009210000c0e450061000c3d00c19000020000598080c0100108080d101010f092410448400041151182c214055662150080c4c0d0410386ca20300c214401544900c9809040780c14098040006511103124208403046901410f03041d54042c10250282a42d0b4194103401e40749842c20001c140100d0b0001e01095407284205900802d242803601c4010f4500e9407080002034494080c100041081176144050a40e4003142c491002824800a40c092814080045030311100d64000389410007807810403c0c117807600110500d6a6a80c0c90b01c1c0c214514503c42d00d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 755029865 1250 755028615 755028629
    0x1e02030a030e0a120606060225260a0b070201050a0606050304020d0609080705010504050c060c1f020d0e0a0213060b0d0515040e0d23072a080706020106060e0a0e070306 74
    0x14901c0070108602504a44100d4065400300ca01ca01506170311011a140582d40402c281100360400304240f240d0703220071504080d82c2d0300381c400f400c1910ad0580c40c14111400c4080e00e0007509030081c48516507091007110f60045011104000c0d89040c078100920510018001038458481d14840c1000c0c080d055100504040e8407240071a51205180b40941c00b91400711002d4600d4052002c408803242807620441e4103041e41c0340041c0a2802100103280801025040070061055080c0308850043d0a503120302d1454030781c12401406501c076a441004050700d100075040140d01e00b000c80802001180c0c01c242c400411b10302001051a0b42c800c000c2c0c41720140804403041e800b03424090b100711a903101007481ca0315185240e691745400b819980c1d1310741c10000c1c40c070803034801d19008008810100304d880c0d080c2c002803504608202c9541d41d59145600d03420700c035030b0040100381d00a0a02003044580907c5a400144803604042151880c1c502c009a0315030384501c281e00b9010020b82c000740e407051003644100090002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 755031115 1250 755029865 755029889
    0x403032c0d141b070e060a050604050405070e030f250311150702040906090219030215180d120801090c0509010e0301020d051f060c05280b040b041e02030a030e0a 71
    0x6840f403119601d8440e44916440280380d600410154140710040d44103035400030708501d10b000c3c07030700d0140710003460000c0401c0e04100d007148142103196400c0c024218000c80701402030014807842c011503495861025091100741240d03250410000d00f03200c3c401c0385c2110701264846120111140d43c480c4910440c0d200070344c0146010b0310707842040600d60140f19464025600317918034404800000c07032002014040690310403000d100726414100d14000804031a02d04042d4032620341403030004502062000b4404860305404c0030301d801c0d00c481c1d0100609005002020007842501c10030f100180c41c1c2e11603148c115040040d41c0208030642c0d01d09404594210b1201041008185071800701c41c22302442c0003915152540542400184180c420382c0b5000800c0c0c1c100014054039032800030003480b13130400c100345030103c1e400d06042c06c030101d00c0c450b0905c0e01c60750040080704210b15092802004950b01480b2024090095481003405a10f000800c19525903040c10815800c016910002c0d030300320700c01d9100c0c03090341c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 755032365 1250 755031115 755031157
    0xd020a02010c03050705070309031704030803090307060b0619230c1b0a050105030c070c0f171c080a050a0e0d0302091002010b061219050403032c0d14 66
    0x94158000701e803548079030f07a0401c0b90341c4600c101124203104018000c0e0005110304028004a0300300b650b900c2441c41e0000500e4540745c0e43c2d584040d05034004a8161038581c0011900d002401224050a0b00c044021522540b80c030414000302d92050b00841c0300e00d0100b00050035660302d954403034200200b5000300680c559440e00f516220950307a0f000740c1590742031003c60380b410458448c10b0480d00070066a4058441b24250b81d1400701ca0b041036040a001601d00d14406500090000d1075408094050416044511510008070088601c0c204400c1d0b8201507d1012403601081070340d114010b00e800107a00702001c143c80e141c4550080140c0f854591460180c060b8481c030b2502107416038010240034505441c1c1200d0340c02c3c4900107908980f10b01e49102d800010820074118076091074424641e00010303400240700205401901a0101c52040b20101c0100365160481d50105109a81030034020903041444051001080f0b0746c0b80e2203280000f1510b0511104070b00036a20900254140e0303824411900b59091250 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 755033615 1250 755032365 755032367
    0x50115050a03151a090117070b0f0d020f090612071d0a12020a0e09031b0f2e0504080918060310021b06040f03090603020403081206010c0204050903090a050409021c080d020a 76
    0x40c3d01f400910b050b0b44150400000d0600700ca03800d0b5000300e07140030803a6041440001c0d881300654000000031018207420414008159030f0034010707004a880300c4030124a03a10b003060380076249041c0c0140b0421101d08060032603e40340d44440920301950800003a01c65074100304d1002c241040d400307070080082089044e04000000300004040c01d4010340907000c502800c452111130b592104012a18480075800140c1d00c0c0c8107680d90452175240d07d11225801e0090b070f00000407440c0440c1d00945003200e14050020f0011040c1c0b03044d4121601c0c0000c00c00c4060524140f01300040d54640f102040c4061640d00417a0031942010102448100b0f0080703103090b15260b141c24600807450720814881180420313107200000c00c000d8031a1081c0c406a80d44003000c0e81c5170000d01c1000508505d03004201070304111700e0050050060301c0e64002c882c002c03a40d00f0022342e12610200e003045808042900110301661501002d040583d032207540c06074203130030f41c3e10585100b07000d10700b40311500c1c1c401c0c0108150442d0000070481102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 755034865 1250 755033615 755033639
    0x30f061d1b06040e0105090712020a0c06060e07090918023a050a020103110d230601020d0c021512090703020301060605040608181603050115050a03151a0901 69
    0x501071104009040101c44040201c079014902070303035003043e90502c0140f00500340884603a03040003042c14108103001824081405a911110304140000c1c031140700501049a02c1c0a840007910300c40510035418901140e0060904074070303104148440e502c134442c859140c1b6107102140011500580140c52441c82ca01c400c6007120080e503001c02d0381050307145070100d407090724294002c81e0340d9211028001e452055001140500303689500c40884d100100003a00c40e510f0144146020f55881c85250410840d000c100e10ba000440146094195002a86051b4505500103450816140e0445031131003080c5414406084501a0845e582a516502000d02012480000fa8001141c1c8228024491152504001c61301030086114040c040b43e1903c0104114019109080060180000840b4003c2500c00c4517004010309170750043e10703581d6468481905003200e804404000d080b0a4030a01760985c5940c0d80c81488500d08034a150f40303140d80c8c00100003a0900b00c0120341590000a1000810b035841d840780c0c0c403074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 755035971 1106 755034865 755034883
    0xa03020a120c1e020d0f1211070b091603020907080702010e060c0c1605011704032c030c09060a0603230411030610050a030f061d 57
    0x5480c44502c914074500d8060f40e5405564000031003e0700c181d850480400b001c640040403c3c0204a40003680c6802c840740503c2c0131a600c00c101c2c4192001001541c2d00c40d40b95100010342c030300034400341c02080d6008444103000d99a19040401400b0f8549029100007500132058000103600301d401a82c2c100e6000c1c00384d0001003212841c1c07101290400000715605000c2403400708850740c1c16582002051120399410010403146c9040c1000a400201e441323140d841d1030b00144000904040c071440000c6061401810510710800c500302c40d1a60181c00c92034401d00911981440c1780b054030b00b081c2094001d050280010b56078905000048001d481010400340501150180f400c401902c14220304d88078501070b43c0440000801d21041600304800a0040720410304021014061980c0d1203080c001260381c055034055004a1501d0840d0140440840301c0c2510300c5004601e0b070000d9804140318503 = true := by decide +kernel

theorem cover : BRFrame.Cov 754856115 755035971 := by
  have h0 := BRFrame.cov_init 754856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 754856115 ≤ n) (h2 : n < 755035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
