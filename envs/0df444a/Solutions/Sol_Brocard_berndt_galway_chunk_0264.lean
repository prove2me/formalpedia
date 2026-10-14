-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0264
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:50:13.907053+00:00
-- url     : https://prove2.me/submissions/385429aa-02cb-46f2-b05d-f7e58baabfe0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 47302162 ≤ n < 47482018 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 47303412 1250 47302162 47302183
    0x40201030b03190201030605031f021303120305010518040f0b040501110c0f10090506010e0603010906020c0a0b0a060803090118050316030b0c03150105090f0a0b0405030708011404080c 81
    0x1121441d1812201c90f0301001c0310a6001c07400301c0c3c80d01c58009801c3c10007040d10313030704c0701749503040d0000c03600480b03d030000a50b11200050900b90400c070008000194240004408041160f40018070b40d0b040030140813005609543c0d0340c002144000800c0300062400c0001d542d42e65014180f8078032620b50740380c441c2c09000140700c13400403203e0224100084910000d4200d81051800040703c103919600c1c81501d003203a00c03960380944150403e0f001448005041e07410f003900000c001d400000c440d50140c56840886e0010160a56603822000c0e52400384503c0d10f59032307500845099020040c40380f40c0030006550344250600350307051180d04401c00041c42c042286000045c00050103a8842da00011000140c03850180012664501d44102260255000c04141c80c401c92455244501c12018a070054450750000c5e034010b40e014400d640018015103805403200010724002500e1520707542050105800e20116802030200341c4c3c035100000c0c01c0d107213104450703030f41158116a410b0343d10f01a00e5103480c20040580d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 47304662 1250 47303412 47303419
    0x3060e0703060e030a140909041707020a030303020903010507020c0105040603090201090312030b0312271909020306010f02120706051f03050d09060f080a0c050d09050102040906120b0c03040201030b 87
    0xd40f4810084040f0042894101984d01c0b200040c810749a040030340d02800c201c05130015000c00c000340010b2200c5115440c8242c041801d1401d009003580050362801980d0400c40009401050780d5050742024080ea0317801490380d0010340a05050100024414040e504ca000e0070181c0354544c510645e40905c100310080c1d90000c0010a8410050300301901030800401654081d10501030203814007460b01b82520300a03c002054896001003003826509400d100c0420300354014411504001d40502090540b0000d000921000d038803445c0980000d0100c07018048800150340101120740707125110001142d40e402e600c0035000620762101001c42e103d600f070011200798180e9144070b002c010b0003000942900c60a44554449148648688089a8030f00d580001b01012606840204407000304035000071a0503440c0d40740c0030703040c1014546840c094030700e02042501d4071b0b54006400d1048115900030000904848030400313810466607951a848440000c05401c1020804808502160311903005801c0c60030005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 47305912 1250 47304662 47304671
    0x150204050a03110a0608100308030a0e030304061e06030506060d0f12020307110d0302060703090503250218071202070c0e25030e10090c08060c03010e010806060a03060e070306 77
    0x24900481e1100603c0c0e0110321402000c1400a0a64410010b1038401c03011480c0d10040b69240d941c6c5c02201e0340024000b804202d03294501582c0121040000d50711803402104045500803886000d00020300c5221040d01c403060411105001181c07000403541c2c1c00c003901341c43c1d9100074025800c1c003940b80e661101004040841385501190a1350303000000d0200c15002d603454a090607580003c00214882c4000001d0260b000100091003481c06a03010010550042040e249420f141c0419440b01100c00700444110001000702d041c00d40c10404c20720206100c0401c030464a40c00c05074070192082d1069549211142d0300020204100001901c0070402001081590300d0b00741403401d50040000c102544003d55140b01c0100901d043d4400d000300100c051400c800b429240304005000c0340034080c1e100003a03c3c0450100c0c00000e04040400c070003489214100601c984a5040441c00c8802031810792007517440b603100f4000d105007076540c007402500f2280d2018000941c0000350110f02d0030020f0341e620103008917250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 47307162 1250 47305912 47305919
    0x260c0303071101020a08070302031810060e0c04031a040f0507060509040f05012105030f0c010b0306090c0f0120010e030a0f03090f0807020102122709040b04150204050a 74
    0x202540c001c401d2929407041041039a440c0b18200e0140041010008100d0f00104400600a50007103070400049828140c291070240d5200d07180c00404072104a05907907038035003004031081c80a400c9400c8582850903900d010b286841c4c036180d840840801800e05001d4501150402414404081700c081e4081c080e140816560701014015820611619010354181454021101c20703d1003840d041c1d401e00948640f412141e140120000d252040e001c46440c4410040c080e034240c0740303001a01402c0c0c6690008036070840710400341410311b10060511030043c0d021006411043d5142c00e0700034a905421b01c2c10107044541d6510701c5904d00300007035195005503e018185c40f0140400310003864050b0315500c80c3c1c440d0ba10800310480031504e0040d0080c095482c80c0320380c0d80011300c1407002049403c0c014412950751038241c20080d20603501c010701c165044030f10304a030340d440703116000c4088035080c1003141c9000d580d2910f5110f104c1d41540080006000289805001c074402d0070550554015000151514900c180c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 47308412 1250 47307162 47307187
    0x1407120c0b060603040302061f03020312090103060509040c0311010504090c09030303110906030c07020109030503030a050906010e04050606091f1e0b0705070e07020705270108030a0c26 81
    0x4112409a07a00c10200c0000340c9103080c050b00702d9000c0c1d50725034010608c039904c95881d2225440d4a10500d1080703040c144000015030741c20402403d51300c8401e001d4550300c0b42000005030488070139510060046920800304404150119603082c100c0790071100260b24580b4001c0126200c2c4105d400c003405480c80d108003402d410f640064028240c0f8400e0320104007080c0040c181d0350380d5008224503103a03c40030800c006017040308501d0240c4507161042c18459010340d103e56a081c15900f04561200611341d83c3c1c010484525001c000e0745004249504030081d2500342511600d46496004040c5409284138001082c0042c0680c000040486c0039482c400c1885030b103071094440400442102080c4102d40c81d2000f14200c6003034030480d81e1580d400740c020603003e45000c08035181074500512400c01c0d40a918270002d080e407110f00030210005520b0054080c200141101c0f1400700506810900036a070091040303c000c150018203843c40e55400480380c5000750050340c012019031600514416a501d4007003041c866454 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 47309662 1250 47308412 47308427
    0x9090c130f02070204020a081b03090a080702030a0c0602030a090b0906121810091b120210030f020a0e0118051525030c0506090607050d020906091509040b010302040f030201140712 79
    0x450081c80270341032100d0f04441c10130502083e00d144a4640044c298440045c91150048c00d1142c07010302a01c1c03a0503055115841d03110601d0f0301c480d026800c0000c0102c003c0b584101c0e0500078000d08d07094a400c001100c8080785250241f1a409128031140e0b4010500003a4100029020180104221120252032036011006404d4510341285c0c0f12404420303118080340e03900900819a0703903113100200310360000d8003005281d401031280c90b400d02d41e50b80c01400780c1c4003081c00100000f024980719000c48460007400100310200e03001650450080c101401e0000f40e881403c250901202121181e84541c1c2c4002481050102107440d1140542404540c00405030080501c42c0c1c5c0074080c4007603078480d42d1b41c0343c0126281c1808442c403100144c000c02031581c45a10aa0143c440d80d04054070090401d0388460104601c4262105083c54100e00801c0c954035a20b41030195a017500e20078a0b0940c1044c0c940603440344d0a603031502000381880b00d4800803124401c2c0b1001500c000307a410142d481c00b9540c1e224801360295 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 47310912 1250 47309662 47309671
    0x80f09060d051f0f03020d12051207080f09030316030e0c0307030b060406060c080702010305070e030d030501031e0305090906030a0b04150c050a0509090c1b01020909090c130f02070204020a08 84
    0x204050f0b00c0c00a84140c4103144035088030b801071f003000c00303240715652078440040703244a0000078440c00340304c007003040c5042c0440c00d84500c074103440e01072150515980d0f00500c01401024000e40750b00400411481d501c01c0e50f0a421104000c2c1030109100c0e03110b100283c100301c6000c3c0c129425101d00c440c00001d0001036405940200c0c400d507820428a91140d104071003000800101601c241c80800c2201e006520a0340065800586490075030350710000d10300041d0810030042211380000352103600500c1400055a600d4140c001849003a020340d001607940503209001e0340104512511800d800a01c1c69101408100c0da0717280e2044c041c2460f480e1501e4a0510b10340c00c421004041ca24002c0101d50340d9024104a4895221a0310394909202d821000c016541100414210340f5207414048080003010001042c00300704070746400580c036250f66400340815204003c16400150703121114003a07039038448640b281c400d0003c01001054481010f0031500280c4110000290454400a50383d405554030041c2d03540034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 47312162 1250 47310912 47310961
    0xf170f03011e0e011208040506040e04030801090c090306050411060a090305060a06051804020a050303030a0c0201110f190c020307090902011d09010501050901020a0204090b0f010b07080f09060d05 86
    0xb081d450640c4071441e0003150181c03c8401203200014000c000d210312680c4401c030310030b00020b490140c4880201d00305401a6011005400394041413004158005030590b003d403070150000c0111424408008003004014030025011a9036100424280700c114103c008000330090592a80c2d540c0c003900080c85200c03144000c1d5010702862001c6400540180543c508840c0010114040200100509000f858000e0800c82c1c2c00290f94400007000e803000e001840c41880c80d0705000400d942c04400190a5403520943ca04880c2010400c00740c00020000c1911445150388a000e110710400100079204c00b00f480d640690306210742580040c030640f554007d01000d520030798690354403080d00085408211400e9903103540c0403602c00014440381d44100c01500c0304480c144103c1380d00100607004581200c00803141969031441ca101007100030394085002a0040000c60745140c03926803140c951245d40e02652500d045509000036048805950300c8013a104141e660000801150608210882e80d107103076600b10404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 47313412 1250 47312162 47312189
    0x6040506010e01060801060c170d1a0a061704030302090109080a0b07090b030417220b03090c011403040209040c090f0609060506040806060402030a02041212020606040c020a0f170f0301 81
    0x40e118032484840b8107c501716180c948c6081090703518428917900e8180e26008040c410b00190380c080340c09d8001c80f031003c80000015200858a5828007040f000c4580003c001d0116542c07000402c101031042c841c0d03010381c06140044c1c03111071480040f40c035403401d80c1c030004480c8038000080060052841680340035401e1034944415042d52103085183e51300040703038090103400b220680304000d041da11004102c000b84201c060001040885d0030b04c9241c150680100003503240c04010422042400c01498407000024200300001144135404801c2d644030040000b030007003000da800f05040080b407800300030150014002c24004a208032081034001c200500c0390340002070401400044a041a6040720182d64406001d420704d0382e10102400061342c0098002c0708082d82c00c0100194400c521403610107103a00c1000c91104000403030b03000a250100c0a003400703100f00e184c1030361800602d400165407000103a01854030500040d03203041c880d489404c0f04003911040c40c000106040140030f00c80055040e103012301e40440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 47314662 1250 47313412 47313419
    0xe0a03030209040b0409020319080405030d0302070537030201020f030702031305100507060203060a090c09030c0603020f070f020d1401090b0901060f06121e050106030f0e060c0a09030506040506010e01 88
    0x101b40c0c0c1e9a03a0003e501604178050480b1603003514100c001d0414000d0039200c0c6040c0d80c13038000c82d25040c141c20b06c00000990108000c001c2203811302100c102181590980d0782c1d8905c542200190b0100201c83c0c400f0b116002a00000405001790161100e008210f4410781e12482d01030000382d120342c800e01d50441514000c1e00007007207a103801c03008000e6608140d44c80f00c0c20700d409950790400940c00941460341c000c5142e800082e00100502035040e0030a82991200103051030341c0347c0191070209a400600c10f0500600c441e4034403005000035502c60540109610091000e00e0010400402160001034034040741c040d0381e02c410103015000084000c0c8100041d0702c60340c0d106c156890803506c00740600791044520b0f080412580e0310079aa00841070400c40030028120b00c03864040103054540846512001c1d032a0340040081580512440540c3c1b00c407601d0a0007100078202515443d04401030265100c0440810700b806100d1141d080320001d564030030116a02401c1c45d040441d510b0009129041d8032000f44030010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 47315912 1250 47314662 47314669
    0x60405011107090c0504030b0603151303090f150906230a032003070e031b0103050c0412030e09010504180204050c1209150601230306060c0d0c020102070b0a0806040b040e0a03030209040b 82
    0x602008c0162404005107803070398034140f0035142c2100b3303003503003006007590010a918a4880c00100108506c40d81d4541803181034501600e920019842001800003184d60700003080360044503281400c1c80c02c0b0700c05648280ca03203000d030000c09003084c02d065040c40300e02404429100308e01c011400340c0030f01c0e29000c0b048031000040580d9154503000300c039403001d00c2d0b4040c04c07038650181d04104d404c80800150142403a40b2003e0880100d80e0032202a400125443c3d80040181481e071001805008180e0302401841c107200c2101c1c015031a0b88074002c0c0140d56541c0021048284070341641c5125082c0340040c8480d04000c00003a07a14184000580c81740c2080c2c80201e4903545c003031801860004102401607140348601c000d0660950801800c442e048241040b02ca0500310080c084c005c081d01450301d8a101000440c00024603001081c1c00c800120785040140d560380b203400c60111030f1f000c4811140890300c15407000c003040c00f4012065041c00a8850600e00b0010590150084c1041d8001501d04005154504082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 47317162 1250 47315912 47315923
    0x30c0506160605070306031505010608100b0307140c030c0610050a0e040b04020d080a020d0909021812010908030c12090105060604090b0d050f030a02010e0309060405011107090c0504030b0603 84
    0x44400122940181c80005161500721540c400d0050a0000b06a580da464032a0140403204c02810074035510001800b0307130ac1c3c202044980103518803421990540c1040d030352500600c40a018881031008088032612401c0d6510100c49034100c0c0320007503e07110040c3c218902d58844068030780d91001184601c000c21642070403c009411610b8544440c0c1103074942c0d88030a1036204000d00203a030000030140006009c525940010005070000750300a1807003c0d0683c00c002c01441c0746412502c0214010052082210301545251400a10449800c000c0c0c50814060900420034540010304441010040100507080a4041d06100071445000701c5144d0b1000566800c030b9100f11035040d80541c080c0001d1141010581c0800407203e40a49049091940c0f0784800b481c080c00451940c03129800001c000700d00c2030b82030181c03840300701845004505213a811800100107001340e003c0c0604000c045881b00c100d481c0304110080080240c50070400503003516110062160380580000c1c2c52401e900c002250031170500040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 47318412 1250 47317162 47317177
    0x10c0807050a021903053c010f051006020c0405040201020c19050d0b070f020708061b07020a0f05031b21100615031b02070501051602180906060d03020d050706061509030c0506 77
    0x306200d8090f44c0b0002d2001f014101c03e10b0b041d6070741d40c41a108042c2d903002d10495019590042040b0300003032508030000d140080e80703903000340228205000d01c80140d8000030082c6503014102c90f0f02d00d001030192410000310710180c1c071090f80020405031070814840c994031968003c04003a91b640d007000345070140980e50350031a0300c20300710540d21000000b0000c90740e100310b020038000d40c07440b8589003100c660001038148c10260814803801c41c00c07440820051404108008151003801400b50f0034180d02c031b0009102041340b958161120f041c000c04450005410311101070784407200c090030803000e074032540400807680030f041952011034600440c0004200e006c0103014040d50440d03008144003802c141c01120700d034000d040044280c003211262200142e86003020b0166524212002054502d000d6222914221004e0046402500a24a403802007079001c14102c40e4050a82000d139500d030742c540780003401460a0ba1013400005c2c08a03d10501e501c2e886040801140d0040e2105404140c0365420861107104980 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 47319662 1250 47318412 47318473
    0x304050304090218060714070909080306090a02071a06011202040b03070e0406050a2903040c06080c0405090c09040f0506030a11030f0a150e010209010c0807050a02190305 75
    0x1204020303600b0150020003409035000c006022074410307040850300340d4001e0b1200b1540700c101c2e091008080d20b001c0285d100203080880c0140300c5030b801e40e10b80140707521000d44440c0c050583c1c00002209891180c0450703030312581c42081c0082c241c400b141c0c2c071010000260748580c0000d06104962000202c24002d070341c10742c0e0081d1001451a00d422505440c04080700108a030803584950000401d99200b243c4d0000a0500c046428404101d030031403084030884c0f002403081c03da4030a0042c000810289059201a2021410001e1031901c0b01c4440c0780482c002d540c0019403244003c1d0411500c503070006c000d8021024203590034000007000890341e0003500c100310354194240d400707000c02e000850350103182e01e101c0410243c251920086600030707250620140c04000d0328508100300c103614105186100b01c2d5401143d0600860800300503000003480c8122911000c0c108110104252049c002c0900c882034400e40d0040c0301e09800c1501691141e0291020300c0240d50900414220442d146072810401c910307803070847e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 47320912 1250 47319662 47319667
    0x20a050103090c0e01180f0606020c060a03020c031314120d0f03090602030f060a12030c14031c0b0307090504050309061e070609060c0201020703080c1c09060203100b03040503 77
    0x280110010070b1600416540d5a0340f101e40044d9044001c0000b601800301800901080b2410403038250503520341d189140c0140f803600c01d080140e50717400310307184007031a900300c40c1e41ba82c07510b0b0480c04601900500e4181000c4e80000500b01e41c20101100c0480708950740380c1030044018821ba41080a4803030a16010800c6030422800038100300c3c41001d0601655166040000340c005440e21a030040382c000701c5800304480b03440018000240340c60394410340280f50a8014400002103035900400807071404500030840307202920003000020301407065400d00301102da500703501c6d43e42c001c190b44040d11a6081d00349c040c1c0a030490204000b042802900d00c40e036000002149484440b000784101c07035104401c007240b112506003135410300b942070800414009000301e40c0441c5800b6642020001c840ca20721100701960b10400c868000a5004030407241e0081409107510313190f0000c20310700307801c01f10060290900d140c03802e80c101c0304000556014502441c0a201500c20f4551a400d00b402035100a803000780443e4000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 47322162 1250 47320912 47320919
    0x1030b180f0c130b030a17160b040c08030c1506040f090303090b01151710050a06020601060810051c020f0301020403140105010819060c02011e0f0b04020307050901032309030c011107020a 82
    0x82040c1000e070310054480c2e05e2408d040240110240041c06100f00c2e0403a02e542e00f0300040c4a05080340748060300c18040a189090703980c106095962060058144d80c103501800010003507560b0380e20101c0007500c044414041c04106180044c01010300304012100c0d41c07454800860041085a50200020400d0329024140501c0380200f8107030100c000c12000d05a503035010041f03029100c000036280204440d030010003095040c40c0000e805010010702c462904030000d0001c01c540c0d611400e21816200300104100c10340d80d05400415001c001681d5615003642c0000341c00030801000e28112075541304540002c220340c4c1d0300e41301400e4480c4103071602c10714014088058035000c10203030351112110410303900002903482c05a800c004000f03110000a00c078550b642c0c00300481d60346040d01a034105808210b5045180d4a00124042c0c00c5010b05003201d41056504c04026a0700321280920140d040c5080c1c40340745c0c16203802190580c2d261702500994190303508043c40c00600c0410f0328161707403580354000c0071420280e08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 47323412 1250 47322162 47322173
    0x615090a050f0619050309101401060503040302010905060106110c09040206071b03050109060c030e01050105090a230109021e0a080109090305090d03021606020303010e01030b180f0c130b030a 84
    0x75001c1c65540c0004104000d000c480504004062400e106417107240d02da142280c50241003203a400042e800c05820f19010000007101c42028906660480c100140c987d2618142280140b0b01d18400500e02d1140c100040303101d60300044070078070b091142011550401c003004140302c000e210560b002908400184030990000300c1c2e810070300580d4281c44024ac103110f47d07030340c039990300795511b17140150341460303840c1000d2403103580c98019024a105410006c1c0860b501d00b4000c43e50000f0018008c101255580310107890b03201c0980d0203000c0c403c800a102c0303002542c403011071a0003580901d01a0416940305480880030a04c184107032010310806441e076420780e81c41c3c0405003000d00380c100002c60401c2800c1207c404260f4030380c2c004085c3d02d4042e078020210544c5416040304001d1445e04084255030042c80104110685500101d065a81c080041060303512a1000300d03424100ca0b900c03161050081c00303450311582c7c40000b80c411310034408840d0043c2d419800b040107021501708000d030681580000c1240e030301191 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 47324662 1250 47323412 47323429
    0x105030d0203040f1502030705010c0807030f05060a060e060702151201060f0c03180e040605040b0105030703200a0b0307030905060c03090309010c030e040609021309021303140a020402120615090a05 87
    0x105c3e02d0040d41e24000c01c0b41d54040c211030002401c3c4000c6445a0107210314035905105e0814800040c1d20200301b90304010b4006031810046c1d10505007003200003000d1503d40d46410064805840e40034140e1608031408031094003d5410030007040e0050200c1100025005104a0044039030040907140d0a802414944049640601035441c2c00107030310b01e105001650b43d0000d000a845a070007018001000e042c6894000c0300d4101c1039022030300c27030790200009101040700b49810508418503c8151030807446c41c0b40101e90f402041e544204075481d03005c070401c20601c0d015040000d0491040b0b040e1111a592220449032a0009460b4074540c0d90041c4031520603540112550745500f4060b04060140281642c00202130310304c1c60704080c520356000315206002940600c4071714050b094400d02542002150000300000325840c0c40b0140c001201c031f1800b511100801d12440d281560060010340d0340341c11070600280580e0f41a01c882d4010380445103c0c4d07280020401c19070b014050010024211207250a08010144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 47325912 1250 47324662 47324699
    0xb0412050f16060c03020306030706030e0a050d1d010309031e11060a0e0609030405010c0b0a020405031006060e0108010807140111030d06032a12031101060e0105030d0203040f 77
    0x2904008450885140c00090264080354214402002c00c1070700e40001655940100001414018402e101c010b9030045180400c1d500507260005140703907000480c9182038144407015045000328010140e005c5d0707208110480011491180c91400790a440045040304c40207400600081c4040362070000100440e00c241c0840403503494402104840c80302d4083c1044419031b48511880d641e0722482500d00f005116455200310144091030400349000000382c6600806140148852100742c00a41034210580c10389014002c060708480b00071101c0c08114004001900450000c1140008400c80942c4074400c8641078a8102c0c010f4108185031100105a4803c40380c035041c14441003204030341c000b110400140040401414001c030300d240c9581004940a081a2144948908000891103c1c0351034900303000112050305000041c0c881c0389080440340580078030808003065087c1a4005214169550b00c58142c0d4012810356075520720210b403c3e0396921892150601580f10410204080700d1005d201c800e04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 47327162 1250 47325912 47325917
    0x60901050a0309050601060f170903041a04030b01036e0709050105031c140403020607120f050c06060f03030702090a021c0e0a020907120207030c12020105040b0412 72
    0x1050281d5180e90034401d00740c210a00241a440e401501c40340e01c4154486104090300040002b4101207400035124415030061480e20b4018805240320803101c00c0c102e40046800c91185d0328156102e26055040c2010000c01c201d000d0444400c0c80d803148d8101c2102841130009000c100011140c000851902c9000c24180401c83d8081400010018902c009000000408000900305190074134004804540c0d06030403440c040d80c40300703615403007000074020003003074040d0b00341408083e24408020b5544680303d070341c00007500903501150075400c1046004007240600c0701510743c001011003601044a03e8080c09101e0042d5501500118403d4103089115583c4440050241c034942145500400e01c3d18000f6100a24442d900289100e000c001d0020389942da592429014444500d21080490340c03071950001c003a1240089601050007240200b0031082d08480c104410742d00c681d828140903100c600c00d00d2041d9100c2c0b6040f00c8004000740706100e100d01c6540d00003005000c589968640c0d41c0760700c6581011a09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 47328412 1250 47327162 47327171
    0x703050907050301110d0e0703030203030c0304051603200603070504030f020f0d03080123010503010b0d060f06030603020117040803070c03020322050f0a0806070f0207030b070206100b09060901050a03 88
    0x490f9242030294100072038178824a0355991041c500742c00c007250002007505500350842281030000a03400b10450343c00140034585280c40e6122410143e050260212242d42d4584034030800004100002440368011082165008046140301d814480a0301c0300300d0f8180300180c0c0400041c800550003060313060030240068011000301c5400c1020440f40d818844055010400c8500108860100c2c00303002c07004002d0b803c2183d4150005500080d0003030006004280400340f02042c3c807a0071003504c1d8001002400e128103604c042c107640d0a8040c0007041103000c00e90000b0207101400c80192124411180074582c002034080c55035903600802c0320b00e012251030490441c0002c000d00072601040c21928044105d00c8044051650718000030000c0c6191041e10f4180a1465400c040249180208205034400703071a0030702c01c1c031002018608a040c902190001000040c0a2303051080c0b4650020b03800303100e0030851540a00441c1c60f2000d41c460760042d0040250310040801c07240b4055403041025060036285401e000c207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 47329662 1250 47328412 47328419
    0x705190801021b0f07030b0c0d090209011503060605040807140114030906071e020a02091b030408030907050a030809041d03070f0209070507030914030a05031206010909050f0703050907 81
    0x103007a0303031222018050310034192403d0325182109008030340304500808000d001052a6594105031404001c0202d41c2c2850b01140b218203030801900300e03a0003558000c004580d9036868862692610f008103151301d0001c1c3c82d0031800325442c0c3c0640116415070f1a1a4000d0001c1032900010018540c0c12041040c10403112600c005500c04030750b00a103000c0c2c80098058003803441c21701d100074000d0103000391130752030064035128242c209070b004203104810750703019580c1c40003a40e80c0d0048a82140903c0252489450740001000140309510002d1809070415006079480c4c1c84e616001c011010006010140c1650010840500300d17180a90208528100d04514621010207070900e1505540212100ba10203801040d102401c601c2c0483c0f0309580029503042242c00c081c11528010000841c0740514103040c00c1544102a42e45d40822a00c9100395102c01140d550344e03518545005815015500a40400c900341c601040071401401418070030703400860070461564401e01c08801800740a44401c0d00750240c88000b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 47330912 1250 47329662 47329679
    0x6011b02040f060e010306060602010c0503060d35030a1107020a090f09020a06080702070515040612090203030408070617040308132301090308011203050318030c06070c060e010c02070519 82
    0x245c0294015000090220300d0080040e0070359108922080400c6030800421240355242951072108641284060800e03442300d00c1c070210003042000300e070308445405050210340c810324103000398400c3c4040d110900c603130038800f5410030590290250003544882e07034040907c4100c8403035003c4056409501c20101d88110190003250003a4569008000010128803c0103004c80d010404540206015146002e0700c00c0406da1464250080b030141e0310030001174600002901c0d009402c1841c13155001000d1366500c40d0388440b0a59940f895105070b1000c10303174501c1280da400c545411124402d07501500ea4010f184d0750b4101106c100c854a42c011205400c00e010b81f86030142d4032400d40209c41a0100c00007a0211080c10080c08501d016800121011400020403000a0f4888141d0750002410b0046036004100012200c0c00d50141c0c0240c100381e8800c000420030050741c81824510400d0244400700300d40320072514080c0c2640e408905000250b805090100501e080c0490540001d02008600c01441500d4074003c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 47332162 1250 47330912 47330939
    0xc070f080301090e0f0a0305041211060c0604140102031006260702030901030e0705030c040207080d051512010207030f08060102010207060f050603070f0e060105090a030203060403080f06011b02040f06 88
    0xb4800c450383c1c0e0b03414030780e0b1100400017070785140359220007008018560341c0e000302984a540580b0a180503401c540c54100209030250649000d4001c182a4071190341200017903032400215404d8441021150064441c69410f200b12400f6044010000b90554180700041d00d0400220900c140c0900190006004010716045030038010042c940c081c3d9543c03941200010245d03801d03c038142c00f8580043c0c804109540d000035640e80c0e80801583d0158440c00507003448072280c021000610b00250400c1c04114040c2007030082e80000c8030048614525000884031811700700d00410b0001400329540c4040340724102d0003a00102d510440c1407002518002c92030703441c802990f0130111240c1d00c0315114020b00c0441c1ca010b00c0440c01400251880e600c5680c54011040c944041c003428403814070000042c5000a40c54401d5110701540d00682141d1041c145460010b144045c01c4580c19031550361000840e0040d841920802240004141b050903410003540801004005130315140140f2507aa6600185151000705c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 47333412 1250 47332162 47332169
    0x51b0304061802184501090f03050405014a030a1109011a0f07020a030b07020c010905060f1b100c090e0a02030112080d0b041e140f0c070f080301 64
    0x10b13000150814045862200540305042200c3c03004030010600c803010310322149203402c90450010045603060380b007954010404a48050314401c0c12109070400d06400400800440d40b080e07075140801c207000c0692411700080c568900aa800b051007500d440101c0c0015076038024010740e0100c0e0400311078440082e01e000811402146d0201e003030151800c0c10f00c1d080d0400350040002251b284007a450100c000703080b9103c1c0d8541d01c5000d80001c901d10040d5160481e00c840519403044c02c0e10128248454081c2d6030341d60310701c4514005842030402041900b40b22040d5501d0310060741d461810282c11600c1040d41000c1611400c8003403003009403140c49010390b8040d070140c184081c0c56806055080140000011000410b601042c40c01040100100d44041440b49105600040109e4854102c000844043d1040d00b090943c410b09004400080800060320310100c1c40c5412410080c40d03a40c200409543e44c4d00300c03101c461204072580003443d0080114001e007402e512842840b4240d403404c1d40d0b041c9141d0030a80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 47334662 1250 47333412 47333449
    0x14090411190e06060909040f03020a0803010311040c0e030309010c030e04020414100f0e060d1e0b12060c040b070510090503190e1f03020904091104051b0304061802 72
    0x141c040101141214030b40707821150566040d40b030840004049a22480003038402044030520004103428503200f40311407030340c1584c030100340c1c4e03641d50390385c03c000c0b4855540e0a41a4401ea18000b148040c05014650b009501039024000e58104071190b00107558614030143d054044c001d941c06c00743d042d9699840200080c04560003a81d03841000300c0300b8421070300103030400041030180c19030001d03804641007500c17081e51301400c903040307942c0c0c0e100c41407004054041c000140c980104402c4940c403040b102e5800243e0315440c25511800010140c0250b1960b9440a40c0e4401c071860081000740800d000340401030003418010b404860180309400250401c6620f182010303101f6800101714240d0700c6405141540c07824001d80b5108100c0f0314030100141002e0001001e61000440780312910103054000d40540d0a01080108100001c08190a12421404401034124070440c40c2c50000758120410b51406007100d09109200390840d07403035a80741d80040c00b200004410b146003540354400143d5600c0902800c010300301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 47335912 1250 47334662 47334709
    0x14071d13060e010609210609060207050f0a290a020306010306031403040509061008070819140406050a0203011203030213050402030a0920060a030b0a080307140706080114090411 78
    0x29000800c2c0d1211074000340000c06031201c3e920620b06c40c01c01c04409841d00503100141c134407083d10301040217100f150001001030141d012110940c0303601003a800f5005010f03480048a14540c2da070700d00050302c0b107103140f00226000100450b00d0a4002d501440d8010018140024421345030b441e1860070301101105000305a000003824803041c1460744500f0341107802940c81d20304040f88240c0240ca000c100a00100030002c5000c005041080d074450b440d08008180441000b982d40f00724520340e18041c0c102c0c2e055600a080801090345115948200c0c1e049425000f8580818035066400302c0c0030f9801100c20707546c003220703810011506a4a5100030b5000f1050b654001491081d41d1800500020f12480c0c01500700402840100458540108880582903a0f1800044050200c000105200ca086c3c20a0002d484049141010403600c604803444000d507140031580380c190b40d01e004507080c0303409010740003003200c0541012085003016100660041d200305070ba0541203000c0c601184004030002d1403400010000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 47337162 1250 47335912 47335919
    0x130203060c04060e0a1404150b0a05070302011401080c130908130305010e0c0307120807081b10060f0603022b0c030606020a02090c13090203040303020301030614071d13060e01 77
    0x4010180980007003910b113814217600d401000034091000c464070b90b010301d4655107004540501002200045e11204240d280c441c031070300b5002007054001c40741c05c50140d03103000c80d110744d820316103014281210504e100400d07a0303c501ca0103021940e421a80136000f420384500c2d24400058526000d4484060608809030400d4910300346203003528400c00100c4041c1d00b01301980440d640340030421310256074040303281c985481454608903140384a0301c0c501070270070000412184003405035460320360320020601045859226000d080b54007224410f21400d8454810440d0401585010750064078000c12070018a40741d031075140a00b83d500c807c2c0140313150788555680700710802c1070382c03d8401c2d2005481280b008124842955001c034100702d0b0080c20402d03a022001c100e0100c0040c02c2e0001e80054a00f2480954076400c1901d4060f02941082c042141c200d4100045c10900d00100356401e4072450180d580c08090400100c400000c080c401003503aa0015200c0e607003030740b41d412140580001010701c1780c1c480007190314 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 47338412 1250 47337162 47337167
    0xf05070b04050610090e0c0f0a05030303150a170c0108071709070608011d040206070c03020a1706010e07020309090601030e0703150b0102030f0a031112010b070303060506030717130203060c0406 85
    0x2460700301d03500c82e502d052020803046c100081c2045140704180c800c000102c0d030714000111428500c0d445251725200000c10454403c0301003d48071215403094a14110058544913040c0320000c0c0700c11040010341c0103050610306903101d410710b960070410905108031403228502e01e02c01d20400844801e000c5600c403080401c0291342c08182c00e801007581c0c41c040142c44000c00840d4081d9440944041c6c815000820014184001c00000800131a1b006003d4a80199242494040c40c0040610500769020304c400000723116010faa0741c2da22409950380511f140010b10340c104924000040c18850405588540d0300c02501800c10141c2c002d940281d0041a001031800c0c0403070f09540002541904540044c840030468a46040a5400c02c86c41828089069041d4008009090245804e2340c0e00d050310b9070300000707651040a802825840d0180d0fa0030301c0b8281c0c50700c00b4452288415503403000000e502c200c4041e2a0641c0c2d0035125004900c15062000e48100390300001d182c01c1c0e00303a542c0c40c0d1700c8000107400c211568 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 47339662 1250 47338412 47338441
    0x80c0d050a090b101511011d07030c0803090a09090f02090c07020910030305030c030403030b0a0906060e0a0b030109020f090415051e01080103030813060603111003060305030a0f05070b040506 84
    0x205100b40301c04030700c0c01c1c0440a07192017a502c400b08140228041d02000007103081d00102000e04101440f4210300f40d400725201c0d036960740c912054503015a88a00400e0021020046460018000c3e1040380e0040c03600401c0d10040000d510107075084603180200e1001680c41d9449c00340201440008245c80340ca40d401040410800648902c0d40803034402010000250000d00b90b07984104038002080d120380c0c450034181c4c0a0f0015400a80d480300f0005008920ac52195100c0700a4840690b54400c50031846001d000d18040c1a000c0c0844189092004105158150b0014641c80031400c100740d041c03140f58004075041c2c0308200600d09002c880b60030280401e0400740d41600e069010310880000750202c00c0000381c03103c101030001600b086a000300103001180c29444c000d05165020740e04010040c1e0b030742000400e014120320b010b440340b04102c0940e4000d42c480e014a400390394001002d1480d161100500343c4654080c01e003040103205081c0004404121814500c80c8a03d01440c0940003a02e4608005c50290 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 47340912 1250 47339662 47339671
    0x1509030e0a0506210709171f0b0904060c0e04060b0415020a0b06010c0309080d0908070602030405130203100b041701050109020c0a062d0f06050f01050703080c0d050a090b 75
    0x2803c09000b010300d0144599061020342104801040032600c0d4040c0445001e00c2c0ea820040e01c061028a102d02030700c0000910f2400745000e00304030101000143d10101c01c0c0c52040703070f029501600240100d004948030741c0c40302c16070b00d28505000c51380003462070125082e50507a60007030144c90004903042015001c5c2e0054815003c0c06880a8088400c0d41d6172500240310000d41074604000c1c55510450405014003804405024600129240c4020340c8030020700510140c06600d059000300d07940014114000401d07541039901c020540300d0740d5440807211030001d400c0280b442e007040d0071707904000510a07514401803001e0801d031800c0610340c0441101903404d640e81a4040440c040c410042118a4030b408a881c2c44019800310010580f00203481c0b113030f200408a211004110300d0510300400c0e620009610500d84e405100e402448aa9519420000403210301c40005012840c104580400070313102c1c682c116401a02080101d04000c2246220411541c04841d800651580c40c440034040c044523600480c1c1c0f1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 47342162 1250 47340912 47340919
    0x80f18011b02100e0f1e0a0605160f080c09120c12030c06010b07030e06090a080f0706020118030507140709090303020304030216030c210204050a050610080f0f041509030e0a05 77
    0x5032450240c00e6951081ea1051b800102c00030901e055460003814050f0040540c0c10020901c9a4200071031403144140108400e80d0203c0d0880000d50700700742c016490720f84239001c034001c5981846082001e011612201000440441c0183c290322070090f9902c241c0f0f0003040012000460311910141d014034907046041c0c110f43c12400e0b05101013000694400c40480d000d46007640e0301600c502080003c101210b2040d0048a0503000c0c442c4841c4861000281080880e4956402070041c40d8110160314071401d00c03000c010340020710030400c41c0046240c00091204c800000c0084803441540d400d00c1c0412128003c1007100002e03000405d00060543c100012280e00280c403030120f181c3c0345556141807001c8541d100351001c500c80c10307400725907201c0700c0c810b40c000498029106100d00e140c10b100c140c00601c07040b21072510131808a500086601e110300c0d4918441d01461014900035100c1d03860200980c10010000c40b2007845044200e00311004030f0007801c0015119481c0d181d94125404c0c200041e40280f43c1100e0700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 47343412 1250 47342162 47342173
    0x3090c17100e0d0e03031c020c100501210c08030403050331030b061309080406080f0c0403110f03010e06060109090e06040b0408090307060206010303030b01080f18011b02100e 77
    0x22640701c0070401d030481d04141d00300001c0c01c01449012034114000c42c0a0f1050310307687c000d041a62150550020629804040c0030750307103294040400c4400301d0340301b0f000301d4401c404038841c281e000001e1000110f00301c60140314100103282d0f650001d51702d56803050700101c07099000890049044400e185541c0480722006c07000100b20320141d020030002503214400506030300c1012020454a49414904c10103545d41680140a084602d040c100f040b1b6025100d00710026101a00003005110004003160040038600441440c0070315545511b2580028142c07056481418050507221540e024862441316005100140550386014000903025000c258808070b2510300b000f440c050211000302d60b4503071045c4c0c0001c0c0c40722035440d0f03814a00d1090281e030350440e80510480b0008601c2980000704581200d1180e41c003481000024801102e564205449001c070300c5410303902061341c0d0420030030a40368509101c40001a006205180000c0d00800baa4400009d40c016a240030200c1c40103004241040d01841c0c010329 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 47344662 1250 47343412 47343431
    0x1080603101d0a050c0a0801060e130206041206050621030f0f04050a0b03010306060909080304060c1101020a030c020c1f0c0303140103080d05100812070303090c1710 73
    0x944510a49041104080e5600c0e02c400703084500a10b80580501c5950440b1030b445010b10302503980b02191301007648160803610b400241c6c540140902010b84040e0040329036580c60f0003184104649a464040741e02030421b000100c1e5095480070380004035800351001040030304000040c011402d070700340e206210304914161082d018140000c1121071502e8038440c441e990343d080310200466406640c0110344e000310103180000d00d1104400145050303030b0040d0303030800805903584024000c464100d40000d100d6070007400050301060310b0703510190746150141442d40980002010b6582241c1c84a0003100200340d4480c644c081841d4104264031b403d5505841565036a2400c01e41d0070f9011f000300402004210884405404061094001c864a0020968040036a503107070f250049098218211043c3c00a14000000300c4110010210741e048a0100000d002900394108132458284c0c030030341040d4141521003004100003004648048020613054801214640745000c0e070b80c0c00d000225a400c0402400e0800c0b04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 47345912 1250 47344662 47344669
    0x40302060c0c07050a0303080f0106030603030f050d021b1b0f130e120a02010f05070f080402010302030a0b0901090209040e0d08010b070c0b0315040b060724060e01060203090f010806 80
    0x10303801074001854540c8550111800c1032901d0310f03d410040e08013485400020406401400560090150b044003403560782e00da1804800f2039405102c0600050146401d800c1420b02500082c0b078111400040580381c80d980780b181070319603448904042c096078044003c4403001502003101d09944141110004143c2e00010001388140d041d00c174010381411398038851041c015401304034045c4045521040d49840f103550030000713802044006000c807906410b1400040780c42d4419a0507041b050600d44542c440b644458004600030b402c0203100140c5150f5454a4840941d142c0b04090300824000d6405aa544441004c0c40700351449850b0040296000c1c55a541c2c2c43d9410a1003281900d50200d00c4940301c4541d8100000250081c0e40044400302c800002d0200c05007016501c0400240191418840111000c041c00018811030764050251160b43c29002801481b024030000400ca62a0000c90300984401980403990007e900080c05684006410007507070030130950500f190402424112828038244011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 47347162 1250 47345912 47345923
    0x103020a1202030601020102070b0a0501050307270f11070c050a0b03160804020415030b1602160501030e010b030303010b0409050a091a06030f0106060507030216080d051312030503061008040302 85
    0x100300900b6004000200c1d141d00c01d505840010390401c102c03e0481c10581840300090200303019541c041d002d003903008144e05680c2050414980c100600300c00d2810407140e40311300107050190910105980b26161090800b44500180002034024802000c0d041d141c50200112032a0560203500310040901c2080721306c08020341d41d8001c410301410036103050307a2244001001000c00750b40554000203103260210502c017544802905c2002d1402c0340b01e500008018061783d035034025900000c04125581c0003030156500c42d800403544407407051f001140781080355000a003103810076000902111000700e400c211420780b5005250700140030b0341c0208200780c0c00340c440c0650b4000c0b41240c80c1000351104080348280e2000c022003107883c540500204050f517168100109154400c41d4150010311034100340003201030b00781003000c04840b8200300030407a036080c100c4140ea031600113001a15100c0c0348241c00240846c50100d071a03070014441d64074242e60345094020400040d9410302000100035032a0b0401001a03000110b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 47348412 1250 47347162 47347187
    0x1805040603050a1e150b03011d03030a110d0e060702070b07050a02040908130b0a0e09090a0318090e0610090912080a09050f01020c010606140904020d0615120b0103020a 74
    0x8030112881000c15031100e105400604201040c0f00c2c180d8950f841c1e42c4901b544100460080c411440341149010103000c500c10b541c1e08079042000494502c4410340d2000c204074021000d081e00302140141020121003860f40405515000502000203040d4140403400c098800c85825504046160300d4a03540c0d0101c1c00e40c028000c5035103140040a00c03112400380d03600e040714006ca421900b5100d207a0703040590050101440410843c4081583d14a40f131103a65100390840401082040c52030b13141110b28004681d01a950101c1c031031400300390030110b401015090140c01008001d01d080c000d412624155003644408001032500d2449000154601c44c02e0000f5040361400d0140c5848031307116400240180c24008129110701c0302c07501c64100045d00580310700c2241900800c101541c0c2c5030141e400d400c01d103019416440c002c11800310f040c940355000e040b0a0266410021710292141700d441503d2000383c909001141c0c10040e5109e00780346902600c440200c00786000c0d0306001e40240081c1007a500e40d00e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 47349662 1250 47348412 47348423
    0x602070b040e070c020316030203010c140d0203041b12030f0c0812071b0b04021f02030a05030403170403020c030d1d040e030f0f030f09072409151805040603050a 71
    0x100b010180700303200c4c2d03c0340e003034009083e02d58101e410610080741b42d1161208901035400c10400c2e641e00c0340551005040c08031404486440e10000020380340007035100034811102a601441000034000c148507054016220819100c0041c00c0107041c05440241071030900030820904819250024000c0425030744440005c0752041101d03102e522081c3c44c7c2000c030a07020002e186235080c42c00140400305590b5402180281c5029801c50032848c4501d00070640c040016000da0b10400289091603c6076005640c018000d161101e00d0055001038560080804d407004e0300140d00078052034003d0302d82800000e00c1e4050b541090948100c3c2540c07440a8540b2092400707114035a6a42048220b00091017200e0211001c40c80465071840b2402c5c03a9515034205a50301080e003039040380021070401d0001030b58070990381d81c0040a08010705d42100d540040c0c054040010402617a0b01c000a20000301700a405039085050326102c1c900745625249070002c0b413103541310314440c0341030810410102c2d41c04100f000320641c229 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 47350912 1250 47349662 47349689
    0x50706110c0d060b030f120909060a060923100305160e0f0613031b08070b040f0b09040f0515030c030604020906010507031709010902181510030e1b04060602070b04 72
    0xa000082c02c0007844070a01c038080c0a1014128407d01c15007004143c0a44210340a08040e1203c3c014444032480f035002c0d6001003407540c130051010b1213680b82485d5411040320160303034050b42c0500105034800c607403010071008603403214103000008000702c1c014024881645054007101c180380b40015a401080c5500c00c0c081c40000800401c088a02000400036540003075549641c00720707810350004821040c0c0710b4021f00d4001d040d0f002c00d00703112100403a030460366080b4105407840e0a03e540c000ca140c1c41b010710150b1290f03440c6200704000c10f29010b054810b07441c40c0c00202c02c09411206150800300314005640c86904810100030041e95101c43c002e801480030b1a00980710380381c0f89805e8540b4102d5000e0000180444e074200140c0c24015082202c82501c02e840f0b0050010070b1010b2485843c00c01c1e100080c100501d00c1100f079690034001d08072002074031545008a444907501c9103035400c0c2002c011080301050b00514400e100c5003807501036200144205d100500c00d840c64004454407a01a43c0241607840050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 47352162 1250 47350912 47350931
    0x3060102100509060402150301060801090c030b030f0a02120a0b0109020a1107080c10030b060a0c03030f060b09190e1302011e0c030206010503010506010905011b06020304050706110c0d06 82
    0x1c1103860311030000c0300303400c00c09803c011448994681040700c00720f1003030034405240c0030312051b1a010b0328100c0319251070303105c2240d090403c228050140300c002d140c105a911090f004403507904110703248008660b540546410710050040c8449141d0750340380080320f42d02191064000032001848035044410505005844107510709040b00c01000016904103544550781002c900000c000c640a0008001145c0781010b0241e010000e074140c90795000c00682c0003006001000a850117008a00c003070750701c40c0c500010307907030b0054590303c0844005030044d007000d60001c180810141046001c55296840300c030bc05050251402c04214002c00b0018001f042e61072a180f605405c59028594842a190401c00340a0723402c201c610300144a004056000d034014819040001400c1c10706211701402040103130758a61019047c48010f4519460100e0755100e9070000c889002c002c55098400f46000d1071081c0041e01903189843c000070100c0c088000303060110380001650080c50364888600c0c1d0a15540440302281d070707294 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 47353412 1250 47352162 47352167
    0x606040b060708160f08040e1e060108060a0819050c0a050303070f26030601021915111b030a120b0a0320030111030a0c0507050601090b1203040b030604050703090506010308030601 79
    0x313000e000103103e802d1540307440041120071005802503910181c0c494040ba941c424103000c405282e2100c080d6490301d00070220b8219441200785990011025042941d0307a41c0e01e5030054544080141c00392b20080710040d21508000040c0102d40b00b00004030340c83c4e54640d05080003c2c0d200c1c0b10b40d0800a1090000c0c03419181009103602c03815a8611032000c0d40790704080035100030720541c0d104403249401409002c0045040c10030741150b0780d000742d8210488001450548850720014001e8402c00000c511091020807040128003d0780706000c49818051521050203540140200306400380c001081402c140c0a2409a155001c0510490750480c85142407000b000c00d000e48060301c03400306203402d0b5003428403040131401c0780d0000303600075907016008100103098600b0490b00c078016903400500a800400040000710002d811858108000500c2c40e0140865200024035560055204520600022040088628182c46a5544142a410306104035003969843c5626a030701400004c00042d0080003145143c1d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 47354662 1250 47353412 47353447
    0x2060f070e1503040302010504060501050927010b0d0c0302090106050c030d1508030a030e0c121207110604090606030c0504081c0203090604140a0b07020a0905150901030605090606040b060708 84
    0x140e52000075aa1381094240240641412035083d202c1c2c1c5d091000004840c02c148866a200d51801003040c0c0b100d62011001c101480ca44800c07030a4190348030755224551760381c1c0344004007407607126000301e002c0507156205000a40c001648003009004d41031082403044000402180c80b0540c1b0b07132100062074119652218103014568009011500c00803800c4091350b509a030164400c0d15000301251002081c1c6410404100c4049121580c1c94001c40520076000607480301408111348981c13100c0f1030040e01000800c0090704903500648100e612020100308440c3c1510a101800b00c080c1350951070309040c581c0300c540e228103c4988010240d40303140c9960301c0904c02e000382e035080310009240301e40c0c0303d81d501120021001c1001d841381c8995036650f07001410351003250484a85a9025040e041c032186082460390050034020407074101d201d0721b4500e0008540e11070520034080d40c441e4000140f035082000340b0620340b03440100b5060140703151540c2b0b6000e503696401034811156028110b2656054001d442e180d005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 47355912 1250 47354662 47354689
    0x60301030b15150c010e0f0d0c03080a06031a0403030c080f061e0603010b071b210503040e070815030d140c1002191202040b04060e030c091609050102060f070e 70
    0x40400e141130300b0501900b100b200411391a080b560b109241142d00c50f250031621031000082a2074107600360001e405203150580c88406040300041c807964944a080300450a00540d014101c40c2001f00020180c26214204a1070344e18600342c111031900d00d46104d510b4101821251040074141e8030a801c2c240360a089448400000d0046503c950751f405030309185810507081100c007a241d03207104401c0a0403002c1c889088074100c81c40100c03d51011041c515603017031a41000d49441c002048003094038804803c1d01e41c050503055030b1303110613480c041404800c0c0280d5850b00368443c2c2c000300d040c440c0c00c50f8850381c0c451020343c1d1150381540d1401074800540c5841c181c0c28a2a2342a400450003c2c2158018003024411504503141c22802c00103400301c039400c0b032180e07000d4511081d8041c4803e110361407103000b0080ca1400b01800315881d02401e800055160201290080c402d90003100250560651200b821001054217000600d5a410700e4600101004070041000c41040806e404101190740e82c403035019040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 47357162 1250 47355912 47355949
    0x201020c04051f0b04090608011103180a08120a0c0804050d050903070816080c03030322150207150c03020a020a140a0b0a06052e0f05130602011a060301030b15 70
    0x3c581d140c00624081d0802e108881a141c0303403580002e0a010103000b07000c00700e986070030003c0c5540c1c0c444201001009445d5038806443c402c0340c00640020344d202c0001d10344200c1c01141d0740304520b00103290400741d41c54108000d00708040340c8140000214005202550300140f0700b400c58450072030f10046440d102d8240c2c0000c11134842c030301142c031200303a10198810946141500703a0346181d4800061640e68130040c1c4600c4200c1441e58145203483d680c01b614004000d00c61000080210903600c2c0340c8d0140e800150f0284c40c00e999589071401514114401d01c00241400c0c1019800c01041d4440a0340718a09100041d1900c0002204e44082242c18170095240941c090084402c038103100003035800410040c000d9600458903880e031090201c080f000c0f002d044140030080c207414620300c803508807003140c100d8040409200b02840401c510004844022024000503400083c44020502c602024034822b8207825002d01d004000500120f401c50300c2459100203e60750b083c40c1c2c60080c1c4041303080c0b0146070302d10004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 47358412 1250 47357162 47357221
    0x21201020c0709050a0e01050402092a190801050109120602070503120903041406190f030902060d0f0501090b030d080c070606090c180b1e0909070302070b0f01030201020c0405 77
    0x3c280b0200c3e44424001d03040380c181041a20a19030030103088880917034019511007645400100f4171054418000c86075480c0011405036084242140201c030303040b0540748400e5250840300302c80c603981d004218900412092a05100c494500540c00080903801c801c041c02d00b5800280c0078081c07080c00c100300d9240002da410300c00311914140386820f880750006e010300240880d12400a08103480c00300c0503101d20000c40030080c8640714451205442010500c42178000741600c0350000005a41e546010748100ea50240001c120846e02c2180f820031030f1070581003404054070381f000300b800ca5140080c24684640700c5041050154031058140b0105018030800140490306040e400f2903901e485402456a01800b6146d0000740000751070300c0400d40c400b5018114821005004103242c00340c410424501800c03040188929001e103510221f800b21000300d500c640801e400103068010410310942c440d0303102c1c2440d44009019415940001c1d00c503548065294440d41d200c1010403200f001d0750f11a4410410681a03101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 47359662 1250 47358412 47358419
    0x140a03090615030803042006030f07170a06062309060901120603052118040c090801020403060203010501111f05100b13060f03020711130e0304080c04060506090607021201020c07 78
    0x50740d98000c6801f21202c1c0c60107041c3c414005510243c040c601c8074000e244038116515403518080d2940001d00714010416861702e070340d4039110042283c500900d200d01d4080f5402c0c0c1030400107045009a0403200100c00e1319403800802458405050b41c0c0103500890300743d50b1316641140100c480c0030022080801d014076151000081200025444481c0c000c48400b01c50706005040c4200024042e55117545061070340509901128170303040d8484d26059240d401c04202c034546580010342260480e800c22140c070383c6c2c0000180241d603088254076030244e02c1a00104120724401c521f03110b5011304081000030140d2034502086d004038540090001524480f00c099844440108140c800c00d0080d108010104d41142000c101075031090080b2030400d0b17080503140c41070510709000c0c490101c1d000e04080004540e1103054110101080c40248000c1c5144c40c020011055608104400c5030b04c590b100714401d0804100c0d82304152a208141c4003826012290701c5030b030b1195100d043c1d02920400a00c0d070440c0c000e68a022 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 47360912 1250 47359662 47359673
    0x1507030e06070507060b0d0b15060c1b040506060403031706060706020703021f0510050607021305070c11012f0c060c01060603050603030a02071502010204090507050316140a0309061503 81
    0x2820071324051001400307001080300902c00b94910010014140840d000c00081d00003200a50150288401400c5103107050020b107169801c028062010040074030500c202032503d032410740038446e041075080b59024a030038039594001d0148060040700010142110000900c1599620f040c1c681c0c82c0e8100805543d110160f2800071740700d02c06e490100c084200c90719180c0700004003a100d401d200300c610481902e9190704000811200d500800b008036400820400a1120b0300c41074002c4500032401c2c0d0701c445030003000d1880c1c800201d11130081c1c0749041000144001c031000741c07802ca2948034100c041d5107034090078000b210864103106c003000386540c103d80c0010b01c075480b140341540301204403641941c0c100041e44643d0201034403403066156030401640001803c0c020310007904081c90707507600240001407500343d0300d008150680d2030444818000c82c0d804410400c050024245900c400500c81c605a00000010344101c0020300030200b180081540e42c0201c00200b107140da0040e0f2000080c0f440032480c6540d00c0c500f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 47362162 1250 47360912 47360917
    0x10c030309051203070f02010504080901030209150d02120a020c0a0f030203090d030206011e08030702010311070606060e0f010201020901090b03071107080f0f0f07030201050702060403020d0b041209081507030e060705 95
    0x541780010005019a9000d078030600c02e00340699442a1080c0c17410640000440280d00701109845d4402c0500c080c034000c9080c0040205401000f1240c0541c403959030b100b404003441e6000b0300b0351741071600400445009107408519004180c0c0d014101c400e0f00019420704a145010341801550810000c841c41c10038036400142c164100d4205084003521900d44e031303003828490390381c502c10f0382002d40c4244010401903000b50820201c0b4000d04003e641000c0f0351b502e42d941a0307100c691103540455411f4229036414140b510000030310200c03c0c0003d51801031680002000142148600800081c001c004180200d2050a100700b1070351040003101c0c00d1945940905444030200e5414038400e206540c18100b0800740824071a0304446000c0181203454a540c0055a965103c0f040c2282e11260400001c40166101c8841c8201076001d0113001d21945068900046145030852540045c00581d04040001035000165040314100c90b000070449501c80f460158091709210700307501d43d41c0c0a0001048a403607845000b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 47363412 1250 47362162 47362171
    0x30c0d090b0105030d2c010c150b0406050904020612070e0409030809070602010504120c02030709020f18031f1a04090308040c0905070e0d03020a0c180608071202010c030309051203 79
    0x351a0111128075041e540790940f580c01e0100c130a0941d48441500c02c805081e81b610700018104a10003580c00d43d105000003400340d4000d01c403a039a8070f94881450600c3e11400c00505406d07500303800b90b41050340004078240100e502040500401c0000250b01038451003428000d118050024040c80c1034601c6d014140ca141101c4c4840a0312030340034005082841405201d0103290400d00310f084400701d42d0400c4910740320b5120705a030184244c0000141d402c04a10040110b80c0300d6884003916007201b0b00060050fa41d440d103140e482079100701e6071044402030006410400382c02402000809803004190715004869002c2003561040c507181c0490103154018000d10b12503842500d03d008440c6d140c0c1c0c050401c50300103580c2c88000406000020201d03003848407038041054003d00454100410654441814240380d422510364017000e07240402030b0311210b005240113001c48101500c1d01504051500319140c40d40007020781000940300036001490b010380d00c1108101c0d0002c040d204801b4105803040d01c940c2c015107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 47364662 1250 47363412 47363419
    0x11401080a020f191803110306060a061b02010e09040803040212030313030f050c0706020106080118120e0a081218010e1003050a0b0a15030e0313030602030c0d090b0105 74
    0xc00081c003031200d07032088500414412250606080c0c424500c1000d071821112800180007207068a131002451342c184c6480154483e00c510080200703080300f81418514007428903030162402c0003007130140c150040850000488081001c000c0481e00e400100c0c1e40340d803400c11207a04096540140014011500010b5118074000d5404804c0195400000c5540c1e00c4125400c0181841e00701c0c4000000348964000071144190380b400905102c540c550660601030a5800b200c05070f90740c8c40d400c00002c0028000c100240d1590407103014100065111929070911514100c02003100030048503150303070744005c1003902424040040340d05100d2114030315001d03035005203111400e5000401d041940c56214030300300000407901403c6032000d5031080134190090100505901c460720344030034020802d500c0d000240300041c0450150503c0024a041011301111804004c00003550010440e00c0404a00c021a00702125440140145c1c0d0b42d84001c100262801904280d0b0040c90401c0301140510030809900c0d030507101c0c0ac4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 47365912 1250 47364662 47364677
    0x414030c09090a080a14030a050114040e03040504020c010e0d020105041b1211010917030304140c03073609021e100305040204091a010806070e0d060b04060e011401 72
    0x58100088007800301d50018803503000052040004a410020700708546445c282084018110503824855400032241c81242075960750042258101070000e03082001c200740d804024513503a80d5040b035140d2160b40142406260006007140f00a039096000c80203200096090301c0d0042d485280c02406840142d07001d454103042c01c0b00e0b540110204c0c0c03944004070b03141d42d0074985401d09260758402250700380100880c140b080c0080001070001d50b006000a030011403031f02850381c81c078052511108a480420401e5031642c40070314120b042d42c038001111307000d4400240280400d000509046840300646c0d4201030030900c0340c1825491070b1111034110203c1c0034421982c0600024002101c4c1e05012001025071f40d015440c00e0041580314060381c00560000d001400115024440c5d4560070604c954148c40300b4107116100c4010800c1c090300703200c0e07140c004445107050603440c3d2001000410100300c244016100ca65103076904491541c4a5009000501c9441d03922a141c0d0380d0340d01c0c240041d209546c0d046011403901c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 47367162 1250 47365912 47365933
    0x807030b0a03020f04060320030f070f03080d0e0d0528080a0f0906020307020606010f0201090203030301060f0315080c0f0906150f040308190f020a150c020106050402041403 76
    0x64090030000c8580941030405607441c68007044070501d070052050390055a11003010003c18400352601031008203904108810f032500c2014145022441c00c40b06090f030704991004d120a019070380c0500b0459400580d11a142d01880485000400e5014003000e40c40c4900c0c1004505940c101c8003400e195207c17030010f107603040e215070060012440c0b407844846c00245a01d00040c4030600c41d6001386c4285007094000a441d81c00351751000c1c2281c0c0305035145005640540b003000860340e400403c540c8800403920007808250503981c08a5a00d02040c000c160500000c00c0845410600c00da00011680c901c2181a050b01d030b0351004801c7d01c9a4001d00c0c01d078064052440c1088850805164981c02000084c1c0304c001c120220503800f55a6400c0001180040d500c204400804118000043c09041141078224001401c007001e001e0115203001081c4419504444920004070314841c914a018003451440410b1003004520102c1c010a083e400071a03100d8400b08001c00c0d1410180540000d1020503401c0710b081042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 47368412 1250 47367162 47367167
    0x2061501020f0d080a060803070804050a0503032d160b0402190509040f061103070e130902010e041d03130306060b040f030f03050d0501030501050708070f090e130606150807 76
    0x8070300a190301c0d804280b402403014800c4c0b0809074000c1c5460070001d201c1e81c91790340407401c1da400840140c070421008642407202d0719080130a01c008100440003903103004880c1c06400100071211b049060002026100d011131f81c0d0100c1d01311000c0082c0383c2116810b400301803610036175401d81500d00768003800030300082c85240b00f6001040d1054410040005106c0e551701c3d540c8141c00540300034110313580c5407209444009a025080a94005d03001d540f20b5125030130380101402007451041451441140c2840a10720260740c00100c43c080c0780c0300581e070101d507111615100c9071038100c0308507580c4000c5c0300000e0b00030301da01c681d02c00c1c403801e480c4030314014000150b90b45000d002d24000c0e80254684902c3d00e03102080080e40d41c180d01034105200303042081c28600d0544081d8101c80c000d9105440d00d9454000b08405190701c84802c070b5014845041c04001c2c0c01c09024000c00801c0036000f0345c0399a92244001c80c4d00350350748200f000710a0345e0010342409029180d0b0031800b5803d16100e94000802c0c00310300490541030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 47369662 1250 47368412 47368423
    0x30f1202070f180207050601080a11040606080c0d1508010c180503120703020705030304060f030e06010e011413050403090602070e0903030c0906070f0507050307090b0303120c190206150102 83
    0x2400c01e02000c0c2118204161010001201450b2030b000c142e08000e17142c002003007032145a00078180c0300050002c0750407034140400c0a40c1c4060390144218a0701e501441504e4204000c2c03500403c40001e420b40355407a000084008001000301c5060025030034034001482c42d01508130007916081550313480802c14a50844500050580c0650740d81034000400700c410040c04400a000d456010f8412142e81030303501c2000c242164440d4010000082402c0c1c00e040d11107815000e6010302e54094030003880d41d9850a810b40224040c18000c2d07e08103074881c03400d80d949942740790004c1c0c1c281122400411490038a88bc0c044d100403850300c6550058015104001500012482004d1090820501440c0b85070764008280019a0107070032403a0b030084c01400302002048000103030403c120300c00c0d00140407607401c00040600c2c0c801150301c03501d6154200240c2aa0a4401000f654058900c0062640311900e4101c0031100600a12100c1c0110003010100d80f01410341c0016100c1c0114110402450b036130241c4c0d001240c442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 47370912 1250 47369662 47369669
    0x71b05061b0c0703020d02180408070204050106021902010f0201090602040902092103031306090f061a06090307050409050a02060f0d05070c0803060f01020c040c0305090607020d140304020105070606030f120207 92
    0x30b80020710f081001d800d2003107041040300d00c020203001c500c0020600107480390070190350079102c0c100e011910741c0450401c5e1013600d014000500080010b803228800d40a10140301342c40081c1001840300e0107005480c003d41110b103a03181c2c814010b540321501c03501194000d400000300705100d640f200d840d40100f060440725008100000c0750165195542e02000d40c086100e11000840c2c0103542c80121b0000b1920003171564055500c5040d0118122003880b11110f075507801061a00c0c4982c0c0c04014030b5010303650002c1e840382141c8050300e02041500e85818442e003000c200020180d00305a002440307120020b40c4e24010141000385440030031aa460f000801c031100200d0040c014841d40c400c00100301c0c0c9140400c101c0320710305014811900100402000701d030555100101d8580402c2d111000d12181d0780e41802040d6204c91f05100070690241c040b00006c281039140241e98503608070000104096920440403640080d030841001d010050340c4e07140c4803204807441041560a08030f00d6a0b0909201e20219030803048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 47372162 1250 47370912 47370937
    0x315010e0406021e0a0206040203010f1107060e0102090a06090e09030a0c080d06090e0c03010e0604051e0c06040e04050c0a03080901030b120d020d0f02060408030f071b05061b 77
    0x4950300c6a90b640700079408903c0c02c03190b500840c105001e0032010000180503c0c0516405443d60303081c94414107003900c3c01d20000710645400c0040e071440204038481514200c44d0020340100d8280141d041e01c0d80280320f4a1444c5401c102042400318820381c0101000c411610b007801d604185540d00300d140b90720384c082c3c05041c1e400135400c1c04007140800d000c50003a02984280c50000580c203591101100304072480d501404103540c1001c200c0401d185800e204003d9010b9581c8050320b0140f8003555034644850f0030f2700048000c019400441011400100b003415000d2001400e466521a1180d040044100088800b12a2071040003003c040030b0034461001b5048903032081446080c195020015005044481d080c2a04500100c0010408100c1000051103270405500901040000100002c12690416508800395840541404009200401103d50080904001c40266110700e0f50407181c10800c20b0107502a00540351f640d01c24403a010035003034050b106e1222071404039848190f079881c20b03000e0030103031205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 47373412 1250 47372162 47372189
    0x12040605031311040504030915050315010c031707050403060614030a020402090d15090c0b0a02061518160801050a03050715031803020102030601030b040e0c01110313060509031501 79
    0xb0003000e100e422500701c500c624411004404454045411904111030540020f0442a02001225040380c0c10f6401010b9900c1c103645145801e0b40c2111050b241000949c1c10059480960402e040c0308601c40720349174071014000c5200c6d00308003500918641103400b0070b0b10b0040c940000068021078041420110300c1001d03010b003040c060309400b04802500100312840d00481407049600004043d0020035074420040440065100e5440c100940d52400700c0d040301c004d1450805c5440141d50300090141da1020030910310380c1180d20034030702040c2489000d032003d00301030401d40140410b007020070003185c2808400399035103030b1581e903104200038940b01c0790b10002c0c0850f00705401c244010001c4401581800b01c5500303000c5900b4010700b004400710808802d081c1c0050358013109201c0700d90307854020b11102c2c84045606002294400c8200398403025840c1000d41400702d1200385058041d42031042c5c5200c400c0c04082e0085090b80c4202c0900700e984102c440e00c0c880d0241820f20040c245980700c12a042e07615140e001c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 47374662 1250 47373412 47373421
    0x12a020606010804080d0c020304031202061023090403030b040b0a0b0d0e0102040305150403020c0a050906010302030a1506030b031501060203040509040c03020301050114040f0b030c061b010c020d021204060503 92
    0x44007000041c1c03042c4c0d0b5201d006c00403506c4010320741c0100e06252020768011640c80c1d00d5810000101b840280b010003c5420540900c00071040401d554002d0314040040260700c0850001c0c550701c06008000170b02d40001b82d000c200014140c0517800b80900407400c1d01c00b8080300c0b1b401c008101a0f82d1240c0a266071100090088001d001d80e140d1107000c0245030003000525140e102e071201850495000007214810036040f040200f0546d0601c10345440c0e440c15121540403a091600007079034003c00130700c85410180d0102c005a150406604020449007003240d031590780a8641c00c000b006000804101402441a611b6440b01a1041c0765111704035980d903070140d41071a0418080204180300504250348500300d0503800b20243e07400b846803500a202d800c562003d031540035820f000c1910b21910150943d2807508401892603140401e45034100a4111155555500f0170100440c03040050340f8160501d40c68490364010140d000190345003040e402c0e4003102d0240c060240382c90403621035800303140b002400600114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 47375912 1250 47374662 47374667
    0x71a0402090c09032b090801110a0f05090a0905010f060c0b0708130501020d050106030b030c0a150504230102161203050f0f0c010b0f0301021e030405010e0a05012a02060601 76
    0x101620300f00202a514135280710180c1c880382c0301c0e880c140000d0083c06440d450f00450380200c007800c000e1a100c0024850a41e00c288091421b004545020040c8101180581b40c1d0a03c40d200301c4a62050041803081000d88610304000100800d0060b8180e50280410103c0c0560003840c50003011039100b400c42e502075443c1c05044501b20009020f16982065008000000810031300103030070740620078000014a580b4150b402015140300c1800140a50040584ea50090b110b00c20844c00b92120310404003000c00404400712400c2c89a80d01c5802c0ca802003d603403100c810400c078400078100d0008d0f07084888001846854846d04921031080020a0300c0c80f8540000007409a0050809000801625824503443d100190704c5d650000101600301c1c0d5403030151003804c0c42d0540c003043e0384241c150021400c01010040004804c40c50b54401e512100300880000c003000b00941010710403040c81c00c2034508100345d43c5460780c00784c5120618414011a14014519500c0d6240c043c0b00000085500070302e00b50700d809005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 47377162 1250 47375912 47375917
    0x1030f03030b060315030706050901080a050613020a0507060b01050309151306020c06040b0106090b090d1127011e0303050c07030b010b1309060605040314030915071a0402090c 77
    0xc605040c1c44401940b80c6940c0d0b80043c500ca072601040b03448007002060200b60070080c0a40100c4184401401118a942d90100e0000c4d4003000b030480010b4561540c2c0002401c452003c218041c185000007100d4030070700e500001805107c1d1140200b4130400d2f0303c410040d20b09000c11500c00300c50740d10000c05281e580c6888500c864000300031171030460403015141c0760003059900c4100c183c0c040d640881d0500080014101c58940103040e01e16041060b54141844600d041c883e68034410301c1050503140803828000304046240c2c507072400415020306c0031841001d42403c8100440d14840d491004e000020304018004c010039144413190401c464000e0969405407015001803031965254840c4500c0480000c14809a1030301910002000d40d482d1901503000300282882da400c1403d0a40c1001410403c40f9004070580c0c09981c1d1100b422a07407150301e081aa803442c010008503990125510281c0b9000240382001441c205004510411f503403101d0000c00010b11005030707002908a0025000030781e035848c00c1f401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 47378412 1250 47377162 47377193
    0x9020105190918050f0901050f0a1d060106090e0a0e06190902100201050a0c0504080703140a05030a0801051011120c0c0d0510050f0112060c0e13060609060203040e0103 74
    0x810002c0603032100b00480b4002000344900d08201c1c1d0303c80c24852083d02084d500356006a04100900c9180b03001500c180d51580c024010040c800d071174420000050b614544c1084c41c2c1c1030143c0896403290380d11030000b8005500e6202c3c8201d01401c0780c022503112100c3d40524009600c1c40c100506a41c0c071501803910482001110700040140e0303800103840146c0d0341000c03207176011059500105007030034104119422213011903c10b4090010820042010f00c01c003044900c2100d4100030b03140604680b4200c1282018140d200051240c000000d14805c11500040e515042c0ea41c281ea0001c0d0104c245d400540d441c500604c048001503011507a8081800040b4009004004182090f20200310310a0017246007500204030480700e50304010943c09a00545104490b484144082c00481c02d5242a1200c5140c61420402508168444d01000800382c0941e10901803084c02a0080c8042d1000b200c1c2e50005180d00d01418000807443c5400054951000069400f90307114403540300b0840c2d19603a28103008401601 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 47379662 1250 47378412 47378417
    0x1409091c110a0605090105070e03060a0203040203010e240709180c0e0a060c06051612090203010204050d030c0b07050405010e0d02040f05010314070602030403031d0103110408070e01090902010519 86
    0x80381e0000c100d400d0210392101481600d0100d002e05280d101242500c80003030490342005101c2200300451ba900040c00c4c4d0308180003060041ea65290341c00031901401c0c0c40d180c02d14161059071000440300104000b10030b91a01054189070098031380c3d40b4100c50074102072140354151a220a159146800c50394003030214000300341412541c02800402140100900750b01101c080ba20240703000f014010309000302c0d603004800c001402600c40300e01c84060a80c12500d074001494654940c14074045440175412580a020002c01d42030008255140044c8140320f028400c4500c0d00401c03000c01c4541c1e000d10242c4003500c00c16104c1280c1c040c8800c00303120b6404507604050b80c0c0140c4034101c0700c5c103030040c03886400d001e14000d4800b042e000c9821941f0903d0071903180e01c50b50441d4001c000402c0071a512401c803912540914800300650080310004901900040041d5140703050002400240c1c954000b500f0350449010040140f0783c0d83c2e894000000711014024040c2c00700e1810030481c524000e400c14040c50104150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 47380912 1250 47379662 47379677
    0x90603040b07111b0307121e150207080a030c030b150d061d010503070e04120305090a121e0306030515070203040f03060c030b030102031302041d10061409091c 70
    0x1d0494520b4a000100303500aa820307060f40f46822800e051000c5001f03801541a00c82210b00345954030700148035500c1455054400103625101003226000c0c02c4801566500c0c019510341020f402d1400c0d07181d20200c4420040392501c040d514030540603000348107a03c50010716950700c00001da2020140b61b44822044115944e503040b001c83c0500c4081804031950000c51400c910b40c0d0704003802e01d49400c90a401203c280b802d45020080090b88c07140307403942e039501c5626001c5182d8542d00c0d0f440f032a100424038010407244003042e08440055000d80c034286550041b0315000e2040045040660448800740405040c0e5000141010710f040a0081041d4002000d4030489280c80d0f03507003854141004032900110b030440d0b103410706010b06030703850f02074a540070800b20021440e5041c94a00020040580e0303900901861303c0d02d403400e03180b5041011840f012801003082d50102800c401415000304040e015404c29004000d01420700c1c3d08156094501c81d264050043c203400658044060840e64008203070410003001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 47382162 1250 47380912 47380937
    0x22120305090322030201021615030207080712020c0a050d05070e0c070c0803040810020301121704050406030309080111040e0f06150415021c020a03050c030f070521090603040b07 78
    0x4020000300c1646611590043c40d0940c0b00083c14070307041012140b5074207440b41c404c0c0645e40e030b603021070070120703c60742401640c0b541e007890700302e0721070080301400703081c0950402c108480c1d9038010513a140c1055040700c440c6401c50700c607410480000266280038000342e004035001c0c415a044900c0098210007a4100181009107035a16803040f20155040485d058002140400c02000c0811480d0040400454103500710b40c140700c0b450040700701444010385995540e0382000c03d00c0291350100d402503d0007610034002c854503414040e01c2c541d8244a00c60b095880c00210505c20802601514140d0700c070020280c070a9191113412180c00380020781101d82c00f0810400e124030743d15030f0100620040a805e5814010030714040b1000c1e0816000b010003100c1c406160702e004000759804605404810742c5400c14584504024454a195015540200c44800400100d41c0d00340b040004214001c5001d01c040c0b80d0030008a440381c0120790280c9540e068211000f440418001400b80c02c04030360281d1796244c0381d07a10009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 47383412 1250 47382162 47382187
    0x20a110a050a080a030f050a0e0d030c0b09010c090b030105060702011d0603040f051605010203031f0f090e0709110409090302010b090a020901110c06040b0f040f0905221203050903 79
    0x4483c0e01c1600c1c0341c0d11060392581015007000017030740d50140c5400c200d4104006114081d219030544001c0701d115110310040902010701035400480700a030005a6103242e4076107a101c1a00a14814082c10041403400f140001c0381d05070b5004883c10780e00050503890030000164010741d10a11059003618819520343c900c0e88160f12400301541c4514000ca080c0c21084420b03051803401d0100d13a01200801da24900c100b80880e0740c0000c21260020807000c0b100306d80c6082400b03000f040034003503000000303001054180041d0080850b0041b07044c0740f0b0314100f0384100650396051642210701c10140f4821100040c03008200c15070072580304406590007030002182074411171001461500085440c8410941d012920000650348100d011102480a034018a075020b20360380000e030107010b1481040e2032004001411000a0301102c1540c0c024608044c4220941c0d0b101c2210300e01500b0100e4410f40302d901481a920703140e005429a440e6016003101420340c1c00100407504401501c070040030300a1510007007122840016 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 47384662 1250 47383412 47383429
    0x60409090302070315090203070314030c070806070315060804020d020d2901050a05010203070605040f080403050607030b151c110c06010905060103020a0f2106030602030f07030c020a110a05 83
    0x41c4030b40c0c081c1c103040e030841c03170304a0340101c11060040109203000e84400041c2c0f030000b03003041520303004800340320010300d02180e41c0d24620501420404600604a001078601c400260540c000d04542e00c00b8450200303080c1050411942c5445040300040e265400300d0003605166482c3d210a03400604009100d4072242c0b110501d01032080603181020160780310400c40070240d0054603015110458110b0315031458900000e699003d811405403000359110041000c000012840015a0364445c142a44a598034140141c80700310444810f800710303081104500c1c035890442580480401e0f005401c60510141040b54000380f100f4000600c5001d40c3c801c0303600c2040900b00084d241c150300400040c020b641c1052105402d9801c00340c001c43c10f02d4010303c2078070340f0035402c4407a40a491f4036600e8a01d035107421402e0416501e0340c03504103140c05589011408024000190011440b0304410a610ba64070b03200c0400490403039030040084030040c3c105206001c009100082c51f007121303030340003040440000e8840c000a240326 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 47385912 1250 47384662 47384681
    0x3050a120515030f061005060318010501060206101a040e1f090603030e040c0504050907051207050d140105130b040b10050310140d06020309010f0c0207060917070b030402060409 78
    0xc0300c03080b901095074074080280c6241d84000002900c460704101c40491103050040c02194810000800002c10620380c503401b0350300e0011000000c0c0401d507074910020307481d007200ba0307000a00440442008a144522055040300c0405800b0159152601d8001003c0300303c0701c0a840c0c0c003008004403c008d100380a030460140f001d050f5034500010b2030751a5103805461031044407442805941081c20100401d80c014040d0307421034106841014955450342d0040b11584140b0b5030305050070300e12206120b01c1d240d11a01502020407820b00c2007000c1403040042c1c83d0103860902c10700354490a20310a1944010f200d0304000300088001d040400e82c0040721000a00348150030240c2c0c8000744000c8100a200d204049108004181400d1a25003000500d00450030030100e46101805d125000000704001e0642584a41652010488200040c940c14039000b912220b40d486440c0c0006c90090000c224185440c2c1107060201000005001107031504009008580000f0300990b1310080c24807001884101c2401008100c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 47387162 1250 47385912 47385931
    0x10509031902071202040b060408060109090b0112050d0e04110f070302010b010503010b09010c11061603110c01020601030609050708030a0e03070b090306040f02060c01060b0403060c03051303050a1205 88
    0x2151015900c245012007440c1c0e5040c1198800642000750510841d203510300d0b00d40603076002c1003200c01031010030020b11407076010305500d12620000085c140690b40c8203040907440780d2100c08007a6a07800000d264030020020140075178205601101000780500800b4078407441c042c01c0411050428030040c00130360054840200c81a90014032641003550a00c150701d41d4440c00d01f041815941410b026259a00409810f03a05225015a1a405101c809030340320603401c10003401283d13205035002e0040b010740000c0742d0440104111116690f02c41d00f01003861050490103900422103680b0715250080640b01008059825015150012652000c00d1000b003201000a03110082c0d542007030006e0514000c2290300014260707409000f40315a666001c5103554216070002d005843e14415070000854070710408050030381c2d6629083c1c1c00110100f450010308100c900a401c20032840b81c0c20202541943c9046856000d10f040710a002c0340041c0c0900b014000d00c54040c90f01c0d43c5082290340c000307021140c080d201080d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 47388412 1250 47387162 47387167
    0x612070306020c0d020109030804120e09070e040c0306120602031503030a050c120301150f020f010c03140606090604050d060906020310080f01271406010311130c05160206090301050903 81
    0x10b20300404c025400c00d400e02031000304130202c080c1c3c800402507000035100409030804e40e0758502003244610940c00032080001c0c240fa8540c00e14200140c4603103c0703d20b0150149080104c032070465400f0380f19490031114030147d0540a0560ba0761400000e500003451810b80250700381c1c1100103503c04101820795812151612660b60509041030b0345002a04091426013060400050152220b144810039002d41d540c100345091581c103a400f03a0030005c5103041c0800b20b41c6459030141095a06400c403041810941001b42d0058480b102400038501c1042c80b06a00001c00b004200010308001c0c040848040c01428002011000317651000c4c01c0c1e0307006683c0916142c80e41c520610111b03205001e01c0c0003e64101000304100c0e80a0503503c401400e5000c2121650b042c1f40403511b0500107120b03c03c16280c94080d0130b4980b5503840e460400c0c0b80000490541d4020200200c010090004900c101c1003801c0b069180c590808620010040800c034154500700d0700300c007007801070b084552000d000341d600400351400511f8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 47389662 1250 47388412 47388427
    0x60801030c08010516080601020c0910060e0d0c050609030312010801151401090603050601050408010204080331030b06012601050906010504050913170f0a0201060605090f09061207030602 82
    0x45140080e40c00000b0964588800d1004103001c9844081480032030703081c007200d50303620580180c2c10724101c5000241c00c0411603041001004400100380f0644040e0b071145075088070000140540e8528200d401845211101400c0c40f01c1c1c60044064400708100404036450300e1616914506000740a0740091000ea440300120303000300c050200c0c090080c04240c00400d00e0035240c44002040080144180700c10705644001090080c0d01c00c104403400341041400955480d0f503945119079890707001c1e24682000d0702d691080400c3c09200000000f50100744185110b902d5800d50700c42052a90014141c00e05210800040340394106111090076000d40c08443c040d60300750300d4401400b034034400040840b41000303420441070000341d8802140350380000300b10030700d1070034000a858940c10407490507068030036807800441c00c0e003150145440240b2106c4810760003400f00540d10401540c01d8020101b030268401ca10805032103003404c003008200d5100d400144421403034041d8042d0706040468071380003501c8040c0c0005118 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 47390912 1250 47389662 47389673
    0x60f07020312030423010f020f090906030a03050a0f030f0f0f0c0927091407060f080f0f04020d060f0903230a080a02040320090a0e060712020705010606080103 70
    0x44825402040c0b8914520b056074590549200b1310001c6035500d100e083c880303100707800300750302540b2251641c01c800c41d0340da038031201c1e81d0246030020051a4031901030a00010550304000c121a03010a40c141c071010b04190440e0001e55800322048004420199545a5080310040354020f50440e503000c903000041130b90000b4801029104103040c0c08041c010354140400101900382c4440d42500b110b0384050b40c3c0410040401d0015080d05640035007140940c911040b410080402e8100403601d07280c8401d1503507404520b00791034800703048450251a4054900040e8141001411198090f100500f2000201110398a20080701c0c600741c0104030762a41e0f4507900d002c0641002d00b030785c101c59804080001090081124003000d2003034500203010031840801003002c141d4690181d901841d844040034040c16a002090341d080c40718080001d215003d00d102080381c4581034824041e481c004031000d842950b0b11103000340c6818442c2c0d480d42e0311060b42048035030003069003032042801414081e0350b041c50952441c2400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 47392162 1250 47390912 47390923
    0xa1703220f0b060d030504090b010c0c0b03060901080a0201020703060e0f010c030b030709021303060b01050706020301140414060a1401090801020309010b04060602120409050a061203030b10020c06030a0207060209060f070203 98
    0x20540a8840701c000741340401e80180564003181d03850403012914464902c01240c00800e08038009000010075a80440c1480d11f180141d445203a081c0c2d0551196aa15a40c15607034404681004c0d016030400b0b00700b8004942c168124400141d200b8080f1030040782141c03081c41c00c54994461402c00243d035a184080c1da4601030003d8401421150815810310030446811069103110740710003070800b503460103244016400b074000e035502c59402170703c119207a41c1d64652050694002c840c00034070451400e000719403e01c40b074102d03140c0103203405050781c11980c1c1003181624544801c40301e0b40e810312140d144005403000d802d0000354840d1035010b0000c240e0502031001d000564040390000c1c0203640000350315010060039a4281c60468180c56408906a111110000010031590308000c60240082c15008107158060b04000c0b20000700352141902c6001e96201203071030319a21110164051400c101207503503160180c014144081c0079120052a0038142000a071440d0301079001300140400c04200d8006618083c441d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 47393412 1250 47392162 47392171
    0x4120311070302030f09031f050a0c140a08071803060911030609060c0a0e0603130308010515070201080405190302060417040f1707080d03020c0606030a1703220f0b 72
    0x600c0390a1603030742d680c065180e0258000c0c0f2600d400002c2403218482e507003002020b5210f01c19080c01140d42c4120400036000d010111000a07141d418030b101034074a070b40f09000600005041c0c01000d810404c10301000c80710483c0180c090b0302004800602045c0800940074003400441c03013128001210308007807400052500e04001000c1c440d030003150403c21900c10101c3c01503846031b8074950307199035409030800648200d2403049482d508850302004000402480702c00000d601c1e8002e4031003a00607030340c4104018200b480c0c58400b000e00c41040c45964015400340c98103941240c400e5090344d541500d104140f107134602040405130010380c80b0038248400e004032080655010a40046014640303414440350250741c02e0140b00d01e41412140911b0130300b50840921007071010300342410940d031a00c0d1f000340009000e508104150a018000c4402081051900003804505150700c011a4420714030000e041c0042504000c003100300c502c100003c001044551400d00e240405c0c402d00d07258084040c14100030a42c0000100b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 47394662 1250 47393412 47393441
    0x90907080f0a08121306051e0604060b09010c1406091e010209090105010c050102072a05011b060b13050702030304060b0909061f180e0f0d121d0303041203 68
    0x980c000300c1e003001c00316201000010001c400da522001417000010b04401e2000e40b006160409020044424a0b4816900e03103030030003200202d0300c404013004200c400b2803180d0700420f80c2c10400d0024550240312031041d00c9000d10004007951800200541c01c1c582d048030001e41941000c00104a0040e4003080300042a82c104021818071100f18003190014006001e81410f1042e8201000c04100702501182c842070f5004078400300c140380710303550a030103901d20383d03c81030908803a110003090551164000380c980010a010048a462460311450002c1c4045603840c0e0304095140c190f8100d425142c00b034203000c1c03045680210f5580c41d144c1450011904c100c0f207003a1160b10580184030402e03000048840d000060040c00344000e0900d40001030820701503030301c050910554200762070b514035010340c0025803203d0300b0b00c02d446124014006c031940720b0309144104004985c01280c50001680143d00c0140c0b0755005402d4072410071004240366165800c1142d007110031200301501c0e4040654135008111403c5940e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 47395912 1250 47394662 47394673
    0x90405100308072013050417130915080604080a091d040201030e010f1416050405011409010201020921011505010c030e0d12020a0515070c020d11090907080f 69
    0x41d40d40c90030034881d0350790281c2031900750503d40c00b007030b04c1d151510307004604c008114111415980c0403c0300540000c440641c1d404020141d03208010f4014001c0300c80c4411800614081d203800c00d82550020100031401c04000328141e500070500020400c0301600441c040d07041d01d0340740ea442480040a440080d00040160758060700003400d520210040260410350908001c41c0645d072480c00c140c010b110340ca4803a4120f034140410140c80c0e1014100041c020030000c1903d0111001d00c040a407a5031140c1d10a0900240c2e01210039582600440050030340d00605100251070803021600103404120251400c8189403102c2e00044400c0c41c0c05d20801d0740a101c06101c21204030b141000203484009250000742c184900304695501655950200d000e0707150b400030003584103200c2402c0081d030340c84110004035054420102201d11810001011501c1803000d80d6603011481c845600344a8480f40001c803c0351000714180029486a440c1071b200392041048000601c1c01c00c0c40c0c03491b41490400e00801054458002e03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 47397162 1250 47395912 47395919
    0x813140105040308030a0b1c0201030f05060319170307110d0c02030712080408060c030610020a0b06060a0201020d06030809011403010e011e0305010207060603230714060409060b09040510 82
    0x16003070b50b003120380090358161281d031407400c908082c00c019680141c4c8202c0114003400014541c080c24030829000713a90400400c1100310380c2002b151303c01c1d00c9075603141e800100001c0d00000000301b140c6101d44100701c08429110558844d109d00d4006a944401180304490f06001c1d061041140e0341d1840700a190036011441d0395004240c581c3e165000d4a207048c40034890701400c0c07080303480854000781003000442c0caa40c80c0140f0303440d0315038000307030b603100c1c890034141c0c00000c0c8862002400c00d0220b5080004440c051f104e281c20890306034800194142595000c0c090090140c04902c01c1c40020750161001942c0c0e10310180c0010045a010710070400040030504c010300540e4000c20409040da8102c4608642c0096200103501c824081c65200500c0d641c00001d0b01c41c2000060f0f0050703801c41e0b22900000440c209407414202c401d0070103450090700c4e988a03050800021110309a2132007807220142000d032800361a4a102415903503e608a08038408002031002000c3c24540314103944280e1509020314842d09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 47398412 1250 47397162 47397167
    0xf14010911090c0702090916170622062408011e0f02070f1109011d0601180b0a020f0606060304030504060f03060504020d0c0305091b090907030c0308131401 69
    0x6150740007030040e4100400100a4040d400481e030a040d0014245426407500c41e40d52a914005007014003400c3d005003400140080c3e000c4001c4241c4d811980c09021180c1d54414800b48a80d185801803009030400011500072402d544509120b80d032030900051154289030b02150a004055400101e8aa01d0409010780380300c100c1c5003406407400e1503a80440c600c0b2481903110007901407090080e08000d0050400c2e0100302d13802c41c21a0702d42c04190754600c110b81c2c0c0c9094007007151903690008030000381324500050b000d40c4152441c0c44035810948690611588821500800307401103a041809a88507408410b02548100300896010f84200c403014038501d00741d68020071038000c1d403284c5010b2202e843c400402d285c1c0250040800341c070024100319190143c0071101c0001e042200e40700f80c04686000c0220b40d003080c0c00b007000c2e001c48400030a02d01014405a0503c0f04944000784000440d014650740400081d41c003808c01c90095000d8a01c19071a0241c1c00880350084000c0d07803004094101c0014910f9043c0d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 47399662 1250 47398412 47398433
    0xb060a09060e13050f01061103030403082208030c0901020705030a03090b0a020f0604060c0806010305010605031902041e05190e07030f091b06020106061704111206040f140109 77
    0x14510b01d80401100006400724101c020b400125529040c141400c00c07080788a4200303818100c909503914a031001114407519a01d0380310030b0302d010f000220400005011210040c0420000042d04507270800303a070a2580b201c01c8150025100150084000120000c580da4108102800b62408801510440c611030b540039051800b140300740080c0305000300d150b201c102e00030312501098000075010f03501149008c3c0703882c500501c000d4203480c020503c018045012948684030340c41c1691081d4803814615200d0580301c14804d1803808261a000c2d0b0200310100d10180901c111441c03800e00300c1c3c0d00408180c02e040400071648800a5843e00e0050b1450040045e503840c40841908442c0a04000540e0400c45490b00d000d406140800303450780d000d080e841e40c1e00c880b01e01694402c80d2541d6008001e41d580720710b0129940d4080003d4811401c120070007040c045a003140041644980003460070181a00f4440010f080c00c1c07040b14103650180d4503401000a208100085024621110000704000191540c4061415 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 47400912 1250 47399662 47399669
    0x406051503070f1704030c06050c09030a080c01090804030b04050601050d0b060d17190206010501020d021002180d0f05060c0901021902010216080c0a0506070f080702040204050406030803060102010b060a09 90
    0x11141c0707070f007048016020390081d103865001101e4200407441c00e42000741221a082000301d4000340f07807000080c4480201e070141e0b90800c40080242c030180946894090191300940708803081e656031220325200050035100104000d5124000d40e481c1d615040c101342c3c3c1024016400700c2d0003480801503000002d8030744203105520000031500310b405140b103400d04588401008038514041100001c107079400d040815031558000320311b90b08485450ba264001240c868802c1d503d040056480b01603c600c415009401078484041070701c45109200d914600010008070716040d090b9076100940c054030090240c00d000d80f030b0303104d0351f08600b45260101c0600002e66075034800b44506840d05030120703003504581c400d001c031015060600301102d0801e911034990b5a207400704008024441c1d50009d000013403509084058a12217600f081400c1c0c9001d6072038071010031950220030100d82c815800c0001142955491080030055030140d81455141e1500c4400682104d40050300f171441103d0902c08000b10035484102e207800d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 47402162 1250 47400912 47400917
    0x10506030a0b0a09020402030a0e060a06060c1502120709030507080a0305030f07020f0105100e0112032a050a0b01051806060412050f0601120c06050c03030f070c05010c030b040605150307 82
    0x21941e445203c02e00406519000a51042c000001d20a070752885400800c410b01488040d11825102e1800640803280300d0b100e00c0740400c0024998202103205400449668413004401510302000c103440c04078251411140440800c00c88041441842010040c00c00606508801001141201d4401501c14040240500b059001d0034000600c004e01c00e104600f95051140f0091180e404d1580c81e10b203055071507000b8010482d900500024461041200d0440d499402d0384542003224800000c1d520340c1149805015203103105290514006842000203644681c01440024915410310040102c01a801e61071030103000380743e0043c801540c1c1c070781c002c59049030110304071085000e203e450302d0b0741008003c100345900e5010f04c0000061812110314aa10340500c264003440c41c094403541d00391140d02802404a080342e10500005406114980740c1d15001081414070350f070301c00c00b559101030946800304140c5d00002c4d03d81c59503420a04041c000c0201a0108850803109441d8612040e0054013004122008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 47403412 1250 47402162 47402183
    0x61012020609010e130b1309170702120703080304060e0307030f0509040908030412020606010c12030b060f13060905041a0d020411030c03062b02010f0203041e080f010506030a 77
    0x140c0d40c1c000d00030480e200d4800740000d0003442017100340f10300510340c88260074045c64500d44405c1180c0c4262044480319640b000c40382c24002e902d416003d28542000200300e0300501454034460031480100640401188030310305203a501c3c40c103442c0101c1941c50700c441212542d4010300c02d00c000a41c11a120341010345240c070f07101e5180c481d0040020080d10f40340201a00e20000002800144210a0010b8603004820340866140f40c07118001111412903503a40030f0807088890788581070061081d00100c03043c1c40010081801d00040c41480c051591001008070141d40721b11104103c140e42080b0900014001218100300038019a110b91444504800140c0d100724030750051101117585907801070042807076203540c2545030303d41403041c2d03680381d40b0948050f8440c0e440340c1c01004203401e0240700b85048090301c003505c400c84c0c1600d50055a1080f4800d40700e8003035000034000420884040031408580c0c03009103418840c46468180d9036070074400a005003280690501c810800d43e6103000900c0040150b000300c0001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 47404662 1250 47403412 47403427
    0x903040b0f070501050106020a0206070803040c0302060c0d080907080a0303110c0a0b07030b060f2505010f09031205010605041206020f19030506030619020f1e0403050610120206 78
    0x505612403a04440209100411244401400325002d01200b5104000030003c0741d032582426651003d02c072000943c06a0204403c1000400c40800b0b950030034440c40b48075080503202d90000e40c43d90045c41004607650302400260300040d510020013600013008101510348142800d4440740c80d441904009828541c680c11403006e1541d82c42d044600e0046400140c542c15042ca01d030196088070182c85c0d070400a81064240e0b491440c1000840360036103010301d48546084001a0322007544030301c250450070740151030b00c2d108010510070302560308100740700c040000d0160681e00d00035001802040c504004a40303024014030074142c124040754281c81108040e050590b0075450243c3c01f0784122500341c1200700300461401401000b140300340020bc0e01940b42400b00b55191000c1c55502e0604445440b6904001c9100000308800d541c010800c240c200c02007145014402c28010204100f401120b000b4042c0c009000c006104003400009d0300102c1c600c0d116010603143c2140303005203c1e002040030740706100006826 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 47405912 1250 47404662 47404681
    0xe010c0219090608060906091b041d1c0c080909060d08121b0c0601060305070908030412030e0d030e0f01091d010317090a03060911061606060509011805 67
    0x20304110700c1c0d003882400e0032912428000c02811492043c90b4191090402044420001089040c440c43c203890040c0b0b0105c81461040c203401440c5006140c1190b41c2d02c2102c1c0c000d1311520b0035000d0307059200380140b41d10450454810071080c0f840004208010303d0003007000c00181b8a10894043c00380443d42c07944580ca95400203a0942c00c143c0c0300a0030004001501c03801110501e05052040c00d800700007080c058101442100b441c46003920090980e000301005104060003940596000b4490b49060f08bc103e0305c1d103103542e01c4d50307005030000448402c1e4208948201680542000709402d0150b131a200e21114581c0c003d0710102c83c80002d075118119030150f91100c0d07481500c200b00100001001442411410990042c007420203010640311114800a00003620300d90138120340c005103015000c01c1c02c50f07166480e188010701560764100c8228009440c0300c0e00035074030070001d0003429200c0c0d95481002441c40c64145c04540d6294005030048544100400940950541880384e0315410440401d556031044e850 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 47407162 1250 47405912 47405929
    0x60c03091003090506010b0307080406151806050f0d0f080c0a021e0f0301020a020c0d05120c06010f05220e0f0f0d230f07031106070e0315070e010c02 66
    0x65500022410200a41c1d01c0e0315401600503e402135040d1001c0340d8a5002d5180607200c1140c24001051080c070106001580c103910032070201d060307081100d28039521503640c84841e8511084105045032030f507100f0710152522010200d0700b068216100d150f060b04641e0b503202054500d0b84040d0414201103241d100054061200346441503009250700240c0c043e0000c031550641c00401d00074041d0407003a40007685410305100f00c909400301074005008032140642000310404180c00c00b11a41d00400304290380281c03000303019104d5090a00d0140029604203c0072003000300a0340c0c1f15511034004a4100c80620100c8d2a00041c000d484140100d0b001003565103c03482c00c00d140076400458414180c10003492400402c070031030784c60740f1640d80225104400603541008494404241001d40c0100b00349101e02c0b082c0401400164800d0405010303540d802058242080e204550100101756138850030501490305102460101c0a043c500d80c00d82d0a0015005240c407142140071818050610703800d20541d510b0244 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 47408412 1250 47407162 47407177
    0x100311060f0904151701090201120c050403050102070c061805060a050702010c02030d020706020c030f07060c03170114010e06070b0601050f0705030414010306080f030d090c17071707030b06060c03 86
    0xf8040d660420b803032410001c1040c170130303055500a940101003040304103004600c00d09405942e0b401c440c0103048940ea005240152102d42404400c120001c0068020700140c068207004010285480349004806448000240190f1440701c0f9585001c0c402c1c2c0d50f0300c00584210400c28079146440e00210b10041c0c03890f600130300000e5030510450401a0701640e00058050940718203a0075203413504001c0d010706a0b140c1d0521412000c2c2c0d04408000e209032841159441d8000d4007901c2d2503c0d50903c0c05840b080c20389400e1304110b14541052200202d19600140d504400200a80382945450115142e020b00c0c0103016120710304021002424480c4061100191040c1036000300c1075030366895460000d180340b0070314820240d020a0900500007060240410741c212100420750180d480d0031604407401c00280318841341120180200c001c08600728042c00f07520064840404005d28074541000402d03440000c22062138200c6034001c620030300c0045c46014229800140503209940c4842c00c03c00715a096005210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 47409662 1250 47408412 47408419
    0x30c04050424120807140a080408060610080103031709010f14040c1a030a0c090f120203010e060c040519030209040b04060506100806060a2a0b100311060f09 69
    0x1075124800303881102e850018003290060511109588200d40c1c0325000d032040000c0c040b03c809111410108000c80d04480800709050709640c00542c040e0f540701c1d200e40145d0410902070788a28100940c03810001c251100006040c00d1482c050f616640d0001c000c1c06515080c0c2070f8280d64200410f100006c2504500449030b0b190324203000500107145141c4400e00100d40a0360400020000003510b1407141c20fa0030806c044007580a451507a502c01002d0182005c41610820004040400134080303440046a00180c0320055143c58000b042c1d00405084d103980c8105d0f4200c503000403060188038070f0800101c8089580c00e48036049011084410300801d481c0c3ca9002039040b41c52001080100f01c03c0d1011244075501ca0f0340e041280342c60764801c1c0090103407a04c03a000003080200020132051724003c005848052510320300140113100c02848601c8100c00f0703000451100c01125210000c108000b050154004400c0e41041505451038484880b04074101051074042c00c000281c00306107002e400c1c1128007d09018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 47410912 1250 47409662 47409671
    0xd14030a030c08060f01020c091503011b020105091c0e0102011b0206070f08070507020108091f05180a0203030904020708040e0c040306060501020c0904020f0103020714060411091605030c040504 85
    0x10300900901464045800050028030003e0030500c0d110750710303c15400041c0d00070071003444500d043c840b08040142a13058030080140c07a003c0103903424094041c058400300300c440c804e0341901d01c0181c203540c8080d044413450707046280c0b08030200100d0b042e03006400e100d901d031206403502030307400503030040c00144201442281140001d4506940000392240030715020703650710304911500c1000712031603082914a400015010094a40035611865107503401504203811b40b041000040c1c4014585036105515104154032101040316290741c1c41904003c03000114041c04076080b00e41d00194581c0b0070703032144620840e8046400c0302070ac0040302c00d075070280135043e9224440e0b04110010f910340d60424441100c2d020304104021890317500c003164540c1c0300fa0020389404043d0b100c03a400c028150a240400504155003400300744080340f483e1031411258101c09020b40194205410515140046010702600072101d07407090102041c001652900d10404900d0001c0c0c071b0b600c17201c0c0780c980c1a1140e540030a40c040e041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 47412162 1250 47410912 47410927
    0x40501090b0a06080103030206070e01120203070801090f0204030503030a1505030f03040503070902091c06110d020c1501080d08130206030405060a0507030b031213050409210804110d1403 82
    0xc0e507000140300d070400c0720001c068950300e074011108070f2000d000060050300302002103580c450180c0c18036800000305061104145409050000403600301322051400182c9803030040100d00b88a00c00d07014144241d6000303500d05400c5440300360380c03403102a00d041480b0b42c2c0c900c4a0710003011203a210b035001c0d04008042d034982901d1700c0c480e241c2c3c0b40c210b07002c0d2510034003404900040201480c421141c69400c0500091044960682158100c1d240e0403c1959800c0e00c071060b0404003a0003000820000c40488001078441584016440ca814880304200f00280c4454005209001d8000350402e14034940b8a4100c1482c0e03610301c0000f40351083d002d0006d40140020042c401000b1020403070500c00c600c0f1a0081003160b0700c21070101c040d41e042d50715a9406800596482e2240c210b42001486500c284220200b4101e545d10003180803a0180501076444081e0012030200028040c1d5010504000740d103401e48003401d00d601d421009403021840240300d001058040410012061600440c10000509a944030040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 47413412 1250 47412162 47412179
    0x8010e0d0206070201060608010b16060e010204081b0609060318010c0305062d1905060a1110090b010e060d06050f010501090b030f0109021c0e03190c05060a05060103020702040501 79
    0x280322034440241c060000040d201c0343c8144195400c540142d601c62140380d180522104203235000500d00050f5141c81e5107900d01040c3d0303d010f07a00380380f03d8020006a0302d524003003446080c0344036081020312002c41e9134010a03044e69040c05031440c800040f644144e0303075142c0180c40c0040041c104444102c6508000d041c000c0c5507010f5001d184521800c0e100300c00018070441c4580c4040e254000c2c5000c1043d054503110440f420000c0d954462a40c803071890800c2244c4910004d03140d9040240d4444c0000c0c2c051404c41c1e0100014800d00c410b221415906000c449296034516a074007605001d02c0545901c0100040d40c1540d82900842419400c079504100d142017144208013014004d00560b80400d150650001b0140e0b082c074210ba110707582e1100c841e5a203900700b4041802079031000c4503001d03c40300d0b140215181ca258600ca4003901e84000401140c0c1c0300301110450050100c02214030b030034440040c030180040b400104006500c4404a0350000782c0303035500e1006a0080c00b4040300a9001071a00317001040d1640e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 47414662 1250 47413412 47413423
    0x3108120d060b0304030f0f2d0f08070801030312020f0703090302040e19020609030c0604090203070f030501080a060504240204050f0613060c05070902030405010b10050910120608010e 80
    0x8100c0e440c203004254540c4404001c40c8000e4500600244610414101152190032030001103481e030b151140d00b011010004490701c200d0149840141e141119640c070f1110303006400e00300321403e07908081c01e40b0300c1c180b440540007480500c805403c0c0308d06811607070044841541200c9a40340e80501d910b0f11200a801d00034aa0881d034001280a07602d824111052040002001e040ca202809004020010384d0390070702c8842d0700030901580d09407042c0b446641f05982c4840252025003010480143c80c0e103849a402062626124041000c0c10311b03000c01800440c80129240282c503400013008105a01da80c9042d030320001c1d2083c3d402c5040100e00c210304065208031b0300240102d5004440c3c400d20314003c14100501c9200e90b07017010b1b44066090700200a014024003801c45281e02070320640715180c0d51030801d50f059a0040b18201c61903590b0716000002803501045101964403546001d50400655101040794002900d0840307042c010115050350000d052904404040c1c0072201c02808107000d0626000e541d00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 47415912 1250 47414662 47414677
    0x70e090a0201020f071401230304120e0103150308070314040902040614030606030f041104050c030a0c11070b160c1203080109180311010905070e01150203310812 71
    0x500400d503040ba9130f40b80c001401d405485003001700d0000411701b0001540c40c0c210051115008081085910b01c52454002c0034600c201d00881035101142e1200303400401c401c1d030015009062501d403544c0022082400704081c416a5408855103030760314554241030303a0390602d603141d4040c541000603012a4817542c40d0080c008071109503c8445917000c0c1c841e1806100e0008840150b08103800784001112548403148864000e405100c4140c01800071f04080303002d561040350721940500e0000203010010080d03200d1541400ca1518041c05081c03059852140ca031100c40c4a0003032651800f02e840803d4a4141c060707c981c1e264001d0005d034807190703184011001c1000e40803003500425400000000d003002a809403400085100f482c25002102079581621200d62001000306699620302003031001a0b4200715aa02900081199070727039940c585181c0030f4100a02140007002c5400911050f1201000b280100307940c05001c1d0707a00441c1003030301484030004404551040031544070b441c1d1180c11240080c030082558 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 47417162 1250 47415912 47415917
    0x51f03050303060603061c350d0c12060f140f01020d0806040e030706151e0605030a02121f06020313032006040b0c0106050607050a020904080c01060b0301081b01020618070e090a0201 80
    0x1d0603448c20100c80c3c0032401000310251034904000103240303107425500000704c1c83c10605120508100c070004050480f00c5682200160840c00801800034107078910043c0041030b0201c0d100440c5441150000303486980b9212030f6400d2041d0600442c9c16030f503d43d00035040360000c40f000c03603894041d942040e00107403000342d00000d152440c811000c604510003c02c040c8852009881c0c2000603403070f0240440301540010020901181d0903c10320800103004084540a03800000f000741003401d0182c3c123900314142079030003407065500800440000008a500c800d00326a0050000610030301b866141d00c221940b02068180c1c0078500040105045070000050031a0021300302c020404541c40d0001c1c41681e102d94080035100350f12001c402d2005240182e140c582c0244106601d0741000b02c0c0d1280c69080d40c10740e40026003009004001844241020041041c410f9009503004a84c0c81c1d180c40040e4445a0241c804091007036400f10034840030b2003c00013030b001440141c845031881d2400d02005501da82d07154904070300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 47418412 1250 47417162 47417213
    0x120e0109030212070614010b090307060207050d0f1401110d05100303171302040218091003080306130912030902030d230a0c020a09051f03050303060603061c 69
    0x14051181580d0316900d900108200312400e07000c203c00e9041000202e0700700361140d00e08000213001c064058002c20188417265100d0600d04101410820142c002604540c03040b14104016519820080d070481d07048081c00c4c40394815400c0041182d009001c25031030f03960812007070f141240703031000c0103000d8184001c00c10441c980300d01100303442d004040c8c03002800144100044842c1500c1e006510f58000340c1ea41240b40144003e179010a003a40c0090104150341c04003c00c40e802941044244254850b5501400030350702c50440e91218140e00024001c41c1c06a00c200622698100243d031201e5401d40d00300100e0406604140d1009003c1d00980e2401c9007e4052082103521680c080c0700a04504c10f006c0a5101052494004400d200d80106a1000270403100c51501700150720f55062000150907240c8010034039151100c0c0b1203040001c86000105c40000103001000420000300541e904601d0454016035652101400183c0064024032810038020801004400f0440104a1255003a880105c400f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 47419662 1250 47418412 47418431
    0x151003050603030f0d1401030c1509081e030409090b04150902030601050f010918021e07030801060305040c210530030405120301060903050c04020901020a14120a12 72
    0x20240c03501900c0303240e0150f0040c010a4564280c0d0f2010b1308000b007a0100c0001c1d010f401b41501408a68207070300654020020071411702c6941003614011322231848c035040ca01a1245880d005540d103400c2c610341006000807410030750f44030000030700446005245510043c0541c0040781841860508141c50464138040030b0142c0c0f010396201e40c080c200d60b0030380040213012541e00c0c1c042403018075081c031038500d41042010700340400c45070011890010a04440040181c445040c0100e03806059545005e020040c0340c24000003000a81c0482c0302815282140f0f0040b5030b035103a910380710040743c40c1030f0461640800b46021642c030708002d1b2803000280741d000310200c5110714180c03100441040b80c406001d1050110503924640c40c0d0904000a60b0800d1045086400f2054000450000b0381c10a8001d100000c6c08200200280f1004021031250600125001c514004420b40041d68500c0c0b4a90300030031807000388882c00d1f01c0c4041882000c0c0c86a400e404103941e58540454004c100102101c0c1c6480031a29060090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 47420912 1250 47419662 47419667
    0x90d020115061b0203010b060f030103021905090c090301021303030804030f080c07060b060c030408070f0902040e1504060902030106050a1101020702010c030c050f010923010b0112020703090e1510 86
    0x1004a0b0a162524420b00ca0b661540302d040c84050b110998156403100d43c4040725486140040081c084e40305995902da5040d44100440120702c094980c001e101c94840c03d101d2503503044100d640210283e91840e507105158400701c1d02902440d050b403804209411000001c0c16044140e852141d4172a0760340c60719500e048401603869207001d6400050324079052100d0380000e070480d4465000550024000d0703041c01030165549245501ca0f400c162035641241c401084102c01400038036020b080454019410b050070100c1034031012030001e010004111401c0c00099003070300e566000c1070141a90700002c0d952076854150240003030b480310078060300145071088852480c50040c400d542101e60305170340e2200e0105803900d003101c00c0c80401c40c0983e03550103034946000c0c02da802440b5404042c1d11504842d020200300480e41950080c50b0006148507905041c2039200b02d0380c0c003071211140c89040e50b20058407a0901d04044034100043d41002c0010107290040c03103410590000c1490340001d0840303004080440c8000704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 47422162 1250 47420912 47420951
    0x908030c04060e1203180301020702090a0b1002060903191206140a0501021912090e04050604020405060105030601020a0201110a050609010f0b0303130902090d060c080f061009050d0317090d0201 85
    0x71340072250030602104010b960400304d900004240100050b04100745500010050035007512980805995040c16843c0744c186001c034040d000740540054211450081641030701c0e80f01d410844000101d001c41920000360254030080400a040c0c001001503d1326000c1900ca40c0c00d820301e0f85840764903482c0001070740750303c00600b40d0030303002e48103480009450a640c0e443c84100114030114042c001c01840100300031012600342031141c3e019000501040c1440c1c0140411200e02074842e9040040c10010000143d1b00014100540c2c0d90a10340040c207400000b1a403402c00d01c441000620600a080502407411015002200034170a50701d010460342985404050fa28401d8808000354807000d034504001100080e400b8111450001d040325401032003903513a0781c045410301d900440119900e403060104510801d403249901040c150341c082c1484c046000c000d429610144503042c444c10041d242c0307208141c80341c555060318079510364441d00c003401d01d003034110f48486540c00000300540c6018182004000c000c0030303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 47423412 1250 47422162 47422189
    0xa02011d010504140a0308071104060506070b070c080c011410050d0308070e06070804080102030415020a140702060405031903021612030309020102120307180e15060703030908030c04060e 82
    0x490b81e10341440c4c9044035050011884040764440f0100c2400004200da803001000c80c144140c250142d8010702c04100700489020b81c11031802444d06100b002c1c0002c0e4040714040e0019031304e00f0700014080107842c00060500c19203030003031569401c001c2c50071120740000010f5070280038a5110598000d446000f80858240001c401800040c181004990854003e08035070003e0313070003c1c3c402480c20300c82d9124103c040d881f941c0300a0191398000200002c1c0030080c50046060399205400b9441d105410000804d0680c1e003140905084000042220440d40c99504640040074098141d45d0302e4814034440406440880d4003e6000d40034080c4102840c900390045502694050031201a00040c13a4801314024021980101d056200709002c40107004682d9001e14070480c4941d84103085006801c10042c1a0480360f44101031070030243d000d00086c101200c01030348030310509944154443c14203080440c0a01004a80506280e40010600101e020140001c100380c0319107407583c0c82204440e0050001c00e940c10380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 47424662 1250 47423412 47423417
    0xa02070e040503190507051b0f0d05120f0706060b09120102070f1101110111040519051804080d02030f1e0f07030e070801021308010e0a0c0b0a0c050d020a02011d01 72
    0x10f144583c0003c04128880c81c0d004d890103d0070a055030303440610b40824203050485060409000c420309181c03c221040040d00261241080f02c4003a541d100d82d110102484001800004505190192030380401e0b40d00c0b40c3d41026043c48040e50799a81510781d5400503104c030f030007020250b02c8910803281c14000c903491140d100c8040382e010405030300c3d5001c056075827124860410035403a41005c44004240100410301d041d001304035540d01d24000030096903030742c07405050301e01c4c0c0e0380c10000300950354a00809070610b80d00c0240c00c10300c0c2c1d07485180a0505205201d030050740e4030b2002c0309005401e003070807103070511411090401c20518011901031104c0d1040c11240515840310340300008441c107120383c0000d030300080c0321400c42c3c039145e8841072901d007660818100d400c1c07003900c25170302046099400d00075000e4404101e000360025000316207403035021041901030f1250500300060b19044483c882d40c61001055005829145010315202e4025150910160168006400030152044c40541803140c03000303a62058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 47425912 1250 47424662 47424667
    0x20d090311010305191d061602060f060319030905040609180210030b040614030622030509010e04020d140105010e0d0b06030f060108070305010608010203070903061a04110a02070e040503 82
    0x21070044010300b000070940910104401c000144181090050401c009481004560700010130f0b42105c0c42d00c88000c050030a84131480c080000a99000700300b99410000c000d240c2d00f81c607560f08010918106201400b1a1b03500c60b401c4550060652240720304050310000c4900b4000c0701da907071003050282c0704a02c103103d85801040811000525080010114894190401051fa4102540060b08076000c50b032020b40d00303203209590381260703140034091964000380178000d490005002941403601d6564114004081c041c3c00503203812568003501542c0080c00e0014029959403c2802c007400107042c11001c03220300201040700200300c0790b0040c80400303c0b40c5406081131481000341d4035181072031030010b4125a0140181c41d0282c11048051048a0290240da07008000407480e600d040c0342186c6155000400507441030003400b9000364890b60350307402c07070f60080b80102c0c010341c503080580212a00d030039200ea48039180003215106a514800500145070a640969010350795481e2410240c0e40c08640040c19600304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 47427162 1250 47425912 47425943
    0x703061d0c07151a011806170709031707021903020102060604180804080307120207050d020405180616030605011b0204090c0305030a080a0b03030c060a0c03021c090201020d0903 78
    0x41c0300544409805000c920b00c000040840220844205584040a2403103605408105503000054096a2034400100452103450030758000c0c94a450210000d0a1111680110f00d50707521580225002d15048854900119030031600550194480b40049003c0e840302007003c032007080140000403c80e601a009401c0507940e031401c00000b403140180c0181c80c0d403660361000d0003040300c84000d8000f4100401c01550b840074682448540c05003a031110300c0440d800501d05000740c1c2c82c3c07020444070040d81501c000c501c030789400d015003414902101c0b20510307501c02c00040100100c00070f2828002c00c0d41c0c03030701e003000180d495000454a0f10384205224004446a070714600050505a1000c0042401400e640c03c805803242d41c0e003400c5074002d88207000090030440500040514912480c41403150803030045143c00716040d90540c8580009064503005d66903246a03d1400d07010b501124107400c0004194083d00d091141403000608000106900604c50100142180b034069164402074a4004080710b000010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 47428412 1250 47427162 47427181
    0x3120203070306080a0515010e0112060507050405040c170702010c02190c0302090a0501052e0f02070b040902031504110708160605090303160f0e0d020a05030303040b0703061d 77
    0x40070309940101540e40c1e400042c440024000050064860340c007806031904954600103410406030050034800c04658010490104407603580b001850340300740040341c156100e0302d0546550055600180d00701e400c040314014525400703400050340b801c400c48514403d4480e500304908980c100750464000d6841203540035520f01c06044d02d000b001c2d215000c6810001c0c0c8940c0030410b0403005664410405885070010b1041d45080d041c405219030300381c100e030404404640b070a4130f06a00741c103d032001030181d9820341540c000c2c400c2c451070020b01420070b50140c0e29030345c0d6a1050000d60080320280701c90b1800301e444505034a031901401c082450701000c25810300f066503c810100354000c03100309400a08402043c0c0003c0c8035406901d04ca001d03508003440d103a250500c98070b165002841140d1040040403403c500c0d50b079400c403800c4942d122b07080d82c203107000407041c0c40400d8000c00700340c11940d07240c44040100070420850b1074900b071246002c1c0d54107004250707032a0750307a040011408035009086060103000540028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 47429662 1250 47428412 47428417
    0xa030c031a1201061706151c021207030b01080a03020f0c091906050a03031d0f0a09020702010507020918120903071818080409150503060103080306120115170604031202 74
    0x10708071000007420590fa00b5040d5505000c0d1940191240c0240041140220025072030903074503542a98401c0c030440040000203285023810b100280701d0b60050300800500710302000143d018680c03240280c2403c1d40c552074019691460510110014401c0c4051201a01c6001c508900081405000c01403640c071540c03600c1940d201418211001160780d0000001c0b6680e6140341040158060f403680028402c510501b101d415056201c0c80380035010291400805445101c550401c0f95800040140c4681103440100e407184106240690312070151420300000941c04145010176000c9242204d242941241d2201c0d01401900145a850303007249804021600903608859403441c1281c0e000a9001d030159540c2210f0154500261220003021500380300c05012485001280611140076416092070b200c00260350f41e070140002010350b00702002080060f21003054880003400300400034029008000a402d404a946200d05600000c0860724881e0100c4080b911b180607940507a582515102c0c1d01e65120040e6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 47430912 1250 47429662 47429689
    0x90402160b070e01080c120601110a020301020711030f06010e0402040b010e03060406050403030f09210905090103050a0b061c0b040201050c070b0d0b01020c010f0309030306030602030702030a030c031a 88
    0x1440c0540400010440201c8a114030290b841c0d052400844000041c883d020041c1b4010142000b00714905401c0101c9044030380c410403d207014180c011607283e4840c1005404240250150b001041c440700f048018240d051140c0710503800c5910401051090559410083c40348042030401c100108000d42850341000300040320604090071400c10060110b40380100c202d4094524507661130900c800c041c3d050160300004038900c2d00a005800c05501c0b504805607540d404000201030034a81c004096014418040003060b0080c0303011415030f503d05141d40c803101040c0041711008508000600989001602a070250708a10046100c0441e03560b52990742410241c001d0b03051220500454841d51410800703903003d00070030003900e82c5034040b08100f4000d643d0b451211605542204036210071a981c0b2141d81d2210460700d1030046000c0450341400c2d0004c00c1030360800750060b8000810003032040c0c1c0020040030482c51942d400c0000b492100070440440e5058994058200f9000c0003840543c80d1508412098 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 47432162 1250 47430912 47430937
    0x3020a0611010b09012c060a060c0c0f080304094a1207170703080f100f0902040305060a06050906012006040507060f090803040e0703150308030a0b060f090402 70
    0x82c0c603d024001445000264402d0740120103004440d2107a6564504a1740304610400c0d070ba41080c02c2501c00104e218900c0c0c040e0504111442d10142d051000c01c00300c810003001004000c06d2040d44841c00c558aa60050050341d200341c4c10440220034014100400c6800e444092002e041800301224000100806440d80307442c4c04d8040c0c1005070070403a8144540b04484031020780841c0c1d152028506910f20701e91424494444410a0010f070021035000920350364440110f1100c1c40181d03403143c0c04a55801c6c00c50b0000c080701640304c140400d084181c0d034024000c0d03d0040d4211605c40d41c80c0c50100c8140caa00340103082d0400c80d41c1000c6a16540507110100301c801e0b80900c0a080040d6103501d462600d8421030307007a202c9a000540030495130350012140c4044140c146003c1c600c3c00c0c04e014046640e88160311a0b02d103542d004000140c16148a1b030b000c0c10106c8903515401c5001d968908040081d90001c0c1c410075241c3c0c0c070700308242440b46002d5044032108d80b0090790a0b400c10032074100704002900605271072240c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 47433412 1250 47432162 47432171
    0x405060915070b0708150612040f020a0e07030203041a04020a0302011d06030c1e0307270305060403110d0e0306060613120305070b0709080c120129030c01080103020a061101 76
    0x81d040402e4648120b003140d51703103d21481c1900b400d480321841c5081c01780c05810100042c0113030f2502c2c010144e5016800804420200e0050700c08940042e0055200071031160010082c4024564035400440c0107500894803003080325010984201641415039000f0752081110701b00700b0040d4062034101c03107031058800703048402c005040301040c07003507000b100d1500041c84c002a100d40f03814002c0c2905a20102a6062141940382c682d102500b03400c50b900c485001c0041d6442c210f600e00d1580007510014640c002d081e18200c0c2844c0c6001b90108a480c81c4c09a12401513512038a4814071401020041150040c000d0142d03403070304400e0111990000300e20030400f1802c402c010400064009848128074481d5071110b075101c01c5800c02702c0310440c001d0860810480380d91420045400e0000d20305500480444544010b002416401e60042040b080c210000301c401c007020b2139009007080030b0084411001d4044c1d884203c0600700441b83e0725000d0000940c80070029405118951203403000d40c20050a400c000038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 47434662 1250 47433412 47433427
    0x30606120515040f230c040e0405120c0c040608030a0c0803180a050607030c030b0a0b090d0c0807030203072c090307020a150e0414070c0606030218061002030405060915 74
    0x60650348890301c0644d90304e40b900401001140b14030703541300c0d0884103605c1c488420704009882d2030240c0710714410808441c0f54040440c0601005008483e110000c01c01229070b20f1030038000c040d80b5175400828491055280c190000b40606010044070101c072443d0f9565941e04110fa40c2d0a842394201501c905900703c0d50140300a80c0b8030042101030022401180249014030345010001c00303403061411030750304043c2001001500c60b292000700205a4240c8205551112204001305591100548000d80002a41000000c4008011801a05990080c0c06480030291107019103480c00008102038814200140c141200420040d0002500640c2c14000e5034500001c0b81c000070242001500022058051034482240080e003008091010b244e0907242032040c2d00c8400315054440304001d10704405d1019190b4030380c0030041c00d03600a10207550700500202c14261868401c01e548841128141e01500c0d00810303401595000100b59021644001c002d94039007400303d000d01c402d00044440302c17040941c041c011103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 47435912 1250 47434662 47434669
    0x20105090d03020a1407141b0312070203010b040f0b13020702090708060d0602040b03010501030c3207020d0c03110102070e0c1303121101110406050d020f161b0501030606120515 78
    0x3e003071b1140120340051411607801380d91410054446040482e910704002d203131910351004152003a141e008604185c0e241d10303150022a005d8a02c89840d03a07030281c42c00f00304012002644d80315285900c07042c0c0d80300d07454600c1c0081c024100c1c030580c0c0010754018008000106842e11400c140c0c1e40c001030290085030301c030300319035588002ea0b00150407943c031a810100043c0300c156410f218440c64550a441c0412001102c002d54107040b44a203009801c6810260000300038180c003000460304d206a0151411340d6507106802c010440400b02d0104880712802002c0f01e44640d803000802d08107440e004004001942c455001c1114503a100e0b00c603080881c43c0784000000810762825101d0904c030b05075241c0c148146114061142140d4030610303481009c3c0420b03c81404055130100036220401d001d00401aa01d00d00c82c682c10000d0300520f10200840e041d00840034042006039991285111155a90503240030b0b2580015400d480c468050703100050444680d01c501c1c2c80303480d0000354004041f848003883d1030320a075020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 47437162 1250 47435912 47435917
    0x402060a030b0d06140c161b05130203010f1403030307030b030c060d0b01090504020f040501080406090609050706030e01200d0e0f0d121413060e010518010507020105090d03020a14 79
    0x113440c1c0381e558202c10b01c101801071007015405070702c1c0d01c0954548110152484c001a03640c04014003000c00c189207a1aa5400000920026080090161103000c0c40307a038000010354424060501c5601d4465400100e11480700314036112404000d020350305641d1a0901140209441c282d4954940304080d0414251340f60740c002090404054000480d06880715000500b0300441503109a0181d132041000d0300040d10b1a00a170307070aa075424a01500781f0740703076814110302420710901e014200c186041700c0300f010480000f031410308a842c02d0300c0a200d240401544203080703c44106042c000c005200c0d000ea08200100300041200220706440050407c0c41030f6039541c030700442c2400c031641950103100a10000c0d030b00854844040e8030b45103400d0010502602d84070210301409020745c202d01e004a103529040181c5900080c280c0c042c0ba4008128610780300508001170304100d421100e540d446d00002c074043e0f40c4180505481040c24000504940c03005480c104c3c000e500c410041803c0142c151980c11040c120b0000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 47438412 1250 47437162 47437189
    0x9011b0c03060209180405030412030207050a0837020d03051c0506030114010302100e012c120114011404020403020301090807020a0e1005011d0603040507060311120402060a030b 78
    0x44c1c0703880c8034009000904840b84520310300b80080e03208020000f5000001c4401380c45490b000d25011210034a02645421000d07006294844c001e44008204000f0001e100030700360a003143c0c1203659030010b1203140e03080620b019503a020701c040308022001504005444010303203803280c60f040303107045155240f10461103d80488020070350340380c03814400980790074080c030800a0126102c0c44110751642d40011120032078594582d0a1080701892410a6030107070a650890520026414211650041e006000345c01421100392003180808000805400d0500c10084141080410903645034200050450381980d00840301d944079808000100050300c080c0198080c0d140f01d02c03500c940b54005841004003a550340c0d0020000c0720011420003140340590414141256000c0c02c3c442e940080341c407500c5004005052006422100010603c4104280004c4000440c0d1036994100600d108041d81c1c0783c9244130303540252003003205000203d00980f03000d000a00c561007443c100043c10031046404210308409416 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 47439662 1250 47438412 47438423
    0x1e0d06030201020c011812031b0302010c1b0308070c02040f110405120c011d01020c0406030807030306090501141504120305041a07080f090f090109020d0b03070b09011b0c03 76
    0x81001196010007040d42e40e00001d0900c1c100c03916001c00c4411001a0500c9803550380c0e0103c2c107556080c903000305600041026403146881504080d07050182c082e22038144100300107464120600c1c07460540e800403000060b456a9080b0b101c1e2140001101d80e81a107040581c0e0041da9100303d000000e1191060910701d0010301010345d101d900d010100031541c440c1e00080440f641140500d5072080c1c1c0d0042c1e0701d400460f41c10003c5012500d40b140101c1c50580c008040070742051902c14044244a003420203440a1071195070184112903c40c96084269275081c421010301c200e1514130501d4916041c0c41001351f299208030303101d04003561004010b10346200040181c012900c00203060000308030f800301c0c8030706900302c4200040c40d081c0555655007051040000b8100c07020000315800300981d54440c03194544400c01810b07200103584039441300c0025030080140c0c1010600d0300d0015a41410003013140c00c1282c88a0441174101140c4000550300d01c1d1701031030000c9080e550842201c002548801c00b040185000d032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 47440912 1250 47439662 47439671
    0x6081008010e0c040605040b060a080403090506030a0203040204050610080115020a06060f1502060c0405040906020d09050102090102010e010e0a0602030415020304030309030e01170406200d0504020a1d0c1e0d 91
    0x3c50902049466540004d0300030b9080c4802c8110036212501120104600c5107820481552641003c0354041c1c41a0020340e8001000000e010164401e03801450090b1b0007124108801e4854104000d40071707000e901078802042402e00100014641503000c07100410aa005480b5480010f548007030448055402540403426448003c1c007050901c60516018200d440c001803810f07041a60000e01240154480c0c54411a21892107400304582c940580b86480318594007481011000d10340309010703410100070b00303006610300000502d00303500500506016580c501d0151402e002191292806944000e005980d034445502c8400c2d19051a44025032080b03000780d0b8005038101040c90000d003410000c401d59810032072150032080303540807400180380e0441da2016000038035080001c405200d0540503440c11040d0100030901428035821a0401880b4a02c201d91101d0140d80740c040b84006c040c07000300443c0741d42e140e0000007402a1100d40c000c180702d0b14800c111110a03d00d10032840520f91001000c41c0180d5284d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 47442162 1250 47440912 47440933
    0x6020601050105041d0a020d020310181a120109020d050708120c06070e04061e080d0c0503070308250309030201050a020301061b020609040e0604050d050f0406081008010e 75
    0x5001a60140c102460150310b800c0c50702c181c0050500d541c820741d1540544074400300310040300c258121050f21950349815522072038030f81c82444400406d032203501c1c001201001c807820841e08d035100d600c06d102a41d83c2c00e00080300d40c01050040131103400e24180c481d076580f8200c000259554a5440700460711420013030450f00e090030030a506000b1040359100d9060414002c123004036201240090f0302071000c1c68691a162415000107000e041c02d94018030513090502c1c0f541c124036040102050551342c10204a0f0403000008204031202c608050f80a0025001401520006440341d002c0f950014444000d09c2034100c401c100c40380c4901080b4506101107641c070b00ba41410550280070f11940815207603011030456140c68000b0340302d0b21002140040c0e07084001c01c84000c5640e44015903030444001b401c100003800204201c01c0d80ca41082d541a502d070712800d8860360305144a5401c542e0351031041c100e020305052401005403502c5c140500301711002c2000320710105084500740301d200118241900240074074440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 47443412 1250 47442162 47442167
    0xc0b030f16021603030f030f0614120f0c060c0715031b08040b010b0a120c0201021b03030103030c020d050c120c010e01020a080a2d03090201081e0406020c0a0b09010606 74
    0x4201d46440203541014240b544040341d10501d2030f084941508102e410800201d50440040140c81c0c0307091001880c1034030103e00d040910300203d503642c1094402c1c010400100100b1640c4180400d462211035210303000200c05414050081e09403100b01e1011078150740e48900003022682507080f039003000295240c9070240d0040d03010b81425118011410151100c0c1403d8032a03004e06981405040400306002440001c2180b18540055428214500030415070490b0b1800078041c1d40982c0607220320506241c4140f100300307008000c0f02c3c101c2e0b0381030302c800e810301946600b0300190518810080d520b5000300780c0400c01c00d0303c034241407400343c495803000340036114201000940f8000329603194904552040403418002150070b01110610078141c2000850f81c6c03c02d103040c4022106403c80e0070f01442d031044201039429090b401c10059140f0036200d0f48400d47e1554810080d901c2c0c050024403d00001d803000c18086a55079000700a40703000c4c402603071408003007500d40081001064800031081c1e950341d14100300c46035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 47444662 1250 47443412 47443441
    0x1030f0207020f060a02030d050c040e010f0803070215160b16090608150f0a0e0a050a020a021902010219050304050307080109050307060e0304180c030e03090a120c0b030f 75
    0x88010118200125600411000000a040240540000651070364038138001c000340d40050303010311810b100d83d04c0d0403981040c6d944c1040c8038002c000702081c000400e00c04100200881621b0b145401035051101940030030541103419085894514010800c8696140e1101030030408240109940d0205081110450340c00026030f40607002007104220040c811b030f680c030008103900845c11500900c11130004000041031094524480c2e6404401590b00203010300380c8001c401e1003030001c140b0030081745c1d41c3c0010384010ba2080d51a10b20050b002a451007855540a128444000e0b0045c4101da05d146410030391080204020241650a0361001c5010400c6107410000d09014091590007800340400c07983e200c50703032802003800007404039498580c210051601001643c0007002600d20503900342850240b0000102064942503000078100f0040340044107000007101c0c2c65580c083c0803840c0c05407500c04002d40241c044002101d22000003607001918003190790107580211903c0300c1098150602c1c05652170b111 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 47445912 1250 47444662 47444681
    0x15010f020d020d180b0307180f0b120907170a1419021203090603040303050109050609100b1606060305060702070f0b03062803050f0f010e060a0b0a030609030302090103 74
    0x1940110401d01840b540812a00c1d803800050070305541040b254900202c04407101d03041000e55100210801018940c0104881c503907820701c02d083c0c02a0f03510741c50380f4803001e126400780300340c5400200708401130403280c0501c443d4001c0c0340c00103440a96031102600503000c0017401101c1095030017048501c00b844403200c4000c0c0c0d0142454010662007013a406440240e400030311000e44a031b58400088107140344107204455a12200030081c0350f407483d240ca0003800404003806a0ba5443d4030740400580b242c101440103038000c00c07a52400041140c41c04441c01d60651024980390101e0500d803510200090541c015940550300c6440a00014981800001c0c0350103040e9015828000300010100440c0340014100c03034001c2003c2c3c5000140310042e414070320032407041d90000c2c00100302169001080c0600031482c186030041c0c8400752111085100c41d86800c1c2d5100c680d8841090f0005c00100d212101154880104800050503149500303659407103510445458510581c04240c0010f00000310790780c10322460004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 47447162 1250 47445912 47445917
    0xa030f02090a0b0f131206050a09020f04020c0a150912020607141e07050a02030106171b011b03030c031503080d111611090603063c15010f 61
    0x40048410018422140078400c043c18441c0000300c420094482070101d0f40c11900d000210306519564030503482c200011070105440040c6041c000c2000100c580c040c80c00c10f150024501071032024002c00f00030080d802024404003078403c0b88001c1002a06001c265040900380c0f400005444605042055042c4048030107401150022020814942d03004028a900440e842c2c01c00750b103030780702006041002d50b03c56010030b540c45800308014040200c0060002d041c24400c0e0001d014099880446003520000305106140b103070041d00840042003145d000342c030288041417400355188541e490983c00502c1c0c4500341580080c2e00c038100c12032100d405002e04038a06942c0e902c13440b1a1031541e01ca0020728003c69070450903803038445c1820710002d03030034030155404801c0305a00894900c0e40307481e0254030000028200e030b010b41c20040c0050158034001c41e0551040b00a1785804800848002c0c048210200842c240408040808840402d622248040380c1c441d0440030010b030600c11b0504d00241428640c030464004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 47448412 1250 47447162 47447167
    0x3030c02041d03030a020a1206090c0201110405150705010b040c0801060e0a0608160c021306060306140904030c030315150e030f07180603080f07030909020705070e04050f01060b0a030f02 82
    0x342e0300041200d520400300040180c4810070600101c501c1c500e60040415920700305007002c0344c010900d80c0151a004001d40003005415003452101c0142c1c0039078802c41e540700010020b68503007620f9420080c44a144111f00000c2e1b16040200080c0071110340c0748003000000d04110052083c0c41d046407500c041721a00300c501022403840c1c4403000304150700003032811150449040c4541207032801070003101007040e401040d80c0e92007601000f000e4014200c0b4481c100000e4100710700024410002c1350030301c0f10742e04003400b411029a6543c4064600d0a41401c0480401d0b0791488034414507035603810a40040c2c201010581e00c00707a0301f004000c4c0307681e1a1040301d903c2600240c010003920b04d000106442241d80440e480c40000001104000080240c0e81c005818140300083e010ba02c600360100405d60644a915800c2e1800d0f20383c0052401c1b4010480d004286500000041c09080341030003407203a00520480c00c50326074034021201d55080d502c490740904075070240402c403180482d41501520340580c100c0300c000c50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 47449662 1250 47448412 47448461
    0x8100b0403080a050c0c0307060302031b090303070303180c0e0a0b060a0806040c0903080d0c091a030105040b0d02030a261e07020406081b030d2c0a080703030c0204 72
    0x60b074850410007500384000018400316241003030182d131070341e090001d05560b800c41e62580007a002c0d51045400106038400d054030603240103601d406641c05070070060300450601189a42c00d400508104207005901e11002c48030800081c0740c0d04415000d80200c900040c090b05001101005640880e041144250b2080c480030f480c00f544000502d5210710100c40c08200310b441c00d001602c007141141c001034500f40f00040c0c80d9200180c1c90f00040080c103150394400042c5682c0700c4122002c2109004c00c0c641c900c0d41040100504c2c60b26400183c0302c54070003001074405d001030768002480c1410f204011598808104040c80d00c9003010800201400742c8407102500e043c0545910306615a4017400441c8400c2001c2840029525264007000c05899000c04540309584200041090840e120107014840d1241200034849107105075a02c40409003980d051000c282824000e03220003165001500c0e030010064900050000d5040008200550007a200c5640351111401400251480c801700d0740c00c0700d01e0540980 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 47450912 1250 47449662 47449673
    0xc0a0f0b0714070b0606040801090c080d0203040503030315041b0f030501140f0111030c01060f0e011203051207170109060303180f030b0405030c0105010e0123100e0402160308100b0403 81
    0x3c4426a0780300d10844080d640322030001e190b500490304166129071074141c2d064100300c0005071a10030707034040340d0481c0d05000308090100d80da4801c50180a4240d0800d2001c43c85d400b020030300700c8401d5503006101240c3c00c01c003400c1c4070441c500d02c0b01642000400080080c20b56030b401d80f2500307000d0700c080b0704083d6100340000045101e1003e00c1c07414030b0400aa03030f240c4021030ad00a0080c0c0310108041c0000b409425a40d4001c20030442c1c2c18000c103c10503501c03c000040c07d00d0703060018180d99525031a002d04018404602c807481c584010201404d118681d2442c200d03218502d800103000e0150041c00184060450500500c0901101039040040e4109841802001c034800d038020102c9510402a01d56507845140c810b0841c0100c441e103642a600300b00000c2170701c14659008906a507581242c10140c10003258210b403203103004801d055048000469614501c03441041100344418002d4409450f040040b00101c000c00c43c0345005800103607103172042c005055007101c01c8074010a00d00000380d042c00d01796280c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 47452162 1250 47450912 47450917
    0xc0f020601080d0c030315030812070206090a0b040f120f02070b04051f0504080106030b0106080a05071d01030608060108010b04060e191503020301180308060d05060f0403050c0a0f0b0714 82
    0x148031944481c5030805109800007400c0c960129100607c2940d00c1c039140c000da402102c002000e00320010002094144000340f0140308251500003050352000a444d806008a000f074000c3e582020104801c0c07010401c081045071084410703580b25404901d82400c000d0800e01c0942205610746401c0108100f1a91502c2c1000360f07510520010210111000c0c00a40d228803e41d48160715a50800074000140400014928100ca0143e1a20030361682c0f01550241241e10486032100070413840d1103c0c9148600002c0401010901070400003485500c1e2018240303824807d80c4210780e503a46070300c40c0c2d4110b804c2502032840200a00d1510b181107041040d0302890040441c5101300a0a546800c50002e00001605000056401400800c0403074100180100e14001c000030a802140e2800701048081c00d044001c00c03034454000b0042c014948802800d40701400d0f02400950030040c0038445040310250501036811090303c03074007504003403002c05e28010032a408001c00303510520089105100b1040e022208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 47453412 1250 47452162 47452183
    0x5090706091401090312030506030c041107030804050c130617070806070c080f0d02030601030605060903070b03102105060a060510051e04060e090c0304020d0813050607060c0f02060108 81
    0x581c8000b4411000101c88480c8281e00282050303102c071101c00360300b5405910076401104103030141c410000c1c84206000989a0390700c811455180100000b0010a100788511a0410720803000c2d5400c503601040062201c81102d9000d1750308070354512003040011020b1890080d03144c2c41d0006004010310b4001090b440d188014908018044a04034200402400404a50344500c0c0400302688a003070460803d00290030465460340424902030001c035551800d6410750702500c90040040c40e010f428016415030941020b000c0700c060100b41800401c06a8200e800400c0c0042d40020514902c1c5160400a180039030207410000143d151a9003031110743c8501030401c41408880c10110382d41d07451020382104048403102101000c00001c0340101c1c905601402d0500d5081e42282c4640c1603848001c1a01c1d85071109a078000c1d442020303418004d001030020710140001001d9908448a007644d0b404c041800d0b54003030703a011141d0540d209285442141c0000300345015913480d02c001c00c0f0b10b60510560300da031030302c8195 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 47454662 1250 47453412 47453429
    0x408100908031b04080a0c09051b041a12010305010c080f070801060c0311060f060a050102011803030e03120114010908060405120d020912070f080615090c16050601090509070609 78
    0x40030f012424101d007080310010581441111483c08440c248000c07481024020300c0115814900450b1540241c00c1b170b0a01c41c0000004110318103441e0204a600400340e401c2403e07400702040c03250402100340c40c5507860086d4010b030004980051f00d00c0004040003030041201c81880f00c2d00c030502a01590000071141900c2060400d502280e0320390600396031290900d81761820b00e110390010819032007201c11949009030b00907a134000c000360b00c0d0f8005a003a00d034080c00c0c4060601c0b000c107400001ca0f01c00d40116648201010540789480d1340080040060072098001418034111401c200c202541c0c03011042c0f00801840000e40640d05142e52926200d5a000f0b400c0160241c2c08958018180150750413608000c100410034054851000600c50701c6601d1486004250030304e03403000081000d80810090f10a240620740d50140b030281c4010441404005403914407420400d011085103842c0070741c810380820740203200400307a540c90b050000301910401001e55080c1c1d000031504101a68100032540240c0d039494 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 47455912 1250 47454662 47454691
    0xb090f01060509010509042d02040b0f1b0601080a020109050f010e210a030c05010f021309020706020708030c0d1a0f040f18081308010209061602010201060302090c040810090803 78
    0x2500101c9a40c09012030180d40203280400c840031a0030900e101420210740005089041048e402d01001280242d21429000440800c001c12681880b80000c001c0e101580650030f0504071480c40306450700c002608941119400f21304800107540c0c101d1080001454210f40e84140c2d4803100000030108040641e00b00d00459156101c00c80f107003200490184d00d0b860120072203040c00038606009224102c07803581910554030300071107140e80031030038021030f01e080c18594140c51f51030b45025208ca009500290003611125420f103c070f03100258101c030045000ba005200d009403542c01803010441124041381c002a10607001402e0421162158081544141401c0b540014001901d488131000340107010705170840b2642c0c00e900c00c000c00242d407000d441c983d8030500390040d4541e00c5000d403500300e210b02d1540940c05001401010310500405205126061040c4008580103680350301098900d039090355044d4208102080900080b50f04000c0c8000b6060b400d14140140390302516004094400070303248640e5651031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 47457162 1250 47455912 47455927
    0x5150a09180210050406030e07051011010f061401020c04060608060103020c070e0403020d080f010302030601090504080d060b0a0e0301060f0e1308070c150f0801090510080102070c0503010b090f010605 88
    0x18807880c001540240035064182403524004120303512038012000442e2800d0f00c14503105000250500a0301c4002d0709012171401180000e5420341010b074007010a9640301c2c80001c00c074a030340703010742e600070440c00c03900c084c2c00d034404c1001908140b801c011607806280340c1201000203d600c8070641d03070000b01c2800c0069503584140c2d0024144001c0703800458804410700180070400da400610744401000c1da948031289502e594580c07141e03e19081c40301035071640c80900140602c0320541c4c05150401d00c11a9500d241c148140c0360003086e12103030b80c0b103004003005c040340c002e40d101e4201c00400351103d0120700810503079040540c14001240203004040c4080300500008005d691040824000c25402280305500c0e840d0304c2c6004040c044081c000c80180030101a0012916030180c40c26640c40c0c1c90b00d44031031425a00304548480100b40007451036000b402c060300005000e01d000e10003070543c1da0140f0251880c2c207040c4070506080d03a4280784001e00451502c0e0030450244041c0000c90706480140c074016981d1003a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 47458412 1250 47457162 47457191
    0x4051b03010221100e0f070807030207120e1e060f09030a0c0b0d0614130b0f06160501050f071e020109060f050603060903090d030e060d05180105150a09 67
    0x526107100b000d80700da125800800d8590120080c1300b000407a2804904648644841000340011386651241071084004034100c41e000e295241d43c461098a0018204611901d48801d5102c20035000c0000c25640c4c2411000da00308000d0700003250b5a901d011540c83c00c00710000c25070751311545401c1409440c011500c41e030265000d0240a05694000c0c14002c250740d00c070701c0381498561100c001408043c0c5801320020f88021403503040010001d009040e1904812321070b0448015040101500da0f1203500c500b9007003480d941d410050000d202e017031000426010b03400d240160031160040c20107244900050b040110751a40704009072162140c0c1240c00030b4180c442c0c0800e90140030070010080481d401c00e034003010340900c00e03800103101c3c01c4101e08031041901c1d4520610b0300e03403041000c120b400c6040043c11001281c0038404802d170045002d40243d103070041c1d4803031000854500380c84001e12428041c43c00c20031341c8400d02a0780d8100c5219a0005c0404500038001071611401e885500b87c450384480c0300880c0b100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 47459662 1250 47458412 47458417
    0x7150612020d05010e0706020f101404080306040b03070914090a050a030c03120615020d031a040207110d030519080712110c0d020304150302030f0601030902120f07060f020604051b030102 82
    0xd1700d15017204c665a03141c00c00039443d481c41516542803482244440c0d0510516401284102c041d5810700d1041d81e1a66202d03071002d580001d06a0350849e8603900c00079010b40b0304011144c0100400e000c001800c1c1d5528041140740c08024022505503801407107000b002c2200443d81083c01130740b41c01e0010001e1464501030f60300811070840003140d185403500000360480c68400c13100d0070340c2c090790a4030f040c0000001d09408a4900c4240c08100182d680121030342806e0540c0140303c0346020301c0a43c0e4098101e4400180c10701101e1000b200061408510209654240108154600201c1c00e054a140c501914000c000b21064105155030170749800d5940304103210802103840300350102040c0c4220180700e0001a50b2076105101c0c21441c020006140760001d440b030720030749000302601c200500c1036481d01d400440240411040990740240d90085002c2c0844003007091500080062014004482c60544040c0100961000310300654210000701f0002450100e00c1005010a2041e151080151480424020f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 47460912 1250 47459662 47459681
    0x9041d0105090601091d0601090c0c0609080705060f16080709171605030d09090504031b0605070e01080708040201110309130617071d0619030807150612020d0501 71
    0x25403074031090000500022071518161000e00205100c10303607107035002040e00d030018105802207402c504011710524855400c0702040e01c2070b078903040c2e44281060f12a40c0803101500005c8695a0001480400f004014000e0907400320404102100c20303d800c450f807601040b800005101007104540019440e00c1c040c00154018101c1c0c0d080d02429044502c444968801c44103080d8903071070b00349580000e140c3c600003030300054031841d5540310301c5180d02c0d05034034001030000079000300c0900a07280092a00005620201c14105004507000304260518440142843d40044080b07810452a042004141030f00703d0011354102d642880d21900d0a14103605403400d40c05003100940d8442c1c080203081450a2050300314009554552440404c0107261820896440003a4850721240b01101914400007138442040c8a80c8180060901e05d60184140403111902001d50022030b9000004540181405a03540186400d82341d0030608200c00343c02c140c84008980c0721004001d1050f031001c603480c8204a001e4102e034114 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 47462162 1250 47460912 47460971
    0x30912040e040201080109050903040b0c030f0c07060905010905011b020d0b0c0703110703051203220c0e060a0807140301021b060405060705070b0c07060e07030813050f03030904 78
    0x4403912840440503480040e2403c1e0f0009185000201d81d4018502c24180141c445500441c034142ca000550b560640080b66a40c040c0c0c0014440300401d00f1070f04c2d00414003410760401829002c2d0800401400741c00154000c03e0400c080c00c0c00500c8166000010010f18030201c280000e544141440015881803142a000b819034040c2c0341405400c0c204c640c00b030b250691007030300c4030740020f00c80940e915580d0040d88000b41c0b0660207079000d4000407005200940e0003265804503030604400220340f40300c01a101182c11903800785030340c1c020040b5028910542c0c0c0c0100b030480c0c180b148140b070000b1103940ca0450f4010054900c050010b4410f050340c0950444580e5025600c824072140744680308241c580201310b4003550b442c010000000c010340c1c4101d00f10750496901100044858403403005080d40b5401c009000c0312266507400c20070400c40c03420030000c1e00843c82004c0b203607515100c0900f00186d21080303611040c0a80165070740f0680564010080d14228034080c2e400042952290071070401850504025940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 47463412 1250 47462162 47462167
    0x504020f160803011d06030a020f0102210301030c060c020117060307030204060305010209010306081203041e08030412120c0203030402090c16050102091f1704050f070b090a0b030f040305030912 85
    0xc1029100c00745040307500d200711056640d4610460724085c0b03030085503070562603001900201e0061400d074030f402210400c107104850004480b000c0404c0c0c1122410780140da5690040010400c200e800c450b1a00503008a140c1088002d00c4e5600281038009502d00b0113440100241c005525520100302010095800400030321200d507a900b0700a000750301ca0700d00c40b4000303400c0050100745603a0001c2c4641140c800801d02d01c0c60344d607858072824058488603003034995200c003a43c0203601040300f80c0c0145000f24095086829407000910003d000003c0c0807114501d09400c05a0085103190003005881d480741d01920300c40400d80c1d030303840c20341102c0c0306003401d141046400031107075000c0c09015406016084c005031000b8005400442020b610441d2040c440400541600300148a6013000c0d034035160001e100d142100d41200100300340b1801c00c1ca007500110b400f03040c0401c05071074070729040070044002d0400c3c0c402d003850b41c00d0010012001400051003e800c3c40800004918170020804c0000d940081f40404030340c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 47464662 1250 47463412 47463457
    0x140c030d0c020405070c0213020a1e050d0501080d020a081806070b100509040b2707171009030801120c080105040f06050f09060601180f06020601060f050c070504020f 73
    0x40400c5001007003680203a03c0c00340084c1c0c4242c003598550b098542c00514a554450201032801e002c2d510403ca040d080020608801403540c802e08409000c441c6503480b080c0e00c03402c001071400b0486605a109030703115484001100c0642d500429074403034694210b000180e40d0800188074824080180d8a00340d04000c0004200b42404000d00019001d498280c0f40c8440450340d1784200107941c013041e2006018085a0008075007a1380344080140748050946445100840b1411810742c20501168440190980f030607901c2d6002180c00c0c05400000c3c21201800c018081e044d0724001e0072000c0c140113080c80c04940c1c80f0028280070611988100030702425000b400b1928162818074200144c561044843e02c1c10040480e442c54904540d0b1886205c4050050100c0c1d507551004680c41441d81e0002480008004008109140d00b10150006095145c006000742d5142907070003404200c0c14144041000410b1000754070940740410b05000310790f0200da000d62520048010032516104d50a03011200c0b40b0244800c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 47465912 1250 47464662 47464667
    0xf131e0506090d0f0c082505060f220f0f09050f04140a0501020d0f0e580e03030313020d0212060a0903020705030706090b03040501060e010905090706030b010507140c030d 75
    0x1050316a005061f82e40d84205c1101c000c40c1c84140c80d006041c2d22107424800c038807580e580880078101c1a18481c3d5940070b6640c292080001492440e088034a80498030030040c00508683c40600c00200380d038241c2000580b51000200001203c00f0308000c010f0000542c01c0000b01c2410800488a16007280007150b0710b510f42d007403000c0100714913000281110304080d01e04a07074100205010b001c61810425155041a220015521240c8800700707810080c00b052941c01d420910714804208044c1c07248408030f840c40301690b0003030b00d00b0b290180d0261080d4010010000040308001140d0103465040c1d8026400028510005e0340f10081e401203406948580c108000800c0720701c0c2c20211019000740c090f41d401e01d4079132003890f4031103582e80645c00124400c01c2e400c00c080c00f0b44030000c1d9130081c0210000650613880e95044103181000303030700c40e850003070710b80040c014450b0080c41040c1c01001c2030b080030062032040f2000a801800380300c1029103c0e2011141c0d1020314074003401a54010200202070b01c1c446503031440003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 47467162 1250 47465912 47465923
    0x212030f030901020a140708030a0c0201020c07081506150f070303090609030c0b010906060f180302032d010902010f08040302010e010509030d0e030a0503060d080f131e0506090d0f0c08 81
    0xc0c1c85c00641e00d180c074407850101c5401200c0203150050001841d44c2c1d250750700c07040071701601c100100444d9401c02080761142c0c014812600178050b0040a04514003100d141d4804800007e00700ca403041003016948e0302d0001418003255144003444038400d40341c81c410708080e0f00401440d503000c0e003030b24103094003d81096400300044134031078031826910100c0d0340c03120302004c211101030003200d010800c0507034070b10744460041d42e000c0001c0540c04411244580c07a580407a0900001040d9840041908201e01b010041081c00034102080004c0c001c20407480a500000d00c1803000410706070034040328002040070300d03100707400200b00061540b00900147c100000a9596130380305d07404c0e284585e854034107032920f21000072084507200b68085d41c0c1c4c1815a1600d004100844074610011103802c04100110751480100b4806020000310301d0b206040814589100c080c801c4800c804081401c03122034109010580d00d4105070784643c0003c0d200c3d03c514450704e1425103510540380c40b02401403e801a400203490800090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 47468412 1250 47467162 47467177
    0x70803040f0203010507020109020109091505180f13050a08031f060e0102010e030306090f130510061406092107050d0b0411030a03020303010b1c0c03090204050c0f03040212030f03090102 82
    0x17000681d0360408100c3c00c0b48e078246402070005003004410024402c5680040c1000402030941c21080c0b951000000c0e8104860b0901d142c00c403106404100d0f02010380803a442d4846401e0101c0d40c1014a40e07903070f440e19103d07480c6008000340801300100f101c80c01e10710040c1200b8584680e65000213500c83c04041e10021298240c0d500560a1031401e01c05e211000c41a00d0050344043d0070200c8645480d5600410f642c801071451440d121041916000300b8010800f007001c0c0100480001485803e02c5028000348024801581c01890308022202c20f544501e6200480c100742203071b0881c0041440c641e520f003401c0e4190700281d0300903c203d41c401c09101d0300000081c040c5208005510012500a00b03058031860440c07405409078205100420010444100401d4020480505444c030010f02d6400b5078201c0311284103000009668014580441c14184100d50308840c6c4482d200d401c10800030004003c5120060000f4040c20025041b420319120400a4400e1b80403e2010581c407486d10b200e205000350172640307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 47469662 1250 47468412 47468419
    0x60a0c050d0306080c0d0f0503120f06010504032604050315012607060e01050d06060206090d050405031f060506071b0608011401030c090b0c0a051c05160602070803040f02 75
    0x607071180c0718082e10501003200e0613240908501541e036400c111052554081c00c0e41d008403201e1404000030001d00040220f004602c00b04041803c0c48411601240c41c01800a418007200300818008a804a03800075075503d884405549095484a1501c1c100e010b2540026058420301041c0d11804000d4142141030300c4942c0d443c07241d141c00043c041c81c41002280c5c00120710f034100c02400c3c0a0180304200d030750180c0703c06040c8103280c041103001c83c030110751003a0302041c0160805070601c00c00a00a0060368110b90b16890218146414580040d848a19502600e01d0403882003014014080040d0888001070900034161074641e25182407075404c9480300c00410741d00081c121030218240e805800303803605860075040f8810340420b007440154028144000400e00703101d2240c0001900052040041c005150007070080c10142055140881c50312000ca4048908041a91040000c0c1c82e4408261800014100f5100c0303035903811070a054000784210b01d00a0310242d000802c22081c4545d941030701c02054400d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 47470912 1250 47469662 47469673
    0xd050a12120e010b09060d06020702060703050c10151e030501050108010914070311040504022d0a06030b0f01140c10060f06030b0f1002010b03030309010506010912052a060a0c05 78
    0x1c400c40d00300d851004d0060f40c40b514030300c0841c8641c00d044010a03100b5208200052900f00c83e5000038001c1e4003c43c00c00c50025200290303159140c03c061140d02d03010040100140f08084010454500c01e1105028000301104448808015964402e2162005540210081005586604c5d100d030207801c0f5503900383c40d0b0340032048800e4102080024000304503a00410391f0752414000c081000050031001d0300507079016006c21800c03554010101e0000d140c0012059281858503ea00b00b44140f5103080c0d40803c06142c0f030003009110f15203d482d003418a2100034607001c01004081c0c1e4030004180911440181103102c4c440300e07840011130035404001500d400b211101d10460740c40390110305990419400365040340859030310495a003480c08200003280c0c540e000101c0e59100c0340700400d01e9a04121200d6003940e440302e0511081d5600428020003401c1007041000c0d010302c00343c8507a035903503980b0051208411407460942080030100031960000c5100105007983d03d40d80c4070b400402002040d001910f85000d503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 47472162 1250 47470912 47470931
    0x1b02060c0301080d050901031103130201030b03030c0703080c0304030b0c0306090a02030c0a12110d0504060c110d05092e2a080c0a06060e0708010501050f04050d050a1212 75
    0xc0c00c252070403990320400a1242d283c030481e0440301a0010a03540d81455201c42d02c61540703c10042c06144111400c401207544220b040c0001410b030350740540302c070340a07130000c001c0c040d0821000306200b400d5030307002042036a40e055a480003902e184941e5001902c007409132018495a0f202d0100210b005010490381d80c849074840c00e03d0380089100a54020202800420a00a0380d90007106200540305000c0400038203035000740d4811500b94007404080c001555034208100401566100e110481e00c6940742a011001819502c40d0b43c600028140f1402c1c0300f004940c940e400c3c0c1d00e20480040c5d8648025203000810004515038080041000b07404c0f01155a100c14003e440f8800d00740d00010070200fa04141100c0032139258100c1c0d55000a440321250b0068410103804100a405000d009018065020b40c0620780310500504844040e0855410014200864440b900c0b2150948068480407101c4c070000500d03501d00a0701e8940e0301c00c4001c009200c46004104202e0b00030f860060004520841480040300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 47473412 1250 47472162 47472181
    0x50315090105010903110d0c0602070302150301030c0501050705030903070308070302010e06060112020d0204050603010b0403031202030f15011214070201060e0f01030311030d0e0307020f09090c04020f07061b0206 93
    0x40900403140094a41c8030100003240c01c6c2c8034070201038080684070f041d46002c251600d0902c50b8240d0007000151748010307001c0046047c440e1800c19600c2e01c40e01110304550540e80c400910f80301c1403040031304104021641c442031100c02d0085134200c0e0401000c6481d01640d0b490000003580100c20305801551138106181c0b0700e85400704d80d083c842c10b0140e4442e1401c07100401030500940003040400c0c02c1990a00000c0790039196070008601a054165810b03889600d10319008100c1e0084910400d0313814010300c18030034454001c00469810508050300c100441145500480e07420f6052551261410704142240000f40c004004660140445034000c0c401d05803150703c0b200d455003060710045a0031208400420109108454980c414800070083d00d1600361041081400d641c004104000960800610b44003180307420015000440c00c140c0d400c0c074440c03802e8504140c8400d1002409405103130000703048180c1780c00348422102c2590340f00c83c041010151450605010080988002025120b42008134841c0700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 47474662 1250 47473412 47473429
    0x10608010519030201080c0702030106120501050c0c07060e0609060a1709011802060a0306030503120709050d0213050405011d03070b0711250302060301030302010e1c050a051305030706050315 84
    0x1540044142901d0f443c5500449004600511041040c0420301c0b42c6070050fa403e005a00003084107090200500d083d50a141c1c0c2101c00c0a410150780500402100401072008038414040718400c2c2803220130390307108030089045403060040c11340c1d0010000440807881034200101c448403034116071507807100d950780c288058201c920165000201200c0c030071209005103029002054961690318010450598a50300e00d4a16000203541c841e40400c08000c019a540d80446420001c10003100c42508002082c6c0206414640f04011404c0f1291104001810700900b5041881a0b201c800c044c50080e407403103442030380c0b03903000003004481418140c000716403261b00c42c0b200c642008864402401d2084449401c02852101c0104034000701340b86a07100001594400d40558025406900040b840141710a006414003a601d8003d600e003400071075800700340c245e0100640d0441c50a9040c101d5881c042d9181480c40d03144c1542c80290b01d4400d841021405640c8071018500a000c41d500119656029204101c0e058 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 47475912 1250 47474662 47474689
    0x30b0c1806131e05030303161107050a03060e0c0307060e0f09070e09070309020d0303020a0216030510020c01060801020706060305072301050304030c0c03050c031204150806060c0f060106080105 85
    0x20080c4209100815803c2d4401d10282d1030010000241c40da510080ba055801c101c403151712a04103c5c1c03201c8540c980258035528401d800002030032416041000007140b290b02400080d04060380c3d00c0c0001c84980c800c002428108a004040341c4403d0754502004105c000031100040c02203c0040344104103091803801c0c0c41c013030852511002c05005560040c4580010b004210004042d110304505002d41c980ca011000f405000780c0e00940e40f90301d041c5010f071800d00d080001c005240e804800400101d030000c03800d60a030b03000460f00941d0301e82c010f0350058007600c0e164001003055480059503204219090307200740200e82c0700b00150b17125650355070601003140c2c01c01140c2a813202c051007031200107236110f44011680284281081c06507104141c40e1040c0c41442e075081151107030321400c1c0812580c46e04120b4018003000b5825011f00c0d10f41026000304a22540d04415401d2100c1e50003c19850354407102980e080d0035002e0103d411230802a510195200701c28030407200400c00c1c0300b00109240c01c103200d000c41c1d032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 47477162 1250 47475912 47475937
    0x6020d03060e010314070f0e0411030f15070e031501080d08071e14130302010905100c11010c0506040b07091409060f0a08010f05010812090102060f0c04030b0c1806 72
    0x90b80c44c41d21410b015a01c00007a80d0707454020710801050b0340010005081c0941064841c140303e0740b400e440c0440000c0c5903906407030f1103a4480368071083c40c2071000036407481a10458400c3d005640300c000b010b603aa25600c0d42101e43c14060104408802c511001c08181240c91020407950f0b42245640d0907546988161007800004441e080745250a101d942070007420b540c218a0b21080b002c4001c550386400c1c0c0c100f00044a418080e040003041550ba0002e0b40c20040e010880b00b42c0c4a05401b4903028020303030b40b0140020712003180c18850354080da001700c1400480366003280c203a030400c4c601031400c1c4110013012240c00d4081041c146002c21000d030054501220396001400f100001e442e45010400c3c0401c020086540c4140d8109021822030350038000c41038005044d9070080b03855418600e14505143e10503903520788204d82480f1022440e039000a03182d4018102020110040d1101104480b0a100d00e4001904404e4200188000070400500400703001c0440340c5099a00042041007141600c00c00308480070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 47478412 1250 47477162 47477189
    0x102070204061a0d0c05090607060f060501090b070f0812040302030d18080a030f0f0c05040501031a060306061e0a170a090302030405060a0504030501050103060b09011403030703030e0f150106020d0306 88
    0x3688049a4055178040d481810854240058203001074211741c0801c00440c0c003a52079900b000ba5010a0b40a900c002c1c18090901c6486c840c10110003d69038001c00102804441d01c0c22081000e1025180403a405601c504c0e00303420aa18250501940d01da0000204482c01442e2070040e81152100302580006580d100d040e0750301d4101000012406000590300c805c455980c0c508000c0c5448520b4802d01c241d15117035442d240c0d1900e00e400005400c4804d0007d1240e420b000c58a0513480c1d503a24070007102e80c048000c4403055140d4100b105070360030b002042aa0340800e40400200031200f2174003e81c12800c64110419151103d0743c0c0c680700e140541d104000c008016134014081403101d4030380323000602504174a514119080645d80d80741e107801d40b031081e881030b14140d903a0700c59501e440c103100711480c1c00342001074102ca0441c0f518030f01080e030ba885030f0400a000c16a0b141000c4260020521090584448182c00c41d8104085d6035500140f145081c4661000b6108201c14410700301d000780211801c80d529042d2074207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 47479662 1250 47478412 47478427
    0x90102040b09010e180718050d020f01030504030512040807020a080d12050c16060608010506060c03030601030203040821070201051003020a170111040608060312030613091103010e0102070204061a 86
    0x4a0322446144010391100d400c03d204852000c40c080c01d2840340c5031540d121a07c80c1c8407009001c0c0801050b42202d4014882c1c1c079039a9000d0303144d00c0c0c501e691a62003841d0000d281c0c0d884e03080c200c841c0c0c020112440f10b1418610284070600030502c0140540c14002c440700360010b80c0e62400c20fa92500c101c16140041040100020400c4a40741e002d154415100d0504510b8160307aa4101041120903807000c4520580d90801444088402d1140e6544a4000d480c3d252810007040310b056583e000c004c010034105600003000070100901d007030598146040442006c00312048400052641840407a4403000640c070300310001d618290300c416020200c80e005060301422074207110203421100c0740001a5413081d920340405d2141400c0001c01000209959650800d003400c16004140c01c0c111450300d0f40d9400d04041c001e000c841c1c0c2c0d0f000302481a41c00c030b604001400301c205240609644000415484d030551030020080d80300071041d002402464822602004940c4c6ca074002c0100440d1200742d002c43c001801d102a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 47480912 1250 47479662 47479667
    0x5060403022d03010908130602030906070b19020d021207320c0601121a011d040c03170a09091a0105070302010621020909060106050a030c09050406061106090102040b0901 75
    0x60715940e02c921100c20750280d424000c00c0c03c0d1004080102c3d03a01000103502640311081e42c0c01c0380043d00c00c604c09940380191080009156024004002e8010504000881e140400001e030445040352615015512401851841c1c0001c3d0040d0051451080b40c0c0c00014414a1082492a0b00740c5540d000301072070040012040100e52414201c440e0b09000c08224046045100300203107030080002d2a0160703034030440d515015203041030810500001c40c220340010b015405125603041ca02040200f038080640ea92400c15003075844107580081c151440d00480c40420110a800600d002601911000380e0355507500507a0b0215880d0940520028560000004956100c0d10040c50600d000340300100b100ca072100700361810f00c540740070b03400b080e940c40302c25120440c00c151403070039480710105014014039890404050200d00c2a11001005c25075a224a0245140180c21000182c4005401002840e444030400360443c0b41001e40280648208000038131244814000c41e000e4640d419851801e01a808006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 47482018 1106 47480912 47480959
    0x15021b060f0a0e03130602030405030d0c050c0904150e0a03030f090c06110304180905010b10020c041104030b0a1a101707020c0a0306060e010506040302 67
    0x400071031186030380165a102484040c0482d480c2d800c0c0c0c004604500c036001142440700304951010550f2940080a04140d40c2c0690845074100c0245005844401d50940c006085510000d551001414a003100e5034203e48102584011401c07038003c2d00090342c52251000446502001070601070651600414400c1481800c0c2008013140030b8680310500c0741c0a0040bd420720400c05007800c000c0c3d6013001100d009000306103000c00c0c0d070800c412062000d069400300a9030307190309281048540e46441d0035807041d131f078001d80c009101c141a500c061102400100c0400c00c2c04100501000000c81c4a1900c114802c00d0f01c0030000400144e51520f412940b2100b2020b94001c4e1001c000d0090f55540005941c0b20b40c0161101296081d680c484040386407103841002c4641050740700600104001c2c1c207030012401c0c0c840e0a0328030030480ea2903600b40001401284070280d03103c1000309110303100307103071102c1e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 47302162 47482018 := by
  have h0 := BRFrame.cov_init 47302162
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47302162 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 47302162 ≤ n) (h2 : n < 47482018) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
