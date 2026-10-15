-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:38:52.632325+00:00
-- url     : https://prove2.me/submissions/01675476-fc33-49b5-b24a-37152891f9a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 741906474 ≤ n < 742086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 741907724 1250 741906474 741906479
    0xa0e0306060a1a1c0603030c0312050712020f0903010903020c03061501020a080d0b0405010e010906080a0203030906130b0a17013203120f13050118331701 68
    0x5110a02d030b01110b181c5102c03c003c0c1d10480240c400c06400a035003407881c00011015040c08501244600c078040d43c441c0e01c0e190401801c6041c001c0540321000c0304103038140c1c54182030044160308503440080c421001c10002d6075400b24001c4076206409548502601507090040030b07010581c000c00ca00c40441002d508036082540e03068100c614058446030b0035070240c0c02400048002c40c000380010b141c482484500400c80008034004101160f40981c4000403400302c590060000300c2ca01d014141c0280010001002e402c0d0450700080d80303d00c5900411407041d4000520a600e444046100c80003c0050f00c0c0d000341c0701d22038900c0152100d040c0740001c80281d01800e0001c60f0140300540004050f0300100001346d0620f155103c0c1101030b428264509616101c2c203250304444108003001816500c86c0c0034299130321203c40c800385101c044a180c000c2414049400c00c0a1000e0900c007140804917032119000008041e01000c0c0d16420f01f042c03031551405500c00000c490a01500f1020444800030303820b50f0030341180c2c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 741908974 1250 741907724 741907729
    0xc0303090c030a0c051915030b01020d091a07110904050a06060e0c031906270c0509060f07020103060509160914010c06020d0e1905011103010e04061a03030a0e030606 73
    0x1070781c0070000d20380300f2113040611480c00d000215400c0c038102c290200e10070a80b51152525041c070300c0c2603818002a00d4459048840d68180b02448407108241031850409040803124058038841e01c80b08802100d0100d0810140141d150030f00b0740d84a0050601c10716420a81405503c034034074400b003500c1641c203204000800b81c0c0d55041851207049410242402d544500c4503080b021158100e0307411500c0c1e00c61802080380c0b402c030a0b00f401e1005943d1a00402d24441305400000e40309414000f0b010302100340b080c220f8680ba0300d001c60b605820101075080e40c03040300c1d2006900800c41500101e40001c0d26034104040c079001205038104030810741e01c0380844543e0700c0118480300b240c040c0d070540c0014103da001000203910f98004c0c260700c442c5028045a1000c11542c0c41d1700d00030350a03000120b141c201460b10f009014082c4245810903600814091a660604580d5403603244080e1009001c9652480c040b0300002a10107948100000181926511099018020306080b000070074203100c1e0080308003151162 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 741910224 1250 741908974 741908983
    0x3041a0315060304050708060114030f060f0103120314130b090109030210020a110f01020a09121a0c0d06150905030f0a0b040203030d0203010f1703070b010510050702060c0303090c03 80
    0x2074003603040c00640342410205002c0550405802140c8a00c81c0000100300305405018480c0030b02480c01020308104082c40030103141c561700c90ba035040950482070038009560440950710303041d00d400c8443e080c10031407007601c01c034000d00410701c0e020380082c14802400a411051189681000e0180c02011166118083e03c142203958031a07008000d64081d01505640c0340290300901070004840c20112140d181081210382810340d690b070704022696000422030026504415540e02030080084d0110f002480f6585181540900d40311100450250307200040d02c1c60a048112620403010a5092015565440d1125030400c842030003400464150760012403107044c0007480c94000c801010003481149819252501c440501610a9805000030800340e01d142847d40000c600138071035200c0c030b1802a85061860703a03020026400300810b40d0010001c541c0882c1506403803e05441084039030b0414284920804d803098890303000c000303405c0800403030865a03022010028501c01d42c0320381c00395101d0065220416484 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 741911474 1250 741910224 741910231
    0x3120f0908161d09070e0910090602070516030809040218040906060e09030f1210050d1a0f0601053108060609010504021309020306030a140115051e060d061703041a03 73
    0x7994424401044051b584461954010b4001d100790f070f01104011b47c40300141c60704080141e0781035030005104802c02c9001c024050441e0010ba0442600301e080d541c50380a24844c4000d243e129603004200710303907454000305400008000c010010010b1150620345100503000e00c6c0705903014001a10b001903290030b400310854a180315042e0019107840c01c44407104c8a80c0c08042c0c484800d40440c04804038403a00c41c16280c00103103018806600c1d020b01e06045010181c00d00801440101d41034500b4089140d8110742a5030400303100201c80711101480125150990480e4144003018541d900000641c07501c01260300c0c1d0180c08181e0325400e45a03240c0d000c2c8410b920a0107800000680214010000d01045601a40d000300c401000e50f80c0151251300e03500310000e658221102142d42d100290742d0051070120b00c8100508040d14404000740e01c0c06151900019884a1700d4002c16000030040b4080380290f1011014140303030b003000c64011403d004a030380d59130028010b4410651040030511203030f030300d9030090f280f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 741912724 1250 741911474 741911491
    0x10f091109071e140405060f030114010e1c020d150603062912010b04050412030c0e030d0c05030c0303161103090303180d050706031a090103120f0908161d 68
    0x5404072000080391002c60b5044e07507a4440c81c05100100e0269101f100500ba03000040d01902c1d00d9504101440500faa080f44a4030305202e001d500c08115500d80c003850f00c00b00b102e00e81c4042908800742c00841e8901036a600002e10040480b6580c0c158501c072644138505a9000e2300b020400728444008220315166485e80d410519010b0007411841841c0901180520012900021a1a54002000c20f0682e10190740842d42e224207581846111581032140d8068140c041c13501c0510103e10101207600c030b6840560305070800c40d0b440034103024800308200f01c0e8032011340701003260ba80745040c0290111007441c4400e00030004d080c1c0d4420500d055000000d80700f4a07800100a0761030980d241c40d00d40c40f1100780881290300410304941200c0442c8081c0701100c020310381034074042500c1c04960b11000c000000720f1400b070320807504d540050000c25030304400030700748a0550803d085060901c0e1803e41b041c1c4e82c81d9001440d42d01c40c000700100d1041441300191304031070503420803000095024252800060040340c2624 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 741913974 1250 741912724 741912767
    0xc1707080105090c0d030203130909290f0901060317090301060f0f23120d0e01110c04090204110315011e021903050c151b0306130b03010f09110907 65
    0x400303483c00b00901201c3c0791080c011207227410340780d0031260001d400b82e6210588099480038950705012428000d40a180e2916020b8406100030482180d80690b0261111071b031b90280000007614180d0960001000e03680000d60302003034041c10110a000381c2d0003016164020350070f00c0800aa00808003040d50140c070003d241414069041c082601134040c19840419042c100f29182400f00f51521007072407465082c4100a080030346060356028003e420710b4120141005505070300002c8880c40400c0c141140401107030080741c2d20b410fa00018000e406809000c400c200400414030003034504182c0d55460320a07081c1c841580700401e11410302003007141d284c4100096004401c0322404603540e04502100341303100b800c0aa080078a84000189001d1001c3c080c60200c00b842818410f544007100701c0c0c08c80c0e01c015585003624500d40400841c0022030070056100d0443e4507110000703e60354082d0011044d00281e00010402000607040c8040001030445033faa02402c8001c01003402d00748120b83c10392000c0b01c01c0d00b600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 741915224 1250 741913974 741913993
    0x1050d030f030605090f04030e060a020a0809040b040e0a050123070e01090b0d020a020601080a050d0521130605060904020a1208040f09050403020d021b0906030102070c170708010509 80
    0x703681c12080c0080e040708150b5504004a640d1342c643c0203042c0035440b407008880046c601890081d00140e1810342c400c1c82240240003002002e030340001c01c551640e600821003511030400c400400c029007440f0100c1030b4403505013034184039581c4000482803a121301420007400300031202000d070030343c842d0070011421000320110002900f550150b0000001f00c00b06152000e1019039440c5101340701d81140b60980c00d4690005107000c24554100a22409001480c0246c0f01204150751516039400c9804215070500c00041684800390845210040050301c0c07450301040189000c501c208400f0f07a807100110342032171074034000c6070b01806c1074030341c0f07034421030340580414042c50400d0004120342150a004032007406d0100004580c21446441c1180146100f59005c102ca013041d16000c0d09141c14941c00508660040740e13a801c02c441d08140380304084c1015039400586441d80008640079204490300507240d103d004c00002806a5482644a20302081000742c42507a529980341d94240e4009858060b82c560004051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 741916474 1250 741915224 741915227
    0x1e1c02160510021306081003060b01110d02010501030c09020316080a0222030203060606071e020105041205150a0608060a0c050c0717011a03061602100f06080106050901050d03 77
    0x40c080129900d5480c0d80c0060a552214035051084044100c959000300b00040100e00002d04500902420305080040745040800342103c00c140784406402d142e15640180001d034080c0302080030410858041d1a801440b04602074041c000078402284c2840c1c4074070001400c14014402c0d00d0103000c1001e0f5564140c40580c10171201f110020300182a82ca50070482c904200c1c0d400c812800100081d90780d0180d5480c41d5004160420800034032a5004e10820002030001500034081c5400904234001d00043d00003c0d0300040780c1c2800340303420040284403c0503001c01807201c00a07640381d0160301402e4840303055a88024034002d0740d80500c10382c1c1c1e05521503c0441d40c02c0b50709810803820500319207449410401640c0c0540e00e4040a54406944482c103280c54014544080c01010000c00880103001d503020a4500425a992801404c41c40c1d003885030320408085c03c2c424058031103003100114050001a05d00c1d0000c20082140e40f1660f8503540c41c02e140021103090050744541298402000042c04c3c440c036450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 741917724 1250 741916474 741916477
    0x30307020909011d01051e0402090406050c0f0a020303161418060f2d0a080103020906120f010e010e0a030504030b1518090d02011a010c0c08070305031e1c02 69
    0x80c56110f9503c80440c00003881050b02c02c0c54070380c0d21810001c1161704002c51111304d80301c81c42c58810306c88560581040056262a9003881e0015482000000c19a4034011910054002d0b660382001440002884001d11380e80080518020aa840304030f032107600d4021015a440c040d403c418542102041c000ca8440541843e007015810b140a424903160500000c03028007107900c82e0703803014540c060414a1141c180407410565000200009009150030202c200240107007005100007407007155158001807031511404e02d0a8810b00d440811100440c1d020039009029041040352803c0390b601c2d00d01c0c40111910001903100507250582c0b141854907046803240449560024890603503010a410401c01c00d8949101d075112002d9004d500300014106000518107103006201c03558216810080d8003074800e500c5030515913080b942400c110303144000a180c0018010425848403400f4081c20400000348030000c00281060500d451440c000900d4180c201240e602030310307581c100800811500000503030107960 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 741918974 1250 741917724 741917731
    0x30515150f0903030a03021201091a0f03030c0a05010b010e011e0e011b0b04020a0e0f01060807020f0a05031201060503150d020d0b1014010306060503040b1b03010b03010f090b0303070209 82
    0x1da03107524000401000c82d00c2c40d8094004107001950018010140030846003e040c054030000c401409000d08200300600b00d01040720003a8443c00e403074140210255010021500046144026941d84c2036650400300e0082c0a04071949011909050b4001380c0c0790f1107001241010031f60003034450f40c041d55505003200d01040c0000080d050000c0140582c60ba5440030220903409403240292080620700351040c0040c9042c00d510076442103d950702445400e02172107001a043d21054a004002d070b40d695403040f0f00e0005841e0b808c60041c0130b504005028004040000e00f10200000a42c0209980e5030000f210184411510044000482c0c49a0b40c1c803446c1004900f070409000810034403101ca520349800d0020b01c41500d80f02c0708282505c00801584e103001c50804125102401e040006504d882406415444001c000802034000b1500180c541042c0300390750f2080c5c00080020903145e42c0c4a000c0c03e0100d500a0161940c8603840f030400090380c01490040111031580900510b003405441e41c00d1104803000074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 741920224 1250 741918974 741918997
    0x3091e1e040b221808070506090c040b030307020d03051611100e0a0b070c03080d1505040c0c0f060f0c08070305093d0507030c090807060917030412060c03051515 71
    0x440a04c08140c030840074110040c081d901030010fa00300a20040e1524a00f410400d0260b801c00b020403541d95030202c1510003164041c0c40c079010020725494200d42c02e10074001000422034a11210805215041e8083e80e0303140c0f42607408117403100000303000761140d07138070310040962061401b10107008285800014000b0184905a03442034240c8076960070001d03400425900c92882c0d55000700c4c860079442070f216000102000e907010003450510001c0103288908400f0003a03c0d07819400c03560300030000c1700c2e03010b003008e1b009009040001032078401d0020600d10041c2e501c074000a080c8000f04080060104008040c03040ea05ca020b80412106424050011a0398080e100d01d4501001c0c6400b611000703010f054800e4450340c0d80043c000b98100009000303842d50750090645503214000c14007405d5040b0303902c070b811f4505d40070340003a0303015001d40c12603e5881580c100110000c101482e600c2009000d42214504106580702848160f4807010403481000c0400003055004624250030118096108000c0c000502d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 741921474 1250 741920224 741920261
    0x301080303010b160b0a0b010807030606052512270608041401140106021c05130b0c070306090b0a0507031b0f032703020705010504060203091e1e040b22 67
    0x4541719810b5803001210301c158019280e9011480c5981d100074100d502000505040244a0500c10010201d008000926080c92200c0111400e507120342d000b02102a640200001180350b089100248281c09660795200981c0d2170481d0780e006456005150003d590303642d55802890b40d5541c8038103250080440c8800c4003556140300844d801000829024041d0009800070a00e081c080340b901602203c1030340c10319040050a005403d142040b056240085401e55010b1581b0784d01500d003114140240ca0740300a01242c5043e00400c10002c821000a21a4005240c100000d507103010099060710407d6021100341c5001c11680d141e0785010760b04140504507140740024401080711082c0104000c0031162940c0350114000000402d5810407007080500000e1034828145031a0150280d503d02520400c0742c0b20f801144820540d20b140c2d94085410800002c08400c1500300714030f00444900350311846030740a1802d00a050110741040c80519049000305e403208441841e8201c803450040404030314400ca072401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 741922724 1250 741921474 741921517
    0xd03050a06050316150509011b0503040807090e0d031e050a110c0a0b01060c0b0109020c0c060403061a0604051c14010c09090c18092c010915020301080303010b 70
    0x30b0401111305091a400c0e90f1a48041c101421040310514511802c030030030008016030701c03190341d01c4840083c480d44481002100400c0500c0e10505600035071308403011920980900046229083c1c100e00d002c00c20b11016201c094150050032000d80303060541d83e8598150050b690b40669040d5804103030302026406c0700280341d030040103c4c00100ea000030004e8049038802c0341d903034040c411420b90749801081079050110b4803095a81c2c4050480d0414420b40b400c4941c0440e502d42005414418028a4100202000da940742c80e07103403d1004120860b540c410208004000d01045d003401d004840030f49034010100010880380c45251941c07100c0c1c040c1c045600b00209a45840034100034000d01c0f44d4545180c0b102d07030032203090540d5a0101c5411011050400c48090646103d80903500800d50035610400c0010bd0722211101207035100c0801e0f290580003559599203401900c54043d80310011040c817414000303025007450800e20041c3e00081c0120500381d04204010403142c03484000600401c0504400e404400c034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 741923974 1250 741922724 741922729
    0xf052416020120060c180301110318060702061b070203030706091a0601120c20010e1207020f040902011b0803070801120b061c020a090e0609030c0d03050a0605 70
    0x8019050029203950304246200071507802c851440c11414402100c48016400d40e42c5440da26800070380156012100016401803182010082103030840002e4003c3c0450080003005034080e40c412142c500d1080f045c0c0d544114198004900c50740503480c268014006502c03a0700c107a4448180307204030802c0007402004000f005850500c081d00ba020f000324800216082d03203050500c200c409501070480b41020842c10000540e03040034400400d100c407502c0c00190140f01320383c2074800402e05042101c040000ca1002031041d641508911501300030201911034201c1d00c0e201507403140c069520002d5010071150390092141c10203600a9114070700515040340061300c10b112101c00f42071814002d480809001041042d4690803041250052581100c6640920031030b032601d155202020340140c3c414004100040d1041c0110342e074900b415030b0020178a000c1d02d80e4a10321032004241c141d200d00e4a40c0154000a280904003005a940d00d06600c0050045203500c0b000490082400804c0350162540d2034074003043d00d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 741925224 1250 741923974 741923977
    0x1103070314070311090907060e060d02120612210f0f0304031d0d030c20220501060905030a1203180305030603011a101d0d050a1a010f0524 61
    0x40000c1c5018050803400d50604403d802d000d03045243c00750b005038007030015040b00000e0510071140c0c1407070800c41c0501d868001480c1403050030b0ba003024460000c280b0380b031180f4031110722602820040340c2d4030b0321040160202d15121052484400511240c0c40c0d1201a031800b1400100b10b410030009050b4502075910040d80681d0f00b055400b0740001c0c01080c04080001d0302050b6850720400101c0d8891851041650000d283c030390688001071000b502c900c0c510502c0c035400d500300c0300c1d0740d14010b000815921201c803c035481c01403a1002d02e00c0e21800c0c072000040190180610400742c0743c02401905007820141c8880c2d0070b541000d2121010180e0301d4180309007540c0c55001107015140b19075222a9a42490800c15003580c6071149640c180580e03c0c96819010741d5501504a04c1070b4080c00e148030303004c0325450076000310048400010781007003158403403d0400070f01081c940382c698400c0e1b1100c603050200f02a4200e100200340207001048051003000d0005140140a0088070305e03401e2903200c0b02001c1030300804690b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 741926474 1250 741925224 741925253
    0x4110901032a1710050901091a06031f0e070507140a020d080403050d030e1e3301170a020904080702031614060f120705040f08030d2711030703 63
    0x61400254040f0740054846083d0041400752660340d1075810b040000394042d0062090009035036490b00c3c0010f0302d0b02000c2428015080c0188200e8591804032104814581041e2410b010b104020f1808100309602d5800c032405180700d40d54003030030405203030390f202100b4210b0154003005124101c80500148d0302c15500905e001d00c42c0640e951a10f246140c200d140c80b00c01083c82040c5820516040c16800300040c650711042c4050510262400501340c1081c141f9440b84051542c100308510303400c072601c90320b0b2079a181da001021400a070580c0e841d03600c503401c40450380b0b00c240250440c2c040000540380500580340c21600507a866440d240042e8006480d1038422465205400c0102c0c3d0304100107141814401540542590703558030b41070700c1004440c0188113001c0c000b0100c0100c1e402143c1035034414025140600204030762115460340700c40030035560360030075031007040d1040c10304058565402007c1001c031824a450707e6035109210042d60b5104104070a902082c2d00740c841d0380400030214510f07016003c00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 741927724 1250 741926474 741926477
    0x408040b07170d0c0e030a03170703020409052703030c0d15080105070207080c0a08030f1308160312030e0d0c060b06040f180e1c090302130209010e04110901032a 71
    0x21118061310024100b203001d910340c0e5205e40c200103141e90100b608030b0f03141300c601d50556801031340c9541c82d408140c00900407900541000ea1a0000300003607041b41003402c019146817900444444910380220580c1c0703200c1140e44140041d400e01a0380180d80303a642001c0003160b010340c01141c1040e01e5504250841d80304440b81e030010307030088400300680c0c0c2c0140407403c0c10003800d46151001d03e0401c11000d40c0c070b00c02e003856201c1d10a000a014120f401601c80c01002070540c9105503010b48840c20009402c204003801b05881c40744c200c42017840e10358040c0c440c040d103020181024040180b0b9101c4140e400003182c01c000d50307495480e001044159a00d6200031f0000c1d010007000055018101041508040d480c8210102e42c00d01e0103010344074002e030000d0b036031011109280e40683da5070f110400031240550f1581c0003d40244960295422680b007940180001c18000c1c0d907144840c00c00c4604000607640444e60503540b91204000000b415403003900459401001d40032002c180f140100c000402080d50002c6460 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741928974 1250 741927724 741927731
    0x40b0402160b070212121008061e07021612020310020313060501080f060f1801020f030105011e0905010e011704060b0913170703170903030a0c080408040b07170d 71
    0x4200070300700400c0b0350407450303610007400020024a80c4000a11443c0c07100080c111540000508180315501584040c1803407506845041c20701c0741a4024003440c82d604d00c03080c0c0e014180011401440010004400c5070320090500e00c451420340c200c02400c144030300980e014050b4809010381c000c1c950004500031403200d00c46883c4000142095011030360180c218200582011030040c2c1c100780001403031a0040700005600196443d070f50504000ca200c41005591994004520900072164510246040b24070030f894110322800c210f6209540160b82c40c00131b00114bc54118184034a522403150280307a01c1041c101030107650544540301001d64403c942c1201d00343d0300c0d41c03000f60b85403c0801105400c840c040410f01c0c0300c042c03039035a400540950341481b1441c0c00d801288000c281032240300d5034800b000400b01048500e0512080c042d40b250b00450b120f51107541800071008005200d42590b030321444e0402d5010382828200f440b00010f81d845000140c1d014104210380c1c24841c40d0120050213500031058000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 741930224 1250 741928974 741929017
    0x1401150f080303060603011725050a080f28080c010906110c0703030305071b0606080d1d090720060406050f060306131e0302060402030105010902031003030e040b0402 73
    0x4030440c04240d080100260401d2050112070313294801a07905640009a1944415a1000c2c2645c6041c3d50b031081c0c140e080300d01500d1084145852105081070b500d0945942c000c0c180c4800c2401d541d0401c0b141064043e9010b01c50711001070240c038441003801d84036603500700400c40240d02c41c8625600320300c0c041400d03a5903884c400d40411072903104040424038400b03030b00c80c03c000c00444401c0c0c803030b00144030107014540c9583c00131300154841d4806c0422001148440c0541c03101ca8201500204228000c60340148904540361509600900103800b0070981c800240c41c0400d411401e002c0200409003170300050103164101c00c1d51140f04a02d200c000b001e0780000520b40c0b4942414100c2c01d1f2000031306407100ca501182e06000c40c2e41c4021030119406003402c242102e0b90390552030070014000c0310306840c4d6942c6910300c1c9000c0400d540807031898002d40c0200e00034003460744c032800c220040b40300668924620700300800080000038040c15202c4641640204009401808c0001090507a80021041c0d00022010a0304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 741931474 1250 741930224 741930239
    0x70f0314150709060503130c080a020f19121403030702060a0f09030504060f09090608030705100c0c0210121803110f07090b120106060f1d0d020409140115 68
    0x4501c01c240403511071412400d01c18800b911203400c030700800341040f80010004403401c440410480070340da030142001c0e0881e903803801e9032607c4d80b0380e03040128440c00000d07103909101d241c01000c49200c0b441841000410500d80246160000d00d110412507a0074080000d11011034400d10145100c0c0d1f64507000341501d03240c62020082220701540c0d44010403858000f045d4040b9a000c0d041d50192203150030700204245440d202626411070552004c49041e06240740461844004806007000301d2144080307490880956141c80151755980c601d810010b08025507170000742c508040c03040244d4482c1e00b00000d00c030b01000107410a4078008418540044604402142010b0303016204010f0800c0140180c14031118503401d040c1c0b1000726100b000d916540b101c07103008403659422a01054195090020031990744d541038041c040d08950a121707808500300100060002035440e120f00da80d0708008044031001051542048020a4003640c1512104c19042c80f8480000302441b624050420410514460501c0c0400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 741932724 1250 741931474 741931483
    0x4050109140a080301090b0112091b050a0e04060203040305253503060a270513030801031704031a040c08010b0901030204090302011e06090f020307020c090603070f0314 74
    0x1d85014603400740032180c01168005065905460f400c4102162406034500120784400c1c070200390721441440e20154108115106480840c1d0b105404c14072503d403951002044111281c603c20241076080c40b10000e030002d12140d00459200c1d111341003040c2004d40d1544814041c00c1d820240f41000e07a0160f441106002084101c01c04904050700c4540070940300b502010701e0740501940c50801c2c0e260110200d40e007651890005030151462190703010508130315288000d402030500792440840f0745001c01160592946102d080b0443d03401d9199111a0f91841e603841200ca00700151550000b4424000840010400304100d23041e22a0340000e09024180b9040c40035071040385070b1200d0441d03031501c540d1440311340f0748017035039230440760100e90000706a14281020380c050540d01088000a008440308800b09554030340c00001a81d126100400210040b40c0340213049100680c0c00d200507a002c0c2034012110300d00503d90f00e62201001c3c054907010341d942c6418074041002034004403200000f03d4140c8800440810 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 741933974 1250 741932724 741932753
    0x120a090302010f1107020108040809030109081c09050307031d090129030928080a02060702070806150910050406092712050a09051005070209090714131404050109 71
    0x184100145105060a100d485c80b0b040c02c0241844509000201880713061000c1c0c9880c000e0180c003e004d0aa61460141841c1d48200240015204072035072049295003c0d02c2840d08080d0300100541c40c00856440a844481400303509408021007910750380e11039102d06200300e0092220440488505d45024000204c11504840e4001c50200078410440b0091000581100e0318403070406401d1a96010304003400b031354507001d00182492000103980c00b191503000a64a206140e40c0c0d00303841c01161100f100c5d0b40c0310781003038454145107103025405000c28646000880d410410041c18280381954450102d0244c0b102640049181581c86c0c0c40501c880104898842e51085040045110319106035a503001500000902c40104040840c10480c064000c0e402c100c05044010480c0413458003940e4000c1c12940880c4040740100c50300703030204244040010f400c0054a4800207410214411a800d10103044034511755a400341e600c48450990403050011002d0265004600218181805003045511410201d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 741935224 1250 741933974 741934001
    0x40b0430020f040f0b031e060a05040c06080604090204052d01031e0f0605102606011802070222050c07080a05070f140115090b060403110402120a09030201 68
    0x40030900040c2e55441c0c1000300810212800651000d50300c455a004151981c0405d07018411403100d0611400141400780503140d5076001c807503180c0c0d0741101000644405540040803a00ca458041c0045405400115402a405080065108030f940c0000b401c0e207030195010701c00e00a112050300610341840034090b11501d200800701d84a945155504843c003104065080041601c491069042082194456072055000b440c00d00840c10208086046442e16108145020304242101c0043d19080064803201d2403003000504020303803030304184000041c00c0c08100008103030700300a21030040e83d88111000143e0b03101c101c001c0f0325000340e1340250100c40000e040c81240703207400c1c8207510006e5070f12030840e0700001c460b20b405078580041d880c05144002c0c060358000c0501a0111000200410540c81110164101c0c1656003001c3c2d911103100003218450606190050000c010500200c0c0344281c8225a208010700014584280c0ca4102d90460340309440c10302d15a40c41d00140c1c5c080c141e09025014a8000c0ca = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 741936474 1250 741935224 741935309
    0x527100905060123030a021b010f141e190c020601180603050307030c0507030c0b0309011401050105040905100b270109140f010c080318061e0c0f040b04 67
    0x200b014186040c3c00462004c07902000000069110543c540559460022200d0f80388101200000c03c0c2d800390200341c5080c81010314110042c8500a01c94244602643e440800c1d0b0007a010759014014051034000c0885040702d41c08090000008140e21880640171a20750207030240c0c2d4140480714014215000c10300000d01e003800030500204002200300d94070250315052030110180103250041c02c140e000c2e44050034201f800403000401001040007503110b003094000030881c650b4484422400c4890030b010701c500241003400244105003503075110302d0308005004820740c6004e07600c18401e521544240280c0310903480344c00d509a01c42078001c5100841405c00d0a080d1003c60501185580c080d52000361188a82207c00400c9620790141041c8400d1582129450340d032842d22000448200720f00c498444441d11132a4006aa511103da000000c7c080c00450413101e0707520381c05c2000350a504003803419142c0c400c00304000034583d000e02000348006c001014841040d809000980c110780710854443c1b0410759034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 741937724 1250 741936474 741936497
    0x10b12010615050a0908030a09030b09070e07030b061e0403031805102105010f08070902120708061203041d0c0715020a05070623090a030905271009050601 68
    0x2c0044030140382103150860300c1d8040b00604403040b921036403200055000c00108010090307400f500e8a804d481c041c040c000c44030303110760303601e9a40d44501e0310400455007003400c08200c150f4032175080000141c4000301f4076400c040880003182260081c00d604a5010100020100101504841c28629074907500c46117403d5180b03014040b4180306010070f03045041003604a43d904155801c0b00d100e161124842d0380c10000c03503071a022001c9030882140508142ca104040e00020702d4162130084460500e141c00410704591200300c0183d50040010700a0f5911501ea000101380050003000940020500701008080042c003000e1346641d4847c01400c21a04101c0c03c000d4000412814201100c0c030190b00a401681d400d00840115441c0c00b42c048020241400d180700c0d44580100e02c8a1100d841ca403046101e06940c4480304600e5071401d001200502044200008102e54680340542039481c00f52902440e10050105040b0940402e02301d411a5200202031024440c10b00c00744240bc0d0b003c8000e0070232508044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 741938974 1250 741937724 741937739
    0xe01081005210d030e10020a0207030809031e03130603060825180207050607180308090d020d06020a0215430f020c0402031611120408010b120106 64
    0x32803070300807180102c0611144500c070080321080784006402c908240e0781003698048005000d4503003002955000d10400c81e80103020b64092088038504640c030f40003468007901d941d403032020640101c551694503000d20645d440303441004401e440d40ca1a00c45008e995651100503c000c151345a98000900300f51419005105590340016201c082d180082c00d040c080e81401000f942e000c2d50030340c208462001030700d1100c0000e40099009003800511900544015960b0380404076113a0ba107400c500035050040000800c00302c0c1090300101032400d8041c18503059441d50750089011100310350b204842e0303182d00041c10f42d0140e40c10b0045203182c04a945061a00b13040042c00288480c04c0240f1515029851100714802d210918103108120403041c20404600080075001901d005000c0e40c4c040050f006000c0c80c4105803030203100304d030b10444d400c3d11001100b01124200300ca240d003481880300b00c181319543c0034100900b6200c000d400100b801100200b06c02030204240030480da4010303907000d41c5070f0501c1414402c41d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 741940224 1250 741938974 741939001
    0x307030504062d050c0c041b17060d020607061803050418050f150d050706030c110609070e090307060f0b121f05060316061d0d0210140f12070e0108 65
    0x20f09140140d00d540c2a401c0c1e440c1809404c4020940c05403500b142c604201d403200c4003488a0381e03000e885e20340404015281d2211700c8801241c2403580710110704501d074010314042024043c40303405078500150380012404900fa0900d14440305030041070002c2001c1111442050400d0900d000d405001d0140e070410082c1d103201d81402424850750722030004c00c3c0744016107850211440054200007180c4c01e6aa441d1070180c01401c41c1583e0b413002400ba42e03518094020001202c1f80078550b44002083c4442c9800390308044008003500c00403450004000390004a0498000d007501101c5880c00010b400c1ca410040000c086005a522032080c1c00031f240d0014008101040c49501490590000c0b0325a82c40c10b001070f0620040c01c14030302e03003d14415400308070541e1200d020601d00110f00314121403184060208030505288000080d8410101d0451701c4007144903030311441400c080995a94180704102c81c45030115008008240d12024080003000040c60b400791504141c80e0080c00c0c446aa170600d60707020b0900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 741941474 1250 741940224 741940307
    0xc030a06081515031f0902100804080d020f091012150b070b0a140403080406112d091e03010c11030d0b01021203070305181c030e0a05030703050406 65
    0x3e518803029510050b1028410b207a00d0010485d0780c4454910f2901d4000018400440180d000703030341100d5400f0580707000304076940c00303a40c00403282030801d1400102040a0741c00848681c0110f641408414000d4803004802d001480194945803082c46440c41114200e41c0c043d40b19080c00318000004000c2ca1405c0022174040c507400404240d0956554131414002e00080c1400400c910a448208418035074041c00705406640318003418040c07200030158108680c05224500c200000c4486228060480c0009819605d0400c22003840c0c104041350001410319456075100c2c0341e403910080c4000c40c2c949400c0c0304080200c103650412020988003180401e5580c01240201c10010342d4481074880143e000f0450907880204610354543e880c07a04442c004c0240006443c0d06101c081e0b030103442c0c0d03260007020034850680e50343c5c0c070400d180300c049004086019004620004040340a445482004101c080c4010150707280a52240c554861400340b004250391000311140364054081204403040c07094100d0700854 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 741942724 1250 741941474 741941491
    0x17102406030f06080604080414150901030e01060f1d06090403170a2a110105220c030206040303030b0a0605040503060a050402040b030601060206060f0301062105150c030a060815 78
    0x6039104804580c074000d24403504002c100f80305c2e6004102c00c2041a80007801540c11045051807055401d80600c6500468100502400241400b6a10903035100c1d078006041c9000300b100202d2826625030381c3c40c1c000749030f40e00107d10340c24038460845c0d288030b5910452504000705650000d900d10700b90710000c01514544100c1e2006818072404200d44003180d4000940ea08414641c1083c1c0d0144180c108143c0c503105d006035000b2500e600d50280180e28180310b5144960407249104519104041c1c5140c00001c01c0501120f01c012072207400b20140e111034000c2c001030b51013a28005410110340081040b507114580c4001c080001c10003060180340c80204080f03800100c0c0d42e40105658546100040103825004440c9415204400000440a5000032068041c6c5030503101d080c10407135001c05042c00e8075040d025924005140c3c1c41c0520641c030a1039180c68100f030090054840700008002e403210b40e1903090b070342c88101d40710200c1031041032513080c0311301002400345400030110a0804204c07030380d0302403006040c2035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 741943974 1250 741942724 741942731
    0x273717060609091507200d0e0907032004080f0601061e050c100510120b01031e0503040e040c150e2e090e090105040203061f1710240603 60
    0x50700c1040812100c81520007210001c4c1c1c0c6440e00000040c003843e0000340007526050f041c030008801e14404101c450b08000fa550341c1d82d20324035441c410700c01d240c0006001c03841003640d200c1440030381c0684481202c0e5503045199046950304d1814040a02c0e016400d4402e0b5902d4008100410400d03410564080e200007511035100c1d108150b144082d035140c00354110110290184d0380000071201c001d503108901c203031030040c01480026211462110403007000c45c00103000000a40042c0301007121090200310407925041e011000460365690242990055402683c00e10540d00500003040043c440c3c21028240807030b9030841088900000400040340c0401581c000c110507500070800c3d1011007050442d500d4812050b0b45084480c0c40004e241e21118418951400310f0a4040f4607544e506000b9240211740042c01800c650301e58058041112214078407070080c01c81c2e013031000924465228805075000041d4400344c0005809890100103541c0fa03100002c44580d080401e00082d41c914007003a0041d20010714000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 741945224 1250 741943974 741943981
    0x706020111030f25080901050c0c19110a23030604020d020f0102120c0f0118020306010509070302070b0406090302010e07031e050f03030a20273717060609 68
    0x2440911054254501d21381c035480c0152103a9900415a5400f8894400c000c0181e56240c000003a028050b945840340340c1d0f04401c00119000840c0810888100e01410b00130420110140016100d1026907200781a03060ba880111401499441d42c0e041d100c150581c007622081c13800303500060359403000c0100248101c0100d5400c0b05a1f920030400503203d99480a40315a9400b88209a00e03943e842c414400c041540c200200c1041d40820b0420403a00e0507400f80083c100e036401c00081048040c3c00528ac5000c05034244581b40c04507410031411800340e03001300000107802d402820001e00b51200500d00014541c040c2400300002180521075400b1031203070440c280013080d002d14046040c25600716071221207210100c00d10011450517032001c0103055580d60080044c3c68001d182001500822200d8090700050902100302d04c0c20480e8800b81e02d4030f006000f0050071920001c42007205000705000720b4000c0c0c610030010700001141480c1c0300580079020078091088039520300d2a60385c44004003220302400c40803010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 741946474 1250 741945224 741945241
    0x624170a0905011b120c05040e18031e0702011209020a0902030606070209010305010b030c0a0803190309060219091e050d1a04030203130f050603281404050706020111030f 75
    0x2031125104ca0742c43c2c0340c003810300c220014100c6405e4045a03110340e18120740b40c503083d8000d008450490b04c850b945440540e50b80300d50604c2c082000420920540010000300011a1035110300451414524000903200c800d5800010f0403548081070074042c0c0d91030b1524031009640c415482c1b01c216451024050390380d030355a00124585000b200402034020043c00b00100c03c000040d040f4026054041d8112840140e00504010000065114106068208000807585581c09240d4001c1b078800a050100e602d02456035a00100c1e404010a0005032002c2140b00b00039580c0700c500c2c40000e0000020380d540701c0d000d4801c0303031090150b00d07c80e85105110099a01d41000780440e05401c1300a587e40c04208585050306000c0c5d1249d000154010107403180300800b140c2c1c1036000400d10306030354000e0455420365840044040c4d082c0c602d07002d21906584914041030240040d8050720008214400d105040703802d180c600f09141014580144081da4100701e02484c1103015003040c6c80c0c0c04110040750b0455611400304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 741947724 1250 741946474 741946481
    0xd0504030917070e07030b09010306050405070b040b0d0f0e070e04020f03010204060f080c0307080c0918070f030b0d030507020d0f050102280c050d0c0c090624170a090501 75
    0x3011003842c1d03a4070580a5035540208070001150f14140030040c0d1030755400003c40440b030303000b0381e595444480d8100610200e00c2962000342d0240c800c0044070702c410380703c040c0e519080c0c00c01d52181c031200340e0000701900c0401c0e050043c00503440480c541801a000020000c0e07440d074035203018882640d440c0c20000bd0135503541e16507000000030060300031507480761989401400e01c203d820036180842d096030080b440d000b9050381124851103180d5600002c0343c4501d15020841d40c0444101d0754009150703a4441d201d49051b00100e4000c00300d54580054600e00b1980c06006d072209103404600c9036060b07611510101c0c0e00082200c20ba02d50444640d0040c081c10318004034020152900900f0039032000c14540d0300002940d090002c207110400304469101342e0098112543c4000c104000c086030000c4004440003805800d526840502c00d401050b24141c54902130303011240181d0103440d99451041e402e4241c03e42368010f61030a55424604080302c03526680740300c9540140a0b0580300342c580d5410903501489000c0d803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 741948974 1250 741947724 741947729
    0x1509251809020705070b031e070302073302070b06090c0f041d01050d050a021c02030f060406060602062203111501090b01170402040903020f030f0a140307050d05040309 74
    0x40e50325101a10340c218180290400b0000700d80b64820358002003110259203060301c0c8100034035811130842d04000324450182e0b49018010205254003480200c0000b03a80c2d4040c0c980107441e44419151101540c280d812464104c0030100b44040d1040010101203815044101d91140341902d00c4046a1100a20306c1c42c2c2e440f404600d18140c410116002c180244140200c3d0211020010046648d1741c0300c60802010000d5060014096031140100500504110000c1142c00c0794240c030300d14501070305c0d4000c80c2c2402c01641030030000341c00c00d9007040104201803046802400c51480180b40c640f5008080000036101090f180c1a91100801448105072007030405104000d002401d4a00080f0212180321400c1c000380250080241406160b96055120f50740c080000c0304000c1000050791601e40070b020017440c2000c4241c0441c0030388000c42d00c01190800044c5050f101d0325074616950030610354014413141040c2e02c0f4822001040080c4103009070700c5010798425002c003500005940d201d41c9000d4912031140d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 741950224 1250 741948974 741949007
    0x206070b010f14150307030f02040b040906030501180c030b0912300c040509040606120b0a15120201110c360c030f0a060306050f150925 60
    0x12514660000d4000210b80c50902c140302c050501c002002035001804e041140e0f609030900008030110312907044151300202000005142580780c41a48003664090f41100ca83d454907480304200300b140911400582c101d005062007802a04ea95900d880200c2e24480a440c884a481c04621002801d01018601441c035090703856840400c126603c4450030030103480d031080c1101c448042c800c88604294035119088a5480c28034207030412041040c10a0050401d2b02c0d000d95500d80412a6483c000311020070502071860700b81c02d0300d040f0b03481c1c0e0140d84541140c00c610b034518400801015000b40d43c443c1e10181c0c2420001c00c03001e10505414904660207411a9106c000300c0e030b005c00c040c60140d00c000c518a00c2030154100040941d1891a015981034482c4041200f0410000340e403144009900c41c0c00010940f0f0100b0ba850380d0745c0b1040c054420543d6201a811a540140002c01111030050781c03000301c05030b5441d000c9150880000b241e4806640305a06030b00005018848154400c1c1c2c2c41e00e01c2000203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 741951474 1250 741950224 741950243
    0x14010e0a060902090708390304112803060f022107030614030d050a05130303171302030a030302031e04420c09091811100e0409020607 59
    0x7030401801404101105070700030220301001c41c165912503900b05200700702d01d4441200340400c003140420200c8107440380700e1009102000900181180c50000c5004034040c0503c140038115039010070000002030f151520800c04507404291031404801e42900849801010008005c2c2d0740c8043c0c42d01900c1545895000c29503200c7c001c03282d550088451501071645668100095616030b51009910028140c4040d49580202c0001d964640f18800405c61041107160003030820318800c000451450662300200d0114502c00c4094005824400c01c80390301100340710b8551080750307061b00402d03143c0b6941100a410036400200041072081c00c00103041540790390400203025450182070030a00b1099410782d85441c5085504161203000b40701e4000c034000d01d00414082804661011117070003d25203243c050f000d102c1c419500155a84091041d260b420744116004040ca1116103403080c0303100000d20345540700e100003031104a0000d41c88503844500d03a2041c0d40014149109000061450040a0009020303c42 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 741952724 1250 741951474 741951493
    0x10f140a02010e0f010207020d08032806080d0c0b191b0804050705150d02130b07050114010e01120f051011180621151315051c14010e 59
    0x41c154800e1501ea0b00002c151000f89144020250a038420070401079070100c034083c01840855540c00087d83c0000210b9040400da00a40d07060403181040d03902013001007075681d10200180803062181d07280c818801d02d40510103860941e01e240f486400607103083d03500c80e0011942d12100300c80303a12106002c0d03483c4190080b012840d410090030b03180211070848080c0500500094142400588001003059041c0d1140c14103e110260310002c0d0011202c10f614134140700c200140c501e41314002810b900d400781c4004542080710071041d1a054806030701042d100701f080c1004100361040c03110350466450788110245000714190070220f1034411000b6050760075500d444036100c0c00c0481403008200d500300f140500c035800c508810821410b80210003808030f159040c3c04546025005141c000d9034804084041050140d54800200766036a5021107400c440998481001100005c8034965900800d4211142d0500864000c0c84d0754648503e000c00615039414410040031250082d0040603030700c00c9620444900e142d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 741953974 1250 741952724 741952727
    0x3b0f0307020117040c050d052127010f03021e03010f08210711120d0207330c03020a080f041a03040f02010e060d11030f0c0c0c010f140a 60
    0x9215030412400314100c6040700201003000a08107100740e81116643c1c0d00e0b240351405011428407203410440301c1d03002d5002d1800c001e4800d40850207100c4012000c82c2e480d2860800c00c40c91415072506a120750004030102c1001d6a0382c4020030700b4003450540f5000d6102c4620102240040015248118282e10003000214814880400c2c00c403c031403041c400c4488243c41c1100b650358002ea65114141389001c10412800883c0c1824601850031b100a00100515102d4040071400c0c142100d413080016041020100240718049e00d40080381040c0035046105610440c9000040401d90b4140350305002c8140b5402040c140244580001030390440b505c07681d201f0a000707141069500034000c880400d071400031a50840d0001005503442a0341c04561906d84042c1500107603a0b000c0f426440d02d900102c20400b8080a00e0240a43d1400c21800c810990b1641051020a40c542100900482101c402030208075a12203001030b01000420082c20006140900840304070f498850304c00102c3c01030040002c8a42041d07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 741955224 1250 741953974 741953977
    0x4170a020406051806010c0c051e040c11190c05060a0c03020706030b0f090424050f01060c0c0b090103020d060b03091b0f120115030c0e01093b0f03 65
    0x14030850301040082c0c0c846080002044035009001200e0440700001840c079405041851031050150b00c0c0c28030000e40e60b00c00210001d03d01c0007200e1394000c88845180702d508150044074003141c164100241118415440b041e071b50131403454041e81e40561488a00c0c04d1044920b01c020103410701400c51070b912344000318083c001c603007001012401449072540014105d07200b403194001203070b00104000c06521488042044501d13000d4802c1d1221210592110865411162810140c084d4900c001ca0f82d8648a04000c3c0102c40590261088c0200d4550000001d0480c0c072255069070310040c40f8a486c2c05540780101c0c0240220703004c0c0001e00385032141c00301d074444c140b0029500c5044070000b116071030410f404084070440041c040d000d4028500f400c40c140e940c40d144000403204d044120002400440148122803503880300d17402507512894050060118a4000f42000d002d4000280c1c140601c032035401c03031040c400f0a00b180101c103141c0f00c4920110421f00792094080d43e01d001404a9140b402c0c4a00d803207450707 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 741956474 1250 741955224 741955243
    0x41d0c040806010b03010602150601050427061206061401020a0b1033030603030915021002130501080703050c09091503150712180204180602031312030b0306070e060417 74
    0x54800e8400e18027185c0310b8016401d100d000182d481500340f51400341c210b802d200380c1d490442031000c1d541d01182120750a07441200c001b091703008aa028103816500785942240e803d6000405509200060b5450a0360001040c0e0f480c1030b804200c1e2461035a60003800c060410164000c800410140d09401e4a0007120899030074107242145a002141d40c190001541100c840c2e21000307000c140e01080820494800341c1000c010081c1c00d0040d2803e003030250b1040c4c2c04980c00594400c845840d01d500622007940c0c03149207990300c02c0c07042c1820011400d10502c00c0d4440d014025005210b4041c0600040301c4981d03406804260800c050204c0f1522070444a0103000030000700d8040c0300050307240c21090310030300319030040705074080200d480491400706a4007407101911351710400480385120680001c00291940c4000d501c0703918034540c46a8580d80610f0310425805c200d01074a42094103240242046603008154550806645c0c106440c440e40410003240c4907001c0c90340000726041c0c1104181c84a10f5010511561 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 741957724 1250 741956474 741956477
    0x150925020a1103061e180a0c090b180609061f020601050f01020c06071b0b070b04030207170615040e3c03180609100c1106041d0c040806010b030106 65
    0x102200802c2071554944041301d0b0000390070305a42852400701451181d040d04400c002040c900c0709150743c3c2c01d180c0f804203009822241004102420050101984151140b424003120b411455000c0300380001c3d0308a174042c00311031054119801058083c0e880c00314108900f50005d840122481c50701c0c0c0082d40781c040902c0b0356806040c1c001c1040903903620100c0c503020b0480c001401d950038004562940501800d0031107803e070b41c0c3da60580000c03500200d5a405060901e1250303150403158905450000e0409141e42d014a5600c05108400d032440480802d4150703010b10700c0c122604054411800040103400c945402800c140100300103c208001140032203041c80c4c0c0c0780c3c1d1a0110140841c41d10240d103484008103440680c03c14080380800031000c00b410021040010a0181424075130800517001c41d10031002000494035458000040010185000d020110111206800e01d0700d40f19417047c000750b44e14030381c105500e001400150141220b400307840260403c1c000320b031285c5d07031680ca4903211648203024400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 741958974 1250 741957724 741957743
    0x31407081504110a0c020d0b09060901060918021c06050a02090102060c13060f0905090a0506240904021b01020f0901021204061d031e0c0f0108150925020a 68
    0x8aa00b49401003000000060b5841450440040c10480e01e509445404981c0080300002101c081003c148080e80520448406441d060921051441c04c5401c0e681c00404210308080410100c80301403000440c82d42d4061721240c210f1940103065560b0801e0018000702010710b00307818030250310b00342d50141040782420780858080380c440d00c8450f003881c0240980d219030300c4072412080c49503078851414a0b185480780d050121041c1e072104e0015000d0042207801403191540c58007001218a004ca07401841d51140c482d0450440004005200b942c0c82020800341c01180c000450016003d249107020030001c5088000f1511521101009880c1d9400521500c2c018803038403048400b100d80c08012102200c2c1540c4450b100b0013890244540d4118111a54652500800305920480010401c081d08a00d01520141c520101400c3c00c1050112030100b0644c104500c25040103000d00080c20314169103030048480c80f6681e41c1b04130342020b03200b0300020702072401c3d07104c003031001030700c6070006030010116200380c6610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 741960224 1250 741958974 741959011
    0x504050310061206090201020a14010c1b0f03200111070606062604030e03011506020f01020a0206130827130209030604062c0703020a320103140708 65
    0x41d00791402c074040c2030300c00c0d030981c0d10b04000540340b94460a0410b1060042c2e911101d01030319031800440d002105ca5540703944a00284261030340c01400040c00038907411415444100c96100c116400e0100315008003030180d4080f01d43c2c118031601c9444807403403540d680207000c00030003142001c00e0341c0c005000481d103c03404c0050101d0300d41d00580505000c0b005600100c0d41002031180d08100c1c042010384160240182c03000841455242805080e15141e490184010a2403401100919110961800a0180c2d01c1400350400642c1e011407229000102c00102402c2002541080102441001551845e031408001c080c0040100803000c000706020444a2262407880c20801c80141e00c680001c9942c950020000100010110307030101d20300f001180c4203a000b19070001d42134006291400381301030140d1b000358410001c510b000032540c0c01604070300e96040340d220318030b41c041100c82c954446400303040017100f5004d1509900c07da00810484403812002a851b00744a48041c002d0178003620000301601109609 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 741961474 1250 741960224 741960253
    0x50105010507022d150306010206090606061b0309190905060102031201030b042d050c101709010221040623070311070605040803070809070303020a080a12050705040503 74
    0x5036001c1980140c001500140d24134520104402d00850f21000700d1245003900009440e039041000c25003080c0d155660341e80c107140b0006071400000420021050380210200000c130b0311110103035504074003000b41d00e5902c0b0310308500a50544c020300070601c1c1c0001d0742940d80001004504441402c4854544042100b601d03a0303001207869110340340d42d81034113440a400400016100c000081e62050140c0b0814085c19101c0010203d0001801c20101108660f13a0b411401e00c4424020349101d00000c03944440f1641300904064050035002490101e994017507400104203130001e404484400c009200c0d2030b044942082410171300703950306031004c0d903686242500c81c0d0110054190b0030844440c4100c1200000c1d40c5400044000d4141040310410154042c448003001803001d00460b07014a00c90070940d40c4034074040c4001482514000c10000c4d152348100410004290046641914680c000c807419036945006182030707401d503850045528402c1e10b02420004c1c0c03258020060401e1b11030840999412038034034000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 741962724 1250 741961474 741961477
    0x9020a0b070c0b0901020c211014161b05010507112a0a0503030327120d02250507060201060603150918050a06060e060105041815050d0609060501050105 67
    0xa108403040750b03091290300c0705100507111398201441190101400c1c1c10108603541291211203240ca440d010011041150a0105030225403014500300604c640858a0074400e00000d040c2c4100c122100d48408141442114004810f41034241c40c110300000d1450711078000c0c0011500000019003107541d140b17070013a021601c1c031241e403481d000041d00c0710052015104c40c814069405540b00058403030000d4251030600296101d007800300b8000403c0c41600d422100d514241d07145144507500320b101003c0450100c0c000741c90704011020001030302d800200000b09003140000000d00c09030480c0e0001c120401000003400001e4444e903a0090008139960784041d825100740507002191100c4414061280b088241d03c0601483d0f02c0c0906e00003504001d496060a001002009a42c0c03262142020301c1989041c18585412050070718020340b925151440500b8040541c0072008002c40c1c03100280310444908400c80744c0030789001800c0c51640042450400c00800f40303031104440640c244400028598007500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 741963974 1250 741962724 741962737
    0x19030f2a09030b091b0d0305070b070219050f011a0a1a040f032105090a1202130c1101060e041703130204020a030902130b010f0f11030301060e041a010e1c02120109020a0b 75
    0x22100303400c0080310792b20060b010100070329450461040100e50300c0d0300d00ba104100c86005019030f015140407011400301c0e600307481109401001c0303184820303204c0c0070310b031101552032044511a6060081c6104e03688141c0d10385102e594099420001c0008022051010311100050181401d844403107124000ca00d003506d02d0300a5500300c5600450140d402c00070503540f5030304100c5040c07005110f02401d03140c2e810000f0403600940029000140302092400c080c500920540010341900c050441c51481c041e603c1500c4801c0100105240b044048042561100345101c10392081d9802403055445a0b17100c04010000c2c40f030741106a104044400c0b654469007100d00c1031a0401c4010380d241c000c8002e1641d000e0301c0ca1505583c4450400000780690f40c0344000c24006140a842155954100720030000c1c200000c1c3c5002841c9a00d8401503d83c203103400340c2c0c03c40110100c1100075109130802d070b02c0203540e003140301c0710240d400380d044400340c03554401213001984905411403007141c14031141511980103c0e020301404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 741965224 1250 741963974 741963977
    0xa081f0302150a1e030501151805011d100e13150e131b05101b021005040306110c240a021e19030f2a09030b091b0d03 52
    0x1054851541c103220b002404207140900306401240948000c00140c41d800304160b6000036a5280113102c01c50305000c14801d551041d1505060f00c00759a0562151a50f83e0312030181070007140306001c190b48440400c840080100240b124102029039032002d002c01e400003000e10701c074048900000c003d02095114008551a5000c4403002045c00c5c400d000303560799000f800301039248000512200008404d0480d200020401225200005240c44207010030000f000010005000f0b10000c18001a070340740c0000c5140e185c040780d43d01d44841c000c140682e2244a9a000940003901b007948007804002c071170b00209a40e40f110402c484501c1802944219021a41000320b003201e01481e02140003105c6a401403c24524101e0107604600c46000e0919801d60002e030404010224010180325515014460700447c2c0d00b5032181400205203800801034000341c0c41d100c01100c0b100003002c1030310f120310404105000e103501c08010006410001c0b100c0356222018400640000b032410fa1201c0340341800580040345070340c036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 741966474 1250 741965224 741965239
    0x2d1e07091e090f0b251704110109171b0406030321020d09050a0209010801050903040621181506050a181b03060e0f0609010303080901110a081f0302 65
    0x10301c00020103030600700810781d880c0051039032000110b1000308249006585000d641080c0003d16a0311060010214084400784218440000c0c0c1d00001d622066911650100302e22104400000040e583e0244d41c1d04959030341c4605200742080554001201c500701340e402c510701814007466408000c01c2d54024000103000411031700d001c514002c0480b1501203c5e603142c040250a040c07030080350700211606030784150b49550110b410002542400144070f40504400c1000317000d246440d06805130f4901c0703140301d010100303c0300c00c181e00109181c2049405420000003800d00115541c40c160550001c5101c0081d0707a54880c00e48000f41c2d111980c0b09901c115035024000c90038a52070011550701201009801008254446940000c111071268003905002003645002401a050880712086603800401e041d00314030008050029644e204268681103d81c186461115950740780b201c0d038058440040103140258010a84068841e0012700c1c05104141c01c4651000042c511125280041800d06c4081d402280 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 741967724 1250 741966474 741966521
    0x102040f0b030a0e0d03050114030106030b160e180f0c1c0c021006170106092c070b0a1205070f090902090105070b0c03010303110607022d1e0709 64
    0x340700c005142d11010f02d010002e5000302c801c0c0d01d6411708050307541c0c80703000035540e6006208a07104d5180345220000c041e0001c004990a40c0d9400c0c070b1482000d0140d4101d2401c1122100c0350a20401100c9247c0c5000ba01e071001d039683c1c50b00075004041050b50301c00c03140c4800d10000b6420082c0303881a03a0b80d00c582c2da40e609030548103120170711000b0113041c4031031000c500969a1100d580b49107405280c0c02003c0e0707145607036081501e80000320f0071203002d900001d5650b814514800071b00c0c051100322401003855659150160800186610b18000c01c0e1342c84004220b90100c0e240034580c1e000800c1e002c0030303403410700b05000726a2028411150420103003801804521a03040921092416501500a03030b0018180303640744c015076444282645100b00d0790003c07040d0b00040140105079006040c440300c4044540104060b040900c0065241c1110500000d103a00030303050902440c3c001c25070420030f500381d41d2081d190403a040c00f00b920042ea5240a50707040c0c9118108000070f51b01d110344140c0302ea21003880b989403207410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 741968974 1250 741967724 741967739
    0x80403050708040b2a01090809040209060c060415050f07230c2a09010b16030203040314010f14010602070b0c07051903051b090406090501090b01080a0201080105030102040f 76
    0x20068141900c621000f8000800c40e080310314014103035084041482080741c02c18682d10035050108003d800c4d0701e40d05107a010b100140b01d05003a0b40004c03804840160b103484195011660134007030109000c0d481d215950901091015031101581210a5482c00713011030342c0d4105000e80550000c0e141540080c000041e09100711031113000011140b090307481c805141c012141c40c2c56280c240034080c5400540b24101c03200e01c01ca42103528101012800340d4804000350315000d800d442c60b000d4000005020307461803034040c04152081c403c480296607c40a800d90f02068911107600130300300c000c1d0400d8101d203030048030208802c408021074102d0b00654000c0240b0744c24055043c00680110040380401c1c403d9101c08105030b07840d0419001100070520503801c2240c03560601e54600060341040c0080500c04201d460b030180c85000d0140c0e446a00180003044003611440c08030f0042001100c05400c1442040022a105001142101c0014000d984103100f503600c0781e007014200e1242c0c0c800c4080342c0c52545030401018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 741970224 1250 741968974 741968977
    0x15041110090b1308120903070e060f010c080d0203040c03120c1101030e01150914070f0f35101409161206180e0c01080f100506070b040212030a08040305 67
    0x90900210300f05160307a1440940350020031702114005440c0425100c0c2070342410001440103088a500c0324029007050740c04240300c0c004101c1240e0401414408001c14040070300c0c01c0b103142ea50041d808560303038a058100044006c199020455a00c10b582052500151003a1030700c000d801e0300841484154444000154010080b43c0300d600340c0b5548901e100704400140040410003000b088034045810441c6810203070549000030980002e100340e8480e80c0312182e0f444100c000000d01c0078100010300d41144115682800790f4220715a07034042500c00300c2c040411265085601400c441144280c4880d100c7c030401c461015801c9610750400340c0d800004018030f09441121800d22082e0800342c1130310510306070340350583c1d0181e041852419404d10103143d8181d400e01c0754108492030381015102c00c042d1040000c101c04806007180050382644c1005c6100c45048440d0741c3d00802c0010b0200d81d55000700e192600540c002143c0c140d20038000c913012045100030120440d281ca41183d601c2d2002d036030790355500b0b4805 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 741971474 1250 741970224 741970237
    0xc0618040603060506010e0102071206020f0d18020310110f18030607020303060913030c0605150d052d0703031d30070b04210515041110090b 62
    0x40501884210905460398401e4101541c02124003040c18544040003526084000d194a030455204e41000c0100f0883d20303d644055943c0000c1c09a956000ac8040d03450350b024000e0a040e4552500c1042d02082c41d080d41250092842902520350045103418403000310b415580d05160b0341c0c10100440c07480310204100400075040a0701c040304842101c600800d01d402000c130740820141e480007050282d04c1c40c10b03c0340f44e540502008600c20710740744156402030207980d40d2113004051544483c0840d085001c40c1c0c980240c00d0002600203c0980000d0400a588005c40305450360550070f50b010100203400c110041c0c0300c1884074400202003462556400311000f001584000803541042e0303000c0045607441c80e5000780c202c064070007450f400d100b20041c0501844030b00d903000e807410780c040e102c10804410b1510650381180c405e1100f1068580311030000c142c006000c408001c107540222a920714400190f41289030146018525080f03d0b0107002c5c06100c85801c2c0403110380007064280c80200900d90321207000344075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 741972724 1250 741971474 741971497
    0x9010605060d0b060c16210314030603010605100c0b1005031c020c19033c0f0605090609060a060e0a050a0e0703080901020f0a0f12020f0d02030a030f0903020c06 71
    0x1820841d0300351103040c008a0240d421b11a9007145040001d48242844072a42c401052520614000d50b03035000f420b031242e4a020880c10301070100001c1c001c3c0c0c2d001e6000700e00404000d0300d1021468554003000708410380c050f20484054040c2d101085e84040803052003000da41004d0700802c0394070340700848c400401d854000008218803c00154001c140c4450825101d5840b03e19404005582149028409815800900304650850028140818000590784034901c401074602642c0350500e810080511052800c1c05080c2d18104011700a0604000520724410203165040e54001c0d22201400c00a0359910b01c20040c460030090040780b00c88002e03130300c83d640240c051140001c014003610200fa0800c4c0f8194820381c4c0906001c80c140a60b0758051107144081e01880303000d40811110b903510700e0b00712206100c020344010050089408103034001c0282003400a074900869490700d0240c0402943c1307a00c4414a1000603082070b0001480d9100c1c1e0044050780c940c10f030040d080d01c10520090103401c3d0001d160340d14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 741973974 1250 741972724 741972727
    0x803010b130b0a0f11030310090e0a05060c070b060102030c060f07030204050d112107090903110f161d13020a0909051b09011d1009050106020f0609010605060d0b06 72
    0x10304040400c024030485070162074080d007844000380080c200710000c402c5d80003a81c10401c00c00c00c01203204500d4034240c410310176000404001c10007a05180c01c0380354100408070b210f41c0080c40362a00104010740200d0b8820318074105070f41c0e1035500490b180e000300c7e8040c2c804d543c010008141035030088240aa800f0381f1602d8014106583d030000502c0040c02c1c280103a4000c441c060118105d828100c282c1700c0608040c40c050040c807210050340503510082445001e20003aa160301040c00c05100f04880a04e50920204a440403420391500300c0d100c2900307088802e94402504400120001c80240d40840fa0301142c01290380782e40d03079001c103070000070242400700d901030064040030441c41c005208211855002d2402060100d0012283c500030310a003424091081003001e0040181c5001281e00a000d0020f050340c403003107a1a0000c9032081d040c00d40d0401030140703042c403001051041d8001070f0204450501004c48800f929900d110701c0c220b6166001d55500201d0800ca91514220680c0101460840240c6400d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 741975224 1250 741973974 741973979
    0x101203081e04030f020f010b010207030201050705120c030415210b0a0f090b010834050403050a060f0510080706110a20130b0a060c050109050609010509190803010b13 73
    0x212100e0a040b0381c12408650450003446110360304020703490092522100170422303406d0b4500080c0d683c80b220701c8003d040040c0000c4840c2040014800b0b00e02c43c038030f03e1021585071071280c182c89840f500b00740204000340070b08400106c241d40c40b41d10a103541c0c075841c035503014000c841c500c0014090842c52441581284820100184c0035101841c101d004040d084800a2070304440000140700507005803004444440111191045840c89881186a0103610582044001e140c0030260790718060b030f034000b411901032107600c10240000380d0420b11024403c0202004a5900c0d000a41c180440c0f40c0101c0170182d1194105004036806030206100f0034910300c0803141150006d07914880c1d10000d43c042540921610070b0000517509101c4094810310200c0c02017405118003060220b04200e030a031103484100804001c006090050a50103100c1154001c1b054a40515285428601a1a003900d20394258400c03090b50b1044968007201c507000556001059030314503440d260850119800400b05901092150f0500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 741976474 1250 741975224 741975271
    0x30b0415090f03110705030610061b08070308011503050f060103020d09061803020d090b09091905040c140a030507050d08090a031203050c160201030e030903070b1210120308 76
    0xb03800c2c22910a5444240b5544102115410314040307900c180d00917070000b070500014a0200d81a6401d0f03d445151003038440c84952a00500701d060f4000141500d81d0014400040c5980414001d058071032511324642030301c011a400701c007129001c0b120354a03280c112402160b840e40c86600102031410101c0c0c0d012421200315110710301142c0958030800040006001c1001c200b54050041c00f1991890f820411f02c02842c0c995410344034440d0b036548034814488a00040d4008581130b00d8940003040303d003010000d41c0380c10701d4103418400c605c2c000c407400d840174107a2800b1a881d0240d0108107999106000d03040c12441c210510007842203205040310100350900210a050710382c020b169001710b001d62810035086c00f171404090112200589121503400c000c002003d150300260120030f54642c1d080c64001981ca000790716260460040c0119650715000300c0c1d500145640c1c034000941452181840d1a00c00340d140e0860004042e80c0d20311405501151251880c00802d0240248551242c54207801300e5004803070714203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 741977724 1250 741976474 741976493
    0x40204090b040c0509011b1a01090f0b06040f050402130e090a142406012102090f09040b060d06090501111207030507120f0f05040c06080c04030b041509 67
    0x410440c4595840d6101040c0c6020f00410480d01c0389418441c2c41c00c05028002000d00040004413044804030200900c10001d050b800d521401c140c42c2e400a25558540841c407010b86a800e2580186d0750a181401c6c010707143c070200322801c03110301e03500c0004805d15201c05e00010390044e10b1040d8850740c1200340000c40110700d0410034441e6491101420404c0c030301c2d00c0e00d02c030f04607815508615140c0c00710500b6405120301703a0321041f071504001c02d01c00c6107039a0100100ea0b5114480b410201c04582d1003140c0d0b5081465030050300105408982034010307020344106000c00b29400f02e0303000e0650000d08000c078000d42841000540454010744e8041449a03154480741d09458682c00c91504400d13000484000d83c0000054680d0401c0c11441c05000c503050002004090b80283c00365902225640c1c2018010081683d000c0302000c08400410721003480e25080460100d8940d2040300003080c85140081c412000c03171412602644e80c001c0c070441403903c558031005416000e0f4548218095500d900c2c020200d0b01d07032031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 741978974 1250 741977724 741977729
    0x1401151101110c03030f0c0f040501200717100905030f161b050f100806040b010201090b01080f0f1f2012190e030d090204110406030c0801060912020108090c040204 72
    0x103000315130320b0070039840d0359142c0000180401c1f4a03900c01e00400d0081103000741280d08540c0c09107020720010481030f000519039400079604001d544550080050144140c990124124085109560704c00941d0104070b42940d0b00004024001d403c1005480d25581d401c0000e0030031103081c0000f2408485071980c035042041a803400801011520840400003840d08140b000741c1c807501a05c0840c2000e20240c4083c00e00320020342120f00c00ca0316615040040e9100754050350905800c00095141d03035035076a403144d85580c82400080030501814440108942c0f00180e0700c4080740c8400812480007441000104c010140c8001c10200754403d030358080350030706148000c1d00c0d080600840892031070400460560000740f424554059071800c0c4030292001c0b00e004030503542c010b400110041900c41541c8006001080050a140c120303030300c0458042005c2741e00d40e0000e41e1009041d00e4a0004e0398a510381540c11540b1403040c0c1c054040001c00c5080103500c80c40ca40c50b0040c4d81c0300207e40460642000140607600310344c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 741980224 1250 741978974 741978997
    0x10020c03060c03100f081b0f03120702040b101b0c03140d1e050f1606020f0c0c030115030305130e0c0c011407200a060903090504140115110111 63
    0x1000b800060290079413008020142c00d00f00f5103100707117040d031019200c18490100d4104650291746c0c7c80c0d000d131514900c2102800004060741c40e190b408030000184c5801280c402d900882c43c045051394641461248a0f01c0c466454440c4e40e440c10740f584410707400504801c4200c2c1c3c043c0c08030000100081940c11100364084142e40074143c1c1d40d100302c10041c20704102d6824134000c081481031100800c2c0d0000116101c002445042e5599104440038445418540b00402441d19200007a00c242d4201c0390710280c90800403040a4031000340e03100d020075090f00c0040c50141002c090180040000a0040c00140060100000c0c1c4020403907507a4003400d2442d00454004001020010700424418028481e102480c0c454402c2e4440505103400002c1075070034448100940d00a0044002500311001c200294900d80d00c264184030344405450018031400c92840360038083c6003000d010007000c1060340e0090341650101d907903000701e15076040d204640f0003d07510401207503556503e5070030140c1110400142105100c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 741981474 1250 741980224 741980227
    0x3070515011509150c02150406021f0605150a030f060605030603010608010e06011205030d110d11070203121b03030405070303080906090a02010c02010302040b030f010303020c030d02070510020c03060c 88
    0x18504148141822001c0e080304001d0182001c4c40402c109541840f030203c4985800d0b41c0da2085440030603024404251501c0503803401040003d1081c2d800510164039401c80602003d403511350501c0c0c481581d005002e450790084082c02d450381441610000740c01c0c00b0350b440c80e02041d408122040c40302203c803540c110000182d80041001110700b0240038841c001e11826008010030b6001805280d10342030180252100400720001d400107211082095a05500352408104800d842c5490210900d0740f14016071401103003445031890001042200f9030304180d401a0151021010b64103100e84aa0301126140030b003005c4d8084050422501003000e5480350348100014004a425818090308100c1c00070940d1405a0000c0104041d1070004581907850603420308003100c580c0351a1005038041d010356000028110f0000c020056040700e4034244d5812280a502601e002a41803403c1c10f84809101c81600c01691100c3c0c0b0409c0310b404c0c1502080c603207000701d1054032901c4555100103410400c0c140d40136408040f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 741982724 1250 741981474 741981479
    0x2090d030207090e03040e0c03070507140106030203120421020310090503210402010504091e0e010912030c0c1b09020a26130b150a0f0e010b0f030105060c0307051501 73
    0x144d04c40c9600070603d0740000c604140c9460546c102d003020080200c4040c08020010400060140054403552030340280242008042200141d008209034482a4424803c88504004138640a02102d09496104140c20742440341040d111800000c4281c04136014820b00a101c580c000d8140b2078402000d1251001c2c541d81c1c851909200a840441e042c1550041c550401740300050303800104440464814540200d00304c07030740c020107210361058825113020041c104482078400c5107040d80300103050b030320400f03203400844034846017102190155400301000c16200c3c141c040103c1c0c0e03100c0038500ca4500d090208181107885910342e5043c1d800240c040d0002c1490801c0e400e91003920301000715012042868004000e04e0b00f40c64070001524260000780c1015681c1e004503032000100001c003006100c002c0c0c660115142c1e41d00103012844079920030181c004454038004619411904101c03044030056040e502e040d64245020429158002000740109100821660b00050310900c00045520300406d01d40103d980b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 741983974 1250 741982724 741982739
    0x912061003060605100f1103071b05030f010b0604210f03090509070809061302182a07480e06061303062408010204080706051809070302090d030207 65
    0x401c3d40e0809032003a100f040480c4151a44140c8019440303a1914104400040310428281035124070f08026001c034000c000300e11a40041c81c141d0384c1c100ca1040e0216003058220106040c200c1e03075407032080c80e0b2201080008000350440144190300240f07401c07000c9401c11b010382d81c2c0c0120f1010301c0d5008901240c0303412800c014515080760f00c958868080d08041c41c06181c04061a03403a000024010851058415003070803e54485444112084c95491042201402d19580450300d214184a440341c85400c800300c02c00b9003901690649400992080da07007040d854554850b6064900004581041d144e06c41c00c00d86035010305401c619984040c816001511603041201d51001c441c4020502c41c060f440800084a4009444440d041140d4002800041c1100406071000c403460340c004110000d50300040000c1103e0206600820480341c14400300c0301a5552203400355070900071109200b0b118110a91a81203c0c1171803103a840d48101c540c580107281080d000c0020f9442c82c0c200c9401e400603401001b040c030405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 741985224 1250 741983974 741983981
    0x2703070e0c03040b040c2c100f03020915031015060507150f0f0903080610142704020c030a0206062d0301020f040305210f0f091206100306 61
    0x400005011040c1841e1000d91100380c1d2001034002012168034000207424406041d08031b1010b401c401320003048a41100c006000e60441e41841b040f1008060b00c08544035138480c80c40001210300d8600f031806840d02c0c6408104007030300b0041c45885400d40c000319401c5103640610110007443d412a4000403410229084042c103c1d045401090034428100f00c4000800d6030181c100051000040e801718964048140d10806031204603500e07503940b814a924401007503040710382c0c24841d8006545400c0c0c0c88104840480f0700c0e0100701841c003070003a030821010300c1c9004000c4c3c20030081c01d180901100046107080c0480c040745d2018165a0003500041101c441c025414402e280c1c0041c0110b81f0201840b143c000d11000202801c20f50488464009140e541680c900b901910b40b4420001c8505480320b07030b242442501c42844001d410250881010b11100160b0400e00b541c1c000c09d04004501c0c185445184410185d46c00f0710311081c2d000a05500555103801e04100452280720700040301c8001501d03616000059 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 741986474 1250 741985224 741985229
    0x807080d0f020c0a120312110c010e01092307051003020403030806010309081b070f080f10051e150a06030c140c0a030f17010b07150e0a0b070203270307 67
    0x110741206005141c5640c981c4815020f45160455101100c2c04c2d41c541030307504482d500c10203001d80d41001d102c4c00c08231800a01510980080350b00a003c40119441100c0c200c64185074000c01c4101d030039100140c0c41d124021428002444035040743c540c0c584610004616103c10420407000a40004061040690107004580c01000c2800e05102d600b46681d5a00228003400c04503003201061700078880340b05641041008020000850318500041c1c81382d048a8540904102410b030520841075441031079070161258603c00e00510f601301d01c40d250b1241c03400f10701c10406012100b52007500c4080c1c034941d136a90640031000700850b440c0060340da035131107601034000034284550301c40703c107c14004950740c5800410701c00c4a0302d074180b400f2503241c07804481c155407801003001410783c1007401500104040d0134140051034031500900010344050b4407108100d00f07031016810035000d02c0e001266504005410500d031309030810f0581c010340c1c0c01c045400d4603244502d07002c8503041c0c08108490044940c03134141030002902 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 741987724 1250 741986474 741986477
    0x2040c0215061003200a0207080304030312110d02120405010b0f061b0307080705010c0306050603060d0f0206190306030b07170c0702060706060608062803030503100807080d0f 77
    0x1401c80400384460102001462540910710400c41d8180451280e400702682c4840042650212005520003060780e030001010a805880b400d44042502074002050350102d903450b80d240b0035107c0d8042050400303401d40c0490008044402c0c0945000413060380060200030315000307548151441c007414400c0c00d41d440a21901e0140555500c1c484042c0c6a240846800402c1d1080c43e000c441c03036104801c0d1551182c3c0e1009400f0a0000c110641001410f406c44050300c1e5140d0360900c480c0761508200942c511060307070b81a92080e0390f81303964800582072480348280c9600040c2007a081c0030a0000501d03100203001c20310300001e82d4640c401d10400c5070000042d50000201d140c01503100c80c9400d81315010f114041c1c50b81a00700c030040f074070004640c6d6400c1120340b2554082410310076945c0d130391030103809440140c0d8014402c0358031084803030b403041c0780e6150b2841043d0b480480c500d02c5851500c0030b4566034009003c141da01c4c410001d000c2003042c81000040300030803e05000300341047c07803098001c00d1a20820318100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 741988974 1250 741987724 741987733
    0x130b091b0f071a0f0915040f050a0c030c0504061401030b0409081c05091507081801020d0f05150303030c0d0b03010207120f02010501050a1502100e0619050405300c0a02040c02 77
    0x24031100001502100d180310360602d4403c94946d2304007800b2030284088024028850261500200f040e5000070303004a1380300e0380c020183d158030740c0c00700000e4034040e000e42c0660a41c2080141c3c0e4642c46500040c108040241000036080c4e143d0301d4080c040d50011030042044900c4407600c1ea001c20700303071240d69800710034440644420300e60300c2c481e45c08940e8003520407030070440c410002c130744500e000d6004201c4c0c0a08010003156103404a65800002c0c0031000d403400c04540c40d010000300b079060134001c2000c0c4810018051891a40d5801481d03020b5040b0004910429070b80700c030f907985180c800348001d007507036401401c5840c5000c070f034204c0081040051018040c116410400100b10a464011419080d81c620128030300c0d10041d0301508900d40a5240c0c048240036040203800420b664002c40d00c1030142410003483c407420307a902c095a03016201d05403402040c0b40d00818002c01e0810401110211020002c0001c5403081030a40c0d00004e40d400012486005801c1400300000314641407003500040c0ca114000352 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 741990224 1250 741988974 741988981
    0xe0709020a1209020616031724010c02010804060e0a080d060302030106050a030c060807030e1902010e01020a0c0e0907050d050c1801030807020d060f060b040302130b091b0f071a0f 79
    0x160140241b036003401d400d6550300a100101401010700d01d80080100d0640039061902203c100120707400c081c1c031480f4410441d030404406501c03c050058090790183c544a015445540d51800140101c403680449406803070102e600003004040107008205202c034020420314214010142190700642c4101e00c920454202040000c0a114080044a0507401d042c280b0381d036400c0c070039805840c3d1000030700780300d0180b80800d030222064900f148200c503000383e842000c00031480006a070f03902c40c02e2074003804102800d0406c001480000800c0d55000d0580c07420b442c009580d03540031400e14450700c001152160010005c4d0426400c1403440414220031050862600d5451622105018858100c01901034030030032144200740901a007000740d641c00c1e107032403c11009690740f0f483e000a41003804100d105034145004100160f03100c0c001c031010701d1801069004070340c0318003080480d49c1d090460743c0c0c0c000b204180b00c3c0401c009598009001107174000c5800480d6044140043c2d0b15560b00240b0294006c0e1803070050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 741991474 1250 741990224 741990229
    0xd0c140402041a0a0212031e070e06070f1703090d020c03030702060307120e1b03010f020304110112060317040302210d0c02030708030c01090b09010908090d060e0709020a120902 78
    0x12803040203c18034181d0780c031003681008900f040c520040e1200e404c83d002081c41441000c0064002015460a426034070030b0301d44000c11254101c02821040e8085011f00081e404a050900c0b900c02c407078400c460608446500002d0001c850300207c800c3c41c0745421071410b642e0610f40500c00b41c0282c0c032046016601c0d01300700b5400600140406401c5c0b0040249050319003110041551000d0a9141c102d82150f002c60010207020780c955083c0304520340254202840e900c43c6941d140296400303154000d12803003592503c80011580c0b10840426059510340f41d0310f000001c10503600001c0b80b401c00503c1a10790b0b907410347c010b0001c040c00511000d04142d078440c0081000c035402251031416080d136840c00481c1e20009000092504040d0b03000413809010018400d484a234056200c20b601da442400c80c1c4d50303603a450800b405d00b21911444054006107080000f0401894a20410800c051040d000041e00300c500311025840c240d003580000c01540c1d0b00040082d031090300001224015505800140165804c0390301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 741992724 1250 741991474 741991499
    0xb1e060a0f0c140c1915110a06060608010f060c170a021e0c040e0609030306010e0409050a0b0403021002040807051302160b010513020c031b0106050d0c14040204 71
    0x844404011005030020606881050180d100c103402c2030060380f002d03854940040e00e0308440b04109124100515110151901400348902290700410824240c40701496003582c4001c001c080102c0700b80580780c505c0c0000f030101d03c64440501100c1da0b4184107581004005076121149400c03030414043c40828000004840d241d00d15454510403c880b0385803a40c2007070507440e02c0441e8010303540c4540e59400d403007402d000000e500d0400c0a001c0741c040c0540147e8030032240d120103081d01c110600703030003c00004806501a016a00000780c003d000010018010b4a0741802d1148426007159040a40e400b84800c0c0355041154244104042c101146401d1500c00718598036800e91082ea4001e4440802c000d9050030180c0c10344544000341940301c50081c1b11440e20309d03c1d4000900580d441040116000583c1040920a54120320000d400035864688100840b04003601c1d40b131080d140c29034882001041940320340c40a10395080c849c6d1b0aa04840d810200c001803c0c40100d1000350003540305002c10020540ca1b05ea = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 741993974 1250 741992724 741992737
    0x10815030a17040510031a121005070e04020712030b03060127090c18061409040b1005030111132408070210060312020c01020a200d150b1e06 62
    0x41104042c0c0e00311258003158010350b031005a1104d00d121408003215010f070401e00101d4200100031440340c44030710800c00d07003003c0048040f080ba44030072a0b1103100519a03000341d8202c442c0c1d00308480a10503e0000034144e0384100022640005152900240e03607800d40a90754101c00100d0242c01c0c258103200c4031010012000138114500078200340418000354080e4800c0d170440e50044105189a5110901e0410300d401d0001459985454940c0c00200700003422180380c000080181502c00f503031140d4445104041d80a465000d100e80c07640400034441d80c092040c041d26125442005849040c60301301d03001418055401403820310b000c84001d4101605003c0c0714002d82c00036040181658440c94000ca1030208216903805041e854810044140301094486400c0d5800d1a804c81b41c0b6076074107a00498440108510040c031340d07039005404180001c020521a1030b42003020b810f980300c078403140e1654541e440040084d070706c0c80781e0740c0c0010b10240d091803020b0080e4cd50708108821422588400460300038030811 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 741995224 1250 741993974 741993983
    0x903061d1903050c010501060903050609070e190e10050a110705030409150332151801020c0604060b0f0102030f09271f08070f0e0606090a030b0402010815030a 70
    0x240600030806010784161340780d001da881e000700419a15200050903074901400150b03007911440b00020040c010018002058403000306002c0f845803a46030244003484900d01d892003a0340e0302c807090811151000c20282001240c04440418641010701414003203404010611a84a508000e648003003100041200d0894001d81800100040310b0780c0700340b03440d00482c2c000401042085080c01100c03410b904030301243d500841148000e41c07c1e140c80c0d10750b5818540500301000340920000034089024102544546081040054600180041814204101100c040300c0003545c3d102062502d0a180d5100b49076404280002e42c42d11000e00d01080050080d070307030010302c2a2015420000d00e519100d004c056860b03c40c0d0303040319160400440228044404208908641e81005800915050002041c6049036617a08840c9210741c2842d0841140c0000240101d0f04244100520100350701c03103409500083d070003580c07100c40c0c40c149840018600e02003d071103070f0f8010b41209403200b01954042035200c0d415521 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 741996474 1250 741995224 741995263
    0x130c02210a090302060d020717040305011a1e040e191103150406050405070302060d0902040507080601090605070512070515070c03080c180312130f0602060c03190c0903061d 76
    0x51b694104c01902c61090014950018150651040300c40d44004c0c1040d01d01c202c0c0240f000c000708007008a15500024038007944450300c10f0064038544411200e44041041c00741003c0b44614618014a20301000009101070440000d03001c90188100c0140000d1810800c03000b6010046200c601d0507400f0001902c00f030440366444010402b00300d0304029500083d5800f400141c3c441e4481000807000b0030814030300703070700031810200001d001c1c500c510744942c89a0016110303078001d68241442160540c0200c0c10417125441407a0700003452031403100140803203034841d00041c00c0c4a0210411005044000340000052201c04400300001a4000454035400000b645002e511a5900d444d2200c0585445400076014000d0500e408010401600101350070340e00f590007440180d40d14601c0b03004a41152084800680000d40442c002310018401150011460082e15805081c100301c9901140c054904407408920303a2402001080100c1c06101012482603c4121403010044c2040c3e0f08c5882d11800601d100b41c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 741997724 1250 741996474 741996487
    0x1020a181a2502091003020405060306060102060106050a170f041505151201420509040209061503090105100905070f140f070503040e0609090c0f130c02210a09030206 73
    0x400b0046a08140c00400720742050400000109420842c1d0109a000d542011700154050400040d120301503641039000389040da180c80c1c404c640907044500380b071080100a059a0000441c0b0000450081d429104440b00d82d052a1500c03002c550b0181703c0c50601c4505000c02c2165441d4a181c80c000d4000080d21031020f05016580c2c1b040c01090103071000716a007a00850081d80300b100f840000c04a2942d800054123214044914084110705103100c6c6541c03005031000020014242001c91a411517405070200707190b8403540d20000c4058004454802103030f9074070802c00c80000441d2005074020503141d0410841401e182d04002e01071b80c0d200b01500c091010a405891900901c5811500d003207900440301e5032907a40d175140c0180c480e4014414850199521004101036160044119000d244c100f002441020030395800d001850980b1102940d0144d000442d10701c40c22840e003c2d41704102d50b164090054402c26190040e035440d4101280200000240106803495820800b514256070701100c0b55a114007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 741998974 1250 741997724 741997777
    0x130b04110a0801021201050307060e03100207140a03270303020d08090f03070c0302090a2f0415020a170310140301060b0f070b0f040825020301020a181a 67
    0x180d0080d8910f41c40051036040e6500c8044480b4180e84040b400d40f00415900d884c11980480045515070381a0000c40c01c644525181c4d0b802024000e1160a46c1d0000007401350b500e40c1410184101640410703d03110340c055900040741c8410fa08103804658003080325055481c02503480d85411120b109102c900350108080c9103040125114050f43c800440c1e545110b14617022031341c10b0385444228090101c1d01c010415003d1346001c1e4010850a0186028242050040c1c006216200402440c41e1031030800c03010501c2119500382940d1b01d05190000e0507e44150701e08513007a00c0003e0a50f04072500244107012984024501c810101c40c80c101d841d284012417400020300400d00d50380301c8042c41500040051070003180101901e08640281c8231601142d42d00000c2e0302040c04e007260002c10160301000605402e01c1c3c80c0c00c82c0464000c08500b256500701c8198082401ca0b1300c00310212010501c050b1050f0610070b0440030000c09040040b0310b81c1020f881082d25410240284030381c402015107800410076800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 742000224 1250 741998974 741998989
    0x5040905060a03050607120e12070305070c031725081b010e060403081f0311060c0a0c08011e1a01080603100c0302120106050a0804120e060d0e0105130b0411 69
    0x440d000f50649025080846d0b025100070344191002071058101440281d03542004aa480b2840c4500405207180248682c0e0846417540640c1c8100c5800000d404088085444814251030640b000140b440c0c2e02c41c12641a031242e41042c23140d91145541c0502e04c14001080c0c4010341e40c500c2e801d8900000351481c50030026000d00b0754107035090f006d4440c01040205066000ba00180201e44d4900c881d46100e07055608010202014080a41100386c0c4000156050612000a10100950000340c40302c074422a030b541e900030380344c5070b000b926075070f441d070a00d020a41d202d01a0246004a0008200b10711300f009580c80106242d03911805060200220020304c06031030611010b58100d509000030480c820381034102030025080000706110041e195400070440d0340c09202114000440fa03101e9050382ea0303981e0307144069111440d800d90b0030480c0f44120b0780c04030348410000e0414928510030120341001004003480c2180c6000786402034521109503550041440203c0d907540182d080340e0b0400b041d150800c0480c40c2c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 742001474 1250 742000224 742000229
    0xa0e1915080f150702070b0a0507061103090f01061203080c07030905191a0a1d01090f060c0b0c1e0901020a020918100204140f1203130618030305040905060a 69
    0x65010b100801002c540c00494400007860b81200c400500781c480c0d2a040382e50348803d00503002c15520400034140c030603020b540500605482810003003550104c503205502c203500141c412600c594803040222200650a000e140041c1c4120300400d0b000c00241d80b0000c1840e03030007030048010000001030031018188a0703202e01000c1d2101420300c1101520415002c214901c00707208004d45203004074000216102080101c511004d038640d83e40400f4040c03503011032040001050428180b1590380300c002014051100107000400241e2100c083d00642e0b420281d401074002410b1206890b81000054251020481020144141d172001161900540d00c010b0389040c00c0c100e0041d5020003900c08004641c80c44042c5032515203c0c807005d8408030403c0710f2606040c0c2c0030360300980180007030701c03800030782c00b81018040c1030307014030005129406001c0410426030566002c86c001040007011004103005082d00144424038070900071040c40c07002495900c001303100380194000c02002c1034840c0081140c40d526210300402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 742002724 1250 742001474 742001489
    0x1d190504020f03041202010903080a1802120f070f24030b040603080910080712200c070614040305030d0b0409050f0106060e0105040305060403110a050115050a0e1915 73
    0x1620150100382c08040d41044904551180d804490802558818024a15040e516440ea41510b4450041f494003904040a0031500b0b2401d420142016959901002c0c03010700c400d00103024490090074401381090f031150044407029440c01010400c0d07543e0383c841d078014200603141c0c441c022510000110082d1030318000890b4030030304101012050040940042107848400c5405070420640c0103070035242d1781c5040f81e01034003085115152405151241e00a0500010480c00d59007064249942461143d00b0001d086911940b003001c0520020744c110201b1a40c205084032280e0400e840d641d101c0c2da17680305854104529644843c203544c03254607035401c01802d49a1200c1a10007003071020032628028581c501c03a0000140794540d440886500482c12502503070b40040182a132540d481c1c030240c0b0a2880070150002611503040d0300790210b0001e104420401403d40301241c1c00d180307400208501c141c461381284100d0301800d000d214000074010040d0a002000c108041484c0404104407844001ca5500220 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 742003974 1250 742002724 742002727
    0x1303091203030609051608150d052a0109082104051206070e010e0d080a05120a0606090611030316020313031a1305100921021c1d19050402 61
    0x3010550075030020f80542c2c0c42607404000907510070f0784d600c4d00540d083c0c003800041281d60000c500710100c82031004a61980150014044441c3c642e1a1850040d9007201501840726040e43c40707000816620f91040300307034001d1030b050300d49500780741c1b0700d50f1980302c2070150310f107404245940c0d681440114815240284001032080302c201c424560b400392a03220881d00f02300007410301d424804856016607000040100c0c0030b4800034100a155560280550250004000b8401c081c888c0328850605560554418050070002003525403074004003800d0202207400030400e00400d800100060040001030301d070b00c46104408081e084480b41c00c01d0341980f041517200310200c3e90080740403040c021611803200700c50341c1d0484400800c2c0c1c3c4060103016904021100109650401144000798454503000090490f010303c03c12003946409581210b501c64100c95501e0240c1c10241041a080b003180d980f1115130700e011b00301155800312141c440010000c0d100c64543c491105100207680e008400640a40039020140046 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 742005224 1250 742003974 742004009
    0x32821030203040309090e030f0c1006031a06011403041e0c0602010e06060d02030307300c02030c040e0d0c060e030a0305180c0f310b03011a09130309 66
    0xd010354000c86040e00442e68026001482c03185501c13581ba0488080030103107007400300324044041036500c440030008840c401d00c880b032101c100e034500c02c4400942c071440710f12a03041c0c0d081482c0700c1300b008020000350500c920000c503510781c0c0000e90200c07940140d100041ca50400d0300c000d03419400688000014190360441c030004910f0301d405500209182203108201c4d00039548502c10000140b00050000350990801d00c2000001203407101c1128081c0c012061610040051078411921040f002c243c540001782c2030801c0d0400d5080901003140e01d0b82c01540e042c00046442010b007941c0e407440341452004c001c074a03d0340609010b141d03484001c8810000080e26541c0924650040282200340c428444040344418020f12104001840315040701c1c01403c1100c0e903565080800c150740b200800310880a00001001c0c185503581d50544940c0300d85904000030740495501c0c2030508603042284c600d06800a2300300d00e10758a50b988031500354800010700f01120420024942100c0380203c5910100d129550800e05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 742006474 1250 742005224 742005227
    0x1f0902092808120f1207020a061e05010b07170d0b0603011502151009020d1410030308010b070302210c06090d030c0f080403031104050a0902040e06032821 68
    0x40b10074203000c072407080203401c41400f100d1180d800070040ca040200040603009a00e04881a484201c50050311b8520302c00c1c2e00d0300401c0d10000001c0e0000c4441007801c01104040510607940034145424445040c0302c3e0030b07a101d003215031402040c1c541c81080411011005120381e001044201c102406694070703541d4070400b002200e101a40d0300800f601407100e900d954200811240c0341b0501c10411003228181c07814900c00020340c071200500d076610b920b030003c000e0f4070740080340054018507000c40e4150201d455801c1c0200385880681110010b00020050311002c66800204014008c1c070351802001d4000e20240d200c0c0043c0b08007040c1c1038440c0103e00400134841ca000c10310001036100c075203007440300700e0f1801c070202c80b03402c00d007040f11020804001c04100840c0c442d902c02428440700341840751905450b4000150444007652110298a8000030305010400c0302040898211105030b004110301d2030340c04441e4200340a032582d010901d069940000060000b40b68481039804048183c2010020031082d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 742007724 1250 742006474 742006549
    0x90115080705090a2a050d23062d0f030a030908010c090303140c0a0b010b04030302120f040b0f130e060f09190f1d03121f090209 57
    0x10b000d00c50380030b11002400d482d031540030324a54011380038011104030082d441c9210a0042e04044035042201c1800010300c2c00d41240300d072000c00d80506645030114032008000c2c56540600401090141c040313900c0980040c180b14003121901303041070b241c24140c4041d04004c03410080003940902e85c18800c580d41d550905400100081c142d40c1c0f020024001c64071990825100402c440c03000600080e210804100c03000e80c2c40c00603081403403010703080d681d40c1402d0380c95500d40741704c081e04816641703c8001010800c040d0108422088050828002420044610580015402944600f250f8420001620025002200c00b107440c50043e01d03481d8100e91340c6401d000d094601d0120740e1203000b16031013151a9440d14100040c5440f5070004140d60032074414460107003000d05850b00406120a8490745000910255040a4028894640010340d141c5160781480003070403901619201c05901984448203030030b01090000301c1542d021542c0540d683d1a01c40c0403e800803164050100d54010701403001c0d08415a049 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 742008974 1250 742007724 742007729
    0xd05340e04060b0c2b0c14010c030501050f190501050307020307050307050a29010b090f0306011503061e0501031a0d03030e120a05120402150d020406171e0901150807 73
    0xc04642003405801502e02c0b40700c14107440400c0c5c0104886103500024441d5220011880c461081504800c4254041600391408e4003001000700391204010f00503424001010807100344100c0f0030007051040420300f03034004841801868104280000014101030003003048490391940641203c1da1018035040c90b585401003800104ca1150074411084038070400f02d8038814030040c0d17805800400303902e800d81c80c805903030069807241e8100041c84da84e8080343c2d03001d03c002d600900d00b2180034813820504035002011110745400084044401c4150b219081722a04840c00540f1020b0070005100d9608018039504056039006007a4400c00c3e2110080402d0b13490340100c0b0807080d100b0219505840307981c401c0d440c1070155449600000c0c6041c000200c403204440c80f074540140c006480d42c0b25107800c04c800c82c17565901020f40d03007510940000d400c1009a51240d461041044001c58001c090f040c80b81c44489140030500745d400421000c00d0105d00c074500e0a62001c007400c24500c0815071091703590340449448032078a2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 742010224 1250 742008974 742008997
    0x10e070501031b120e010903030e0d02010504030c08070203100c020d03143d150905010905180406060b03010f031e020d0b1008060c0d05340e04060b 65
    0x164000142540030703000b0b100b9165001c010080c0800da030954112a42d031801000d20030340d182c86985000d0076a0b401e1262080d2940a0382c0d02090f51808844000d281c4158440800c04681c5440e0130407010a92200c001e01c0e803141d0060300d5540c1d890050000a140c03c8960321401000c0786040f1001d960035400203529851440662018001440c0082484500000c1105c4082002c482000b41404042000c0349011840014425036401e0072030000d42e400d85502c0a4108540080801d0a005078082d04140403500602d030074a030440c01c0904020201e000060301c0c55086400e003402c0000300c0c00301716081e00000081e0940c05e100c581c03079680d1410002c0700300781d040c402501c00004130481910341c4001680e010b180d00d0380103000c4000d210000d980e4441e26000003400350002080040c0041280081404903070f00480f140ca2501d51540e514803410780840f01c001d0140b03040038076a0751184464200d004c034003280100d02605000002c0244450540d008894100c0c41c1c3e500520b0568082000d820120280c82c050121 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 742011474 1250 742010224 742010233
    0xf120309040606032a0807030c0c0807080301030b01080703080d020306010c0f0305090a0905010f0b1308010906091202010515010e150c010213150e0603270a0b060312030609090307020d0302010e 85
    0x180c0c01480401d03517201414800046001d400140d081c0d01a4201142075101d92400c0910308100b91520f40c40754010f00011a82040000010402c1c80301d40958140905010000f0f01b80c0355146a5501100340b107a8891a010381d6001710010b03c1c03581c01103420100c81500601e80c909111064030b0300801c107070b2141e114140304640d004804200d072031a80c801d071416104800c420004482c148548204940c200a0003085c01c28411140070aa800c000e024400919100e840c4c0070400d04000d01c1c3c022421401c03441d0000842e03140c9400c200da451300c2800d10380200c4800f0308002c001250290040303502e00b00001c0d8a664050b500003821414206c05600400440c44015100c20317100341c480160750f803060400a0740d03100140e01c03800e00b15800e10341440210342280100351604102407104241350460407809880180c83c1c0c103c6660001070042d510a61540080700306d001d0201081c1080b45014103002c090102c0f0701607517140b40001d40ca810204111200703190000e0036450020018234000b4041d010003500006603015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 742012724 1250 742011474 742011521
    0x50a0605041104030c0b09040204080f0f0c0f01020a060f020d1d01050f04020a060f02010b041a0406050303030c040b130506130609060804021509010c120f09050f0f12030904060603 79
    0xc02c4800d031003d0300c0d4418001c268041c42e2040d121402c1d001040d0aa07801a401c0000040b83ca8007048001d02c1120010060810000b40442480c01c0029400c0c140b8042e4100d414070a41984c1e0124480c00261340c13107080010f1864030410017100030700401c2c01e281d21107840e10b034a07010602075a45c1e13145441407a19000303105503641d01d091400703000c6080d103000f504848112411b01106020700ea002c00803411b1131000140800b450030004060307840300c030a841070f6485529110011420140698000350509800851450511403d15159071196100d0011000804030311900d1044a0414a10040000070169900c0ea00d810000c05944555803242e440840c10a88001071101c2c011958a845070b600245105403100503106140c400381d0110700b5060406c2078400c0c29070005006d0b0140000101510f50303401d070455281c1e810250100c585500218810b15603844c10880540ea1003003076002c0c100094500840d0003000d0303101103145010300403c46a11504048000c9039070b59150380030100001580d40c4402c040030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 742013974 1250 742012724 742012751
    0x105100e15030a14150c070203060f01060206070309020f060f13090b0d030807030938060a090b22090c060809060f15041401171504030804060b04050a060504 69
    0x424110765905a04420300c000007040825001c0d842820112080c0e8070802d030041c00c41000c1c031504546010803094007181940c2942010000300303031f02982e1400c0780b44181d410840081d50726000180a541090f0f1181441c5086403140c45c0207105d4000003604541e119036000b085144035803c100c4441100c4400b55800080e100083c0c014040c80d20006051200d00201c680c40444010300d0092856050541303501d171240005964094081c0041803001c01e1f80d00c044103800010030040a640113001016200b003007804030742d42d40c0d16410021104150303400a4010400008910030b00e40c1e00c020f50989892011402150000c1e0b500710424082c071440c03006508030303103c00040e15446010303210139803554040400207005540008031590400da0702c050000482c001003000405450031556035412010788180108060384003680004940902d50006e0300728070003641d10904100c031703000304050108040c030000319082c490998020801130310003074014842c42c6041d03203640010b04400e11813107002e13528000c0c0024442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 742015224 1250 742013974 742014001
    0x160b0d11030705180a05030d030b090907080c0409170a05040e0a180f081b0f010c1103030a02030c0d0e0109111504050d060209120d0905010f051b0703050105100e 71
    0x202c00d5612140c3c10040d80c0c130b802814202c4099082da4103d0b001c0d10001c200d598041000b020402c02540d40030a110118034180541240050560f290319400007405001c0100d010816084800080e03071f000861001030304014820713101c0d41d20300240f9401d00080c00880c40d5842401001611040e148042158640c0c107028000ca48030010802c0310a8080b031200c100003080f1001d44103203140140030311030500c010004614a03242c0c0c024800380507130384150030540000c0402c1c0214104007000d402e01c0104400c505003940d2b2a44401000601c025600000140c401500720742a0b0f0802c001501040108101c1c0c0541d141c02024240015241400344c10202d2025140107003442400100401c02981002e250005015104216080c1101d0203a021b1181245684600704803070b480c0d080c05001040e0300c00c01c1d010040c050041c1c40c0c200782e042040d00b13054600f403e031304041102d16081c00301c0011410516203442141c10b0a01c19000180154240b0061003601c003003007820030041c0c1c2c1c2d90048001d25034545080c4801e40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 742016474 1250 742015224 742015231
    0x30406050304080d1e1d03030c031f03051002030103030210110901030b010909321021050a08270916110a150f092003160b0d1103 57
    0x10300208001800620000d01502c03c1d40410b007000301d13101041a800550100c98840000001a035031901c00d0502a800303804001084c0078034001d1440d41c2070101c442d142a00c0001c2c001000da140c0014090480c40400742280300568104050b0b80d1494200c0000340c000e03509c20b1006a005101e411400c04034450503104502c0c000b080d00d0a21450001448010750280c4034034190941481442c0c2d0000030361120074007075050b60045100078454419001c0400720191507801c80a0701c0c144440c1800c005409100030030f240c0545101a405003950705a002166003c041640f00041c0301c0e01442580a04001251003c0d04030703000824580c42489884652054101c40c1009074280d100142002003802c00000e942079401d0386d5510f01d440d1400716000d86803145012002403089460700c005001e0080090040d10840302110105001400181600c0c0c8031400c520301400c21001615194101c040c503255001c0088003460102480825a041c2da500400c2e003a07600448010310320320341002120541a549001103030322 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 742017724 1250 742016474 742016477
    0x90405011410120f0204091506020d081f12150b0d02030304090f0e0d0216140d0209091e0606180103080f0702190305010911040b0f120102130e18030406 67
    0x10406801d080071070b80400054102400f00b41d071810301241c030800320b00042002c0c22143c9130101d155101c140540001c0101c6511920454005080e6902a203610102d100e800c030003802070703c3d054250300c41d0b090015072655078081c1c200307191900f5a803020800c0c50000c2d0314689003110301c10003001203900f0501c500591191070095268004000c00d03c00c208003a40301250104044c040080c1c01e8140361065440c00300d800c0450409a408070a0010700700469182200240c5070309619142014903c101160740d003d21080c0c028414980c0d00d00140031004200300b190003904101d9007890040d10659900782d210041a00c0c042e000f0300c030b404194461650707049590380c100d0f9400045035245c88184111b0403c1908001005c90b40100d02d042d0ba03449a2081c5583c14024501036400083c0f4014a45041a01180c4c4003d6050045042000f81140c1d59503c500054240300c8c01d13101e01117114034461181d802407040401c031048580107140040b960380c02e200c807014070030244428020b04604441110302e5403801580f14400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 742018974 1250 742017724 742017739
    0x30e18010e040c27240f090b01020102090d122106030611130608040305070b040c0e06031506010e04020d060b3006280902031504180209190509030904050114 69
    0x154820180c2c0c001c5886021746440d030710601500c0b8000c10714418043c0c0c0704d88440c848911090140d000309120368010807000f4002149040c030071a0114403000e034000300c0640300c910302e115900881d500444429514451282529006c04000c00709800109914003081e581d02d071824107105270f0005182c0c1100c03842d04000c030300100c005151050850f1032810041080742001070501c5141c0008240c101924011445035562041c00303810a80c09804400d0003c0c56944242d01c10280a05500030300c80956402c03a04c00e180c02c11948000c1d00200e0081d00c030700a403403080c02e4a0f1a00004d03c02002c3c0000e0b160140d0b008981010a11303100748607250092800c0d48070281c1e00703101008a83d941c64514010038588001044940d84c060401c10100400b0003d41e20a180c1a5000001c01101181c011525803042c03404a03020094000b00c1161400f03c1000c0000003805002d56001203501c500e1000c1c242802c1003200c0c60305011030f10301090006d8498105101040c0144c0c102000800d4420b00e09504404100018020f907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 742020224 1250 742018974 742019039
    0x30a0309061d0f06071e05070923071b0f051b0a0308040902090409060203090708120f1b0f1c200a020108070509030d05130b0c030304030e18010e040c 66
    0xc185648017010844100060122104600080d611040303001ea00407400303070410600c1d0240d40c005403050324104c2c0c44034180240000318012004190310340c1043c114131b4100602c40d01450070101ca2405018040c080b00c80f9007a044081000000303c1e440a00148034108200722101d1090250320140340c00010b01001052005001000c034560203000420002800469010b501d9111101241e1081d200c1030242d4000d41c2d424041441c0c1002202c100d07902902000f072400707184400c005024010f90040c821110b911207400295402c0800c40f092a66200905403980c3e01c002540c00307090102078a2a07a0089112642039000240c0c000040110041164003d070a009945070300445500c50020480c1c0140720051045628680f0100010034000e8055220349079113180d40035503040000101e42c0300c813000e074508010100c0c45007000720540341c02903414200301c1882074801d030024424000d00081203840122610001551328545015680a1070085e04060f101a841c1c00342400e100c0e1507000461030b6000c401c00364 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 742021474 1250 742020224 742020229
    0x7170304060215090c180f0105030318091b1219060b030a0b2b1b0f0b07030201020c101d0706050f0d110301151706010806040903030b030a0309061d0f 66
    0x40c26030004113881590410716104000600c0000d1043da0060f03081c240c44200084107907034441d041c0c0074000c110000c50402b40070030500084000b44a60707042c05091107201041d00c010303124031002c2e0a821500c80c01911000c415610048602d0100d42080c00600e2111110b4506601d61041c8000e5611074800c4074950f0380c80320120400b40400303041e015044500003101c903000c0c0100340101c102c400005d883c2c5010b100014280050800c000e034079400c89071113800c0810044c03011b48a2103442192031042034640c5400b40d0b07040036802409203030a401c2d00c0d4041d00c000c18100315816030203012003030a10000c48030305813160f9011666401d2180220008210200700100b0300104620241c4140c400140c004501c400c4114811140c80c1c00a9024040c018960f0080034941e503004081c1e680192450403c42d0b0076441c041d40028884130000e428070b401980c2d25000442894400c0c3c01044c821a80038080718034100031480c000b46020054420100041c2c42c03254000310070380550001407040b450080002114074014405c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 742022724 1250 742021474 742021513
    0x810090b0d0c06030501050103110c0a02220203040606180c0e0603101a030f010506070b04170706090507050a092018032512050604030305061c05071703040602 70
    0xd4240c0d010072911060000600b00048041c050b00311660040b805500d010009019075031843ca0074030080380c050000d01d600c0c04001446489440d011596800d1012400b40205031040c0807603010514280004204002c5c45401c0e04a00102d55415582544011700c0000303000403507c2400343c441c0001d8003901840500d29003400030355000941c0c2110b02d8400381ea2010341420301c4803020310058101070040b0800c0154210343d4000ca00402d002e0303c001d0700d4021182c0c0d50420071880103200820404045804801c00c0460200391603520b54001400c00440a0328108195034103403a11499105150000000c69408024007603c0280d901c2048684401d5480340350700e07038140c0c014866504003100c41840500e16960200301c04c40b002507201e0040c400c0700b00d080c1c400301c5144809401c24029094403034010800110005001a400b542614000485803514000a402148000d21481043e84144030850500c0300106220088905100b140f8054401001400ba200e015038443d00016811810301c42d21030711002c40303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 742023974 1250 742022724 742022741
    0x2100504020109090903020c0f04140a0c03061a090306060307081902060d020f0d060e07090b0d0609050117060612060f0403090801090f0b09010b0a090c0e030f03090a06081009 77
    0x52107000f00b6241d0500340102c03100c82c1404d90041c2e100b0342080301103041604d00103420030b4040e6070038446010a13420301030380c007140a84001c2096036079030000301580744642e2100c0081d00c40007440b1005541c40b030421074599041041aa4401d000c1c240114a8928000444e14100c03007494014280150040c50403009101c10f22000307a030489000c201404401009200400240380d21a40241d00c844000b00c0010450352150807616141074510705000b030300c903004101c0c4011640c0070340400307036283d0144d007010019040b6540000300550500c000424070707400b2003002c1400b40188008650440c1e45040c10880010706001e44145107411070400300300f22480e1504c2c1c099016000b0b090600c0c1d010341d20121a42150910a000d03141e65503072603901c504015a4080d00780c0c002010300024000712004400148490a4500c02d1050b45590350f80b01ca28202c1c0a0000303030030f0105006090350107508214078425102c0c2d00c0900011302c42c1030281804519140510034581c011000720200144041c100303010031005004a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 742025224 1250 742023974 742023977
    0x806100f1a0705100504150507051818010609090e01060308040b03060d12020319022113080102041d0f070f18030206071505011a12070309080c0105090715021005040201 74
    0x1c000b42c0c00801c00411111403411016000001c0c140b9042c06d02143c0e101a50f050140c000b810b050a0260407a40034094890101c2d0090075812440c001100046088011054165140b03107100000034403d030b00017807800700300e42003150107112103a0300400031800c956140c00000c0007c1c0082c0018071400c8080300245500000260a100c01d404e020740b181031011140c0c51096006030f0001810f24003d10550428861040301800100040021407e958400c2404008042203013100441c2e1000300382c14400c000b5009000001c02107503555140c010060401c680c60381e480c14000118404118200c82d803601003841010139541c1d01d1140003100c07004548034480c07280005209040d06201001580c1c841c1e00501c03116101d007080d115183c84021040b4107443c0164040c40303103441000c4503d4540010b5104039024452643c40303404241e80c80843c1500241078881c405000a60042508840b4000560101e40204480070455015a9032400360707020388180c80001d6001030301310700c65148049445400c16038119105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 742026474 1250 742025224 742025227
    0x90516141c111203190e010813020406270b01080c0d0509010902090a02071202070f0308030c040f0b0c010e0601120b060f030d0c0c0e1315091b0806100f1a 68
    0x3210000f281d290f410302d00e1141503040061070814007243e81c1c0040000040c03a051860f515528040003915240d001407003a1241204203103518110754450740494040d000712041c8422400216071041008800088000c0c4480c0c6044003001c1b02c2d6002e04440b62194401c41c1c4003624085180301d000d405440c0213000d5960075903c80c60007031300580c0c1e490500c501c00d020111005855250b1810050540d080e014032038000c1d900202c0e8184007070403414124000380d9400440880e6aa107405854220502c500e50112a00400040002c80c0d01e2200d50f00809003200804003d022404160240782c1e01c4110a04c54000c80042c0d11100b480002c2e81da4252a9014030002c00c2002e581c02c510740807070b00341480140c1100002d048103009a04006082c2203070341c050700d610a41c1140c10301d0050300d61050f940c00c1c0800030349500b80d010b100b1298050705810541c10301d07038807403250080040d01d00710081ca2008180501c000d50701460700016070400740a0302c1441110507a642c2c84407403525043c3d05040302407245403100b040200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 742027724 1250 742026474 742026503
    0xd0501060312322a1618060e070c0501020702030604140d0504080a06091407030506070e040510030201032c070e0f130209070e04090516141c 62
    0x7003101c00842c0107941d10b5981183e014002400d03800d58800e48041d0160080b4210441c0c1120704809581a0340f04081003034411850502d03203500c038007046107040e4480e441064403084900c155007000341c04680c500000088030072210303100309040d0b4000b80100580c2d0b14070788000032452032151035500555801040014982032154001c2810f1030021034040d1550411640480c2c1203407410444004000042c1c81d20390708150500d0300c420346601d90008040c02d000e444840c030300c061081000c952224005c2d0344041f500340550b41d14103151100b204980c01c0f00801c1d02203020001a0525000b0b086c80313a420401407640d1076003580d005500400c103c07039011540907152442e5042042004107121a01c52001d0020301c0b95500c1c1004d00002c0e8100100003c221801520900c074190100c07111003044941d0440340740340d8913a40c0810465610340301c03c140303c0e403003070401890b0814050080303114441c0129000072220f03080d40702c552100d265003039400c0c2d050b08601c090068460106a1142c00780c2e14610a590700c216415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 742028974 1250 742027724 742027733
    0x20f033004090213080f0106140d1406010305100f1b1211070f06110702060d020d0f0c030203090717070b090d0c06092c061c0210092606060d05010603 66
    0x20090282825040740e0761101784607102007080401411100c010090095608114100d110300200700000350155103680010802c000141a0141803403c00030201c3c2d541e5a502e0a08541c2c6a000c41d8084c1c880c02d240c04200c0d04141001c0c041c19550b450f07102e0074181c02c5564a2811161903c20202034208a50ba84480c4041781003100018040c090255680c404841040d0500d4001c03204d2440d03001105010800442c00141c5503242a20510705212000580b1500e01032490000340c001481c8109070145421510340c805600740e80914041c51140046588240d22000d0b12001c40c6901c4000c00b081c1d510515040010a10b4403000306003071040681029031000c480ea44a4400090a8010340d012405c0118240041420481c0304065010f01c4e840b5002049000203250210b032501601990044a99402400c800780c15844d1409030303958040c00a2012141121004111481a0080d8040f0400040c4840c415200c40c01d04406070310300d80c0010301040e03210102001001250f450b0129440d5403180c40000108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 742030224 1250 742028974 742028977
    0xe0115031b020a03121503020105070303020f03010b1902120313020d05070602070e070305100e070509130204091802032d06010f060306170705091e1003020f0330040902 74
    0x4810b900100a4200e0701d01d405840328881c400007030082c918002907403284030003c50245003220f0302809d0640d03940e852801e044000e0b00c1781c0075200f80440c2d00040009039903080c00004005580105c00302040c0f030b4229010481e00e406480c6034504400038180085154150001c00c00100c4500c0209014540103581c0d0302d140c20301d0b0142d0300002c05600300c10020040344559500080d4022250320302007109107402e010407901510740340210700220032914005505a0f00900889d0405200100b50b50b1a030030f0019041406540a03000708041e050403d82900c0126a1039148030112030f07402005000305108031901e400302d002940c4030680c050b000f8880c81d090141e0050100901801a04102070b1820342030030005401d1303801035805200d8644810041601e610004030fa5101640c004998041d480c1c2ca591400d0075001c214814401d2180d0f1180041c0091440443c200a0860344241c407100b0110054000301620f8062405820b0100c4c1808121041030702400c00f07007100c00c0952306422505064460b03001e07008a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 742031474 1250 742030224 742030271
    0xe06160f0605060306070f1e0e060711011b021804080405060309010c03150e07210c0c05100e0a0623010806040b0901060f05060d0f020316030f060e011503 68
    0x20550ba8003e1007118141031040b941e05c4203442c1410702020500c1d8074001d000c90100070b0402c10100c800032061560a00c160008461900018041501d50300613080c8110040e42d546c4025002c500314807400038545881100043c05550018101c18025040d0801c410b500b001c000c0c81100c0e03084040102003110b60707590380558000c0e8001400041e81c0b007031007600070b000c0350021240b1404094080340200b00e24070540c84e41c20344c0035a080c5041420412942080c021290018000014550a000020003056441030308080054006c000f02e6210502d00c10320141200c81301680103005801610302d16001c00d07200d8100900c0212901c03003020821043c0b1070b420025007402e8124200e580c2201061200340000c00302c4294024034544000c108043ca000c0084035000c015101c1d9a0140001089420321020b6503440383d0380c2c40003000340a55884c0b42410304803840061354009000820316040011540c012603205c0d5000f0f50b4a00e09480f10564200301c0d0210546200221890802d40c642c0810300d00448180400f056 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 742032724 1250 742031474 742031483
    0xc02060c0d0c0b09030313080904270614161b06090807060c020c03060604110d020c06090706032003190c031b110a03140c0f07050a060305070e06160f 66
    0x9030b544a07481e0402e007590014040340304c16401401400804140c0480103503005520400041d80c0300e0b101c4d4081006803007880e04c01c0741c5030b2501c0740d14114180c601107050803603144101c20030001d81d041c031041300780503a00940340e104c0628002c00540303500c50300a02c0c0845000349100360311108003071190b56140c1600c806803000c07500504086020420042c0a0142d1007004e6600e0028040d045100c4020039650340008010a2040b604c8000d5a034009080004a0fa009050220103659580f141c00a00b540c50b10140c078500a54480c241c00001d9043c864812084080400c4076810921034813001034400d10b4001400f80003015586409209280340380384148410003102d510b000c0ba5070448201945861002c00418070203210002c62170045908010031107140c1c05a15003003c060901c0001d40071403440c000d00346a4121445100b12400002320005004400c4030000c45000344882d40f192000c8040c0d5800f83d61060101d880c0c0921031090386807000282000c050620b01800241d981519101002c1804244c00c1d103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 742033974 1250 742032724 742032737
    0x20f0d11190804020d20030f1c08090319050d090609030806180a0207050a0b0a060f330509270a09032102040909120824010c02060c0d 59
    0x14221041440001c41603254142045a0310341500803401758642c0040c010951038044001c00480000d6040d102c0e21890094200ca012100420480307642e00c40108002e03142d00081448015031511546150703100300c00d0031b00958103051b14280c00b40c00e4140c034440c2540900030240940300400d0002d204811103140520404101000e0703500b8040d008540c06055240140f5040c6611584403c0360008035800c6140c0710030041c0d840c2100d0600d64104128424020017012000085c409078030110b0304043c0507168407d2409c0481e80c0e603614200c01c800000301d810344041175502400d40b09036600326600d00f2403001904000d40351681c00c01c0003807400341c40454074010041c40e0b0f9461246000000f060340d94400b07481c042c10810803513261000313005c9030340c0180c00503004180e4110803604030080c0e0b01139800601c01120b0900184003245003003da0500340300c010038000f507040070028101c12011010411611040040031880c480684011210044840d4003641c124800300030346141c8207020840e20b1100d0481d6907031074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 742035224 1250 742033974 742033987
    0x30e10050315010807090608040203070321080f241f02030d1a010c0b18060124090e0c070302010e070f06111506120c0301051f06020106140103020f0d11 67
    0xc008050700b65110704105000c81085101d58025041c90f00750f0700c0c903080c100c0071540c1d9440064907090098200501402ca000aa11030400110b80142d150b40030b140c0b0f179045940d84034108840b0f000c20440d209032102200301c0003482442080820808566030241942d0780c116800d003d0511005490403d61005903c00a0b000c0007903040e51040ca4244110303c0e110501094684000030309007013a5582c06491100d489000c0390a9160900700c03412402255400d44003550394910341c1d2601d050842040c01000540348540d5615a441445100180c0f5144801744c5c440381c60303208203143e50f83c014031000c03001d6668440c0002c80562080000d840100071081d107215000341051001002014800c51909244c1d1041c906604409500d0b544540d001c00245c801e0508141340b902c11916040030a034125030503520344020b000183c200100c0c0386021226000361900515640c00301203080360814842e882c20024080981030302c0d903100e9001800131050340c4c0500341c01d010003003c20100702d62940840307000c54580050345 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 742036474 1250 742035224 742035241
    0xa050f0616141923101112010b0909150d080403060c020f030c1b0a090e0a11060711060306032409010c0302120a0e03040801020a0305010503060117120304030e100503 73
    0x1d0f4162000030901154902c592551210350102c000e440c240201505030b1100c0c0840d130000c0088a070710706140003050042042e00000000d082c1c2c000c803030081503107181400120702c1c6a1041c003202c80842020380074286690368074002c6a6151800041180e022450020140c04a141180076001450180400088043c1040d80c042c4c43c10b0f007102e4803280c194206000e01034924102140b0050280c0c205902c0c035003407400203c00039050201c103070020302c651803a160005404840c005000e03400c003807150040d0013052400c2000c00c44075002d00c0700001d2200d60034a0202005081c030801071904001d02a00721a0034107110b01450b070071008580a8100701c0c2400e01c0410800410074010407240e51201d040031441c1511004c00d0070001030000302844061515148021042e03442001210001e1101100071500c43c0308200005000d00000cac03050f02d100b40704803400440d50068605100d5030700001000180018540110b00002d0794000810507824821003641401c0300e620b81803504401d90110f41e6805980b850004103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 742037724 1250 742036474 742036483
    0xe030702091929010e090a0e2b030e01020f070219080607020a03030f0513030819020c010204051906020a030c1110030b031507020d050c0102160606080d05090a050f061614 75
    0x3c3c0e250410512100000c0d80d070303c1c0c00070002d400524a990202d10b908003c4070b918942900003600b82e00082c001455040303880c1c3c1c22544030710300d103100c1d0303400b8003004000514960a034014038003000101358080121100618006800031044160440d138815501c0c1c0e5204082e042031811642c0e0340c090f8109180b41030405515110b41228017803441810044c0e1700749400311101944e840d0500402f44400301c008900340756000b407030890320b0a6801f5400c1d55140c20440d10f00d0f010350002e01c02e4601a83d00010303100241c1340000c144000f99082d82d40100310200958030111580c4403045403e950380a46030288078907680390740c50705400d4142d0a4802195003405074052602c0c00c9420716143d0301407140d11040c002c4040d03022500005280441c80d000d5110009805994028443e1004015255601c1610001040903940180c01140c00f110b0a841141c03038501400d484031302ca8017503601c0d0b1003c40c20505000620706041040e803255001390109050440e0614581c6018080010954003070340f464015003800c00c002c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 742038974 1250 742037724 742037801
    0x20a020a0f0c2903060409080c0a030905100302031b2b021b0a02100806031005011d0c0c1f0e0a0f0c06022404050c0a060c030e040e0307020919 63
    0x9402c10f01c001501c111884240005021a072040b5140ea01c40020f00c403100055a04650100c4255140114540360241610301c85100345409240c1910501c03009500038401c0da44a080c0c0e00e01210a00c01c445038080c01d140c1d003c1141c3e689201c0f502c58507d086004005000214190032040050380c44102d8500683d00d0a09100c94641c954401c008140042c0c6078101d90041040b40c0d81459051900e40c00300080c201b0108800f0303100e40074135140001903411070000c0d462203464061031010b0060b46034455846024440c50801003007503440811040113003050356091a40c640380281c8005144141c0a484c1814000c950301c2c113544d040c0d00301168200348040e4814401c0101018001418243c01041410450b0780c0316400d40d640e0304500000040500c04140445440044010032100000d500c928000c0c0401d40484004d40c009080254110050305291042800c0e00c0440c1c0019400c005c0300e07500300300c1c443c034000b084010b07c81c00d00e000710031140081d0700074031142800301c0d541409104050791158401c005582e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 742040224 1250 742038974 742039019
    0x9050a03110108040303020f0705061e13030c2103050a14010f03020405100b12180106060507061505030f0709050a1517031608030916030b010603020a020a0f0c 70
    0x40030000204000c1815400640a0030846095550743c1001c0d0001d0040c40b100b030b04200310004820040160100e0304601c10115400300003e8408034014020440d201100d0b1130a070082c1900ca04030100c6d019020a004642c0304803000c1421905c221301110300c081440038a400820b03150010b224502c050750081c1c011041d50200c00e0f150030f42c5040402d580c3c2c54000e100290140f84da450110b0b80c100301100d400b41c040c24050381c2e502d07070310b02540014a040100c111105010b4100d0700c200d890010030103000708411921103a5415040c55010313241c0c4c000900f1000b070340d032080c542014000902906c040c0304440e00301e22400c020342105c0349000140300036a44014248040c003458480e424442c100b04160a0040e13070591b821010190610341c2d1a1440c6201d094800045a0f185054200c100545080110712a0000c50151580071070201e580b00480c803682d0100414418000300107014241c8680e002e0582c8101c184120f42102c0301c40e8403030004610703600e0303025036070810f00b00c105102d54454010800c2149082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 742041474 1250 742040224 742040239
    0x240d091a0a0c0e04110702120a031b240f05090d020d03060503100b0105070b04200405042f09011d0709080304060f0504031407050310110904090309080303010b04060905 74
    0x60302c50003040c00041c0312150744070303550341c0010136200320455060b1805643e0180050150501c034001c41d079910200c0c0d131000c9000424002501034440818004542d1466228080c0715241b10191a008003013045501e00b8421256104014009541c96018150141c8800001f030001c22000680007402d10800e1580f8505040c28178000f08519200000c0124914201c0e1100240c00c07103203640100c44c01d2081140203001c0c40300381c01c140720501080302c01c15505000100d04480d842c5182e2400d11055600444015062644142c001d036049003030a0360010b1561080417012840c25549400120f034000280c01c05400d8240001b0302020400d145e0460f46c2d00314a990030644402c1d85400c90040d0b4034480d0b030040e0303000c006000b245d18500c60300030020781d0091503001889040f003005444074980e5400252040b244207204020402010640340d01c205184021907050b907e20f410042414000a8455111f04a0400611450006d510f0714280082c50187c11000300c00303950389140900c014008049a04000d224100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 742042724 1250 742041474 742041491
    0x50a11160b2502030a0f030902090604050a020903030403050a0606140303030c2505030d151202220504030c050601081603061509060b04030c0e06240d091a0a 69
    0x140c010805a010351103600341c0c1042d640c8910281411001d403210011001545100e140515004400f41c08180050381d01d099002c03100400441c140d407d0101d0294000c070490001c5445400c0c10f802a503404507200314050300c2c01040d4004203295a020b58000c0d91a40c000584034020003000740101c400812128045162101c4520b000a03104c1c030001d090707035103580c0c400200e881e00d0850058003040718003c451100791008103241000c60700c0c1d60000743e0302c0c2c100d14035055260381b03074800c0f14014205413000403030b1014441c40c007a4240241d405240450f10b010f404028500308035149140075176403185109030350320810f4100702c0c0303052480c0c6001038011fa041034006d15020700284401d54905800c0f00c2e00701d4004294036002c114602d0b1540c4144e08582405401e005007c5442200070b0001e101300d9100300d041c2803026540e0403000140c61402c5d204154015802001d803442c1d408251000b40c0e403120343d141c0c0d2514126404403200d00300c0d0381142003191032201e40040700c91600c0e204000a0f60080c10081e043c46000c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 742043974 1250 742042724 742042747
    0x30903050304080d09290a030902031b131a040b030712030903020306070c1a060d0c08010c12020301030221071d100902032e080a0b011e0605030411150a03050a11 71
    0xc6c0d4986c0d814241d0003001c100006008c0c4aa00452000f80d005001c0c0c94410400c0c00302220001e9070314210074050301400c0d03010b8400766640d100f20888200c02010040c0016610010031001e0481d10540310b03414801c200c404101d6640701480e0380401c2e4843d894040c2001d16520606061010060040050115140b45900441c4903040b4404610702e003500b1010b07695a501c00014640c42020401a00d000e1101c00080b401c0e003415445041000d509880b0480c465032000030f01406d81c80b00b400025001210f600c216140c01d000d418030032212803076120507241c0c56134403106120b00c520031008240c10b4034403144007801f10300110300407408081c0011420039071451410920880d0707445000c01c00c200c1c032014568001d51003814a01042c4014092003020386907121054100504001001e00400c050420078200030351070602000c030008200c0c0e40701e45a05003903603100d4407041c0d20701509010750f54001c000fa4524110550495008200d40e01ca907440010340d900b4a1070f000c1c0c0440380010242c45c10000200020381002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 742045224 1250 742043974 742044029
    0x1101080f0c03040c080114090106120f060e1e010b04140403080415061502011401050105090a061110020c0f0105060a0b0403020f120102040f08160e0c0304030903050304080d09 77
    0x1005020955207440f1860306180e911180d5100a483d546007043c0d1000c0d80503000f0540713000d40d0894000703000841e142c8060180881601400605601c1e181c0e003503800103007158200341000d20500055038022110a0742d1105000c40322100e04540740d54640303030b07010281380074402c803248050052415101490640c0d805010148085d001402c10f26060312030030940401c80c0c020002600441068005085685001074060b00e81d040c184841002c031040045001c8d4444c4081e038414440c000e01d844009440d007441a9119203120300481c606002e5500c4002c000c4645000409005100724001c083d001600d0a055084030f41c05011140f044541010412020a0a00645080c0c07a01180c001140d00c0c180c0000840d64885001c18845c154004123002481c040d18040f03c50440b5a418181d85c0340c2240500144150426070241000f40910b483c081030b5074280c4400950b0388140300703042542c00143c898881c1c903c0c6802039401200c01d43d10030001c02d194540d00171964402001841d0b1142c0c01c20086501c002c0a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 742046474 1250 742045224 742045231
    0x60703110315030c061b0c04091a070314010e0403020d0f0509060f0d1107150c050406080606090901090e0d030b18130605040b070813020121021b010204031101080f 72
    0x40000c402c424501d10342d014468280c648000803c29640d4001105007000002c000c0e4006043d01d020305e400e07038140b86c1032a010354030200b644410000c40141401007460404d03403028020404065465030603181000b02404241c1c041c02c005443c2c89414603082c64002c3c54241d0703080d550b03c200400c541c2e829400f6500001582c0d00702104035402a01c5010351031021056024803c1d8220341941421200b00344d0080031401072001314007910024403440c0980d254503058070003491003a80011420081081028400da10003a00000010b20491401c4054000911044020f0300440009079440c00240d00e5110100080010900035040910a22804800107004d044c010302907642e43c6607422000526041d01800d44030741d000d5118004000c00d042a0500b04001ca0701240c2c0e000124101e00045030784621b0300800da170300b105e505a5412108180c512403455200000c092102c09890b024061742d40640b582094407c1d1048242000503121461814100e104800c07070030170719051004020a00c201100c1d1355594950 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 742047724 1250 742046474 742046491
    0x7170a030b280b0f0f2206050f0d090201050c031c050907050d1401060810090c05010903050d0c0516061d060a0818100903030c03112d0c010615020607031103 69
    0x300c0d402800300140301d03445078035003e21107000f00250b0b40700312030325614480840c11006d9001d5904552241400d5138a441040122280fa400034880b000d0351250b260000302d008e0348103141c40c0d81040ca04601072440e54005404013415460b4000703452502c82d45501c02c243d40891160002c010f0645441d0200303075002920000a02446841140d41000410941140000b4591803007201c40c514140440ba20080803212400c98071040311502c006415032080c808501a031780c10501614100d51602402c2c4e4032044601822a01409200030310a081c14030005010001d01403621400c0401d54501c1c1c50001c40d02420a5040c8501409e11410b18041d500a452652081c21449440c96aa115070500f03440e180c0030140c4d03011030904089a80701090303031680108851101c00d807414041200100110300341d80c0280129101907074048050002802c0b01c0d001218908503030741102c90b2600c2440d040f080c4c01d40d0501d4001040c0300d11302030140c203c8258100851680135405107410803040400205102491001402c0c401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 742048974 1250 742047724 742047727
    0x6090409110d030f0311071112012004050a05040e032209330303021b04020906040806071103040608010e07110f0d11010204080a020607170a030b280b 66
    0x3041141c5440c8240007208000c1410042d11160b1a000307040b11500c0038010f0001741480c1340f4031038940b0359409891b503540e030144412144c4c0d80c691003031110400120708000740e00c0d034903080c3e49008c14150599090300441070300420350380ca1341044244420704d040b42c0c0c081801140b40101380002d40e40d012080c0c030384440b140c03455040741d60a488145581c080c030f0754004804451038101204081810652402104000780c8008000180e407041e107060300009901c03001e000742c1c1000401c070384110400369a41c0481030f4001c1006082c41385820218105030482e402c5008954007034003e0122054202c4401400c15400400861510381400d10003440c1c181c062150540030007c040118500e11700600900e149460048201c98540310200000b030340d0741c3c81000c02d480120300f4408040e4801c0d1018000c803070036a40003000400000d8501d5080c020141d00101051340c2d0041e0020b400901c664a1030300400d1003040682e004960f03825441e04020f107640603001c5031405a07260043c50304c2c20004c040c905904450078058441e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 742050224 1250 742048974 742048991
    0xa0b13050715021506010c0201201e160b1303060b0d1203060509010f0e01050d030e0904030201051509131401021e031902040803031501120c081e06060904 68
    0x74646140da8104458141c1c01c0c8254400d0240e0010303040d820a002054807180d50303100c04e001561000c030300440c0030740002c0c09815000b882c0c07400c2d5070300c2c10120240a004c4403092090400d14081ca03007003c140494458103d400c6080b81c03080c100d0307807401c05010350300c0380b5915100c00c03256500302c0d803001440300404491b10744554000c030765600c1c0d1410321101c0c1c02c56007288986407070700070050081c02c4a010f0315219111540011646003c014113035400e0307590021540030183d091074204040c024502c1011804c11a03801c16411080d150940740d64080c0e84650008102810030151b20300302740600c0c0d10624010109032080051180c80324021070300c200c2d000006141382c1d8810380310941c0a4450440080314500d481c00440b00398082c618001c500c521420545500034006004145059209074420b201e6184d0091000c01c0c0001115910030b0420300c1c0c14181200040e280502c000161400c25044e0380100e800790081140064040e00080a1400b000c4111081880d0801c00205070f07000c0e001d0380314000c0382e0b10b0014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 742051474 1250 742050224 742050233
    0x100b0a050c0d020c540106020c011d061303140607050a090303030902150f04030201110d0e01051c0f050105030c030f1209040902090f06032b0c030e0d05010204080c030a0b13 76
    0x205041c0700c0030a420b2103d0031016085c911410b01c800c02c1032489060005000282c40b500c04100b85051050580d640c0494002c00821080a215907048180c0d12a40400608008109014040000b1840b85000351090403071803d480d420064001c00c11828407100300b104c100311907400085441500d5040c02c0007e031600c0341d800491030700c04008501a60022000980106c03160050b405003088902c00d9940c1e4904585945c00e69465000c022042004240c4600500602e50b0080380a81800a403110200600144180c03986081d40d0034904810441a41c860042c03045003414005103110050540c01020201b00c3d22061540e2040c540030700c00301c58040825440b03c182c0d00ca4000c0306d12240c005000d4081404d00742e10300c000d18001610624864440c00044407008042010114801e004c281186414521001c000340c8481c80960412010085030741c00340303440d07962048c0c0c4009885025400040e01c860038a4400c600e021440d9104903c00c0c2d22510b13881d00081c00e0003100e9688107190b60691080d6500c035180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 742052724 1250 742051474 742051549
    0xf09030301080d0f1806120c14070204020f0c0d080117030304110108070320041d040503090103020a030209180406060f050303070813080d05030901060609051305100b0a050c0d020c 79
    0x10b11000117a004080001c19542c060724881801e00702400411600004c90f0041d65280382101c3d2151510500348845000740c5003c1c0e010340064550000081c0ca07002048401c5030410f0740e5140b0346030204100000501004800d62218171040c101c030002140382d4102030310f50598803854249a2070400100c0340000d41420f201c0d40190005240265120911141c1c800058460b03400c80e0107245802c81410b101c0d015104d80072005503004642040c065481c08001d800118065403041101c03078107254081040c132480d0703125406c0c11019a45088402412424249046000d81d051588240016107001e0030034081c50f90040704483c0055840f00e070a03a5140e41201c15803403070180c2c542c13006956006024480030140d401500840c0714000c0600200f26079500d5020030f4408505500400303810010040e401000e140b12548402c3e00b2080c07940c00e1031a0309560f10707100c02c0c0c01d60103803044100103480415031006010040040c046c020f401e0b400508040000a0041800107e01001c4040d54009840140d11010148513 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 742053974 1250 742052724 742052747
    0x1080f0603032106120d090e060d140d020f010605010e01120906060b03040303200901030203090a0b1f140603070503180327010c150917030405060f09030301080d0f 72
    0x6000c203200b03040b5003c5001020718103c410500481c0e80403103051700648040380a50608100c1c6d100d0000751410f141e06c1500b48c800040038030742c11138000c00403503011404402d102560441840003c9c60034458408009043c0000c9040280050f0704161060045070382111040401c03075020301e0411406103001c41035070080c0100400240035180380c0900030412000c8500254401d41c0031746c4052020785000c070f5010704122a07600000580341800e1061825940c800d800454100300114100e4607410415100c94000e240240e03400c03100e241c46280f8015004e02c00e29015001020b0b0034003a0300e980b6052801180c100c0c440100b6207000c21100100080799800094202585594514102c0317803920440c01e00028440b612141c0016403072004085559598406d8a507164116030080740403150799455030040c1f001d4620b4000845001c41181c41c04032807500c461f07014510560191000309410f041090f0340410f490806022070142c3c2c0c200f080107000404001643c0451869185410901c08802d04411606428650b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 742055224 1250 742053974 742053997
    0x120203070305100e04170705031207031a030309100c0206040e0108060105040608060907091d030d0203040c08030f070f030e0306090a0303061e181d21070201080f060303 74
    0x40148402035074558091440350541c81411480c460700c0c2c0f0102040301c4030464000b08019801c0406400f0002a400548240c0d8821011a17044c911815211014038008070f8510300081d584103807039584000800350711818800c00740e02551501e0065004078115402c209058014841401408011521407204a60082004540d1403c0715611a91101d441d03410a1003610710642c01c0400100303802e0b0003c210207001c1c102e031400500d240c82c54003005201030410a0300b007140f070741070b258241c011229092000300140110340c0001603803440c161a010410b80401d0700018031075441403000400c402190f0088502140c1c1000c100c3c4c0e850101c519045a5403103080c0c40e0030b078160040341c8c18000e242c00c0004000002030310988080c0610394540b1030500c401804221024080074007510200800c600d10101007108054140703001c180d8109960300f140182c850180c22082640c02070500c0120010300c40302c20010048440a15840c14030f080c0c0008003030301d0000c0c155148000860b008625590380030000c848502615 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 742056474 1250 742055224 742055227
    0xf090e060a0e070e03120c190501061d090115060c240f15062f0106170a06050a0209061c06031415010803040303080c0a09330c12030c1202 61
    0x8030000303104e045503003400b078081c1c800d540a1096142c0c1341c905880388081110b008002c3c00210003407c80240040b0b110a503455541c1e860f02007490290300d00c064944101c1c00e10070600c0b90030844403903400c5910b00001200420048001070141c03581c04240c05288580162054902c0040c00c0440d15107403088000a8034007a10b001510000002d4a820400c0c102c151541d41c21039042d80d800054032541ea0220b0f054800b10b029031084c2c42c00e0715080f0f10a000b000c000c50000149940c940341207581150048092800642c0401c0451081003101d0041581c032160a0078154104203614021480d1401001180c4410898102c031900c880189580305100840e040004140320700c89550a00303464500100b0358000719417841d000400e4421000084504499045d9140107550b03443c2500300c4141e0300701803010020485603003000103c1a81702003004040b50040e050002581c070107010240070016001c50765805001c0d01044c0c2d0b401285e0b280150300c94640d65805c011131801c1042004854149068013008600b510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 742057724 1250 742056474 742056481
    0x3070f080c0f040f1d0103030806043206090702070b0a050c190809030d0309080708220b04090501060f02100c020a060e0c0102060105090c07030c020f060c010515010f090e060a0e 78
    0x716400300400c648005e45620190190b07268038003118002400007602090460b03001c54010708241e4040480390551102e000c4181e1441c140c205c40e590300c2c1c0e40349030310709551440030312007a032400403441904060b0900041900900e0900c1ca602d40313004584c10401440404101c000c803006080c061035001c9085080d070782e401002c44e0b182c4085a034000511140c00781c8070780711007603455034002d200b00c0401c5900300000364141401c41d56003000c40d40c4010700c0d0000a01300e18140041c1c0c00040e0300320740094113281035521b450b1400c04082e581240c805a01050401107401801046076030085817109808050580100d6200343c800000c7e440c113045201f00500b450b00e030080040740c400b8007040452070f0035026421780e4000e0741c2e20360402a20500c207544c0da52032075904000007000280201e198207811813002d0800b030803214080d4001666a041000d000050784d4460301040011a20301e221b514170715509080054074840960b030000c00c019902c1c0181c0100f02100d402040d05980c41e14040402031203110a1000380c0d14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 742058974 1250 742057724 742057739
    0x1e030703090311030c1f060522180807120302041206020c010c02060601080a020706090f0b063f0a0c03031106060d11040506010e0301020a020a021503070f080c0f04 72
    0x8016050b800280c42d00152044604040202c03950700b4200c10040c1001ea41c080380c0b82001050741c00a10402c10764403900001c250702c403060714440044964404450a0040b5070060041d41c0f80f94901c560030314400d0782540001102c140550721443e03040700c011003404d0840c0030160001d111301d801c09401e1500d200b50720f200700940354004094940c1040000d102d04081c1e410142e03514202584e0140c0410203100008602c42800d5000c0c0440501034407020902c40303440c0d2211120380c3d410b80340c00e03146803524001b0042e403410420000c50416042030100e00813401500301d002d03c8400e40300c901a0041c60308401c41013030350703008119042c41c00390000c4910103031540d240350240440c0622082c0601e203010340c5001404520f000c51350180041d401c00c031034a030041510b40410000b01001008203061260041801100d51003d10140c1344980d0660020b040000740c500400c03a5000c5a240174000358102081044040c0342d00c000c00310881c4207941020751040d2208503a01c07000d402101000014010041000118413 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 742060224 1250 742058974 742058981
    0xa0b0318160305011407050405100e040c09080d020c011d01020708060f090d03060503211317010b040e0c0904051228030b030c090a090b01090b12211e030703 69
    0x9900c5040200080d60101700250f10242040700c0010100b041440204241e052100200c581c0c4501490301001c2901008002021910001004000600f442d0401c2c40f0203103040100d00701c889034900040c418121020300080484d01e41e0b241c6c1d066000804a0f2903411a4001c0100801419817641035a020f403408662900300c0c85d10442c2c885841d481061b01d41500d486c000e1003444d0680d0000343c00391054120990390146004200c40c07403034442402c20480d48881440d5924124068048802002a69031190071168252062148200c0c491031501003450900305000901d40058802900d4101007941d0b075090031410000c45041f080c1000304c00241c844220039009058080030249554944580301c0418000ca00b21100b020309150154840c801c521064a4640b00507070740060601000300e480e44039503079080940c0000782d2000d0b050545a14505000d441d100b403080d0060103100c0010901e8008007001510401d01e40c02c000d6104120028183c180c807200b8810302d843c0007c42036052503403403c0030300000300103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 742061474 1250 742060224 742060229
    0x31e120c0303061c0f02011409060a020c280909020609060a0207030308161d0f1302030103020f010305090d081504090b040210320c0106270b0a0b031816 67
    0x21204041d01c5072400358415084c1d075110f50480c64080c1d08940c41c0d0700642c0c1208001485680b9500300780565001070742c800c40101940d40302540500720800c120001d12030a05050303815004d8440001e1300c8016400b03551400b990455480b40340110324840d5a00228002c5e01c29401a1504a00005510070754280c00103003200031280f1a5541e400c050795406820488114110000c5002420110200140520800c3d2541c1c680d20004c21040030982e6510014880d4041007210f003528580200040081d498408010240c0303200a007400d0100345003a001803a242d42015050500340000030000c140300e0300c07031207105142071840903100708060001360800384204041160102c0c440c1161034000d034603191161003031207000c0c0412400340e0241c180f1480038131145044c185030001114030034402c1f03808031300c1c0074000d91004182e0080c2648480c029001c5803204915100c0c0b04130700807400c1c20440d0700291240c401000c102d600c4041e07516102d0704c580203c1c0e1081c3c94540b05a113a80c3c40b078000c840e451011042c190108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 742062724 1250 742061474 742061479
    0xd0218032514090c090f10030e060907060504051c0204290f032d2b1403041509050d022a03070618080106090911030c031e120c030306 59
    0x4103196203100c0c031006090b440d52903540040004010851501400c1c000d44080c240051500140c1c000080c0450740c1c0a07000300f10000082d0300e40314440300024003030004a40007019540548440c1d410400085c10310b00c5075104050040c14424003c0400010303100c0691429a401001032289964401080280c1c80d6010b0070141c0d04410840310380010326005424819489000e0041c4c4405130510074000a00e215280c4403c003003929011002c4129281800500d80d249103011903a240940c00c50800d000c3d08070300c10030035000c1c03001100b80e00050040c00f6040d00d0b031043d40b1403034070b4a01071203c203454000fa01502c1d00c004c10300c0c814002611446c0d60082000301400d5030307000103036644140f00002c6061449103942c1c0b107601078010b103c1c14040c091092114020403010000c1980c0c4042e50b42c90441e0031500c072507004807906030340d07424071004210f0700c0780720300004034804c400402c504001d20000a440710604201d038056801101c102102100050114689038402d0454031500d510400d182a41c4a620440d207051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 742063974 1250 742062724 742062793
    0x90405251508070210020c1b2205070e06031008010c111f0f1d060c090a03080a031d0c01090b0301080613030e0a03031805060a0f18170d02071a0d021803 67
    0x5128204000f1a41040701c42c1182c9441d02c17190311107850300402b4060301c003000700000c0756a02c00d0161581e07030046d8026266072a40c80c190300c0c680102c1c1d0f421508809049010400b45034500c0c41407040000d0720072243d44462003041300c0e109004614500134002d02403007124850504400040d000c00040300021403048000942f003542d9100340e114030561082e0504240e022002a1081c8081219500644001062414000340b0441c290740a0340c0e003880202c107021441d0b4000e4035a503106582c42034400700200744c0c1c0c61a140c11541080c1045448907001444241040603000c40d0800341031080070500c03c0010043c0c0410b18503901c908006105282d00e61516410030000d0200140604080d01110f00702d00407035807071a080346003c1b0300803190b0901d020850020030360b00326400b007107240070000b80318040c0c512a402401d15220700c20019040911540c003016010f504103070303080185080f0304115110a03240040042c1ea07034280d43c410168902c08108841c4e01442420411291082c0c9007030704100468072941c4c440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 742065224 1250 742063974 742064023
    0x40b010605040815040204061e14031c08070e04051623041a070606061205100f05060f0d0c0206061507020303040603020309010b090405251508070210020c 68
    0x281c55a10661042582d1a400340103800c0502d412804607540084c0300400118506075500360348194800c0344113100c21107140001081103212824002c0701c010a00aa0261800c4203814490707103100c5034a42034040074003c1d0540040d00c0ea034460410341440c00c0c0000c0040080d401d01280c8072040800300c4501c20b010820041d81401c06148082803804040001c04c406e43c0f0707160900c00742c01c2681c07200001c02d00e011b400500c000400070703c1c14020359010303202c40e5640c2c40f0b00000c08081141500c001801c420382c3e00d03140400910203c5d1035020700106444041c2c41e203941e20321900c1c10030700142c800c081d80d017a0002e14094a00c0d1031158045040c0c0d018000868001e14401070640d00c1003010710810400070350640c400c0000300006800b94000d990b210b90318000004500400740080340b221031048a0845403600415654804d4103644034a0080200c070304090041ca440c06d10002080c6401c040c4000005e0107000c20004402a01c01c10142482010041c010340d22594103401d4280d81341c8080c00407488098844404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 742066474 1250 742065224 742065227
    0xa0b07060b030d320703050f0d020408011b05070c05040e0a060f2003100e040c12030806130e0c090a020915120703020910031a0d0b180604050322030c03030503040b0106 74
    0x104480d0701c0307086a6626017052998180ca161740f000d1551000b1410034071034600b04851030301c040c100030008940007268004d1104008030801d2100c0d034581d01440000d10407400420079503490442a00e40a9500244207440c4c869024900066007400034040d40c1098a036000a8030244c000985450481c8044000c403203040b07154004601040b02d0101d00418001e80801000d42000f804075003107070040101c2c048240e250b1202d80c1000d40c3c2c046003940420913100c00e0007505d0820f0000121140d01d03600b0100000218201d0840d101c114400031240704080312030100e50340204590482d084080003d03c3c041000390440f0084800e41c028034485250f103003001c000108958000d008403008241c0041c0540d42c1d000340303000160002c5c4803004510180200400755a074036174594180c480c6002e4041c0c02c2007c5c90740b818440e80c010307142101c410700300380707411903410f2200244000094940c441c20155891001d0210715110112580b1117074000307480c0d545500400000c0c503410034015400303540107071054403036680c070746a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 742067724 1250 742066474 742066547
    0xf07020307150503160c0b0c0307021b011407141608010c09050904030f120507030f06120f0b04150f27150c0905090403020106150c020a0b07060b030d 66
    0x400e0000b00f40f0030400606030306240c03c60075040000e00c0c117001070121015210100f165908446010044100006000640c1d8042150705443e41e5201040140000c0000009100c02c200c44040c0390301072404140581045402d801e1482000148811180094a03600c40060b40c0041c1d445a120694a13003583d00010074030401108003903a101614159045c1c5850b80c00716100040780c200300341008007a01d070f6000201d8650141c0c90190b2800d07035011a6000d048111401156010b0f8040d1548048404154000511580c0c2000c3d456401c1145040365070f40e035080542030612a54565a51240362288c4140c00149962101401d4400d00322250781c401104400c1440c450f0281d60080c09071540c0070300c10030400030b507030b000803a00340e401e440c01c1ca28940c2c0c1c500109540304000c1e03400306c001d42d444800900640481c800d524070108030382d00c0d0824144c141030700420907083c0c090040c0e600020340000c004083c0000b5801c02c001c0c144004c0d00300c520b607515510004007001c030251015054517400711156282c40d407403d01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 742068974 1250 742067724 742067759
    0x10504120c2003010b1e0a0f0305070b070206040e0c0301031106070f060f0f0516080c0a08190b061c060503070806130c0e01030302010509162102150f07020307 70
    0x182c807610250303811000c6600226000c4181d15648562001c503190301c1700d520144001842076103415510314100c0804c10011110f810480b85040d03441004c01c081400050780d0011200801c2515075600144e0010801c9446281c01c0b00500f041d011050040d00d44020380114100c074051440c2103154098039003004018400c01c280603200071401114040400c0241d07206100400c01c080c3d0010310798024100c20820f0391002c1343c00c082c840f400c5000d04403c407030300405130a510100f41d246461802445007400741070440003601c040b596030f0f409020038550300078603480041d241c24000d10103900c4194442c0000c90401e00c610203504082e00301040003640741000078800055070031281c058600d50b969000e50342489182144140d8480152020004003620900e441074040c500a5001081e94607100c41d0062414880f20000c0d05d51104a0404104100d6254911071644028000440d1501080d0001a085608003680009100000034060300729501c440300400c0c50790f10aa054825659035403041e410300319030702d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 742070224 1250 742068974 742068983
    0x3040e07030c1110050c0c0a0b040b07020319120617010218030304080c01030b0d0212030c0c010c080313030e06030a09020901080a0c051203160c0602010e0f071701021b010504120c 79
    0x501d0b04c44072081054221991003003c101107641404940074034030f8139002841100359044950402400f00b40a400c204081d841180c1380000e518001c021075600340414080e890050800260455080d182041500010020040d416020b641c450040d64400c0c000d5011801c01d0032441d805560381c6400e0b0902105890031221110051b200d0540034100546c042d00044210941c4030018104003001651126a40d810304159900216102c00340740c10320341d1501200300b000a041c0510224120001440c8034201c96111208403a0100390300128941690f020a8aa22080d4030000103c00c00034030100d00c0e4401b2100c14021541d040442c0da8502c0301c640c40b84498140035203240450802846281003040364041080c60301e40840c1d1414a0f81d000d4403140d05000c0e02e00b02c0e2131441d142020050a9824050030302da0400c100081c10380021102d510990b22030b2184600b040000c008100319554100a43c1900c030010301041341166140303442d40703c40d8005c1504540403284030f40401c140180d07091042592506a43d40b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 742071474 1250 742070224 742070233
    0x81807141908070b0906130b091302040302090109022512170c0a0f050c0304121a06090403110f0f16060f1403191d10090201020c040c1103040e07030c11 67
    0x91100e130700d0155004e00806a00060100b00207441042c03481c0b5000024a1a921403c0c2c480320001c08000603025405400c041040c018030080c00540d450204503070448504860061b074964440040040c041d904400048202c0d00e0203461f0740902101c005500c0031044507950f11121403031482c9048400940a40d84d40803038120501c9459035550003401340000450490070882d06003501d1040d054030319841508810074110851002100b0071640044110b500b420703100d4019031507d04403002c201107900042001c3d042061140001c46059014480229010084410ba80e1018042031031545d440ea19408408401642e40c10009503180c130800800a980c840d69031400201c2d83c1039001e10f00941c001810381ea010103154503110203200114450520224094000c01f0102c003c0b100c040c504052040d50f070840a64200000c950042c0e9011803014140300040710001150824044100c40303128110440649a00c030005011500b590517041d0184950615582400f035154560000c070b42503008003114400c240d10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 742072724 1250 742071474 742071479
    0xc050f10021f1118100509010c2607030305061201090c03080f090405040312060609060c02040e030d051f050a06121e110403051908040608180714190807 67
    0x40c00380004402d03111200020500980b02102007902e940403260002c1c5426140034028128141000b401d4030417241c07420030b82e051454031000038094120440e0000c180c189044071040c8080c200646d180c03901280c480460352124081c1c54090010032064850038491000c40c3c502c5030700000140036181c1200e6009d003041084601c0c0d81c4d0307103100070b411003a203560182d4828019142c4da901c41c0e02c5814402c5002e561541d020400741c0281108031925500000c1c10010410b0007800740c5074001120300c4159034182c9000031304403080b0035054194040c9030500c1548134104400d101905201c10107018020015003d0302c0e00e01a641c2c01001a0480242306101c04030306981c0c4200362000a80d407044040006104400d02000d0070190860129103400400c1c0c01a10030110381801400302c1007000c00a428501c1e04050030b2100652107400d500e02913132040c0f004010700400041c1c080480701c5403520072100c0040840c0c1007581c9400b203010342810100d0609019040d00e504400074031403940b49104c102c80404019003000c60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 742073974 1250 742072724 742072753
    0x706050702090a0905060f04200603070528110d0f1205060d0f080315060405030a020d0f0c0807060f05030f0f07090302120309030f1506010f0e09040c050f1002 70
    0xc01c01880308503030f25a20200100030030403d00a09200b060030003859901403619103001103800914400803600e80c803241d114250300b61241e404aa070081154109161594038003078203481140e0000f0031118180c3c03107420702116010780101c509403040000d2010f4401c0040d07500d408484150704202038000086422a000e2500005a401241c01480c0941680b40c440031a4803031050000064a045035040382c000104415105268411000c81004941140c0b9103498000025580d2240749000b80c03186040c102c880081050955569500603409020218110355803940e1a0f1285074510440000c82c0b400d500c1804054070650490344201e0705200101c80c25282c0031161940c81200a0013182840300016020002da0340d80700341c000441400c0001196200080c038181410143d420744022102e0f8080001005540c40324a40d055020704280307041c11901c40c564404446141d910451503801101040603c000d2094031081003054501c165510061007580209001400c03207841c80c41c10068120060007440078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 742075224 1250 742073974 742073989
    0x1e01060b13031b1d040213060e1f240201110906190210020c061503060408030712060b0c030306040510050f04021b010e0d021006030305040612090506011d0105030706050702 76
    0x20203c414908040544844100075940000d00030b09189501181c104001c61800030885103d00c00f140303201f4001c0d1454400340140d00d54000e07005110308c2c06c03402104400345400203d07a5000b0700480d010b40403895010281010002492000000154240f91399081c0300c882c8501220042d40026010902d04840c0c4403c900c2034010700381171101180075136100035043c055640041c2901c4d22000c000f80040d801d005400c585c022490102c040e000b0740000b000c000101c0ca503c0103882d4803150a051903004090400c18001c0140f10680001c940e103580410300d02d001074800070166206140944080240f03482d40407080c541980948145035206807581809450ba007842d07005004074084001e00340c198800d14035102070a450b490710707040050360305c070381c910803900c0d54101f040d0016203000d481c04004e50b80c21520300800303901c5940540e9050009203000005000314a41c8005e200b40d400101740c1d03a45507143d050752036141c1641c1c182504500c400d4000401da03441c2c0810301310200d88068451a01c1c0c1513042c4c0c02e12003030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 742076474 1250 742075224 742075253
    0x50a090e070801020d14180d0809070b030a1a091603020a02010b0a150f08060109061d09040b09070b160210200309090c070b0105211e01060b1303 64
    0x9008a07403002034200c40c240050b044680e040d54004c41c628002e10030440a10300003d0080d40e5000c0061441402c3c000702181d100c017084114030b130002483c0d0700c0c82e000303038070b060340660007038045080c00010000200c100c1d6000b0740240c1595074040305884455802c0012803034059410300383c0000103000303220b419400380c1e0007010b40c000c0c1800007040c030788800800a100800280e003e10101d4400c6140300701440c4d070001e000c403003d01450070246810304001f000240200031500a0034140703d44030610f03440049600c8503021000300b0060014905140500d481c1940071016141006184111540481d20a1030f90040e41c01d00c1c1c540e90304002001110340c081240080d44031800e41c09202280144148070584402c43d050460300041c002d43ea80d03800d100c01c2c0040c10758001c1000641820074456a400598440f05041c11180c084800650b85014401354414103103d02151056034418401c1e10b04c101c031800300510031404590002000b0040e030316140005c0030301c40d10b0448034241d2101c101c00d00028580c00c030154203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 742077724 1250 742076474 742076501
    0x40201090b0c0c0405090c0307051c06090206070206030702101a03060c030a0216080301050a09060e0f0601053007020d051c09140a061d0a03110f06070c0606060504050a09 75
    0x55010b68401290444034286c0e0782c10000e800c103003210003160038100007200007070400b551045801030702800d00b020002d0100d14000c05d03035900c2d01c1c1080700b5942c07100d00355440075800922480d03880c00d04c1c0e0301c041c0d61443ca80c8910034101d81409900e0050f42c00002a4801c1c50314040c0c080e1906a40b0b140c42c100b6644d02c001e0443e645142c2c240b01d9807103246884c1421110192041803902d54a5042c8401c0040c0718035140d1288459604099090050320407201100c0e4100744642e0314440c481e210381c03005942c54080c0760820895510f0101340d03104072907400c111040307255481340c01410003500e60280803600e078a58980c111000c1001081080c900000d140c1410540b180500f600043d40304290f40d542000d911030307040c01c4e012544406410001d03c4401c3c407588050700361944010781c0c1880c2c2c50f1100c9032103900b100d00c064207000415800d140c1c002020b205421039118a10103480c000e00d403d00024007900354100c010740e902d601d414004102c1c1ca00a1044405680c3d004101030724040c90160484080e03c850035082e407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 742078974 1250 742077724 742077733
    0xd060513081b0106050307140609030705090c07020f060f03060d0804030b07080f090c0102071511060103060e0609160e04060e070605031e01050a0b0702030f0d1707020105040201090b0c 81
    0x115450078003500c070382c540e00c0c1e070581c400c081e400c10080c0c2910b4444c0c221500c0f03074002000070004003000c64201032510606503005511648034100080c14195594001d6400c42155070404c061100f03598000e0009901c00c607408414441d10905001c2903000f1030664000500c41000070415030f01d403280c09600d550348540035103840c1c01d03207035070300c0070024001584c1200114a464051011408110110580c0410900d0040c900525070000003551140c00d84605088910705680307403211684900d0400c08199000d404450895a40f40303884070041c00c0e0700c07200742c005002e081c2c04030387c03822380201d1100ba0701940c8082c01c90843d4140741122030710f8603014202b103406640d81c807002c2c01011401d004560090285848060b102d00e450fa034450144010f400d800a8000583c07001441295203450201080e00c00301a00c960320381000d4404646480c1c07040071404824460315011201d015803142600b16411700b0325040c072240c1d8035107800a80c02c0c0d0700305580003804240c42000038005028014090061766450000f140d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 742080224 1250 742078974 742079011
    0x1a061b1f02070b070e0a090b0f03161a13090b0111160e06060a120f06120b0105041407050904050c090a060905120d021f29030606030c0d0605 62
    0x314211a0400400300da2150003054400c02d01100c040400c1c1c1c48105814400070329074a40c0c3c0041c800b1402800380b5640c0a66803030721251661642e14134045a00000f900f22214042d030a00c2550144503581f00b01c1c0000381501c050f05020643c14000d98010103400315071058002c0c1443c1390070006d0030816a5070380c10400e07500e1a015880c0c3d010807114045244406000700305c941020980c44200e81c1c001d01d0107000d04070401c4140c1e4050380c400c0314041040d10078240040c003001a940c0f520083c0500da8411000801c1c2403180000b800880c08880d4100c510071a010002825444049080110301b114500c2c00704005000c404441d0805410881e40505480716203480c1c44008400a0341510305a0003100014054041c2848682803403400c1c00407941000d0020080300c801d45000075620070112154560300314181903844201503090700714480b142e818501c0003640c00c0c09804030849901c0012a414841d20422010070304500340810480803160003c1c3c0b2030031400075035446ea103010b02006005c80c0d80072480780000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 742081474 1250 742080224 742080253
    0x309060304060b28050d1e12030510030f08070620040302180402280e131e2a0b0414090709080c10180f091a061b 50
    0x55200e01d00c50840010f40d00c400700144240d1055041031300c007100007804c1542c00956074410141080f16012186000c03018403a151099045104c2c150fa124000b10701140d2200300161003049403640d032042d540c200207c3d5203441d4143e21100141c40050000e5100310b580001052903400100300c0c550241c0808100884070300100706000c4030305041d80e405400003080c00d0007180790040b0032203030b01108490b031769030070b410944c00040403500ca40c94040850701c01c890782c039141701400318200002402d5511301c000c40381c60709a0a41d201b40780b0a00e01210b0080351203015407030a20540d0742c0768600e03036044001c00c2d03403644140c2c40c2d0381075919052003140c554400c2d004000076036029620040025003595107142da800121141405a800ca015001500784401c02000384184a4002030b02d40a8050455011301d0801040714241da030941964246840110800d40c08643d908000348504101d400c5607904221264045403015101d0000d00f00c416032100b010060504950300054500c4c0340026a401a41c45142c4c01c6d0781e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 742082724 1250 742081474 742081477
    0x10022107033e0609070504090b06010302031305100c0801121709011710171f05061c0b0603070911030402150c060709080c1806090a060506043c090b03030906 69
    0x2c1e011040d9116604000b000c410901982d40100001e076424414107410340d80300d01c5140d600428003410103034007000080413110320402d50046160410142d8001d03480c1000b1180244c00c1002104000c10050030002444803801c1c030305001c600c0e420100015544100d0390700809268001607a450400510380005030385011b820b212140541481c100b1190203030f2811a01080c203600c0d0765601d0805821404810b48180307000308070460f4200d154400080d1f956602400100071031480c259409002d8000c06803a0200034a4104090050200f02c0440d5101c1c0e0380d030081802a141ca14085040305034090021070010b0a140c515032120714640d160b0f81e800c088054800902d41281250100000342c421701d020098000f09000d0400c4000c03017a01c2104608020300840c00c4580320281205000d01203060015444403001e6011101420008120503520345d40d41d45040c1d0507242d101d480d8107a02e511040844200c203058004110107070208441300140d02d01d484030150003441d50514260301030004100a6140f07564110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 742083974 1250 742082724 742082837
    0x3020c1207090c110d030924020d0b0f100e06040e09030a03060602060705030c030a09080a030f06080f0c060f16121116090c0e1002210703 61
    0x30018540ca0b4030b01031070704081d10001411101400b00a6280b0507002d003010940f0b1050081c141004940341206107010002c03c03005010303107442040311000c003103455199900141118516444140031007024074081205500000781495071126050b003a041c00103005000f103c043c404010000d5050030354410340d80950840440d07081c0c1460300009948013003107401d03100ea54041e0101e03100611261410b41800b40142c1300240043d494404040700013941c01e41c454205200c2c00e580040101d4403a000040c0117000781c00d410070300f141d040d420501e0114000100180c41e125a003c000001c0c036101200341c05101e800c0c1c2c00110001c0c080e60003048800741d51496482500142c6204e03404040c07079101a40401844d103060ba07004848a40c01c00480400303040425041e51042d40d82c010b200103071000007e0000c0d034030340b01d1040340660010b601d401c0c0094044c0d000700e900e0b198075808990441c4041076842140b9850300c00c0fa00001c0105810b50035540c03c00c005414054005446a80004500c41007902c02c880c9504840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 742085224 1250 742083974 742084009
    0x11d09130512040b0f07060906150f080a0b07050304031e0c0606062d030f09080301050406060809030a1b1a150a06200a0f0501050f07052503020c 64
    0x18101a040060400c010b41c2000440480b0505103820010f899a0512035082c8410603400b02140c1503084c02015442601d9184c1d214a00300000340701601e034500c10310500d10070403a540301d80b81b00015000101248500084d9444601d8640755920b031203007512141c102901c20707000c2011300e02c00003601b5400b07041c80c3e16031402162602e00844096107840c1041da00d83e41c200000b0041c6208120308540b040400d02001c0e20310510700d00240c022000c0c002ca0013450201011901a418070090105100c0544002c1d4142d40041d581842001c5c0c030350a0070780e0101010b0704e16101641c41040704e08400c85c031500710054480025052000318042e29140c00c4c11083e441d0242004d040302c1101844040c1d065200b24240300081034030b47c80e00042c80c0100140c000c25402881c6c02d5202d0780b041e0040401201444181f92080e44040450700405550a0580c001d0000700c03081824084500b02151099008805031481200070b1652002800b151900464070410021422400d41c450a580785815964071262194144485d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 742086330 1106 742085224 742085251
    0x40e0c07031d2d03010b0a0b180d0210030f050f191a04050c0a08060d0c120609080d090201031802010207030b0916060f0e1806011d09 59
    0x121002e40c10101e200c0008151000707143d00030ba10040400d6008102805c2c000040c440e00c4c00c518020440118818171040201000c42c1c0602080120090718aa600403000e6011500d074510b90103810011a40340c00410210303c803184230b00d5900601c8039600c0121800c05081141011018095400b50300d6103880ea1910101c3d06035803442c0c0075100282c0104268a080c0d003003101350390032107402e0000043c18440072510034501455040203e640140d4814007040c504440005004007400d02225840c1c5c0f200780c803902103503900c4040c10f4003030300c40030b4045545012880010100c0f100b0404004245a05c120001c000d41d90024100e81629407080c0e01440c0751300d602c09540d14203c80b40c3c0002c00d0044001308041082ea503c222040c0c0c0290103a215040e200310380e01c08000440c0b60280e4820800e60414000410541c403c0c2d100e290922300c3c017a41c4cc150784083c0c0f000319280c404100d03580d050300d20340f = true := by decide +kernel

theorem cover : BRFrame.Cov 741906474 742086330 := by
  have h0 := BRFrame.cov_init 741906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 741906474 ≤ n) (h2 : n < 742086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
