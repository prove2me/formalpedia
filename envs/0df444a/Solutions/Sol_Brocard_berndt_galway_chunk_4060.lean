-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:27:07.11447+00:00
-- url     : https://prove2.me/submissions/2734f7ad-d5ce-44a5-87af-a2db9a02cfbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 730035971 ≤ n < 730215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 730037221 1250 730035971 730035997
    0xd06030c0f090203070914031006091409010b03030f0d1103090318010f0e06032a2107051219021c1506090b091206070e010f1713031e031a0303 63
    0x100401c5003445240c9109003031140902030f0303903488070309c4c0d10740505540c0b41d0b50000078902c1d61504d140700d0341300d1070480c51a084015032009001ea0247d1200103696401400c820318504140002d40b4035000c00346520140c141000300140d0b640341d24008030b50f1916030f08440d40e200c0c1c1003601903c039641a0361041d0041600448031f61190740f55480042c081c018039803c001c20100c283d190401c6010b900d030308441c4988080b130091130302e010f603540302c1c00b0032480010010300a545040c81c0b0310000d0108440d084402e449100d080d011407410f855543d02d1450b1803902c90078040074603483c40052003e01c50300901c00020500c1c07003014002e0108048090401080249600c100742c0083c0384610207001c80c0395881c005100182c0000e180d03151a034954405c907070500d0f009407180d0021841288030340c0815600001c1c0103a0550540c10301b040d00c1030a0756504910b5a40040280389092100075a030070415002d84814400a1142d9440303c0075101810000b80007441c0265001c450007131203032140442454000700b140c14071010707a030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 730038471 1250 730037221 730037237
    0x50f0901050c07030c081e04080c01091a070314070609030905030606090a0b01030902031902181b030601030e0105040f1e1e05030c0f1b0901031a06060d06030c0f09020307 75
    0x5141207030524501e91088a01d60010404980a5035074015100c01c0404050225503236030b443e06600514281101140d1410b00c21498010080c070654852685a982084e5103142c0da00d010528007100c032600080041c00d08083d010074010180b03e02540240c09140c401e03110400c100d5110000c15961740c004442c0d9a620112680c0014141942030b049000100418100810032061980c0042c1c20204550641c8002625184502043d032034a606940d03103204000229103081d0902c40d0789240b05103d603c80c4000008000004034a1300d0344280e12490b203405030080204181e0038245041c1c0c55000c0c4003002580c59400a01000c00c1c420104110f5107900c42d0b01c0316810382d089250740c05140c2504a441d60564540c00240003401140509020102c01c112002d0040d121b0508010705092800d422421220f000d010300d10014000100b09c200d40014610340c10342d2211042d039510f0005103c5100302c4924011403414150000300301301400c42c6103400c4e22401b4004c00306003601c0c0c1d8132a004074081180e01c400020054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 730039721 1250 730038471 730038473
    0x611060612010b12010525320403060c090e06030c22050106050a020d0c0807031206033201020705120f2511010c080901030f0f0906050f0901050c07 65
    0x101100c09014854001140d05000d4400007841840030a441c2e04031651110100080000c604500403000040c8403265000b00d21030040060023100c1074100c0360341100040c5005000050b8903003040341d01424235a1001e546d25203920b03005001d0102c0050481c0400d1140b4004904500d80035501840f4450141c01000a02c490750100040594141c000410f520030741d401e001d240300c01902a02d40030307046540345c4907940d03201100300901d000c0700d4020440c1002600e442d6100004c092804440002e609450205400e5080947c00401054180d100a001e40782c050301c07076a51012241030100a040c402c20700810401c40348080e1078242d1081890040c120f8211494405903855101c1c06022140755514080d8140200300b16140000c8140f062450448220280082c040100000e0340c640005801e103410070000c1c0030782e03440c0d0300c07280204000c56040c551101e000000440e0f456012540350f000c00201403044044a040c9100100403c2e1703014513200b00d22030005850761205010b51401344100010540c909055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 730040971 1250 730039721 730039729
    0xc010b0d0305271003090c060c050a08091f0f12020301080c091e010815060607031202091201051302120601061b030e0306090f160b030414010204080d0504090606110606 74
    0x4204403504080c031002443c8440781c0c40306002ca440e00b00d0140c800007600c2130341d41815601010700e82d110800700080c20f407101d40041e20101e040c221705a0301900f12925461400005520303000700454103215111200e044055844e400702420040c00b00c25100d10000c400a40c0c180001e03403000340503d070000d0b80407544402c2d650610359982c0381d1140c1030001740c06481a0311100c4114511382a803040c041c030741c4030700c50307291220000881c0c032500150f04403013030344c54403e0558001c1c00ca48131070480c01c0600c0c1d50108100c02a91a141580c14000e080038008110501d8042030385444014041426400b85111080c0401410740c00152036068a0b41c540302d82860fa118049012002102260300320104054000108110784040040b1809010b03c0c40107400c84102c2058031514028960fa4460702401c7c0500e402c0090400034011a81c1107500551564095040709080502a100c1c2d68031183d4030b031140c2001c4904003036110001c0c006031425880305125190341c030f000490b0f8961403100c00c665244c00120104905141c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 730042221 1250 730040971 730041007
    0xc0d120207050d0b0403020c01031404060c0905030d1107050418080f070f0f050d031a0f03160b0309070501021b0f042a020f150f0712020f0c010b0d0305 67
    0x122403046070300d080d45a0011415140b82e00b18100d031421540c00900007016018000404404020710381007104107016800d8a60640d40a880036091594880704405541d200d1b4020b4000b07000e000e0122104401c0c0081700405c1d1900c0d08002c0c0185020b2104082964985030003070001030030310a030084140e50110b4072101e4440c0c0c804a034100c9880810407e540004211050210034940130300380b0000986a541009401d2441c4a0301c25003c152901241240603040c2808844032414207540c3c4034418203618011078900000c80f140403900120300d050006e4035505281c020751003201040c1c1910042551a801640c0d900d21440b802c86071303080f03401d0500042e802c00000800026900400c0856030440030b0030140801803102000b200c507189400c2000000b01d0f010001203030000c8254008107145054501c1c085200351015090902485610001c47d02e0684070318400d81c291411410215590004081c0e50011688135102002d280d5003042c5003421a8a041017902130000d03056241e0510304004854001c41d680 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 730043471 1250 730042221 730042253
    0xa17010209030a0803060102011a06040b0d1409010c09091116060f050103050303010911040e0105010503041a10051e010c080a050403050a1a10180b01170703060e01080c0d 75
    0x9982404100d1455400700a039515407406210b580d81c0e00c2c10301d10002400d603040081e1b1051940001a070541050b2550004c46040b155000400740d2a10031030300c00c840140c232466042c40210840103042c44a0328106501c0b22410303011a4486541141d0340e000104240c4d4510700b50510501c0f000c1c007941000902c41c0000b0080e0610512001941d20702580320401115801e0b00181c40c69440480140030848082c0704581280e11089142070515241800ba402413440500501e03042003800f202040c00c010740d600348801003440302c40141c2c80360306c0c06441001090007107120b4a4403540340942c00c00c1d200b0400c002c40140170f0006070b40714024065681c9034040a5032088001000300b000420000010030300500140d0302c2c2d02d11482865440c00e0f03034801824482040903200c44084d01d1007030350400c42488800958050441c81c8840415402d082d80300682c3e40c2d05080500010a02c48d060401138003650651081d002d650700c00e4090300450344c075100039981c0d6420b2103141a801070302c55600c10340031403200b4a0486280d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 730044721 1250 730043471 730043473
    0x5090132130212071802040506030a020f04080a110102060606071110050c010e0604140c130e0304030f051e0d0203070327080d0e18010e04021503090a020a050a03020a17 74
    0xa1040394045010743c0301c036551103121074204000c1402061100000740e460700803010810350615080000280f41c92002070890fa010b5035000408a0320000c400090340d0080000b1010b46041d111241040d000040d0032208641c018013514001800301e18240055480e01030308007542241c10000305050050304900c1051040c01e102080c044100700310004d004d104e81c4109404003816050500780382c0540b0414101c0e40c070700e00300c1d08060050445900c07541640024501d2814000c9017422154a00e01c5c19841203400c05851281c0010f100d109100c00040c80f050745609400401048002a2038030a80707e82e400240080146c00421005010900c6501100318500d400c401c01a803601c0c09000d1900c01e02510751007032180c1d4200c00304110072140c00c20f41660404c41c0681d1038203041c1060520010b4441414000c00c5072610101c404035080d0b40b00c2000040c45810038854107a6070742400403810b503440718290000ca120b446040c0e00860a41030994804003140d601800c01d04070743d814203111b20745c0c02c1a0700c1d2440ba65 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 730045971 1250 730044721 730044751
    0xc0403081b01020a021609050906060d150c050301060e03011116050f0d0e010f030b030d050a021c0905030708030705100203071103070602070303050f0712020d15080105090132 77
    0x1c614402e00c0245019070aa80051410504005c442c0c208030300994095100300f4a810200700d840c0c0d1000c03400075440705040b280405000201c0c43c01000160341503101c5800d0740c2c50101c3c4560101e80020080d81600c14640b69a400e140040341007600340c0b0702168503030503c20f405001c1c0307092031a1840b0440a09511034016102d4400d6412107251070420341c4600d06001980704c88404504c3d58101c400f83c40f1024880c542031007545016070100c0d50786c031040d186500801c1000282130b03442e14400d00442090414074a0425007015442100134202c1c50b040c000c041c030a014401c0001074041c0c2c00003c07186031540c414041d02d124a000d010100080d00000d10107010710a549801903e0741c2c03405d00041080b14415400181c4903081c9040007011184014050140055000180090b494101c0c03401c0180c0400c410300540c1c0c0b0480010000c0c0a4103200d40c1000e0440301440011955030419004584203143d001d00821000350b040a003002c440c00035114143d000c0e00748440b009028208001c4081e4054800010034034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730047221 1250 730045971 730046017
    0x302060d060803181801080613020d12030506030f03120f040204090c0b03040b010608060609101b0507090c0801060503010b070501024621111309060504050c040308 72
    0x30640d40603130010712800810b400c00e1143da281c100e045c02021200c542c01e0000310340c101b03040d06540744006051150a400201c82d0b504c110f5030380d00c880000306035009481000484680d030010300901030035607a50b031084c0650400d152100310f00000340e60075420800c0308510542c40306030140d80c1102c00604240d82040d00e44400301d000c50000405038008000500c150741e80c07441d003030410042d540c80681040d0200110041404819500d03001a5094040c0880f4540d0840340102420f5402c1008914001038041d01355030300303109000b4045881c4040720f400110512900e0940001214149800d000b10710100b2400c0c00188010366046000d4001c9a209100041c40c184021041c1180740011000f03454603404110908804a800180760960000300c5100b10044030742c6400c00640340c207015100c0c21640c52000d410903920402c0030340100c4074550b074005540380d482d198012041c01030b0302036000788000182401c400140504040c03181c00e1007041d0f5034a009080c2803c42d40c8800141e03014040d41806906001403600c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 730048471 1250 730047221 730047223
    0xc030a030506030304050d0c1a1804020c0a060501061715100c030504050a0b0319090314090a030b040c03030216051008191103061203090d060e03071b050a0909020a0302060d0608 78
    0x1203c7c00d000d440d11b01c9049251511800c4042104004100c0d0401c050043c0300c600744410f82010030010b4201c8000d40c44002c0400c0d460300c0d0586e8524050420380c1044000100701d604101c2d52010b949400c07800000170741e02e00074040b03c4a1020300300c903500100341d8004001c405108810760b0101e40d100c1d00e0402d140c550b0740c10000c0e01c05180354000d14524100041480042c0700e02c02141038201c0c8004100348079071556906c016000c00004402050341000c005901c1025980d10341010f4040c0d54071020400c0ca509007810708244a43c03047c00304070017501c907000c405500e40e211581c1001c02c81b0001407200c9800380e10340d20101c98009000c0c00c0c03a207000011301360404811a03240640c1c6030b0307000078000d03540d200e10f8501c003002058880825500110f400410902e400c0f521112407050030250000b4010a645042c441600e165100e00c507400760000604029094102038044401011602d00b15035042ca10b0340c03120403000860f80b42031002548907a18a4040005081c0480500420800200002411070340d0b00e41c1e107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 730049721 1250 730048471 730048489
    0xc090714040b040504061202030c060d060824010e1620101e0b060d0c020c060703030606080f061f030e150901110f040608041b2403020c030a03050603030405 69
    0x7445002c80414140000c0c109441008000c004031481d0b6050804160003190319019846401070060000048022461070340387c000c88024007503007040360444541f0300300c860403000078000b10650f503c41400000440311030043c0158005d003030601603c0b11240c1915400c2d80c241c0c40301d03403221034a007125550000c0680000c0c44030945010f00d0300f41c04100c01c2030300b14109403084d02d02c82c110007065242c4003624116403a010151500c1108800c000100700e50500416131918403041000740c2c7c45200040c89508141e4941c11420440c2c000f0345036124240c55000d10000e20810494456400400c4079100700340511014907040f40c0c1d0600ca040006510588402c4281070584014107901289001024010303903078024412620b000003990012400e160140d8048030080c45180300700ca0800c00414086006d1002598081040300a0b500c0034000c031554809991a682c1603030150841c100c000c210540d80424041d008850359007805102551a00c10091000e800426024251380e415102c240000718064131038003c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 730050971 1250 730049721 730049729
    0x309060e150a0c0504030f02040b0301020307110d0302031605090109030506270601081207151d153601060602010e0d0513120312140105010e120c09071404 68
    0x50064030700c45078516920050090401c64020340b41000f0754040a621a06880c1035aa005200103a41c0180d0300015000d00b0311000d000c0e906510000901404940114001c0710304002d40d000d0b1541c00e01e65002c01e030220f020440d6810000d408101007104414032130030040210780c0c81418099601c5440740c60b007518045044034801d4005203050302141e60b104081c00b0360824400b400000300540d60429411944074540e044001c504484049001d20410023150300c0c0e2100415480c0c000c012000d040d844103032818202807100104c90013005c814201101900001c280f141c100f1061204401900c002c1c2910b0703a94081007400002d107414410b0100783c110030b0003901e004001c0e0354004501801c6800445040000c5520f08800380314080140300c1202e480346141d50f0032501840d0262000d00c120b802c040d1042040340110407461441c0c809a40f000982d003155890680d6401c0e03860701c5056000c4c2007031050002e400c410740e4030280c5c041500200079141c680d5002d64440c056182400c1d160144041080b020b8006401c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 730052221 1250 730050971 730050973
    0x140a14061c051008070315020304141615021603080d020d0203090a0512120f07110a060923063c15011d090901150807031407080d030c0309060e 63
    0x511010200b03c64a68001c0c03c0c00b14040e190842c0740d986d540170001203003e016a50300303402000050901c21b44009880300031807900305541545a10110802241400c0c0c05130070900401704290612080c4005507400c0c010400d422210241030a580f07818009400000850040d1502045610300f0102c0500155000c2d40c1c10100400601560f0319000b800c010340007000222024050043e030749174002141081e40c0101c3d02c14040b043c1358079400d00450740340a10b4008008507102d002040d00c00c0062036030240060a004014900103103805010402c240540c1c01010105584100042681042d012410003821860014010092074408415454a0010300c44007003031841c8810070455403040302c0220242208003445e1001000f0801c6804921100c281f042141c02103444800007404070b0000d51040c1100c0030018666421030365210034555403085180021200d807482c1400c40600004006401015190043c0180581d00002e007030450050000c8210072003019101e92151010520a01c24004000820300c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 730053471 1250 730052221 730052231
    0x10060b030c220801111c0219050702041413060c020c240702120f2e15090e101812050d181110020f120d020714010b0a140a14061c 57
    0x1041080910319403005840e0954010424101c003090200f010b0100f4000c80e027485a25400e0380d00100e0300414018001c98492a032140c00e020340c510805003c2c0000c00e1042c481406560340c03d00081ba254101c0d00000c80d0007a0780300c098006080c0c42070201854200001c11040d0811059400040c1c01c0400c145c0188030303680044662480c6680240181d0a02e48000e0084402903e1400103042044003a4a1030024a903958480841c0c02c54400381c1140060161f43e40c148007036812102010b4886909130101d08105140100414118201440d1810b0751904104244001840c5010580c1c003030340b00c600c0d503d07030182e0340f00c0340c030100d0407041c000d04044180a19149a0200030041c140000f010907400c0740c80546d4001600d60b90b645c900020324400b0390074240b0605c0e4551118121203c0640100340000340742d203055101c46210f10300e05500642826500306d40081400d075480c40c6000031840e11201082d0082c08144040c00010414032000d80180c50240c80d0610f000d0f82c0320301c4c54414600e0150890052a210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 730054721 1250 730053471 730053487
    0x306080712030e0906040f050a0606020f07080d050a02070b0f0301140904020a15020f03071b0b04063f05060112060803040e0c0c0a0510060b030c22080111 68
    0x10403941020340111005608051541e031000307440d8004841c44a40700b00300400000781c50751255006250564500c030010b01c100e007000c1c8040c8002d0a0035009000042c807444082004030303800098882d040301c0400001e007c003101900d1045072130b548414600000d52203001000115100680010005200030a290544a50424101c0440f007115000048c2c800c113943c00c00e010240c1e540105650451b0072100d00c00c818400944802da05180041405003805c0c0400f1034030509000420601070319a0070340181960901d510303082c84030b0042c012401090000340305800ca00540c4803071201c18106e00482056007200700340b0881c03a120800758000c6212407185844406000c1d02e56007200300c15a481070048418000e0034100380d0a1941c9008502c5038200d60b031144030206004119100440e01d05509030001d4651110701802c1107680c82e106031104c0d200c4540f17000c03c0001c2c0f41649000380c034000c40c0e6081c28a40340c251030b10041d0080034011301c4c040480a0501c0e000207006a024880c5410f041c94940a140d194140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 730055971 1250 730054721 730054723
    0x207080a050d091202100c0624030c0801090f06091e150507050a0e01080414062a1204020d030909020d0914010c020a02061821010b3c0402040303030608 67
    0x20b40d84074504940d80b03401420011b039036008101700100414640080c50b00101d003001c20152100401ea8401518801420b041c11181c484010064038001d4114000c004e68a4810b0781c2254840340020b417030f00b806080c040c00050407903008010146d0007039180072094608804461450040312504560491131240a20302600050144a6101000d03041c05802e00101002c00b5140360340f14401366041000440000d4208903c070604681d01d02c200b2400c682c1c030761030003081c0e480001c08204041c01c01c903002c08a20821844c2054101c2c0c41c0c4107032000200c0d0a640301c9900b40001e5030300007582241807000c86803000c44d0703417641c074400b41c4410105400d003c00c0c500c03190300b48950032a0070401090680e034101040d42c1102900011038442c21541a1003442c2d030390030700c03440c001540c607101c0c100c82d6400592010820580d081d14030180c4002c41011000f00b00c1d25055508000d0710fa8403024100d1410f02004100c41d02d100c2c1c990b8231424101d1500c0c03501e86000320005000138102c1e80b190708101c02107a5121014801a08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 730057221 1250 730055971 730055987
    0x3160e01080714130305070617010f03150902040209090906060f0102122b060b030a14090705090903071406070f091a0d09050a0303090b0c1c0207030207080a050d 71
    0x6001e003080c8003a4101401c005003d11840190161001c1c80014105500480c15a20030001c542100030b4480c1181c907404d00400c000301d6502c040c003500c003c0c080045404100f0020880071207070f0050380b1038000d83c28a48094050070041d90207980c01a424800c0c454181c5074032005521070480324000d881a89450701c200034144441d009864115480b4284414800c000141150326080c0d01030103006c221250114038540b9201c403441c41100083c14000002a0611400c0140d07016041d00b44082c00881248610441100c0085598015039401080108160700700b80c80310302c1d0040e100b44160703490103045840c1c010b200d40a603030b401441e40c3d00000030044404c0d80089504c80700001e5262030b060003842c01d80544201036181c01844a041c00010703041441c80123980c0210006940b040c2641c00000711800d0140080003d1102981d07140d0309000041c00d104110b000310703100260380541000441006803800b0009411508046040d44100300b004070300000c0c100812440548104024000e803003250000500c901 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 730058471 1250 730057221 730057247
    0x907081207020105091516141b0105031f08161401081e06040615030e070b040614030606040e0115020d080615030703060b2a0303061f0c02060316 64
    0x8014009400180e900c1400c440055108540301e820b00c04801c06c14032171030321550100484540440403901d04000000f581c00300c2c5a0034200907904254484c001c2440507940300701e03075a4006242080050841d0512610394001451280c0c6000c01d120380f03441910307152900c03060388916a507020401c1048182240444d030b0780b440d0390a103480001400d150070820051111942e000c806000044006640c545807580408000d00c3e0310410840d49446000d0064001e00d0301c1c42082445000f40e52021603011000b030211003c40f5441d59508c80c0340345400340d2300c1701d16801c0504007961000c2c00b00400606045800c881c01c0c041d012401045803042c6e00440003a1606891405410903c41d882c0d04100442d658112108905110000c485580341d40d02c4c2002c4005042c580c00c43c0712544c2002c41c0c0c03a0664101d0141c0c0b0703641d00140c0d11480f24041d004003c680c2c0d89000c1282c1c000c9c1d010f11510170104080380341d40303101d0300000c0482c01c0200304c40c3c3c50340c0d0000308950002c50307080003610190203c1c0c400442c0e00c01c5c1c03481004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 730059721 1250 730058471 730058503
    0x15040c020c090c0918220303091a1b07060605090106090f0e011d0603100c05040510020601080604020f13050c070204060b1908061504090e0705030d09060f09030605090708 75
    0x506031001094107010ba032401c0340c000d08001000a05403190021442c4401b482c091044d82d1481d06502c1e020303000340060718040d6440030080070b0b558480142400510f003d48080e050004003086030340440b410340c0d0b00618040340c043e91a64000151078841044580c040d0010fa06e410001303600304074030800940f4940d480302e2080c005100c01000415028190026103000031100c414456940ea00843d14040e0315032303803c0400d54070309007881c14081d41c05400351003941d03802c17100b26001d01d00710001280c1d20302007805441d2450b00302501150061400480c0c07000c41d0100608840c40c01c0903100411412910121010b415081002900c1411813415204423805000480380c0c4c6800c0405a00a0121283c1d4503580502408a6400410260360300c4200f640c1001d0b41114245583d16295608000a4000361031680b9441c07107804400303d1580340104a80b901c8410658401d5005403919008031407105103410900c1c280205080d021011641f180243c6104101440c001e00c075140c40d000d1050310b8030020b24400c00c48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 730060971 1250 730059721 730059727
    0x2030601140f0d03050f090f09040b22170d090804171501060c1104060504060b07120207050102210d051806010e061e060409050f010806010e0c1215040c020c090c 71
    0x25080b10a81b00c5120104807550384640590020038440000700001c00d511038622002c10082000c0c0315005482041c510107030070b141950440c81e01c3d01100c441070004040e41e8010b0200c1030002d42ca00d01070302030f158907807030049013141c2c40782c803800c88a41c00741d0080107808000503030b00480300c001007105006900c07840024500340d40c5000c07401004490110002004181c4880c041c10940d41c1e950880805001c00900c20000c1c0d40d034a10743c110301a804030b14100d0b000741c01a00080b8209001080d01c00c212107041c0c014210448854840c5900340f40ad069000b0f505100074801140700d51558417400e40300f1780d1508181d41c82c656001130843e05d0b00d0b1050380048503038441034040005c84d4455020400c4401d079a0240030390074081c2e080024045021710341100c04440c0c50003007084407610b0319001d000c0c100e465600544070720740d0725442c0a01b550708003125420390956041152000d0b400d6090f00c419440305269019a541c070450400040c00d54001c0c680440041c0d020240d0b2a0346464103d0480da009010100400d01e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 730062221 1250 730060971 730060973
    0x3080411032d070306060b0a0e0a0509070810031a0a150609091521120f020312070c050703150b01030e0a080702060d0f05011814010e0603070302030601140f0d 70
    0x2410501d419142030b603200411004201c1610100b0001c000b666000c0b1083c400280c0303841e04000c02c0d402c0401d1510020300001b080904a080c403004400c10fa030b40140c030342d0305c89a540020507190400c6c09003140100f0340f20943c00001040040e8440c1c425814100300e10442e90800305128004e4480400e442c500400c0c5290080082d9900201004203c0f10701c1034020481020010321414660216480030900540208039003500d9880b84c039460250381d201d0035030006500501041282e0031400038846a01580c400c20048480c40d00c00003006074080201d180403c2c0b00107aa41ea02e07401c01c94a40d00884810800c0568000c01140500503107062800c03c0c40c04003c03014207404480c1d5102c100d484090141d00c4001000015034444d90100e41b0001b00d1031006001002052507000001c20091080c0019010058040301041c1c2d1075010b4a80104001074601a550342001e80d50b020700f040142080c0d070b162149190000042e1001e01242d4000c0101034010401c241c0100d007881114003070009141c0c03050b2100480c1d04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 730063471 1250 730062221 730062253
    0x1e0f1503010b0f010f0c21020f03130e06040207120201090302011a030c06071e1101410d0c0305040209150a14272a09010509040207020402070308041103 67
    0x4000800c3c00d107411859040040020340e6a44040c0c20060311400001000018808044000325100d2081c0c1d801c803010851707500e8149840c4d01406c00c4440144d2100d50b01005400c43d8424000e4026000410040c5405401d558100030694a21481805030b51114900d1081c0764083c41380a1f4500103154000e019508000d0029490794001100c403489044003003401010301c4150303c040c81686800200c0745440c14180e040c01191499002c000c140090b2900903540811800c4c100c10f819400c6104414a00f240888900e000040703200110600c403418041c031680341c2c0c03410140a4078007221825100042c1c2411320703005201103214014410384c0c91000800e007051594850f9208001201c03401d224648100d803820000510850701d91048000b1802c55248040e007009012407228014110f01d01c404420065079040d400c86800004d00c4e503205503800707000e0b10000b540610020b110742c4600920040c80c02000354001000c80e0090a003d0300007440000821081020b0950700b02003801c0110000e0150102d100105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 730064721 1250 730063471 730063489
    0x1404030f08090d09052211070b0912030103020d06150f0810060302030d080702010603020d080a020f010b060a050904060b07110109090e0604030c0f050f100624081e0f1503010b 77
    0x1603000b40d44004c0c042c03000b600c001d562050002c01403001444280440310200c50386420023901695120702500210341d00c09000207118500095032860141980c0c0f8680030010300c045500c0090704c015885071000c075410b034101d041d803074040d280f803101302d140c154100b0050340d15000c0411140c0785490b1821f20207001590300007420b207030b0446040c504080c581e95500000c81c05404594802500f10313000400403406c000c000c001428200000b5802c68004007100b114041c265006440c1c4540c005200b081200c800e42d100701c0007014140e40c080c20200e10341c1d90b039401d008901c0c0d0000340300340c1e0003078241494a001d943e40090510024500c454007030100c10344070014652a140058401814003000320010010041101c455008141e00142501c0200076904d02441e100d9580c0324400784041e103020b0009c00d0400403540109030020440a50341c812108508040d142d16a000d8200105490344800720021003001e6400d1a1041c010030400401d01c0c00c044031a0440302e045180041d101e6414410000d9450310369440b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 730065971 1250 730064721 730064729
    0x618011406210a0f060c210c11160602370c030f06060e180622150213050a0803030f1f09090c050411041202041404030f08090d09 57
    0x80500c150052034403118070707140100022903014807914a410b204980c1d0044c044140a17220600142034000400c88141805107182010480300300354010502541e030b0712030444030b1001d05000d12a0000c082d20940b40c06450315a000110440e0202805034903818000d26605a0503183c070f4041841040c1d03001d10682d4850082c100d1239440d4101b00c0c03410b120b00310f50702c0341c011a040440110700802a0401d040904568081e081d45107400c1001300f000030304080c1c9180c00180000003c0d005030313220001010b071524001c0240b500041c40c0d13030040360701140b0392280504018100c6480140e403071544903903850384012103900c003911480801100700141da01c080700b141d82c0700072003102001040d40c408140c1c10540f00c50724640b5010b13034070b108004590030312960b00c0442060b01a0840c0c24000784c0e40d004110a0b80c00c0d07141c9903400b41d20144400c01501c1c41500e5140f2044d031000b000030480e0905140b41c104a124112402e8001650b9003800c0d00f001c82d04890450f4004410302c1c0503140003400c074440a4548019031003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 730067221 1250 730065971 730065979
    0x110f031f39020609060429071215230a030c060507050106050103060b0403030e03070323010b060703231c1e0603020a061d030304030c0819030c12020a140618011406 72
    0x404166203c3c0e126200307d514109070907240d1070354100000010003001142420340a030a1800b2651100c01c081c1102c0c0b1001c40740194011141c00c1c88406a014040794050503a83d000001400e0110005414180c0880034203030a0342d40c03038ac440301307a070400c107003501d02c0ba03402581414540f08043c8854640300d411142681e0701428209012000d0101091802c0301c50703440a80320303124204c2c1d11111100341d6030711601909031390b600078003a2403640c83c00c100c8a4071900400502280c03080c0000101001d00558820380c50380301d02c42c50703410812081030708a0b50a070242c0c442d42585075150038040d0b22041c1d8201c81e011812001e030341045914210784c040345444182e4007540043c4250361243c640076041501802e61300c9080a005e0342e40f00d89e50f81c0344c910b28940060184588034001d01c0780c424925014510074184064042d0303a01d8804180f5500c44803c01990f540c60315045000704c21041020849007181000c5600001d002400c4501e0507400003100070300e034180c1500c1c240c0d06150180e402d005481202c6a00607000315 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 730068471 1250 730067221 730067243
    0x5091b03060c07230d02120f1222081b0628021b0c010f1809020708070b0403020a110a14090601050702130207110f031f390206090604 59
    0x70070030301194119000c00c101812010741e0f0032881008085041007151111b03030200c640604600900320114080e51868107110364003841030990788080311b1801c079088075180304110040f0400c90f80303030010303030b105501c003500c42c00c00c005030007000c01150311042c80d007032034003000074100714181400b024041d00c98071100655035095407140c100f00c60035030342c0c12503460501140c9041040151000300e0fa031500d5105000501046408043c0c5092502869441e6100c030912581955034a0405a00200a4001040540361100148510000524030a0050307008502a80082885400b289060345000d110070382c800f4085c5010420401c008804080380e0005030310203d895507941ea54000040b520380c01007503c003030b600000f0411444040780840d0b005020507030003a11a400a100e4003824041d001154804103034040e0f0010070300c00300c0e014103029450103000c0c64a01c0492407022080c0301c584046070004c1d4108103948070f0145200400c4a4101c400250020303400540401d150800d40b85495540c01000a0919035a070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 730069721 1250 730068471 730068473
    0x907080619030c090f050408041502031314040c0516060e030d06180c03020f030103060923151302030715050f0a0c11040506090a020d090f050105091b03060c07 70
    0x1042160300c00060856802030240d6681c1000e003124003140c400d80c000b0350700d4903040c0701511a490240710b1080e500b001a4270f10b460b14040d41420341407030781c1d50008114003041c00190f40e203a121414020040c6120210720000e400e01600f0003007181c885050342030074000200300200d0000000040b9101071a04003600049614001c0001400d62198503030403c00c1519003103000c81c01407848419903681110400c82002100c4800000350304034843031408202da851505000420005455403c100b059a124008041c0d9440c413111503030141c240070340c0704845150003c10490302104440410580d01c41100d03103d0b4807006034242c002c00d44a40413030203003151001c0c0e901780084016004100319618060b4825109a81c1c0b104160000d103804026001140c2c00c6a51101c0c164040c9080e000f200d000319001001100151500c80c804d10080d400b40140c009425143c3c0802c0e00402c480e031b003002003070741e000300000704081ca440320b46581004150030310308100000b010110001038900041495015130740401e615030310041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 730070971 1250 730069721 730069729
    0x204020702060c070f0e0906011a0d0e010e0115030206390c0f040c090e06010c0213060906050d05060c0f1603091a0414040221180d0503010509070806 66
    0x3030500080c0d00700400280ca089007000018440d001c07203000000e54a221901d858038056890025560800203500050040c03250b038004002d0340903181c1d20900e10901c1c2c088100303005426500a03103c64074642e5555042401c446a00307000300510388450050403101a411540068107034010841203004038035090b928018072840644101e481c000b03000030b60980e25a1000c0d070140d80c0c2c9030b0100310706005001d000410809070529005104520342907403549600d880c2041c90044120300300604050400200340c1c206000350b160700224200d248046000030410504106035281074684d6940301390b000740040300c1d600b0b01065000c140c8581000c004a4540c1c6e41c2c0d2506d04e054052801603903184d194000c4d4614403a002c15821030380c2002220300516619044004202c00d00042d401184243c8401d9001e120300d4403a02d1509500602c2c03590460159121b16651030a0110030400d0111140100480c0440360305054030410041480312078441d2400ba4607540c109070101d181024041c0c03509003403107000700c04205159a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 730072221 1250 730070971 730070977
    0x6030102070b0c030402180621070f0603151202060f07020d020a080309010e0613030f1403030702030a031521210e0f0a03170f091c020906010921020402 67
    0x240041c6140d0a03801e09034403c4900d6070003900c0492140350742240c00500d10704510301d400e201e0314005103200c0200b090020407058030a00f07004008242e02032410045550304c241020b402c080d0580742d400003081d03140340d0340d100144141340c0c10003041002e4030790b10200160b0741c880480d01740c852116549515000c0a00c0400e070301e8000c81000940c000003211010032100000009808400300991b9007403640a855402d01c643c41c07017800404000401030f603000b440410901d07541710b0000c6101d140d1000b40250700013501402c50300250f50617401a00001074521105606000302c11621141c0d0301c540010500c1c0240303201012091801c1070240031200ba20b020107108103021115018078403009100c1c3c21854070710000b2b207003200d5400244d21035a4007190035949400c01020817426030ba40001e1070759184140106d501c0264100442807041c4000401c40d8030b8030360b02e40d8a8121104241101d560504501e03510400c026001c004081a040000d40c180400c070500080138680c410702c0902407118400d030034500100d0040d00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 730073471 1250 730072221 730072223
    0xc07080c010f0c0f021506030d1d040c11070e4302161d010311061608071709010c02061305090f101706150a030506100303091401170603010207 63
    0x1c0c58018504070321508030318001c4140c2002e500f40e42002c21005150710501b0320a0700c400303405500c1940d42d46001c038080c1c0c00c5480764028a4510f07412140128000a041c2c501c0e5400c80b00009020000c5848200010018030001d00405440510f140c54845071100014411000d804510f449408104c9010002c025191a88650201554648a581d13120107940c90344202ca010199200c4484001010152014a14007007248600242505e9203907880d0180c082c0703034040f081580807404004080d41000010320507140c180c07081c0d42842d120703156802c0c84803e014143d0034100c203403e0304210040080c3c1c0d010040030082d03681151003546591040406003207100e11908040d40002402d4107100c09550010100e611a800807946aa0f0b4591103038a6140d0030399017005441403d51144021414001402c07243c10308445020304a00811035403074030f410340781100c1950351802e04e084403481401859031000d900c0e0003a12505072024644001a400200003860210080d041e120020010841036902034045403155 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 730074721 1250 730073471 730073501
    0x80102030915071404290a08090105060405130201080703021c15170a0b090309060315040f0606090603091a0709060305071d0f010207031b03020301060506030c07080c01 74
    0x1d24002850035030700c03580182d8109200d1080c40008800a01c90790511044021040c0114106490603004071000c44121904040d045d0444001010411203240544104811a66882c2442c1800c800042c212100a00030500441c10b16040002d1040240c4488185a5081c0b8026041e566220780441c002d001ea60525a010340c820664100900d001e508181c002e6241e242000500c613507a440c2e20844405c82008004058001130400004265210030f540ea01003281e006903440c14a801c80015030342d6000b1580c018110004101c1c03800581040c3c071510340401d4041e1020440542800d40290a645c81480b0f0501003545804100c001c12201e660340d01401c001200074070200342807002020341516131500448000078a0031000524052150700144031741040344c0d006400300240c91080c042c102051100e014150700c6492400400101d00700c03441c059003100b0165007208141184105800d41d9615403140c1d10400d403d00900000300e00d10350464410551145540e5990900582d0060141c82111120503031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 730075971 1250 730074721 730074727
    0xb030718080c030f060f0c0c0a0f1514010b031b090307060906080a05010509190e1b030106050f0f101808100f09120302031b03010b120603030f22080102 67
    0x110000200781000b540d0803800e80b8041c011030780940d542d0300022140007200ca500003000c1841030045c00c000b00180d0b80c5901c29514000c40a0312000e9200e16811800c4a510345401052041070071705200d42160200da50792002260751400e041010380b0300018041c1c5501600100c01b00645681d000c0c01c84bc00000081c003541c6100d961014003410003e00c1d031080d2000700e00d0100010344d02c40024482c841c1078481c01090031090f921000c41d40b50052002c440070180351540c500380034904c0441001501000d001030701603a00e007008000706050039208180d000303600034039149140044075a11542c3c40c121154065960740c000002d0f0790001c0310f002078001215000d90480c5070010610034408940041c15040d900c509000c01d0b4001954401112580c00e0f01405030200340320580d40540c4641c00454001203590f2034070182c03c11b5918103c00c0303a4000e074068160fa03040061241003907084030034041e902c14011400b03142485406005003481d031042c61961484800030000d081410300c1042d02c62000340000d00000c43d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 730077221 1250 730075971 730075979
    0x207050f1314060405450f0a050c030312010b0f0909011d01240c03050c012d0204031707020105041a0307020f0f1011070614070f03090c0b030718 64
    0x11800507950240034504140004018901e1886c3c07282c0202d00010748016000312182c0e45a50400c4580b9803004050000f080601004108001c1103c1c440e01d19405403400e440c8510746607103025400740c40d0034020340003800850324100030440c20604494100300003941e112210040d20a1030f00c10010324991080c003030000400c82c0a041031118500d401b410305070f8405c4d80d8943c3d510803c3d0100b401d550b004841c98059181c54464400c42031034455912034180241401f008828243c00c1d10202043e00c0c0800b81030120341c10480d07006c1040e0032117500012008502d443d08507241d00e40c41201181aa52014100040001c01c69100e6000c44005045850260142d841c441c440d9003140c2e8015603150b401445036609200c88100c0104d080050a01410001c2200c50340c206004400b03024501c245000701402072083d040420114050f220341d0707104c04e82c00d0354040d02e48004d02421982079076490204240c40e04014800046541c40084281c4454078649500c0780e0b540c040c2221301e40341c5220080c3c040125070038005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 730078471 1250 730077221 730077251
    0x9080a0e2e1d0a0e2a09010f0c0b011203091a09011d0301020a030204090b03010b030c041a03100905150c090d0213061401020c01020f150408043f030207050f13 70
    0x98055409001c407114071400c0c2002e034201c1170620749220555500c1c1044568150b40c060030b8900d41901190a0046c80034040f0780352a1800c4d2801da02105400845c405076408040d8001000405800034150030b5020000000c040b6245000e4100d84a051051107200d884021980030804032010704000c0c002e43d5602d04481009003e90820700c50f840b42c0c2c17070074801020214a010300410042102c064028000c28005004010241001c203050002c9203816106106a5441c24401240c06031181d000218544002e0f05d0414506a000340a000312000c0d1030381071000304c01d00503003201c242040443c0c0b9108450007030b000050004c1c101c0703004d500303466240c400001840a104580102105001d800f40e0f0030004280006a0b11110041d140c0c0d00700e1f030843c07040711200680543c1c81c103410a00136913102d404e06444540f21014000510304010040c6514154002ea002d0021031075582e4100c0b50003280590311031680d02070b40d2000306004d000d2040b11030000e2007941c1d452748100b00d002ca00d822001032019512102d004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 730079721 1250 730078471 730078499
    0xf0129030a1b020109030807030b04090506090a0308130c0312050c190b060402071703041703072d080403080603011506032708030f070309080a0e2e1d0a 67
    0x16402d2000c00c20105806140107121340c40040f505511001c8150351a00d13021001044000a8281d1060740c8820280120310704001c100e1080c91083c00604075070945d4180500031081c001c1006150104030940080020808604a001c40b90f016083c006055070740700050b02c3e00c0c05940ca0500540c869990808803400300358441c803070910301038401c3c03400d151501804c0c0400d074800e80c24090003101e079468400f2514804000110745c024040c0000103903049182020f0f9050380d1040e1200d50001e031000d0105d1580d6040c1000e40c002c100843c0280c07540201c2c82c4140982600001440541845841c00000b40c40f40c83c02c1d080700100d103100e40082401d40780c8800001e070080c078807130114080c600226140c07485e80c084038110704074040b500941c48e10306590318204900d0b11188000c0c0340c80201034070703024071400144144015220031b91036600d52541407000340052204d03520500d0b10102d00030f55420540036440706401d03000030b0401c40a03d0510551f44040c1200306148058944840d0003c041c0100000c071503445000c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 730080971 1250 730079721 730079741
    0x60406030b0315070c1401050601020a0807170703050c010b01031a060306040e1c02010e060402030712080f04030b070305130803060f03070503070e06091b0a08040f1202061902030f0129030a 83
    0x2280c40b01ba108000881c01c81c2c604840e0b0340e002da4842200407020403840c1d009404041d100c2e03e0001444400740c1d0342c601e156044900118042007000c140f15000d50b6080c082c1031b41c0c0450a00c1d0070010703103950b15001d039030040802ca00c1c00d0103908000041020341e2a55001000410440402c442d24240700f443c1c3e03644040030085100005500c0c1107010601d082c004030b05240241c3e00180140380711420701d032910590030444030045882d02000c203e8540420403160143c40118001c0280382c0c00da282808028040e1500100f0548107008032003110b0001924420036a0b0300001d040e903070741c2030100400010034680641034010030361510400400003420010414000d00c250800d95829816854140600c2596400000c40d907400f6002884600040d0f0311403104954003034018440c0514101c0385884007071403100c504c154800145c002d8003c00c2041718001220364618400000118a1403a1404014500071410b025882d040012880f0601a4028048001196000d90070856960b82050f4008200030103640751 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 730082221 1250 730080971 730080983
    0x50a0902092d01080705222d02091813081c1821140a091406120a09050a2108060a0e06090405011e0603020a05090105060406030b0315070c 61
    0x40c0b025415585480050499942e600101030681c1800c0c10014650321b0000341c40346881e0300b002100d25500140c000c03400d1012000302072003206003040d682c01c2944180183c151244500405c040d194580300c60f2000301329400f180d03011496940b00c0303410848103c0c104d000050030603000820240308030390151814607c004000b010401007070310510307011895030395000c4000c2c0c000309504500d03441c0d230b901e50103000079000c0c0380d0726084441d84081c0c0303280d1070145c00c51b414110000e41004014041031030205860403601004032006401d01c0d6002c0c40000c45900010f000f000002d40f2002c07036170700304407040008041c410350100d6004c00b218981c10580c0308031020b10342440700062000c07020881d18101414041e003982e410080130a213541d030380c0741072084456004d0000c4845650b9170324a41950300e0b1100a02c0c03040d09115401003001855070040180c10304560300424130407001080100881d81d0b0710701c203d5007250b49074100841c80c43e0b00b900002e030030310a09460707199200440318104506568801d901c601c8441c4100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 730083471 1250 730082221 730082281
    0x21c0504170a030c0b1003021201021207021609111b03192a0213051005040b060a020a0b07090308070804050414240d05010f1d0a02060706050a090209 66
    0x21500707942d110060005804103120071808000300b104609500e6001d8503407100705d001c0c00d07035a42c08200c1c0603418203039078034451350701052a10039000720900903600620a0b100800c40d108100d003040c200e10348944034900005548160b01c80d40c00c8401803d41f03251048005000e404103095541c078075145e5105d086188002602400100d40d0f5500a154041021000800a0000d5004540341c02c1c0c10035003440d402e0f44d0001e9555045032812046005051080b068007000209a620340030500c01555191030215203d1801401056603544d0300145080d143c641010740308070b5944540009130b9800b0312a030405000c182c00010002d0a000f0078038028400c03500155801c00c003a01e4060810308802900341c8004201c1d030b20180d4003071120b034054110143d4042d801007001301115601d0341c038642190340703055a4040c21a02c2e5104a010030140503071900358410450068900c510a50340003d40070b1160440061241d5945c5010034174030061a8480008554003a0405ca464141f51103500d95284820349002501404c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 730084721 1250 730083471 730083509
    0x204060f12021321050607030608150402090a0c12020d0207020a090b150c0c0d050105060f0316050405041103030d090b150a0b18100f020607090e041101021c0504 71
    0x2d108481c014039031005142886418500380b51a10312a604242440c0c840f5940304c0070200d042840b00a0141034561000500039282094507030800c0f8025400051070f003020401c100150f00c039451640d600004200001640c00d01001007643d04140f210914021140701145507130601c501603000301b80c524021504d080d201a645c80c0c21009032846401441d03000220303141c00020380340403c8098075114044009030b503110001c03030010680100300307004156690381d10381c000e211041c2400c040401803044241c0c060044c1040301c020101c0c6c01011840345070b000d6540c5100050500c094103003020f9080c500141500d54131400d1240700702c0500020f580c1074404401c45008184c07901c22502e002c14200e507002e46440406c0e46002071b0700c0c0c0c0304d80101c5100554140803842c0d131200ca40c0c0d031a400200450090b02e400b8101b40300f100009103040402032240c0d0a10500f0328043c00814220a0240c0e40310364081e01d60141e42480c1c00040741000c104451003030940301c4d664000001150003502034025a0b645414a42001c025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 730085971 1250 730084721 730084757
    0x1303090504022104060b0d050105011a03040308130507170313150e04051b0c1f060e040f021306060906030e010c0c030809030c1c02010f200703020c040204060f 70
    0x721003840701c14a066090b00050302143d200a142e200b4003030312002510012280c003050820200000444460b503480c4018010440002191015004101c0c0c00d2030641c80c007a60080c081081c00780000002c50401c0301e5550401108010307001c05001003011420400e2503e503010780da81e80107240c0c0303070303040b2140020042040200300000441c0700c469941c0e0702c41ca0b2113001091000030310000c0c01c5619054507824a00102c142848010b09143c0b64810003024000f81040416440618820741030f1061424031030108400400340c5840c903002504030b40c4149005005200041550b120020050b82090900200140141d04480c100d8119040741e01c05002d100310f01d0b0b44180c2222002e21812010a01681d11100400d104914541d400310207178049920340160300c220341d0325051107584c0900564000c0e480b901e072a554207000380510f078103006a041c003400795102100034071b004400841c0b0718110030209141040c14402c01c0b0300c00441302c026100310341c0c42d9241c0500070a809a001a44000704031040840012010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 730087221 1250 730085971 730085977
    0xa0504081e03030c090604030c06080609100305060a0f0212010f0f05190b030c040b0403060603020f090603070e07020309271006020307020103090804082401080a021513030b130309050402 82
    0x54500090740c0f9551303d01400703081c160401000c00b0342004c0148004070010799181c803150081c144a84940d04145000010080310200c001d0001d600320402990400014800080c0d0f01d403c0410000f02190800707610b200b2070003d00541c01c00c0d05000140000002d80c101c6c403055040d0640b5044244440c00b183c481040c0880035012007c11700900314141310400100c01d40780301454003d500c0c028124038085c0c0d945402000c58109400c10390700a59518420411450000e1a0300c025030400e03a440d01d002d141003000251200018401c40000c0802c007000070307c0c0310384240112180ac0c41c0083c002002541c0d004c0e4540041c0c00c03440b8442a0801400d80031a80c0c1005c0700300e41300d0403500160300840c50089a540110080d00b820502103a000754107000c04910320a040c01042d801c0302503200070600c14000010803075404041a03000c1e22854000c844502c0158a5054464000301002901c90f50b0303801224400400d103101507440a400000c0e0981409249601260a216060b003e80d94070362100d6110400c02c02248 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 730088471 1250 730087221 730087273
    0x31509011d04060903020307020303130816060f1215030506041203150b0a090b0415020d05040503072702031e0f0105090601030c031103090a0303181e05010e030a050408 74
    0x159001c000500044080e009081c0c6244030344150380c244a010740c00701749181c02001140103170b1141c2d40c42c03d01080c0401c01c00d425010909401a01c1410f1420b54040c2040300301100850400c000d5007010946a42c0301e40007802c6406080300b0a255143d0350742045500d0b40f006450888166844c000500e580620a02415281004013014080ea4915080964034a548a10120350601402480c00103c12050030007a1006220040700c0843c01340380307030600030308006030944203a0500c2000e10040c0619140044c00509545280c0069010004255011070706a800d0f0808004060700000c00c100e540c1c0f00132100302001c01c0d4095100400c58488800726401510240282ca410880e00b1000400c150b100c2d4001d1540c1c1d03101c90900280b0883c10144000f02c961086070070b05980d510100d40901050340c548501003100c40da0490004c056100c5685041101e48100d141400520b10900c00d030007407003002c0d40000e00041c00541180c0c0d0310315940d07101070849e4004e48500300890042d100941103880411103204400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 730089721 1250 730088471 730088519
    0x1b0509151801110a06051510091404020d020708191d3d0e01090e060d08091c06200a140d0e0312040c0b0c0307060b0d0803150901 57
    0x1940401c0044a05020345042030310940301d14040a0040b4201c3d2140c00d02500800400142c1d009031082403040c681000400401004140b04082207402c0e910b8100100d40781d402c0301c001d40e0b074074000400000607008160014045105c0050010650121804a02200c8905444010015081e0300c003219001c0d540c150410f40000c1090030a40b050000302484400c03940c0d400400107a40540b1107109601d074159510707008041000310328040c42c2e942e088190b02000f4a5010009481890140e01088800248840003009a44081043c09280d60348040a101810303c02c00425111441c40c1826805050f51102000300c20f040d29040042011030a401c40340c1070a00390702e8402003807211014035115030b407000d64035a404581c0c80182c2c03900384505000400d100303800e401c100c1429061609200c0d5560b010341d032010407544020403400381e81c02e40200540304031b203411000000e5001028404034001ea02c0a0174018120030703001081140ca014416408040c040d02500c08107010b80c1c950075003440003a004110301c401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 730090971 1250 730089721 730089757
    0x6050a0b0304060b040207152a0207120305210411010801030f1b05040e011b170714040e0106050c0f06010b0d09080417030c01110f0712031b050915 65
    0x103d0381c41d80004401c1c0303001400062406013251266031110074085c0900c68100d0b02c03066507039081d0400c001e014107400e2903401440012807902d03101941c0e505c0e461040300740071512a441c03101450700640a64582902c410709014511500344284840100210307001c84002c5a000c0398071030300354480c03c40b1a05036a031141c00750a0221603902c400c406c0c600d080e9a000300501104002041585450103200d4204242400200d05040034a4240d80300f80350007020b50040001c02512403001d900c1c3d610141d40c112001e81010060015160100c0c078646c401c07504607100c44102c1400000b000f507031200c000d165402c032480079500d08032031250b0704c292109004e10440d24103441c2030010b80b2106089a0010714260b1040709038a24250380d94002c50321003140002e180045400101b1030603000c60b0280a9910076102c543c0d00c0c0c0e4035004040c00601500d005034103020b00040c1070315000c80d000d14080d904c50100074500b810340324452808044003c090340e11075a0147d0062020400d201540d8800400780c44d500010844d400d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 730092221 1250 730090971 730090973
    0x302070c0509040507051509090a0506060a05030408070b1312020c0618060415090807060503060108040b0402120a1b120521040b07120807020a050a02120f01110a0306050a0b0304 78
    0x2c19840301900030744680c000e070b40d0001241d41c3da11040584074551042c0c00d5440f0704403441042800c030700003045160202d0400c42007204540c0d036003040300c0014890381011038498449040c0000d06014190008100c1d1400c0303000d001040e0717500380ca052560b0344070302d40d2020017100d090412a218450030701e066410003424085003403a0380e5038007026040d40c000540018180341e074803a0944d050900210115002c40d24a030011b01032160144002c10144c011401c0142c91410094002031201c94020005883c800c052408102151b45800f090749508074401e0850f4441145800d100b02001c01d003800e040c01c0750b4054180085e0300d40c046802901842e4020010740b041e48000c010000c24004820f1a10400b107408010100750b003882ea80142c481c90303000d9503516195a810541c09040035034060036070025580722442180002d240003c0810040340d0603180441542a00842c0d14070f040c0c1c2000c10b440040d420315400e0070030044180e0203030040392080d503000d00c00c0c0c503604c806101596249014881030b41c00200b0000d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 730093471 1250 730092221 730092229
    0x100c08070830010b0a050f120108070f0e01050616020d060e06060d02130231050f2e030612030809010c080402030307110f060c06060a060810030f110a0f030b070302070c05 75
    0x80c17420414105245010400c0042c142c469000d040182c030884015401407100140800c40340002e850031560800c042030402c03541c2000084148191403044d14006417010443c61502607010392958043c1c0301404540c40c43c0b4001004e0140c2060b45042889110001103103454001c041e00e51407a0060450000442c0c0005c600000e5070203004003485141981014060603100ca41a60400e001514110204907040808100c130765080007001610400800ea0040424100402103804000104240340c448001452083d00501174035404419150b4000081606240d007200031280b1805400000700324102c9012001d40360742c00c2c152806501035100f80000000105601901455190000d004100141c9280c0000c0e00c550b1003402014040d400100602010341004210314003d410f441c10454003901d80486007000c0001d20b8400500052016145038007030003e8a03c03100a160005021000070646400e070000342800e503840201c1d14460704c1c10010326560311034400d94481a0388654050280b6103040c00308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 730094721 1250 730093471 730093477
    0x1609060e030f07171204240c05030a27080307030f0207030b0a06030b090a0201230405090a0e0f0309210f06040b10050a050f100c08070830010b 63
    0x500e4040c400c141d000c004041007000940024400d0504c081052406440f03200d0900f240005a030140000500092110500030381e2180c44004041d08400030009650030200c800c0d85049001400902000554458080d480f03455850102d40c0b040d5030303203260712031410015004044c6100b0355078503800a12441000030310410354681c040f1554412a03040c9516511580c8087e43c6c00e459040760142d03200b0f410004c10014006280e401092080905044515500040e109142c0c44200410792140f50041c10007625015080d50064440070303001c10010310344040038000030030000505448900c60841142d500318000070485440a102030002c04296240d4074444483c100120f0000070b29000300205022116420414184a203004e00b030f0b105c0113424060114580c0820a8000314080c070340c800c005000c1a01c444c80100b204a0007074a15840480460030200d03440e102000d0300030710390403000440781c0a0003007241c09070641640c1c0c03608000302003a001402c0107565020140601082c2003003c01004141150005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 730095971 1250 730094721 730094747
    0x240507020603040f15050c070c080a05070513020d020d0e061b1204060209120c040b011107180209030a0c0501030609180f06021c05041a071707140304050a0308160906 73
    0x417562404001502c1e06080e0b034005c407050548824081426400d00c0340044035000140445409010640c0c242e44030a5110249402890300680d207490030b80450020035412204400c070003400441d128030701e0200000140c142005090f0591003941d01080c3c0c2d01ca1055840b810b03001020040301d00d004859a045d800010700180240c82c06a420701501400d80c40e8410440c2c81d0a50324006040e00390144402c102c2104c00c80c1006034100004e41100f011140340015490046d900c901c0000c04d21020508422400782c800d03c906950940644070b681c07410418081041420340340243c81c2030181c1502c45c4280360840e40381c0c2c2481e201500c0e280c01d00c070f008030f42c01e1440200c00c1c0d0b005013809403800c01c0120601c4d0000c02d494421240303a03aa100200001e1013a00345943c4e4101304082c54000d964140903200524200c0c4050454030301909000115080350b008000c00100304003100040e948a107014180140c49039821003080e0302107902600003031042c08a0120701520121a074640b0100142030100441d007100c14401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 730097221 1250 730095971 730095983
    0x100908130816090c021c050712030c12050907121505160504150311030c0717070f1209030c0f0501020d0c05072303060103051e0708060705070219240507020603040f 72
    0x286a499005406481d4070712000703803aa01d88e50104c0c1d14014440d1114221000209403800e9141d141040d40020140f1b200d2900324400b00303550700c652541c28140b4207641d002c0307804140081b43c43c0040100c01c0c44211a50740302d010040002d5602e04041d203591150301c5022800143d02084148400561240c10628458252800041000001c2c10039252030f07000b5100039418010214440040125560b030420b000c0c505600c0c1075081c48596564080d25040d921380007091081d0043c40f689100744075181110045030410507490317800347d0700d482d0603500408600441d8018000c502d070380429240a000c0c0301d00c0d0203078000010440180781024940d40c04c0c00800c00740200741c1124180760080c0c1d6003044001d010718003481c090501d11401080c18400d4a4440140640c42e4119a40c100928000410030552058117070401c26038078070841c400684d0740b0300852401c4494a000d40404204084005201b9004001240c451601841c40740400d0301d00d8081c00e60002e51201d001c00003c2c00080c4603a14640c500e612600e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 730098471 1250 730097221 730097233
    0x1110c030607390809032407080105030309090703051518010f170723040c020d02101512021503070804020405010f030201050912100908130816090c02 66
    0x20000904212041d1041c1e000190b02000c2829107000d807060002d001860848000c040300c200240341003002c1031441c009860380c0c4000c00ca05290b41c4003481401c4e1141c1c0e40e030990449640c042c414400340e0380ba0aa40f004001400341c0000718850030000102c401c11640100641c03c240c1d00c004084000c1d0200408071158200b2407044071840c0d0b02c5003441c0b6100f142650305036914039810500e0050084c7d07410b40c008410b00e011060a41c0d901c000104403402540e1140c0032144504503070711f01020744010044441038000b07244c140400b004540c0402e0640210b5942d6098030f1780c6040c69209601512042c64141582c1e0f81c580008000740031882849840d541d201403d40e610301480886012415081103d541c00490030100410046203010712802c0e02401d4500c9280d07100a04540000b8000c0c01903405190040c0345400384c404c00b80030104400d120310071010700c06100c0918185420350090f00011410b0061501c084004101600c0120326480319014160041c0d0801d0719080c00741010300103e0b050b070743c02c0d40100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 730099721 1250 730098471 730098493
    0x6040605041103030d0207060c020a08042114010213060503090309010c050a080f0309010e15010302040216050708100f0b0d1b0e0106080613150611030c010c031b080606090111 77
    0x14400b400d8420480a00141c41c2c0a1f0703400e100003900c540f41c084d1b03021504201030040029007044240c1d4240c481c5051030302450201d20000101440d0f1020f0701511005213811400b100100c150010031b06903610f0880115440d0741c5042c1076030075000549045039980c105000542603548110b003000c6280e40070360111000c10405440e541c1c0c4d00e61000c640c80259400002c104a0840c8090068100407060200101405902c0d454400381c00f05040c0802441150002003941840040c05441d0150980090980f044165529101541c82c810742680003480c50400c6000e0030083e843d0b00c034144200e80042d00240d880403040d6030324550828111104a0640c0882c000800c0401120204e240a0849604c07007a410341040d208005600031811800e04046007401400a1108003c900d1b803003c884e080d0810044041c124241c0600f1409001d0803900b031503107081440407030940d1680010f003120200640700c1401c410000300c11070b1184401c8074501c4d009241080140c02652007030095010300c0e0351410a883d503203c00303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 730100971 1250 730099721 730099723
    0x1b050625120801061107080607030c0e0a0f050f04020f0901080c070503030411011215180f0203090d1e0203030112031b03020d030f02040e0c1b060705040f05010c020306040605041103 80
    0x10351400d074000902e000740180000394001d101c00000070342e1a4010180145032003c40381e03680b00000c004004040e1030b4114281080d020b07540c440b030006402407000d51036940314440c0d0024412540300b06481407038a0400c240325803e052080f01c4001c81945160f80c640800c00380151004400a44002c01000303040216030041901400030754051403040d0700000640d000707200018510710301120040074039450149202c60f04840d4882c9034080b510f505c0c110f4400075884000182c02000b58540c0024800d00000400081d0000843d00405030a80d070384802440c006842c124050089049402001583c000c20051080010300c072006c0c10214403070b10b864040c2002a52003400e4025071410b017200541d00540c4000300b61501401501da413030700740c0c03c001c6082ca0301c0c05207100d08068000c0c0c840d0348410030001d61840300d0280440f03048205090b640494041e801c003840c0042030b80d8420312605d40d041c05e08a001140e90740c802c13070709080c040da00103008040603100d58440000520015100303d03042c0500c42d0b200b100d5528 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 730102221 1250 730100971 730100993
    0x702060702190b0f03010e0c0322021c06020306030106080715120906021803060a05070c08030a0f0c08040314120a022a1b030106051804060209040f091b050625 70
    0x4d89946030383d00d9501d0010190fa041e03001906c1c038125010240104990304e0300740c0390703541145600c1d8068000c41c00c0003070002c1441964441c0c119000103503a1a403903024000a9001140194000d0b40200701e207940c1d405003a48c90303040c18015045071032102180c0d84030151040e40b01c0d48003403500610000b003205a03a03884100700e0b4020221600b0501610220b2281d9180a00c10191f000201c0f070410b200d0791614160042050f00e84050080c148840800804d010f000310384c2c850403810180c00c0d41049010301042c0054448401114102d00246083d14030310240d40703000e07081d5021509a0710740130110351911007458019410200c12140d0103130203200d10861320f1080b003505a80703142c800409011103102ca0045510301c00c1000c80800c0c000e038144501040300307454001d100044609400d02e0b180403516a450450080c0c4204d1810340c1d03016061010a400c420341c40d0784034030442442429460b107001e0200155070040c6805201e981d507c05414040e01c03442da62185420203590390031503281e00104000d681e030942404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 730103471 1250 730102221 730102237
    0x3010e07140901290f071a100302090711030702060403060b100c050d0e010c0209191805031e0712021e061003110a0e010902040807061b1104060e0414120702060702190b 74
    0xc02d01c0d003c1c00d01d00c140c087c44070340c0000102c0d0200c4c80c204c2c10340e00800c2d030006024044104200141004a02c805003d2041c0e61460345d00411043c3d66564a05026000c2c05155a10610880d48041100c4001e0300421158800d140d000c4080c04c041c503840e50302a01e01c0403840d010241440482c40304040142d40700ca5903580300b85550000203801c0031b12404500c0031103018003400855408080b180901084000095903446522011415010712003c04202c6c00c0d4040e00900030200441503a16410b9183c002c9440040c254101c04c40c0748451429086c00d030303520310703040c2d40e00541070514080500c040380e011b80d20a050524040c081d400810f40e148000c1582400980c08640000d43c08541804202d070240140300c020251840c0070000d2500401501000920f80c0700004c0c100700c1c44070740c1011140c8540d0004801491500000c04c100d00c1d103810140b0b040045942c4403441c034017903400b0303400301c564994003681c0c00160040c0a0905220a5901b4010104982c00d8462400383d40c110b00004c40a08040c02030402e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 730104721 1250 730103471 730103483
    0xb1f03060602010c1106010b1b060903070201080f01210204060b0f030114010c030906030b03161403010c1d010c05010f0c200c0114031503010e07140901290f07 70
    0x1146802402421502c0c0840c84030304000c020485040c0d617107000100355041d00c0390403880c981d4581c682a00c5103d1094460355043c41e6001304070411041c00300200281603001e000b1788401d4850703036800c010181c0b1750100340152145482464101c5c5040800a034225038200e1015000088890b1980d078045070302e404c1502141e04d14000000180000f50701807200004050081c20480c3c0c44800030baa014100d00f80f940104801c26540d5802081241d40c06c03c440b20010000c48d00d200d40d100c3d1a241580500207441c00d05030f00940c00c2404030780e011403007600340300d51914102250100004440004440c80200324000751071075922040c052980d020f0900c11902d420096440e24010401104401000142c044103c80d01390381201400c0c041c0c598100004010040600441a941e60b0390794001081c480c1d54000019099031a12810b603000703020010f4504162490710b407440e1001d0752000c0c100705607680c0c240104103c0c0342c1c102c864210007600e000590042107031003003021402d1a01d81491042590494503007a545 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 730105971 1250 730104721 730104731
    0x51902010908030a17070c201c05070b1b0d09030b010e0702100b01050c0a06150509011202040207170d020403210f050a0c06050c07020f030604150b1f03 67
    0x119078100300304030020002c0a000e1418030712025800b030014641620000810a031000000c3c0030240f06142d51141d4a40c4005d0a465107414035081c1100070300b1908083d40514110022961080b444101042c28030f503200780207040f8035040090040d819000410071080b082480141c00403240020b225010390078080790b840d000000c0c51414034400902c0181d000200d1404402d040c4018140e02007548080c1100440002c206080940c0042b901440391194118590203182c4001040140c9504040200c410002c00003025684030820414401800c0c4038503100c6a240759118001424542c015100550040700c0102e2481061000608154040707040c402d601e41c0d0003e824820444400103510480b000e13201c4458170300c00c2d00107010340071400c4069800184040407078410101480352160014540c1d00c0b000600280c1803907245030076075422288049100d04462802884241030004405103c0c5420804081c034101c0858113910090041c840d0b4142c20051400c000e490f0b04134605140900403405940001e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 730107221 1250 730105971 730105973
    0xf040305071811120129030f0405010f0c082a0309030306040f1a01230a0c110306040804090e0309041d0c06034003090e060a0b0307050c0a0519 63
    0x104449085402c0c1250302c00500ca50280c045940c070401d415510841c90a58850205080502c492459180f0400d07280000004203c08c1200040059000c0c0d48030754001d0042225035402e01d000d940320000c805001403070810010300e54508030008c41c0c0940382202481340303d0180b06c1320484a03d44c0102d404102d29440041841164103140c8100089281c2c005010090004140c0c554140c01c00c441d80814100603121048510f071410410860104868460303402d642c4406901c8042d250344003148050b5107103054890b4402141c00c020038000d00c540d51283e2424505400c200c05c40b40141000141032149200622045e10b054039a0706c9050303c44290842401201d98240d0394039450604900031941c001c01c8148240842d90101c0038200044d00c506c10f0601c00e441d84076103881401c5c3e814000c610780502c00c00c0210a018907400141480981c0c0242a1003226540c0b0101404100c0d50944620704240c1070070400070b8080b5110b07c0180a100303448905880d81036006440c0c1c285065100d4103030108541c3c014034640c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 730108471 1250 730107221 730107269
    0xd030507020c09041401141f05090105040b131d060c040501140c100c030506100e060306010f1404030b04120813020906030309220f050f06010c1b03060b040609140604020f04030507 79
    0x6a030040d400c40469008c1c90500c4003060000d10103115403070243d6110086204250303200240120b410040403810066505c01c00c404015071242140c2103e07040c0609404104640020400c4030251034040e142c1108031020703a007409545a00c00c6101c4105406038a190075003441d1540541d00d034241080d5400304003030519004010544444121a07000d00415000e46111074403840143c80d8042c0b001d00740047e20241078042a61046525038480c500301c4070009000c420084840401c50050340038500c010940f5010074810b845401c425514402d016402d000e26038011700d0011009a0f2158002d001d80e42024001340105458100d5062000c1e5101080c0584058904c583c0c0710b000400b010940c0c1c02d0105041c4005960a0064060b100c40d041000c3c1030f1140c2c06100c08050700d68000300f5002000032074155242000c1000300040000144070f1801d1200010340c8860a01602e60300c07210a031800400c589503907080000941c007080145864103002d10000000c2007003800242c000b010500000b80419462801034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 730109721 1250 730108471 730108501
    0x5010e0a0c090b010903080d020724051b090405100b0a0306140604060e060306120607080f0f0103201201020a0512010504050c031501030f18050d030507020c0904140114 74
    0x20401503143c54444101c036a80310a240f0304a0360000c2c6010703690f2030b442c1e801002034415000c0103840c03c080c150a44005d056030780121401c013a0710300b10030440c0e46c998441c4a88840400900700d000c401c0240106140c0e4070707050b4003098010400303581503084140d4554001039107402085100011903903805003002100d181103101c181d0404121605858582020400f0302980910f00500b8040c002c04000100e03c0d848000c0c1c01420203505800b240c945240080307004100820440b030601c0d000e00749034041000490203c031410b0503264086120800c212200204910014a02046030342c814403030040c1040c4d1000c00e00c0107040301c089595807070b40c0c0c0d054180613039680320b0010780c44940514505020400201c6892041d03a4001031030340c03c4020340c4030110004030081c19200221186d020326100040001d10303070342c0c0c1040d480b00380b0420940e0080070310200182d0860314101d5043c009600050079400c0640b47c21380c28150700c54400d50740c0b98407815540f140d00313003114210341d0001c080346564824003001003404056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 730110971 1250 730109721 730109729
    0x60806010201050f0702030f071a010b04080d020111090d2d060513050c01110c0415090b040b03191a073f27112b020d02030a05010e0a0c 60
    0x4d80103050810017002035076403140c6448404d10300b02c0445c00004010600c100c0030302100250159120701e5850321846241507100e4414544284640380c4100c1034680107000d003092070f001c0700220300e040c40701c00002d00c0302d240d01d0240122035060004225a140550404008200c0650f02d0030907182000c091405004861014001803400c48049000e01c0000c1d20001ea0905d484100f8a03004092560b0307065441c0c5002c41034002d6960080c01c0200031504103041580440c110340d00b540c4107104101c084400e1200700c440790705a0b5901a0010043e08551804011140f0116842907000540d45920741c2c5910010741707419a03603500020510f0340360450020321107159402c03000a900340da803c4504040e107080000e03140c14100803003082d202e00c200491011a2006c0c183c02104d000035004c601711803850070800b81c50030307480d00e14031410400715201404540990400c030b101b0a0100f091200039580e40812030071000268049034940b2551039118005082802925900d110720801001421040d140410f611861900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 730112221 1250 730110971 730110991
    0x607180305060a11041503020a2703110607060e0a030e03070b1e0706020a110601140607061113060309020f12030d0e03041a120a0608071401031506080601020105 71
    0x4414008500045541e0360820f00001c40000c14183c815030a62044c0540e5002c50400349000600c540700c544c0680003048072418507515500301181550001d0f0801c2c00c1020b0040101d12040d0f8148001894801321804400f40184402c0c146142659a40705441151003025640d400078018034007016000300d440790401c10b0841c090f00c1114105a10b50200d4002d03540901842c03440e180d281e000b00c20901e411502c4060b0405002c0d0344c0ea0006000191072141c80d00c18494075403152030300015104002a4000c00240720040c9031a00c0c00308140c640c40041c0628030501c2000810420004040b10080500c0d98008c16403510041011784044c0104070002072719601d81401380404208010101f180170080b22040c0e61101e800098000c0003100040c55070043c0c1d004400d454229810441500c03030144003920410150071000c0b9025a00e40d111042614024800e01405070700c400c0080c0408603071001c00b10704404061400062405030b012401904103403960100340450005402d02106580c207018240d44051202 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 730113471 1250 730112221 730112267
    0x10f020717070c0f080d1808070b070c050a12140105040309090e0c0a09020c0f0309030307030c03110114010302011106070206070e04021201080601080f010504030503010506071b03050607 82
    0x284422140100c0c000d81c00110080c0000d03824200560f889540c00941506034502c1e00041d16258642c0d9100c1c3c402c041c010100b14213003110a4081413600d0394030156103201014010030740c500f1010119981000c1d504649941c43d5043c081455187d00742e1442c01018100d600003c000d00504145031100351415049200d64182420000030076041240c4034100c035484000002c2c0317014080300b95401c2407201d40026610031500d4a00040c5075030550040e02e201c0030500c0c15151010401c0c2c00241d0340b407146994842e05900f0a02406010901411594901a0003420700140d851880000117003140c0c0500c042d40040e00043c1c00500079542d024101141d0400c0500051030b6a0a00c00006940c5942c010f084034100601d00d503910030b0f152183d0701529070800b0f00105411703195071103000032a1192024000d1951a11681480110b00e00317050240c0d5000c0e40e01525800e145900780001d00c50345501120058811507401101341e90550144484000118001e8014080508048500030728200550320010404180303c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 730114721 1250 730113471 730113473
    0x60712090807120209150d060b0a0608040f0b060d08040e150436020a30031b020409050f0c0f03010c02100903020c031212070318030f050f1803010f0207 67
    0x450f114401c1d468040326044142d41d038a0750429108107100d81e000f81c100442c00001c1c801c0011a03004101c840004441d031290854848900316007949040780e000c0c01034504200710001080d1180c01c515009000a44086d101c240503842d94070703c5030322581c0300b4848000d800040054417460181ca6485203081108c06011191018021140c00c069802011440c0280b81000220100755200c0807041d251380035016030091036551440d109002042c2040704032141540210700e070940000204804101e46c035803140402c0c00e0405520094400d4001000c9030400d0352600c8941c040741c1c0403c441308110748002e004207107590f411424406101c80c000da809000340e041c8440310312003c1e0045000500d240a9010015080c489803c0403071030f26410140d803a405000ba2803000c3d0550481d600109441c81002c282c1740042d0300c442d0340482c11a10000f5139000c0500c0700b84a81c00c002403156240e2080c1c2c0c0c00900d03001e800d200d00001c00c0b070300c183d02c40301c4840300d8a03842d00b080258504080c000c0c117400c591b1030f0208504101da1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 730115971 1250 730114721 730114739
    0x50a03020d0201050a23090304120c030c06050a051204080412080c010e07080a0b061302040305071e05090f07200a020316080304050d051002030f091501060f03020a0509060712090807 80
    0x24a100700c6d8000b070003420004510a10420940740241071104a10303d940585051110909402e0300069500804002c00484c40600850490360004116502d89262541c140c0d11041d040502074411510035800304800108200005d91615015001c2c10080e070b52003403d941c0450855480300e41c10740c05074102c4501001498404182c04a51070341103ca04035251340ea480000d80404980d00b5020001440424044103020b8005941c4d015108070102003d910101c020700325000b680c0c10722803d1b5018801e02c1c0041d0900350015903580e00042c0134140541c0041c081c5c0384101c1c0e0701d154603000310040c0e0b1142885106500d000c00c40c5500512950b5901f14819040c17441c111303241d100340d0140c41e004070005c030604000c0003010803203400650f0611138215264142210221a0220180e83ca100d4030312410030841800030522003a030381201c000d074a0310b03541440d541c14264040d4100070600c90a200091203000002d0301c3c0c603401000700c148540350007048c4003005003010b06001c40e590002c0b291640000e07424005640 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 730117221 1250 730115971 730116011
    0x70f0e0901270f0e0d11030a0323090f0c041407050a05040f030303050403080a020c060103241a011701080c1909090f05071202031b0d050a03020d0201050a 68
    0x9400311580b00d1440d40b2141c440401e10744a08007044510303240c500080701c50303207a200700c580354224820307140303801020a000c0f140e1400b90700115416030810014031232071030301981c0a4400c0f009020000c00012200301140010180d04440c0d100068000032804031200c00f01340021540028111000c000026a03000b484140940c018808001c0c024002000003196005901707480040c05809401c61a0a48034035005005d0b1a00341c40403400f16007100041a03907044140250380c01082200000d1030a0b07840c5403920550207002c4100000c0f241c1c10314640c07141041c0303240070301c18080b144401e190f50414410000185041c0c8140340480000100c00018828554041071020725190215a140c4040c3c44e138007802d0401d00d801d5400701c0b100a1078080d01d03070308107c0b843c80001c00c0c0c01c0c0200240e40e29155200358107000006c80d10002545900090810540e80d0102c040355542201c0251a100500009a840d02d2500454410a0380076900034000034950360780c2402800c0c2d10268109051100829490310304919107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 730118471 1250 730117221 730117229
    0x10c050c1b030307140c090c040308070f21030504050618061b041706060406060201110d050405010e0d02060a0b040b090621030315010801050402040e01270f05070f0e0901 75
    0x1050706240103107582c00b00705840905801c040031041c1c0c1c03081c0100150350752090405460165040d0400514428290740c01e440440e42c22a070101e161188542d0b4901c19140c0090044817882d0007401400310000700a10213510020b01d40d200011f00d42000c0c00c0031440c2520040041c00c480e9040080c0c60040302011442d540c002020854428910081120a00d1b0500481d044002c9002e4920b21840c1064000140240164030070380701044030b90b031600d904030300703075050b0f03000300c0c007000c45d00f00480a908a6503600644d4010700840000441440341204142800440a81d20f001a4443e0003405650a041e11500b0701c1882c00311405c00c100170100c400724401c0100100720500c03c2c102c0341d6540c05122450310f00d10102c1d4502030150799030707881c0865807811001400100540010324000002c282d0f0700303141c4215010344910300b00d500096881c0000391015400100c4c05200c41280001516800340700c1e0303014a084404103680040740600d0404c000405046910070f04008101401c0e1750281320391216140c1a0640b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 730119721 1250 730118471 730118503
    0x501081311090c071b050f0d0b13030216083f07030c0507062606030601141906030605040c020a0308070807020a140604030e010c080f03040320060405010c050c 70
    0x80e6480107088500b6004400d409031145c0700c1c210b002d0080764100e6014600b555070441d00f400d24226540c080c0200b519503c0c0000309840c10380070100c0e680e241e64615100c2428880d00c1160740800d410f4003220f040032100da00024665001090340036601d22003000d045540b218041080d031a13034603c1e072503c030610141105000381910000980c4400c1c035104091216229401900703c03104595540c1c1d0080210f0800e5076081000d10300d8401403042c4d0708402a03102e0041000500424481e42172950407249a200c0b022010f41c454060b44100e02c80301d07115041c540c000d0416032000910a031a0000307210903204d605130001d086411510b81100000d07081010303541c02507072518044900f540c48013000c2c0d00d010b00e1420003034150303003040c40c3c1403940700c00026981384214465036440a1508070a0015100003c2c2d1030760085c840e5205200942d10342c0395440145074814002d11340b0103036030040040800400c1c0c480c0c900d0180c180c2c0103007080005000003401b0300e629444070b500c1c1143c40e045d404c86c101c4d9110303e00800380c4250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 730120971 1250 730119721 730119739
    0x3203190f03050f030f09160f05152511040e0607080604020d0608100c08070504060f030b1c050c010e13020f0909180705030d1202030a110a03060501081311 68
    0x50520500550312195010b40f4060f0741ca0900c150140e4100b2000c4600841030710607035030025048040c0e801070804a407120b50500945600300b404104550518428101841c8014000c161120307010304c6005c0d6a41c03c8010104417500b00f00d081c06065100302d503012a00445c209907003480075410001e090f80e031244443c90306060580b80d1000080191283c41d020418260400c3c1c008900c1d0000829040da011004000030020481e60800c107603102c00049a040020400900c800c000840c000c0703030312020202240c500000d00800315000281101c50300000030300c80c2c84a0380c0d012010468104441c01e8048400d08020550341510400a0751880c603d0020b160b0040c1c021640850300143c4600b40c80c02d500004104544034540a005600c1841e0440111182071160744d00000c1d642c100895000381c200800d549010580c00a180044042d500c0a0a90b0610a9860750703611034404130304015018114541e07401144162402000402104010b8080e007150600303051a00c0000c0c814181224002034290b4943c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 730122221 1250 730120971 730120973
    0xe070e152409120106060504210b040305210106090519050f10090503030a0503190507142107050309010b0102070810110f19080106020a030206040b060a3203190f 71
    0x8010a1165000d201645c20300b2808596190800080e0058807451402101110180d800c4051240c5e800c0c0d0000d00207403003210108010a1203100140590209000051060215084100e00d2003000b40c0c0214001070319520b0a002510340ba101444441c903800c064502c4860901c1c0c006040740801c5030340c00f445a003008410951180c00b034846840200741c0242038a40720081c00401410980c0200d44110551001c45010021042c03d449642c0c050070aa035980010000d241441b5292540242044440d072201003556001d042010700019208101e9652a07507281d007801c40400e42540c034aa07501c01d041d900050302c1030000300c9000032000f240640700000807480d06d00364000c1c44800d10031601f0200c00c2c61000100148083c110040014001c071781a030303448640da80d031080304986031100000010016044900445c01140140c1c4c0f00c01c3e008800100000d0b01d0319507408507104100030000c81624004800b40b0341c1c3c0c0038009012070902e1050b9050703007d040c02c44a46840c8012000c43c0c940000c2454684228080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 730123471 1250 730122221 730122229
    0x1611010e1e0f030c070317030115080a0209091512070b0f0d2414010804030e09070e30030a0f12090f03050903012417010e070e152409 59
    0x5103102c0c5401c420b80c0d82d03600042e00516201d1900340003d5605408211440d40404420b03c1100e040301d03601c10015140305102113040b5052240604207442c540c0d02804140082d0340c455080c503029000c203000c0c8007810101802440344c0720b030031952200d1060304000801c01200d001e4a00301c03185e0100180c401641c600c0490004001084409404081c7c0d0601a20b8031445d403000000030030a9800701e100c44038002c01c000004441010084800400203103014824032017034180309071103d412404600b0845003609280000c9030020180c0b1036440044000005002c5292010280540e036043e00c0c88003844c5000403801e40079280218407070000e4200b00702690300c01440d042036404600c01030391201450700041c080d130800402036002411160b100b540783c1101800f000d008503000f46154002d04060a14a52a1400003807041e01c1c1403103181065520350407030081464041c415800034101c020071001d001c0c10300c4402001c040c1e6a441c1c40d98000c0c1e001a02824010340c4080501e01c175444849040c566601502c004a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 730124721 1250 730123471 730123483
    0x1c020618030f340b011719020d020103060302090a060f080f0303131a1306050916060c0c050406080a0b0c0909011403190c06110a0f03050310030503031611010e1e 71
    0x3c4148212891070100010060094102c600501c81100038031503e00301d4030340324450061340301d801d03000d20b200703003070060400001c01c1100c0d500504000900340e41d00e0700401d1007503134100e945010f66540c9410a0081269140002019194810041040c046061012a03a80c170002e00180c0c16028510009410032401910217040241d101d030100580d401c03c8080106030361140881210243d0a00000660000c4005800e0126603440c04105228030700c0d21b40142e440324402e41040d100842001d0010540c1d4845014a900074110b0350000d01d13501c0c955040250700428041c007461138601c410408060941d6894803550b0554802c01c0700040708503502c1e8000380c5090b1484c00e51802556515403c2e0041c4036506070b0364021580c040e01c4141081e0744008101d82c860612102c0100100042c01c2090003003407140b00a5640140c019154098442e100e88907203107035070012210140c41c0384c41040d000100f070f680040081000440780c0d000340701004600d500a45ca80c00a12051061455003880c5404044000c02030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 730125971 1250 730124721 730124797
    0x60403061b120b09010b03090c060f040305060106080f010306020310030524090a0c150306080f061b040819080906121605040612020a021c020618030f 66
    0x30411200320341c041402140204940200041900c002c90850803016a0185030900b01c001440c41866a003801c0060409400c00307000c00396940b00c2d42c901d8152684440c8002c1c0070410a2203955a10346140d8a405440c144050700200c6c200007122040c003502c4a0341038101410b480c0c0c000405a2a07903920015650041a26840a0010312400700f2014031034040811804010250300c20340e440568a50310075aa84012882c030040042103180d9080009031082d01030010010010f140110b411613a0f4030107146402800b00550700a50001310074032502404840b030b010000c0058a2101d41400d10703000046031110b0b0401e0b40383c1204c1d45240414410441d501e0121101906d00400141c8c942c0750040c464000751008480ba070404640c0d20b066000c42c14001d0080d9400c854040e80d485c060702010881030340203900480034080540c8110300001a042d42d100c02109a00051341e40100042e141001e4032241001401e550303005107030020010440000208000c070f403004001d10030040209a014030300314030100c0402103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 730127221 1250 730125971 730125983
    0x20c0303161728050315190503060c0406090e06011205041112032d07030f020705030706030e060a0c0f050a09050307060804031d0108060906030102070c0b0417070b0301060806060403 80
    0x542c0401d600b5444043d810903054015041c0e01c680a4214295590b11051b52100500e072030b00840d1840514011460401a200202d014400e580c2d840780842d00c0d03c0b00030707160030040c1d50010600740210b985c0580760318020010742d00022581c2c2000d00002e81142d00002c1400c01583e140c200107010b00c505401c0c00010020003401130b41800640303d9450391250010324031225003190300c500500004408217400c9020010203403805161000c00e0340c0540320310242c451603000354015120000303000e03641131015a00a148030f88002c44d00c1d0400150450a10300c00411007509a464408056102580b1907508071080c171840c101641d487c0060741c8161840d021903801658584299030000c10010303407094130340d40079500c00d44420100e00380404071014400c00034821140085c0e15a00041c08502e402815a90400009000149801c113a92602003030b107803c6400c5441007900c00242005100120710914075115414000307444a40c1c20440080a40d11040c4070318010400310344003051440e03075820300712001940d110f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 730128471 1250 730127221 730127227
    0x607050d2705100f091e021203070503030402010e060715180203070803070c0b19030b0d0b0906040302060c041a0d0608030307030c030506060f0d0c030b0307030c090507020c03031617 80
    0x22070b00d2655003015144903100241041d0b12040500da40e4020303c40001d61156410200302c02200d000d034416040800c0aa0f84058107002c1b076203450034140700900446010310003440e502c3c5098000504040d800604090068000b080340b60081a41d5207400300da0104c4151010480a22901c10038458804e030307a00107903040c0030f49240001c5000c000801000707158072a85071441e90f0366442500c2c2c2e0090042400390404902e16864555000b84260700001c1d4241c00282040600740c2035807034032400180c04507500e50083d4030602c00e1000345030b0100a046e07408541d61241d18a0507007000007098000300c900a104400300e20100b0400103201ea180c120001070108071003280c6d142e26107007000802500d4125007a82c04a8075103030100b9881d05081d006ca0707110043c62107100b4a0b015411412800502c103840c00b20041540d100e080a00300d54040c040d060095004008448440e03081988070303001c40c0e0340681ba4100303552045445254588003c0181c1d0440e030482c00034400c0009250030031031110701d03a40c0b84002c9500400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 730129721 1250 730128471 730128473
    0xf021f050309010c050f0d051e04080307021c0c20270703022b09020a06030608010f0b0a0605031803121f0e060d080d1d0f0607050d27 59
    0x105016600c1140610028001800d01404c2a1003c2c801d422142c83c14900070070941405000355040b40f5044020399405c0e1104805400c3d0b40d55000f801030300c080707a1018000042c450515070401081d50203007040b2109000028410030302030700381640410001e000a083c0c40424025801c08180290f90b4103019240320b804159401d6018610f01520b0500362000d46c2d000003050400e44a0b10945603400402010a000d140b00c0740340890007024216101c4402645864940c1c005803901c00d0401300915907a00c0118165040403000ca095611036000042014031341107008410b03503104182c80d000c03107145041050752515a1040c811b1000f0b081210414070703210000d0300c1420700c02103140162050210a00602100300c032005c122071131144038030800c0c042000000204082d468880d5115088a1145104071701c0e0910354000e4000380c4800800c0803200e407034a4000b03120031342d00600440c17415002e100c0140680303240014002d40310703016504184618681c3c420110880d03100c025445c4d5048001c03a401e5000b00030391 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 730130971 1250 730129721 730129727
    0xd0b0307180c091d0403030522110a0902251a040516080f0706050c10140114030a03090e060a03060e0a050f12030103020d0c270b1c0f021f 61
    0x40090b002000500401d00020a0250511061036000e0802c0c881112601d858174101e01400c0040c00d886800c5001d40035483d40348018402c6120541e1041c040b02c0e540c102301504000411a45901c411740c040c1c0100301d81d0840186c4c0c002142e0f50130b00881c0e611104035032030303044c4040b4030706d500e030500340341401084148002d00100180700704e00c042d6000c440c2c1c40250745501c0600d4844240b280d4000c41d60388454020b0140380d0042c800f428084580d482110400f005c1c0c1c030031120a81e58031428070039a02036184c005200c5041c4041000031010b80c25401810004c0311070742c2c01030503044c03540301b85100001c043c00400c1b0141e8a40d56640001c54200c1c07800e00c055200007030300030303200d40c80114110781501c9080084491075102082081091001c405400d040d43e02c0c1d5020b000c000d0008080480301c04064880104006c0e0720b1860011a01d030105540450032001d1030032100481c0c0c140101244980d00200300329407940d880b412030040250703204540703090003a464400700305503d0f807444824000c5540300c600034400c582c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 730132221 1250 730130971 730130981
    0x2060a18030b091c020d0c0503130b0c10020a0507030507020f04020c032a070b0702210a05010b0a0b0703030b2d040605090f16110604080a0f020c060d0b030718 70
    0x42c944040e908100440304a01490814040740c04c030242e0400304000d42c00380c0c02811701c102500e0050003524a80104010307102d21008aa8204994050340414008a000420002c80d0009203960004500d01403032011301034651300881000408101d0001035850440d280c0c4c140c034022460b40a030040d500d6180080d00107807260000300242080b24142d8141c5918804541850303990300d05842d01070400203003070a01a290607480010300341c0e00850311111500c000c828010003041c00c0e614510207801030f85c040b850030034207460030455550f1040302114018004154010300301c95880b175150900090782c0d02c0d0b100120310001c84c1c0c03a180f1010440c0d048032150b80400c1c49450300d86c812408840812209440700100202600c066611611b036400f4480020900003c51144400d1142e05081082d1194a070700e001c1841d240088608540240011508030207150b000316030007040b0052400a0450524240046496030143c40c12004519413220641020703034505000c20005003075400980e610010760800c0802c0030b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 730133471 1250 730132221 730132231
    0xb041b091a0f0103060e0a090f08042607030b151804060c0912050d050a050d0e0c1e0f060d0b030102040306061d070215060a05061c052202060a18030b 66
    0x40501c010b4100150301c0781c030403c81607440400e00c0714000d880e02a0118002c04030709008548980c08948442e01240205028100400300b800741f050040d08010045150070040d030a40c4e041d15031001c001840004c1000683c0760740082940310314080c810481c0001001d1201941d01c4145041e500f60500c020300c2884d8010815804940e100c1801d0350355500d0035064140003110000c0c0c541d030465605d0110452007840107012035a0285407640c1411444e40b03200b01107030f0501c214075100303600a141c4d00324079040000302c103117100001c0b08000c191410b1180101c0c0400c01c0304600e0178819240020f43c005101c031035511030185a10060004c43d00c50340c5030316041c0020f01c51409003110100407041540900aa24210544076071070a83c09000021103085182045001c0030f03010715405000c241001c201c9807207200c041c00c803203e1201c804403150110000c1c0c9200f190b10150840861001d08036101e0164104103000301500c590540303c8540d5048440011a45148884203010b01464002000401d1000318400e2500075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 730134721 1250 730133471 730133479
    0xb0708061c0507060e461202030d03020703020c10020102130f08011508100911100507030e01090602070e0c0d0203040311121606020d0605031c17040b041b091a 70
    0xc403005004001c80d02d1036001c03420102011100741c86c103280d8207140c03804022852803044454039200311042c1c160020300340e41121318041c051120410540c9010040fa62940181e41021840c015082e20025103a01410b08518010340400204d03c17400b80c804d504a80c00c0316100c144d80030000e0b4583e14200110403041c070541400b50f00b00a9454266401d024207041140c50b41c000605010070002c0020000c0d10030320805580e04080707a8035802c6152594082d030501e0b0900c95880507550026454060316014062501c00d04001c200041846076035000121708094440f030421010b000d0b601c220070701312203214420130105003a00100c14401090f800410390050000700300c00b40d80200444107004012405a00b10082d1031100d0400c2e48004104690700600b04030b50342490100f010364590002c280791400b000c05081d0100c9240e040011543d078001240c96403d05d40d04070030b0311241040d40300c2840f4040050310180111105818100c22203e0080004c8020015500b003030290101402d40c02d8035060300490542c2c0a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 730135971 1250 730134721 730134737
    0x20f0d2012060d0b1f0b0f0415051e1c090305030a1806090c031202061302010309051504150f05061513150c11040524010c0209090a03030e06040b0708061c050706 71
    0x40013906d03100f0b58a1150303941081d40c0c1003e190a95040d41c140041541405001c004c0102e045141c3c065030f212b80d54202844801551821800c00714480d0115100d60356200f1403501d80c1c80c8000aa002045a07006842c030781c1c1c0443c01101c1c404030b2100044100310f0092895192030703da031041051800c8040122402001d50912701d160308002071341c40d14801c85805040d805215440d00040d03000e64054003100e406142100e180041e0002400c0440074160350a90340d540300c01c00c022100b036003a4040c90031120001001488281850300114510311000ba407110311031480030880380d00310855404484000c00300300040861042c0d004101404241420800780d8013140e600005540d07504050003400c2c00313241c510340c003002c8490b4a4040c4803400c2d04403801c60b41c10401c00c10303104c41c05a80c510360000d0240c240035000e4803000b000d900d806000ca84146441c5c1400380c05c07600400011a0300703180c9040c1c1c0500300741400c031119911040000d400c0040c680c02d030354007240c540d0050024001d0004058041daa8030ba10340303240c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 730137221 1250 730135971 730135979
    0x12010f0c050301240527120307030207090b030307230c04060506032a0a1d011701030609080702060a0e0315060a0b1c020f0d2012060d0b1f 61
    0x20140310074040d0030710321062002421040c0405840d60711607000d8918180b400c140808542e101b0007400502e400294071030007145d0900e02c1c508074840150214946004601d41105580d02946542d03817489041c0d1b0302c65440f18031207113a85080c4111003c3c01c0e4070030203002c0300d0301c088021441c4052259610445901c11001c0c15401e44c01c19100d900242c40005040d02e0450b622116034040007441d20f014440000550000c100092407c513020f03000c80d40207038661070722041d07039020305002241c18a80041d040001c11651600040c20060403035040d2a0003403000301e0140802d0501d5442e07032069240003501308400080d44802075034001011702c807000c1c0840130740f884810a0181c00072074081c2500c00030381c4981d1402c0708211160020000f03080d0010a04204c1d1070450407049040120f07080341f03040216204000504118807a124414030441405000da2000000b14170396200300c01e0b01031500071000da224260041601c503079401301080c40b1260b12400150701d5291040500420b02c00404444520740300d00d1700042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 730138471 1250 730137221 730137227
    0xf030a02331303020f011707200303070f0c0602070506011205150c0316020a08030c0c070b0a050d0c0e12010e0c01080f070305040f050d091a07150b01090512010f0c 72
    0x490303107040b9900c1c48441c503065800704001c24040c003804905109400241103881201c81c07401c0c1703110f02c142da02c1d5203403040382c00f03070410758041c0a020700071030950020010070807003a4000c840c4c0c0e03200801e0707880d0a1111201600c2e0041c003d2003000400b404601c10400005240250416218100d5110708c05860b04001c1d42282030440c21415903000d51402c01c14000201000740700d085051039140349104940460000d522001c003141c0c01995900c1401d20700003548030030b02d00108400380003010720b00e46e064900050004020f06d54002d148403030301e1194891181d00001d41c441d0454101d940002401e00b403400b0030034401c290080c100c1c034a03044000d004000c6000701543c01051007030b1040924020f0414955110b600490041500400840d00344480340180008540100251080d0300040c5d21030071300080c10041c0041d00b05160060741004160104102c1c40016201042c807803000390180008148e8130790784001a650032019801080c1c009400780c506441c20681500511031084030708208104410442e0021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 730139721 1250 730138471 730138477
    0xa020307120203131103070f17070f061715040f0b1311030a02070305070b090606150c0d0807050c0f01021c0504170a02100f05070e01020303090c0f030a0233 69
    0x50b0300313450119074140003048011011480800008040d21541a160440032100c000710b50050180800c003460602c41540c000c02c1b498001d0600d50b0724800708a403402c0c400510005101c1441c0762501c00130030109404003010442540c042e180188144030441207556041c006292598211744501540820650188818880c020340380c054035104614550b14664514042d5101d03600440400104001c894042030541403070500411140f0b0282c582414000c0801c5103003007010414600f41801000101002c0f10001401a07684081d41003240079a03a601406659a024401404036140210380341041c1b6190103500400082c01d1080058680c400c544004c0d40c1201c2046400601c010302642603002c4022004000d485000000d1048440302c0030040300b404d0584041080541c0d00b1a126800d0000d09500004540103015081c0b00840c118644080c02c01ea50752808040c4600034501603016250b903460900104007030036005404039113070038003003d88980742904d06400d50404002000303510001840002c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 730140971 1250 730139721 730139731
    0x206070f1101030f05060d030e0f0612011e0b1917090d1707020d0c0606050d0c080d020f0c01210e0d02062409060d12030509100b0a1502030706050a020307120203 71
    0x8a00b41f000c480e0b8080d54406030064940758094a84448081569181d200078036180031f01c103070b40d6040ca5141900e4108041c0c012108a005104100700500c50f60069409541100c1071200410b0706015942d02c0c140d901440500c1d0f079843d08a2040c04001c1c13500c00002d0350180740a9035a6500c1e01d6a402901e04140707107601940c8410060f0008a900340503944100c0c01b9039105405513a0000b00300303131b4620000e0080590b10400300e4161844003c208460350313082c800c00c2000d0491303001405009042d820f50030b4451155400c80ba040c8110007020030b01010301c00c1900b15003050079a108000403c0041c0502d60394080c94401d42c0010310072000001c450341103400012022801e01c82c9011546034071102041004040100700c941c1081c090201c02000c107a001601d00d80c10f4105450019890408100781410121040030010340903040081900c00d0751101c2414034121007a8220304104900020700c100e0441c030503004080c0a141c2000b003440020750b41c541c000c1d4010f107010340321621181103540100c0103070300045503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 730142221 1250 730140971 730140979
    0x6021e0106080606120f0d02010c080c1201090e03040e040602191b06050612240105060c03070803060d0b16020d031e1104091104050a1403070306090206070f1101030f0506 75
    0x3c003050160030310b44040d881910b24072050322480000080c0007440c04404101d0036006030b45800411001c2034000c11115000800203144624243e180d280c0710305132281c10f200380500282d80324002600080c05105460251402000c88400b038200341c1040b0000e0340007101c15403a00a82c5200c41755400d4010103d070300440c1c0b07011a0300a0103280503200c0100408000b00060b402004280c83c082c0300580a00003e22066089240800200d04105510b034502c54142c2116000302030402c101045070700d0000554800503032001090f5566901d643c0401c5c1402c0141c40c00501c0e0500030801c2c4005142d0400040d260301100d80d003100c003814001e142c114103460100382c500596403000201034014001d036401070721084d4010030005250540e90051202102d41201096103691000f190500130344c07030001e164000916420a9607500c0c4010500001d444010500c002044145d0340c8140038119150903050b40d201c3d0360040e00e1100608201d003005038440300840f01150000c0d01d0902d520030300400500c5554052034000e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 730143471 1250 730142221 730142233
    0x13060f0609091e0f200a03050610082805070e0f07020c010e06250210030b0406090b060f1312030503070f09081f111303170a020c010518090106021e010608 68
    0x5e01c51001154a51118101c001440300c00b1400e17503211000404001c41c8560002c000c03d02c3c051041c4207203d040f0f41c0107060b0a800c001e00140780c0e000e0401c205a5008441c4900d90b60003950340c940b182c41c10072141d2040c60592400000c0103055500b080e9080c1c07154580d502a901044005001162452040d400050340700c1824890841d400c140c00403140b0814502181d0390003a01c0c840d80016180640040c1f01100203900e900d4019641d0605026040c0240f640880c240500c50707200b00040c08500464940c2800244080341000121085802c02c0008100701c0018400300301e842e0074002c10980c8100d4000740429020b801c82c0d117a080c400d003000011a42e04401800340e000140c0000850390f000c000c1e44c503900c2e6840b00074040c04203009a00400540040340c01312041140796143c0f60604000c20f8001e02003104080c800d03c588103401203201262118240f8009542e51078485034000000f0b40003400a401424501c00450b01d2034000810035044000e81c0010882207000d49d036803500740c4da032501900500e50010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 730144721 1250 730143471 730143473
    0x7080114040f0e0706021b09070807050d060303020a06050121061a0a08010c0e01020a03050901080402041e0f0608010c0e0609010207150c0b010e070813060f0609091e0f 74
    0x800040980c0c410007440400c40034818844441074410a20b440102c58201c1c40c02049002c0d01040745050848803845007107400d4030180005440d002c4020040424030083c4c40000d081c0340e20036811203107001004542080405e890341002903555400b00704c00c540b80c0385000000b00d0300307003d10b000d4481d24140202c3d0a0b8041e400f00d555203409032245c030008030321401c00365019a010340d941072a010041e0404130300003e0000d004c0701c0c00507d0f82080111090541d000700c250030740440c0d13016084a03031489080c20710b103141e42c03a140b01180007071004800c003000304040c40030407001071a0a0307000501100309001c0e00780b001645840a580c200d81442e100341e00494240d2200d0b103482c0c240310003d01042c45050040d1410f4030341e11103960919541c00c42c00100001c104040802c01c11454817401409046d08003980b000754904441c2c05000c00002501700001c181981c525841080003640069415034810141800b1040c0d03906000b1000c1c00da901d00407540400100c1d000044600f030380c0c840900254210700010030031740701 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 730145971 1250 730144721 730144739
    0xe01140f01020304050a0e04050c010f0807081308070302010f0f0b0a0918050115060212030f010308520f140f010c0809010b0102010603080406110309040f0e070b03070801 75
    0x580400c0c141580018403000403140e48078080003008001d080c0c45007413240303800c0c0742c11810080080082c03414081354045600c4c065030b1101c1d805e50b00c20100d007040310047e110030743c4115003446e101000034454100054141c0402d035040d0055844420021003e000210341d05205074181c980c12188207401c401a42c40400a5020700c1e0018110030000c058a81c2e02c45050340c03110343c01d446211030100000200c031201001002e0781081f82102c00b05041e6582c50441c1030560035441c41c500e041c84054085117022a9495100041e003680c203041404d8180f041c509800d22602400321902000601c107441c1000032619034140d0701c404600100c0720307405140814800203a540742501c4503036241c2113080381d100b4440d8003404400241700d5842a00c0254540704041c3c40d244458500b5a4810344030b0381c0c110b9040180030070000b4031400c1502e041e1046810000403280c0b54108081c03a44c02142c285940c00760910030390300c0a246203a4040c031500380000301603800054664803c00c03241d10041d90300400058000004210000c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 730147221 1250 730145971 730145989
    0x1213032109080406090e0a05060a03230d0e100809030f03070903060908071712010308090409050a110a15140f073c02011b02010c1704030c0e0114 64
    0x28090000140e01e241916030070481d40003500311101003006007034103000039400c1104050340081c50300010b001502c0c21202246519a26220007051800e4900d25451060004894182c24070442030403039510500200009141c010041256030180c640c01e00003e40d003610801101c0d2080407107100461030051100180141ca9000606505c10002041001b0000070403034050f204045008440c907945401e0541002950800e51460ba40610082044213080504204040c00d0449420049003611003090101140141c24030510017849070140e0307200300b01003117190709103c0e102a5064402c2c0c40030f10307118081c0c0d012034521958141c02007020f010300f14030120949802400055141810142001041c4d924181c00c040c01d04080c145084440c0501c00b40381c01e030030314a8103a500745910240040320550300064480545120a801541d81c141c000e60150790049074290185540040d0320210b40c0d447c420244170035003103400b00f169669200400002d154802000b8641651a001c40907004274600100b0006442 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 730148471 1250 730147221 730147277
    0xf01022a1203030906010b0703020d0f110708061902071a04020a091a13051005090606120708150f061204050114010609090e0706050403021c0f08121303 67
    0x11120040c42009074a52007880100301904400954681c00c00f05401400d280d41604a034182920911103c80484d500003450002007040381494407600305000d6040303e41a1103412607182ca88509000001c5165001a10900c01c0b000c111844d11038003806003c0700e007644144030016240031100b84001d00b0365650060700035040752000707001001c1c880d82c0c1c65129080e220b04e503280c8810816111010103207401c043e0720a5007003034403a0324100442c0c03800c002c00b600f002c001401031a016404000c0001d01a454150444901540c1d01225220a24050a009108500440d0120301c0d400c2145407a010608080b0800705408100400c92418081480c242400c1d45000a00c1902c543d92601c1c02c1040c400282c85025001e041c0300e50340c4410440c2000c510b83e09881c11a8070082895005d140d0403c811503104081e039040c0e03a4112002034104070300064080d070a43c2c0005025001d1090f112100c0c00304600c42c070042142e02046517820300c0c43d95611001011090119001801007000680e001200510341c40400c2103134 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 730149721 1250 730148471 730148533
    0x6060307030b1e01180f0b090a0b0f0a1206030510111e030615041514250c051c1118040b010f1a09010c0303140a06030c050f0102 57
    0x502e41d000c00240007180300c3c255000101c1d54444600c3d00c5580c08500c240850300300c403440b048103d107418004034001146100e40104624041781e030b0580c0755154984035008001198041da1503107004102450954083d202c0200850090300c0401d1043d802030250760100c9400a01518240b211081c801c00600f090031b001c500300070410003214080102404003200c4a015400246440e49801d80500c000c003100d200750408503100610082201585054036011f40d6a018500485c405910141c2da81c074138002d005059200550501e6041d043c40000d12019a21a0249803120840c1d544c80052024070407a840100b07000c009001000381c0487c81d5003000c0340203500003034240760001001e905082d088240c107407002c41d0201010001001601110300c00341010301442d0742c08040f130803040910807495104a03403a083c14026030002407000e00d4041c0e48581000415810103903001d15009640c0c5000340b510f4042103c15522003031020500c5d040660b0312074001c03007060b00180102d03500c00c04030070301d4025204408400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 730150971 1250 730149721 730149731
    0x30b04060305100b13090209041b150c1a011202010e03030c07351c03060506041214030315092e060306080d17070c023f060606030703 59
    0x4408020301c181d001c1190900140b859100020040d401c0100c00000c8102424401c0301b10140c4d807503151a6400c21341c04202034103101941030038031895100a9200714500015003000281d06034000c118854058840c41c3d80c103271070810344007007150003c00c02c0c058007074803d4142d0b0f8844015401100c524041147c018200c070b05003141c1c06482032805080d41c2151040c00201e8040814100c8200d000c80c81080101040580700d034490101c40381c1d29403a010400300c03040d40c3c60108066050090303000c0400380030007401c403035075654540c00081d100e4042018100e480409804550b1682c0360b02000760390160000c000354808008200340ac001d0b802d640a1f000a8600c0b208915a0280d10200d400040041c104000d00e602610320700003018044030602c0d405807455800030341f10748488a0340407030200101180c01d0311140d960f80764030904844084c80408002e4100366034600300c80078180c01024904074014400e001c41c01c0d040c180556800d410712100791986942e40580007143c03462509001450b8032400038075002179 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 730152221 1250 730150971 730150973
    0x1030b04200a0806030a0201170a0204050a03030503070815150d0b04090f02030f06040b060904140f070f05010c110405040203030706050a0203041a060f0114090a0801050108010b1203040303030b040603 88
    0x22044201c440940000c0c0e00014542240c075001001c060340142c00b01e010f00307007100741500041c042d4140da5408610040c0301800040b445d40701b41e0b065401910b000b510a9518a07201d29018003d03500c19100e42011644400004408203108003140e03107015000b0300044600164252a41001c0d002001c2c0c180c03089403038118191064840348901007015000e03072242c081001c0c190041c54205144042c0700030710b41d00702d48200004240c4130810207400800a641034401170340c40c0d041918440100086000481c000e800e0a48141c0710000f0f0310b1000d5030346486440300000e5403140152003040700010f00509807003044a08107040e14090f40074552190024041d60700e046142e030388841c21100c1c100c600b0b1600781d074040148001d0000d81111110442c01031505501e182c145500081da029070340f40c501ea41080b0115861500b00c8000c90240c484982014151406e59074503042006d010300b10900884100d50300c1c2004680445c80e003141175a02d25000d440c0550314050660300c04034040d0210f51b13640c44d001070311104000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 730153471 1250 730152221 730152251
    0x50f100e091803190e09071710030f050d0f020a030e131e020406030b0103270510090503030405061b0409020c0c0607030c0204050f190f0b270714030601030b04 70
    0x4420004a266003492102501c1030141030405a605817502a03c004010803200a402034000e18244030a241c2407909039841001e40072820449800050041e12300640500801074001500c44191605483d04444542409412a5215144800580011101c201c07407001400d0010015413414000d000c0890015014519044000110b0014a4105070b0014040001990500c0b07468543ca1092038140200d904184000101c0034403000505100321940c40c0d113408000080000c0101c5040c003005c28810542c0d14180340d0344a070070491b016221802558000780d134850240607030740b100f44d2440110b181000c1c200b0300f0085c025004140300e481a03218210506600e965642d001d488218460340e02e00000d0145841480103880028000d912034000060502075101502c1030356041d0255078403800a0042e900f066900054031361070301d18075000400401013000c6201d00c000024111103c1150781d800c2500c855404450103920090842d15041061020403200c0d03100790080c441c9603000500209910008171040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 730154721 1250 730153471 730153477
    0x1110f1c0e1501080106060507230106060509090112082502090a06140904020f0103090f1502040f060806010206012705070e0a0803041404021606090c050f100e091803 73
    0x203440741c0d80c002080d070b1054203410020b060141c0503a00091140b10700c4e01a01a22a011b031600050011310428000701c0000c5005200c85003001047e002441040c1e40c40c1c0024000d980100310b6580501c090400100c1c2003980c00c440401450303403080225140c071110044040708200200b4014540030589440040941d54248100c1c1c02159002e40006455140110000d6203100d0366448034000c0400c1020800941d070307010742c01c485031070f4203007404148001203107070081004413000b900400b0700c83c52600b25943d104407a8050320075500000d40300800c0a449520030b41d400a011a0405c2c0160700c81c00052007680455220f07040d0702d102c2110403000350202400f9410584d2001c03034441000502c102d01941142c82c3c480e0b90100205600c001452800b400e00751081003604080319050300403500015804140501c401b007032000e10b500510300708201d40513480d000d00d1540741485420702c5031704102c1ca2400e1a01e0300401d12032403a84142c9803410280307008401d00590035401001c080e864481a4014607082da800d00003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 730155971 1250 730154721 730154741
    0x7050c19050610080c0114130f1d091207062c1c050403020109150e0d0606060e040b130504030201020c0a110a080f15100306060602060402090901110f1c 67
    0x2d8111450f106041e4400e582c1c01d9801884242d106121244450742c00030500159001050043ca9540c25130490300c003c514190b0303005500e8000c072808009101d0501e15039090542d5420300c51030f2141c0d101d000c0c0450b59070076000b5141034000002c11480f400642107501107580c0020000c0c12000420895994050300c03428074071400302c44c0e0030031801d40c02c0c40f1180500e4900210441d050250410f429600004e140b100070380201c0710449a042c0740340f034000c0d0180300310f2214000001c3c00c1d00c40c681c44a01e42040507100b2072003040d0100340022507801192920323004664400c9070141c200a445c1401d84020000b8110160066003555405c00258a0120081c0030750509a405405106040440311042c400808141d50020038160007140f542e440194000c00c0c0ca12807148900d00c1072046403541c00144440c28510740c070060406180c80c1000824a4010620b648a40d0080710745420642e80c0403c41030903509c00401c207603606502003112482403003400c00940b011400102103501c902c001004c0310030480c0c0076019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 730157221 1250 730155971 730155973
    0x17012702040b03161e050c120f07120201060302102102030a1a06090a15110d030501141002030405010f030b09130b090f0a020d03020a0b01091b140307050c1905 70
    0x10030400300544192110780300d0902ca1419140c84500e84a02c003211540031700100c42007082c005004440c0500811098100a4442c106250f5940c00c03081e211100740e0007544210394400700c0510f0281007900602c200f00440c4d4020b00340c2080014191022100010302c03000030b86040303e12540d02c610440007480554420291039800281800d52000495141800d00703044901c10383e0204400324041d25000b80e400304450710b20526801c030002c0c64806444000030549404400d200d400c2140c10740e1541600858129041c0c900c2d03002e01c0f04600c40601140c00320004900d0050b9200300030404c49075104511400030302c400361400061403c13203900003d02e2030b60140c7c1e0880280801000302014494a9100a604003240030024000c2c2d0049283d103507203e400600f4040c0c8a14020018102418001d000104225a000014811642c1c403070081c03100920b2922000e903241c0700820380f6903120741d00802c4a0180485203040340d034296500d80d4400c542c690b00c200d003001c0c014003e840b1185c40207054a000109101d100f40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 730158471 1250 730157221 730157227
    0x140c060405240c0904020c1002070b010e090a030f080a0f0e030301330f031b18050604060815010905030f0606090a05040b16091205030903060717012702040b 69
    0x602c80d026140401d58409090b40c007200184585681c01000721100000150340c0941c030382e10080c503c641840390140ca410145800000c64038108141c404a00d4113903514840309a5054542051039503a41c11a520010301044002e95114011401380d5180b951000c2441408a490384414580d40c2c01e0f10003440d0a00f03055800440140540b00c204030703054145000b5020075001000604d060301403040c804c9042c400501460180760480c0030300c01d0b001042015030188204202c0905100000c0a290440240340400965940c0c003051a26000d01268100c0b60f1a030703640d400d9034403071281d0f9410b1904142c00781414030034019800101f0791014820f86003800c221402410302403808074244503030203000402400071946010200000a10032528103904000d018440d44006030b07034000241d80d501c040790014280c0041e5541900c042100000c002e201510043d001e54440743c40c2e02a0969010a20031008000001301800601c50345002400564126a20361401041035801ca440c10701241e1041e01310b40c910790800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 730159721 1250 730158471 730158493
    0x3151c0f1109190b0d0b01080c03010e1606200601180609020703120f150b0403062a082805060319021005070503091c020a081c140c060405 61
    0x900d8280404802c0d14011400d00d0194106954241180c1e0314194056443d420a50b49031074101c0c005da00242d0241008159586840c409039031190b60540c040d00c65820602c4400801801050b8210802c03100100a44c0301420b2500691b006008031700a100126910750302550305020401045008050300356100e071040e400c68074014140c4546802802056004003d00d2000903071100202d4440c141c1c0b0000010341c004c4505c10407024000e05031080603a8002c00a020820307000c100024400c881c400c0c40d080207083c085002e410300603c034042008000c05200c138001c120260082102c2075004402c00040c0000e40c290303040c4210748050420f40014000d80e104c08102a905042100600d0b100030400c5414000340c95500250154041141103820440d01041c03010402c2020020703240b2034000100344000c42d00c070071040c8901e040f4040b101a032040640301d8000071118030103e004c0140d1501d4000c0120043d00190094615070f012445880760700604001540c48000d0a11950f4026841076014116012034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 730160971 1250 730159721 730159733
    0x70201081b0415200f010b040501180e0f0106080c01090602010e0607030c030204120807020123030406090822060908010e03180303210a0609060b03151c0f 68
    0x4010004a40a10414424041c0c4011541035504841d8038407002079003512201c2046618080d00500350140801031030441e081c14801042c500d41030900300000700051030320001000306491080c49005c00c1010320016850703100c40746412200d080200c82007194401c55030704450b5400c49102d58007000b016041214a50b84640e48020902c0c01000e05100038841c1d2508600030a450710300161081e8185075079000d0007030115000381c056900074404203145540740c80550070012501da0282204a0000b03048802903001012004090025480c1b0780c0222411580c855540000070f217001801900c200344140040441c050707041401040444098511221407490010054000501500034042c1a4100b002081e43c5d050b0020030707070340540c0305031031315501685400001c281140b041d900d40705407201903d15018004440340c5001307400744852900400050b0380e02d00030081140c12030f0107180130b901d40400105240d0204844500b40000c4014000c03140d0491250418040200a500c1126110000c2e180e503002c0c488 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 730162221 1250 730160971 730160987
    0x613150302030405030a030b030c041104090c0c2d02040f0b03010e030a140306040603060c05130e040c2c070c020f0904020901031203060b371407030c06050c070201 72
    0x81504055040d41001d980740f90701d9001d01201c00c410150381e00241540c0e95400c101d0b144243c40302400410000a00c0c1e10494001c0e8442d000d02403a02d8180358a1494991085401c440c2550700710000c11401100c69040c1240061400000b0f83c8910110b0800d9025a45512481000c500421400a44085644141800d40d803d400c1c101d585a001032041c1202980c005030000c100c418000c1201c0d03502c0d03482d48005001441c0d13a41000c0d002034174009051880700e4204000304100e5400745d4465040300e544551603000d4210444d0000d0540b4603a450410104002180c00150020000b1188000d040c1901080c40e407204101d8404000400c48642401581843e850201011380c0683c4c8504c1d00f45410740101c0d4125030103100040040b0010244003a00502c41d80c031400243ca5140c803a15036440c0c1003040400070100840c5a100f550488464403000e000c0d4014104010400720380328070208032400e040d1281140c01000064041c0000321000314002407040c45024440c00300350102c1900c80d5414000100846 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 730163471 1250 730162221 730162259
    0xc03190b19320105030d0309061104032405010815040809120607140306030a0201081306110406080f1923010e040c05060c0c1309050d08010e0a02040b090405070e0613 73
    0x59502c5005101c1a2000b20350304001c1c403004c0c1030206510240745480d0700282075122455030302e6803010070b000c010403048202800d4002100d11800c1d10b501032817118002116028801c076601c5038041030003110580d2002031070981c0b05003d42c408500b00155800400d1085408034040800c80c3c1144040200741c6400001d0071402c014032940c2d007801c5250810110b580d9141128000e410300086d040081d00754920b04014508455100400707100c85550300e92401007075009401000c0200e07140600080c0c200e48050319240c864400c6a45402050001c201904000c00c0c1c2c611420305031840382a0400c42a10350200854003d02e5000500101e42c54141403111003101113400c860300c1b41d08100140c2ca04050b0010360b408141c003044507180078038402010740070700411017000014102d002d0100100f04c140e8200c10801d0480368800d009d1402d030b030359a194140c00c9202d01c0c003507240b101c03a05111940c950709141e803040342d00c4603880c01c05454a500e2100010441d801040d0581d8402e034110f04188444103c401c080d100d85 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 730164721 1250 730163471 730163561
    0x60503070f030209150a051e1008040b1f0b12090708010903020706080a140c1308390904050a03110a0804120f0b070504080c03190b19 59
    0x1403411940000e01528010b044d85a142949002e44201a0388046d000d00042a0041c010748100c98119408070a41e0391486082e84101c640ca42030755039907030040031542c1c482d80e4440c08610042d1b80380100e82c1440105544040d1403588159404196007510b00300070a240c01640c0211038882c40e2042e105441c02865400c5040240d050048960010750005100800c0d00c8860070714603a5641c6154000b001020211890303044000c1070014020101d01c40c4008000d130f80501980120250b4464016550301c900840c1e03484c18007080754820381c00c8030182000030300e444050b200b0310301042d251341000154004c1d81a00c040c0c4e60f50b00240645c1c010140c04c11003c0ca00c6a07141000f5020320310b82e0380c90b095003c0c080c5100b010000d0007070700903c1d0b042008012050000136400a07800901e400d101c10001c020740c0241c041c000e000e00c0380c3c4003180d81d0340c0340025031903100f4141e86518440380c80f102d0f42c2c1e2050791040680604284201105402003140282c0611070b80e0b0800900f80f80c42c401c651802150310304084d40d501e0300070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 730165971 1250 730164721 730164749
    0xc29060303040b0901050d090507030605040201030f110409020901020a0f0c1d0108070612150b1801030902030c120a0804031b0501031a1e0901090e010501061701030f0f02060a0306050307 82
    0x8000f20082d41c0360300c4403d08040e903d80c0c00c21000b44000d0615104000c0540c001e4580203c1042015842180100c2c000c0e41e08100356002c440080f4205c0b030505404a0105806001c2084959a55001000e0100c01841952400d410300d60740d4602c03103a0003220848040286244c00e01c04250aa42034070726001c00000d0384103c1d03524002d0b8894a44000340200030402050450702c0a00300c0300c0b0741115511389843c6411280e2581d0745d4148100c150403509400342007194201c685500c66210f030240740003854006025007034402c2d84404001401d080300880c01014059135506601203103603007014000840c0110307541540c1c1d41919086031074141c0320350013240c103041c070b400380345107601d80400d6040031040f100340d0f043d0748100c403c40d4510000d41964071683e548006d8002c00807903450640c3d0002d84060030410f000380201d98036241c0550f4030301d50324508100c442100074010404180c0c5030b20019601d03401001120700c071000c59004216503031300400f0408007194075800100080e0070301300611001030000c080c0300b020f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 730167221 1250 730165971 730165979
    0x6050c070f03080a140709030204150f050913021c03021c020a060c0e0a08153103090b071a011703070b090304050319060b0108060d0605070c2906030304 67
    0x51508880c1c101408108600700080d40800c3c1a80c0b0508480e15540d000914525080c3d00c01008604140070407070096052180d80c5480030048140e11007550240b44002050500700008c3c44050b030710081401056406041301c16000d626640e0302e13811400d00781e000d145800e901504000e0f10b030141e2420f06600700b958140642d46c005074085a9001c00c1640042c011952101c0c1c548202c52480c1804401c41c1c2c0b200c8040400940202c0018503889282611000e158007551180700d40c0000328a101100404800c81d0740206500c044901645c04a4a201e818240b66040d19102c0c040e1054000c0034040354421007610303680614010111005004254019040010440d40c2c00c40c65200d018480c0000c1c8103091850104084110500c1030360050103000d4200d50f06d2410101040196070800c15094400a00e4440c24a22651203007000510920300940405a038240f0b0f69180300040000400840802c0302d46180c440000c0c91042040f08140e100c5500541c0541e801a10589450300c0988250720035401000208 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 730168471 1250 730167221 730167233
    0x1c021b0913020f0d1403040f090b0303030103121803080c060a480c03140301030201050f0a0203070606080705030f0609060f060a08011e0b042f090301051306050c07 72
    0x1100c03032035041c3c5094120015100208032030300580740c00101150440b0507100382810000000c4c0080768150b0300b02481003a5658500011560300031085901904100b0050002c1166002c0f114000704052520780d091154414600407100b070b864004071042c98000800654442040003442d0b00b081c0e0070581000821030150b40015004000310400d042c0c200740348260051000001800300c04907800882e0031170300707081354003004051040c0d2840c12030101d00501c00c81c0c84500c4035102564141e95041e1600c1c0c2c5460213511103e401e580002c80c0540c11440304122103000038105002c3d0301c0c014088403008080c05400c1401301410310060703507001901c543c0700c40f08020348000c001840030f8100c0340c20241c84205031590b50101c1c01c606000d811945046d070a00302c9000d440210310490000365114100f0800110781e880c01004160f40003140381141c1141400c465007045800b800c0c0c2a03803224180303c0d81074903000001e000700c1e0a4807003c580b902d0200c1084c55150050005038028298004a0003180524112032030f9215 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 730169721 1250 730168471 730168501
    0xb030106020303160503060d020108090f0a05060405190c0b030406060902130e0702030f070b04050a020d0c0546050409031715060f2203050c0315010b0a050c1c021b09 73
    0x22b0b040001010100d00c0c00b440030b200d482c1c040c2300f4403010342d91240c040381030103a600d5100b95012205403103504c024075404426a0058580c640c0c0c04094040341c0791405070030103007e401c007520030303103100350f45034000541c210f038520040a225007104441844a890000c1e0301714035141c01807504055400c104648905170744104103e69036150701030840b4100b91102d091035031900d0f42010000b5000008652603c081c4041c0d160010101d030b5080307801821900c94007d803c0d800300c40008118405941760100c140c00c4c1c90560302c2411031418a40c0190052594400014007561451400cd401150001c0d8040e0011440307800400d6008400248502400d0814400b051640c41303000038149401d00003243c03803001c000300d19005138480304034542001601c0e5168105103172100c00c6040d0642c4a48140300b0100410b00c0d190007514100d6a0403d5094106400d0481c00c0d2171552016103881c20310f0080d4845182c503458110301c44110710702c8907030050411403041d0350b094060382d040d26059481390640e41c0811081c40140700e82 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 730170971 1250 730169721 730169723
    0x60a0e10050103020706090623070306050904030806042a0207090e030403030f020a0204050c040801050916150c120f022a060d020904090305180604050d0210090b030106020303160503060d 82
    0x40165905c500b424004c000b0203e044004040a061940e0000703540040c105c0100000c00006d0070104a40340d21000390300301d401500c203050b00595240c0019010074010315949038004405807001c80e504024400c1640c841e4405003800d4000310764000390580807a4100b000c000076100c800d104001540880a035140c1c3c0780070300d11000302040350101b240d540f828801d011340e064280d40607005005500b080e120204a94205000d0034210350f192400281c44d034100003c11804201203117074034411613403e000048044140128040c800e000e00c4040003000590701c82c01c16500b00826940b0030070740c400300e030301e0080c02d10440c0400c01881e54080f8404a0700108110904902d2000c125035060f9218013038110b401c0640100c1924952142c50800c0302e505241e04000104540c00c0201c1c4820f0010601c1e60410602d801280103080d0080c5a051a080060415134410b00c8601c041d410903070320465413803400411541c002d8002d280103030004070901c0120402440014000002400c00700d0841c1350910114540e00c0600344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 730172221 1250 730170971 730170977
    0x703060c02070906051809070e100905060103020a1e0c0b0405030306030d020703030f05090d02040914192f030316030e060c100911030d0e0f060f0a0f05120906060a0e100501 76
    0x10036403841c1f0401050000307007524189580300e894914a8440c1e22003592041250392801c20001580961080c400c81d00d0070380031900d0300c2e02a80d035000e0154014440b500914010301101d11400408114100d40061255124100441c0d0b40d1400d101490700341601e600d00141594407003441400020303007140300c10721a41628640240c0301d00078200058400c440000f0b0107504245054000f0382400b1200481290745501c5004071902d82c1c100800b00d045410404030040c0c01c8650900d20512609014201047d400f82071107078046000c640314000034115070003803010490801701d21a501c1c00701604241e00b60b580307560840d00c1c40c0c2001a00744940323441c3d242100010b40004c7e502c120308010040074040304034034540041c003151000000024041c10400030401054440d50250380081501d24201003160030203000302070301a041c40b030880c4040d80da81d21009000d000f800014090f03030741c21001c091000380c400d030036220051885050080c00e11206140035005003109402400410090304203511008049807001c0ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 730173471 1250 730172221 730172269
    0x415081e01061d070305070504060207030206030604110f03070801050402070c050405090f1b0108010801020703050f1b010911041b09140a0b0d0b030706020f101d0703060c0207090605 80
    0x9510740101066080362480600b240c0c50300310740030701480d14144030b00b89544007004a0707129002c00360303020301a520684c4c006922800c0c01740010700b0310f04040d40d0403440150011030064250481c0303000540091806481c0910040b04114009602850003070041400380e0301146851132989031804070101602030071b405291600701103040d00c1d5040020354500344005050301c6135041c00c0110703903404190700c4071141d0000b400c510003c98212010f00c00c542c0d5607507168940350b1800ca080c084030001a0803541c00e402100704807180d4441080f1081c09400c111a11800010116400302e00c200300c120b4191040200c80e403c00c1c20844040f407a001704e481000e40e4101c008188102c86400b000901007036054021b505010000b00f500f5440d01c5203504030002d8448101c0c141d440312030321408100c1c6d507482d06442840c0f5950041540f0b041c07901c8031382c1c0001010110f2342d09000410340000c5c0700c02e03d03024280e0700c2140c0c030315904e03103c3e1242c160707042c0f105502402c0303004030510202d460940080c103220720300c04001860014003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 730174721 1250 730173471 730173523
    0x60c170c0a061a100203030c0406230d092018060301020c15010317030f0c070311010509210c03030103140102070228060f020a030309110411030402041508 68
    0x41188540d00d030391049091043c824041d407060140119054054007801103601c0568850f4000701c1500e128031a0041d00311705051820804440052142035509404c00c0400035086102d40e01800422a80f00c4800c000300f0351041510f00000c1180f40f19203880b5044903801a0a9100da561100300844044482d100d04001c7d200c0c040007d009120360301c1991143e1003000c40e906510140f1404050490f80a1a035a40c00209a0070314008544812140140694000300010302d40c1203001001e450418080d141811350350103607605950071144151001415603000d201050000d0701c002d43c00c040c41c4002440c51500308400141f0840e52408180001012aa036407136010100403000d506803249141c000b0701034400a88074030800306880007080265524003a45010102d0b1844c050030b00d4001d00c800365070081640c81d0003030300c080740286040e00080303c070a82a2440144140d9a9000350103c40101d50605135032030400e88100001c40d402d26401c0c8446415404040094103c080b4080c5160b4894403c6c14035a2542c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 730175971 1250 730174721 730174723
    0x1806020318220902030c01170a1e05010b03160905010e0609062208061e040f15020f1305040603050a0b1803030106084302030c03030112020a060c170c 66
    0x56070302d680345008000e03621520294260801c0c0b1003607000313070155040e01c004007004696041e200d810010400c40e102020a04103031466211203e806001041c4200501c502212076007070f42c2003071b0300c4444606008428001d95807020740500e17606115030700706500c0c8245041d00181c03061000103042c41c0305140100b0b040f03016444110403181000c100300c0e40c40120320582c60400b154036030f10380961481d83c81a074000600303440d495038030301e200c055501c80012525030b2681d6582c4030481c0c804008441c4990072582900350503000e80090720013002148621900c50042411490004601c0e41c0401c0c802ca05108003000030540100b90100d0064001000b4101961907170522161860500c0c44401d0307074400000001640380d4884583c038010180020640000c0b074220b5250703040945111507a004465200703803100c071503581302c08208a00206900503613081075020060f07541160402da10540d21213008075100411442d0211030300c800b4082509001d0075400712504e50f0031003011610300004030488000352210780008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 730177221 1250 730175971 730175989
    0x181709010c05030406031506051c020703050903010c030b0102150f0f09030c070e190c080c09240c0d02031c111606060e0709080a020f04060509040b0103031806020318 73
    0xc2c0000450f681c81d6640d080080c02410422030009801c0c0d9040c8000c0707841c52080b030440d01e1150068401c8404000301c40c0d0307420020752004000f1001e0140c2008101c07040c0d2028012030568a146880009114910f6000641005100c0c0744002c400c024440030000c0d4000d65000e0135800070010003060b15144e0700d080303806e491413040c0f182e40400c3c5d02c9441e0000902400b003404040c8592081c2ca13131000d501e94035541880c10b07a82441003807400308088900280c0001541f00c0504030b51500245106841003c9070242c040e0003d030000c1c21801210006001100d42c1c4040240c1e000001141c8000e40c5030820328070380c00101c1d40302c04a0301c000e010f03210b00e080d43e2100d0010040d100420340c04aa0200103a20520300040104840d10605500b40e0301c3c14001030700940608890310031200c1c0f400c082c180501c400c1d0300708001e06078449249076019aa4500118864841d60203c0744141c1c807a14500e003c0354114200a01004600d030f00401100f91840f03814010542d000c0181c4560100702558403003500540c0c000184114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 730178471 1250 730177221 730177223
    0x60c15072309130627110403050109290c0a020304030c0602060403140c0c01120f020304080307032405090711060a0603020114090d0b0c0c190204181709010c 69
    0x10841c488954074076110003004082d001401c49422060304081c0300340c4402c0d103104d84103031420a883c01c41c1000390100c40042e240c41c0455906400546484011041000d541040c0c2058611342e642d44613150410480c4030f03040000c20050855074201780b0388400300c007118200043c0342100700907010940030761080c020029500a15441605540c402d0380701d040c003e40d1500d044400340c00103440005100c3d040c92103182150889034081c4c0262142c00c0c51080156100c6520303801198242c1e9643c3c90b00d144000d860302c00f450003103120304603160740c905004a000301030b02d43c11503030f02100c524003c4283c0c4c0e01c149040e5043e01150000d8540d0170441d50340200c160f80d00031030324258100310300549040000e02400c0d584010180c5c3d100f40c85000451940d010103c800e40134040c440c0d500400903241e4000031808111640754400c04842001d03250196641d281d600305038000121114401c9108907403c21403516000d2040c14945600059081c410305880d01d5004507401241c4003560f440c006101100c50b4452400300d1001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 730179721 1250 730178471 730178507
    0x604180b0d030c12030c020309010e0a081914060c03060d06150f15110303010902070f1203140106020c1005031f15020f242809050c060c1507 62
    0x25005042c06000c1680c590030448542c4907420714800918001e1041c0401c480207907009600b000c103450019224810140d0b004c17135010764482000138403c0410040c05d080d0700258040480c40041506e0581035440e5000d40035030154121000b00415400440d050303030b038040e0007100c140320cd640a50a02c540100007140340f100c0c44500c43c4d01c0c0441d44c88000b8620030304a928003603020b2650f01c0807500440724480484803800603034008100400804100d40c014148843c01001c511840945650f960b40c04110390280d2800400c3c3c4880b00d48444400200c10b8500401d154005040020308060010b15880d510300204024003a010011903e130381020f2010502215402d2100441103844054510004842403080c01c01072007108103144e203108004c19602103c105003408683c04550540c0b5088028000620304405110140c080940d0300c80d45201e100d510f0010480c3c0040c80003401c0c242107042100d000b5415016640802c191501c007003001640c26440314206071400703455100c0702e83c1254100850090144a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 730180971 1250 730179721 730179739
    0x190507080708032802071e0311060a0501081204050607150e010c05122805040809040c051e16170d1b020f070303080a0c0903120210050a02090604180b 66
    0x240c4055640181c44c4070505221820030484c28003091000c1e0701c01d41000605121080480e144002c2c2103e009043c103512900b0400341d0320000c14400ba25203802102c0a40110340c6440040009140034230101900000b01e85005107058244004183c003449130020023041b000440c5807410121042d54030105101d44010001e00240d40c0411004102d40c005900d1000c1c080404404118600b0203003050324a1082c00541d142006080004600000c00e0000d0040c0c1ea26402000920f0140d0380324032a00200322100d8541d90380713400501200c0303030b0030440910020803620010040c0314050016070503144481c990004104081400c5850300d031220b800382c41d801c000c4081c10403e94a0700141080f160a145007255403c1b00c510811200b01c0c180c0d541028030025011818400224a0782001ca403c00c0c44220340340d0a240007016a40d94031540a444e0305a40e2000580003000180154000e6025264009111a1065080c800b040c000900b85115078403443d2901800100c01c0c10481d14140c1040c61000001044421 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 730182221 1250 730180971 730180981
    0x301050a0902040e0706090501120e1615080c19050d02070804181407030b030c10180506030c16260703030b010c230717010b100519050708070803 64
    0x4040d20341c01c10102c0c4111300303021407007a03c0900001c8800840d511652100c0015141c00c0054036103a0700022841a260744a02000230030701c100f00700085400c00741c0a94a03241d640f401c00c080c040d440740300509c1020800d9074130900041c003030200700717442c2ca80c4101800640e42e0009420141c80601ca4200402e500130b0001c204d14040c81038800152080340d0f100c0300c05540c142c0c0d1a0301040e00b100d0302815203e216075000d030302051450384660f208101041e030240848400c5949a000181c140c458610050001401d03c0003401c2d2048034011030100804098603c141141014251280240031711800c05420442420500341272005031f41c50b08600002c45100400a44034550302400c841c3e000020540103c1e042241020b2954070841e140400990001c0c1d50b20004c402d82c43c14800140e9401584016070300c01c400002c245102200b5040b004001543c000042c0940d10409000740b0f040d8150024083c82410b001190721241107012850654043c2e10f85540c0c1c41003070346000c000f81d0059880242001c2c3c004002c101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 730183471 1250 730182221 730182241
    0x3060e03090f01050a08070c0f0f050d1b0503040306150f031209270509011b02070e060f0102060408030603071a12010f1208091c0308040b090303151c02030105 70
    0xa0700301e00654030103498021800064506108130250100051498000140e040388105231008102c1e00c200d460341d000d80d10b135440d144c1076480426010b60b81038000010401e2401d4100210014103d0f005c56003000000103034880d95240d0180d88409003260b62629040c1000da1040f12800002c0c00302e000300312145a480382480b40c81d01d078004072100040703861941c0105580401095204d0358411048056040029821a41016000c0502224090b640303035020003910103443c00d0b8224540a003540140543c1d403030601c1c070700c0c60b0030006400540182c0d0090741851043e60b01150a6500580060111b5643c0d11841c000c00d150080660000901080b4048050071080c1000010481d0303020200b80c4e0750543e41c07a40103910b940d810903c03501c1c0b0b4507140000c0010001d1224000f81ca8050002030483e142e180d040c0d04404541c071091501240002c1d0040300b00400c0041000b0303442e400c130811100542c00c500e8142250412031400039150391180c0022000214100d51a0b001e40d0382189d400380c0207001a0400c1002a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 730184721 1250 730183471 730183477
    0x120b130c030c0602010e010510060e12031b060609220c03080d061e050f13020d0e340522060603020a091e060503070513140f0402070b1503030403060e03 67
    0xf00c4015420200c2c0340b5a1160140113103806205610306000c01c16107030400540716036402e07002d15500440c100b4400035562030306201818441c0401d0034216038140a0710f41d51070030100000d210f58400d0940c402407025040e40c50715401d00e40307450366903894110003c904204c81d440900b80d03c010a51400050003414002c801d030005011220a1510384c0d6144000c1d0246c410001c46500605801c20318403842c4131840e14002032110920b00000030300500c0d00c03649040080555a02c20140c04d1582d2000012000030345908000301c001071076024075152034100144007150100480c1c81421f10400307591400c468110092065403c4000300202c040150642da0301000d40a504140c0c03008000c030702d6034000041c03050100040394001c0600201201c041d41c2c2040c005a07842d40000d4100c104106090050f06104543e1002c5c2d100a0080c18402d04050b071294400c2048843e0300d064001c0c0a50f0050240c0c3e0006048400c01036003190b00026035400b0354444801081c658002c0303a03c040c00b914200802d4400000e008001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 730185971 1250 730184721 730184729
    0x141305070e09330402150f070501060602160605030a0218060307020c030607050403020d080d11040b0702040605010908060415021c050910021c0906060905070807030f06120b130c030c 80
    0x502c1403160008244810801c007002900b8511014400094010306d40a14490f0345490b00900550600500384070080c0c403034001d440c00310384c1b0303a566240074001c07280c0421140b42d1000b01d12413040d003844d007041030081c001d000207080d00e02d2403a00070405882002c0b0007500403011070f50140c01c00f80c60b49403850000303590f00403a0942030b029000742e501140980b132042d000c90301643d8003d020301031800044d60780c04c804c9910580d207072102c95903030b03000c0005480d18100040000f80f0500d06c1043d114582801080101e03a180d600c05070520a8010040080c2d0602040e0ba070340c040d42044061030321403540d010400183c8241e007807800d0405540700c42d9102c1520298403c038042d1240c0310843e1155040c0d825441c04910407940039500c0502d142c441004084107a030450510b180c842c41d40440d285a980c0e48280a981d02035610402194042c010440704d140d2500c20485e89002221040c8415494001ca413082d02e150250041c1643c2203180c00128010844410ba1400b580d0141d1001d01c40da5581c10007884c0c100b81802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 730187221 1250 730185971 730186003
    0x40b0105030f0309011b020306040c0305010f050123042c06060d02010c02241b0c044d190f09051c06060f0612141305070e09 55
    0x3080600340010414440c495100c000c5142000380001581e094410303503004d210b0020a01107000060f2410b1041c94004d42c8200928424941145000c50035508606c0c1417111503460100100024111000710011041550b8445c950340c0183ca4041005000c1c0b030418000d040c25640610940d2400004e6024842c030031132401e40c1c1080e215403082204507002c00c4000782c001074500c130b103070230151810420721500000c0f000050200c50880d941a4240e503004200145d04248030400c12034640712081c40701e4078441c0b0048030104a0010340380c200e850410050402081e14401480a02c86102d000c5074030030600030740300d505241d2a288001c01000099202c011050b043c10862030b1200e5010303004544c034601d1043c164480080c0e040c00c160a201d0400908a411145110100841130224000e8440c0320040d105a14001880700d081c2000a0151060068040460351801e0b2511740c00c08440311085820154610416005052b1030401910340113958104e204002052014000300c10400070b154285201070103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 730188471 1250 730187221 730187243
    0x60c040f060c0206030a0506130510090507051c1a0604080a1217010b09011b140601121104020d27020a270b030f0f0c1807091811070b04 60
    0x48200d0b040502e00c0c4000390000710038000714554580e65048030341c2c05030300508107510000d04800003405803682965803540e1311099140a11840c140c86c01001d80c0014241040e503e048071040d0090f044041e94140380c110982d9039608143e0440501444030251301e40100f510b030303ca0382c554400300d444030300d00340c0c003150480c0011030340c0c05000c0c0c004c95200c101342c6000082010143e29105a04409920030000f81d41004030022204511001d40a840d11015002d145401c03829081c032220b00303103001410382100c920380b1000c000c41400604420f0103904441c20035a0090388a0051070540d01c05000c00070100000b00c3d01003200ca044c408480840088194000c85d4039841241e680c01c03c0c0c008013001901d0500d030004e04065410804006a08242211b09001c0c040342c805510440146080070350412060744141c01c11500c9203054074080d508100030200e40cac3c42045d81414000c5018114211074031440c21051643c070354410360407442d0381c402e5042d0f1b90180e80050b65100f452614561904085030211962110b030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 730189721 1250 730188471 730188479
    0x7081203010f1a0a1805060d0c170903160c03080a022b1202070311011a03010b04141306091e031d4e0714100f030e060c040f 55
    0x380c08803201003d101c1c0480c0c6030005030501200c81c02c03844080d100085000c5800000d0f503480e03840081c08004811140003841103031580c0000c0076100750546810518031140140241508044200d0301181540c16801c0080070700341c07910761801075041d8030207458000040b0b40710403855000304100201c82204045441020401c8004403030381d0020a107181c0c000b03206400021030681c0d003039005011442c06810f018464004800740242950b03c070058032003007594054034490b600d003024000c810f500d010848080c04240c03120010a4403288005040c0414404050b4504e010311803203510030781d03000f6041a221001e0850702c654105e03041d0881c2104800003022105921141c030503425045464102c000c10110b0100c00000361030071152202070075201070050f01d00c1c640345900c080c400c1c0c50001c40702103552420284900c3c01220300700f01007940008000b160701c00320b51032143d80d10b640416104010b03007450100b0403150101100282991510f004041c03280c0024031940d44542d50150045907052003008001d1512 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 730190971 1250 730189721 730189739
    0x18150f27140a0c0306110c010c030b0109050108041a04080d0501061706040c02060c0c010f14040b1008071e0905090c120106050a090f0b1005130e041509020307081203010f 75
    0x40d01000f9225140d095803d20020b103050f04200c070030007000200c0c0750810b4058034401c3d0844080394040004250348044100d038075600220b116000384000d003044a01c604d4580c41e8030000804051001d42c4c011000c200140401040c03805681040342e251908000d691703182c0401502240080045010f03c0d610030001515510f00303405500c0565242d680580306585900805078403a03009004200501c1d5203405440c0451001841421030151001c00300d2101803d144c2041e072100c120160003010320350031482080c8852180007520744110b4020010212420f8454822019006d0460708455040d508060a00107104000500d922001c60304172120002e180050020f6800c0324154803405401c400960000c001c0c00e5440d500074151088a000c0201d444484140095030814138000140c01080000c280710142401d219501000b400c091206405242483c2e11006a143d0380e502c2100481a11545d051045460030b000517401483d40170111038a40c2c10003480d81c075a503082401910024040d02e9070002e03003801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 730192221 1250 730190971 730190983
    0x3092d15090314090117070207091406090a060515340302100203061008090a080307091a1201031509061b0e030a080702090405120d020d18150f2714 65
    0x2c1611240746c50407035000c03c40146000101100d042d400354000004008819015200ba0b040648046200c2450a00c00300069100050b10001c082071a002c424001ca0311070405c1880003414881c545602d50395900b4165140c250000b85240300290841c0c0c295801c480020b6102c0713203492094003506c0e102c3e5001d203100b004a010846400368402010148006d815004180f5160403403003031001d4407412901502d5000d01540b09642510001e0b008040402c0108800e042d0418100f10522209240c0386480060000c60041808081c21621802c8051240c1c05501d40c003c039119a8003000a01001f50400c800d040600c0d6101403e4021801d002201112490701140301803240d58840021401c120190302805080c0b030f4010012109403041c0010301d0a2a0451001b414030349030341c036001581d5482540c503c0b0060311001368500441354001400c420020300745480001d600d010308240080c100002804405c0030307003560081158240009008200400454000c10601c1406203501a80001c0c5c0c003034403c0d907285 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 730193471 1250 730192221 730192237
    0x4021b0c090c03011404150602150106080408092b03080a1116110d0501111903050603100c050f220f0b0306060a0e030f011a0103092d15090314 63
    0x4003c100511a501c80c101c0b1303680480c040600006204000340b00c10307502941d003c2c2c03c078002680c80003d424200c00c200511080c007400f41441c200c112401c0540e14284240525001e051080d40c20780c0541c151005400000300e504082440c1d00c4000e8400d6040140040c002591804500360030b11100083d4880e00b00205c0c0c0b80d8048051440c10105016220300440050602100781d0100000d070085006c200c090141c6010001031560300d03070f40c03403c06c1e00320030911600b482c442c02d06150600d020080d8a603004110510203c150f40d6012402240380c9008031607030302c01c45c00d000302040b5003c036025130a040100125140440741c1e01c0031012043e01c4440349103080c0b459100f0001c94420030800105181000c1c0c024203500b1889040c132100b94541840024201088000d60016583d99010030a0701d05540314421000e80703c1c282410424400a40ca500b01d60204450342c0910040b00c0b04000604410344582c00090030b50401154038811003014802d40107010f0802080e000150300c07601210b003929024044454031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 730194721 1250 730193471 730193491
    0x310050a0e0706140d110408030d050618070e0604080708011a09040f030e0a180c080f06060d020c0304090204080d11030a0815011101050703061d06010c2004021b0c09 73
    0xa1303a40008000801d501248078040c1076900c4000880b5041d4428010300041d10844e03001d03603250401403040308102c0700000d011910443c0c01000c0e410b02a221402855000400c40c81c0c0343d26400e69060204401c1c2c4a140e21240d101d202d031007030010340760b10103511110b1136041c0007884800201c1d07a40e0400101c0c04040e038014052810400007180002e00682c120b480703060000d042c2c0000d00e55201c0054400c4603841c500359800580700d01d4140009a071254610390701030500c041d040114186000420081d001d41c80c289500c9a9001a24074030580041059038020b00c0980d0f0251b40c1c03581c0340d1041503210046c3d01c100e180030585c2d00e100d1a201c0400842500c1100080d6541c0d0080c5903551071040708003414018035541444412007040345100000e0091611540960300d0200b000c510300300740c0a030380070340024280d84400d108000f440b040b40e0340300c4400b0350303115000f5800b003880e2007003807100d4540704000d108000d91280c40050280d862400c04102c185c2000c942c02c05680020b2051014411003400440e005046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 730195971 1250 730194721 730194737
    0x1f0b01180303271503050f24010c05010b1f020f01020903060a18021513050102011e09170a03060e060d050a121718010606050c0a02100e0310050a0e0706 67
    0x62221891814201800c081c0e004480fa0740d489003106001020610510006602e50f002c2151800c074880005d50132040c0405804400000e00e111840d043c0c401a060604002c102402403042c420250060710001c4401080541c0d4072048440d4407a403e405447c00d03001600405858130303102c0d6418802d4426440d00a0060141a0ba440441d0b2000b044055600540348c1c044c07110310005a103e007034199004201560085654104a81300b4944204143d0700003811681096060341604481c00e0f07101d0030401d080c00c004104007183d49802e4040f40d004441c11040f4580100d11007048a605411020403101c9903050040b40e43c850b00180940d5008a50700179200d90302103151000040c0c4400d1074521404001e2034a2200c1e40511407615504210503900c203003044220f0710001003414828400d0798000c0090781051458043c051101645610325904003a128000c0c000000407414001c0c0c0100010f4a8001c066400441c00c0808031001044180c0f05040c6041c503018000628a600186003c1515015150101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 730197221 1250 730195971 730195997
    0x61203080702070e15060d1d0111070201020c09060402070209071806030608030a0809070503070b0702040b060304031b15050708041a0601050d1d1507020d030b1008091f0b01180303 79
    0x217100c4540e01e8290b0b0401010849404010918440e80070918502c1000381150504c44039410b003034844403429520b01c2002044480010b0380c00140c024a82c0c9404d881079002e0795034400001d8024081c0d80e10107500703c20703074038104502c13268024480456068030002e03561400d1745a0744201c00311402409140c010f80d0003004560800360044a12039484034804040b506c20644400100c1e00b000e510354030154050101058110862410b8080c0858031071054941909502e45074500404125414541814082a1280c14803e01440f1041c641200b4400c01c000d003c5420f0114000f0110320085809403180030f2004a000c41c540c1200301094010746050b511203003002e590078a600004c5c1000b290360280911400d481300504a001d011805010030b000170819032034548144041d08100b40300589104152030300a58062175500d8641c1001a050a03107860301040da1900c0140749003041c1500501c000c5041c4050002591019400505102e0020381c0c5d50a803c0d1002c0901b110320600b1400018081245054544 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 730198471 1250 730197221 730197241
    0xa1104061b1b0f05030f0303100b16080301030308010512060420010306170109050706020d0c030e012c0f010e0306130203071a0d060b0c06040201050a03090501061203080702070e 78
    0x420706000740540900540c003214400441589540000d80f020a640800c005038074080c00138040102c0b04c0d402440c51441c01540201030103049014030708903621f02240302030380c0d040d1403802464a01c0d4842e160b9544d0b540c43c0d05015040b000c0910a142c8110005400c04100f00c3d070204420307000715444000c00c04800d0311441e6011060140c08007240c1019a114000030f0480c1d401c480b0100140710710307800040c6042450601904090464001c00d00f0756200182035103409901c007003081c0d80d41c1c1c0c051030005220008240103d81101c01c1a81101079402c4a0040405140031601c01038402101207072080c02840a550043da00c1400c0600c03260742c0b40e0014800200c9146500007090305d540d10050641c0d405549690300624250030950340c1d03901194000c501c1180300000f40c400da0f4041c0c6002d141e050300b80840d405055580341d0700100004d04016000c14040e0209000c2d4004503180c40e800300c000e004503a120501007241068501c400c2c0d0020700c4c45004140c0b1b55001180c6501510b2208d10300040f941d0f18a4004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 730199721 1250 730198471 730198517
    0xf040c080307151a0303040b091903080405040f06050907270501090e090a0203060901230405100f0b10030b0406090b0d060903020c06160b1605180402160b0a110406 72
    0x13140703034a401d02d400800c032540c0500092007c0c0c8001020301e0380303d12405041c08081c0d00100c04e0800200303044d800c1400480c1901041e00e0882e00125000302c0e0441035002e0788809010030380e02060b0414559401d10034215000b1411842c1058422054210300711b00980c0d90080c4100c61281d01d001c504403890502240140509850340031500104807500c8a070310f035011901d002c104840025140e5900d20f4903154481c003040e11140141c250540c1c441241c00c290703c609031210f03001d200c003421003031703803401c0b100700d140001d402003118154010030300301c450b20308110040c015003003054589100d6403414101050b8000e5038030404078110009016030020f4401962044000c207030303620342034095105044410700d1030741e1000010103001c01c00003031800501c101e071301d800c1d120700401900c04c41c26546009010f0b0300c0c40d81d100080d90004c103502c1c0c80160303100002c1030100c1c0082c030406101c45103443c4c12070500c0091104a82440c0c0c01401c0c40e803804c1220710440c2407161740c42d000700e001e40b5002842202009a15200d40814 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 730200971 1250 730199721 730199741
    0xf0c090515041e0311030604170310030c18060b0705250e0a020a120b030d0c02010c050a0b0609090d0504271505030f0f150705120f040c08030715 64
    0x20340d28254450f040d90300000703003014010040340c540d900c0600400018040c40d4903900001c1c0c00030324071801d01d566100020004241d070504980c00100004940764401e51006c0015900035944860080d1200c0100c80b2641c4076800024005051200010301d1485110031a58142e4002018200c003210400141141ea000d40c0181d051240c900c42010881510200a56000304006400103942d2640c121000c0d0041103c50041c0d0030680c90303c843d1b04c0c026140440e2010007000c80f807810401e0202144010f07078107180c400202070514401d4040441c02c22403440c07401e03805a0003c80c4c400340b02d0ba54080010740d81d4503e14403903200050092008100c0d044030103c03d002d4106860300c80304099500c5030b494000711011405800040090008100028207040c40304503800e50909001d044030f6500e403a0000e0355a0a280d00e80400401d0b00000a4010f0b80700d80c003610b90b03c22001e0100f501c2c80c14403074501140e01d5030903a4141c5200020003000141000e0000844082170b078010b441c0100e240250042100070500848 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 730202221 1250 730200971 730201009
    0x3080a020f07060306051c020a0302060a1412011406070c0b0313080a03060303181a090d080c060106080a0504051e07080a031d031501030b0a090c06050a030f0c0905 72
    0x512101c00d042c4214000b61000d0b81d0300089262034170040290862040311074005d10306107103a4990241c0c8070090284c060f40e8045d1412136a568000404a42055002d60000c801b40800300d80c503910910040d14546c108e98107101f25010040c0b0510801480703100f041c07001021255011810001050344801644d0301c81c2d254101882c401e0019143d060b80d50348a200c1290000c1d90f100d0083c410160000c644403504012800b01007143c1d810030010310f84402100c00c5502c60140c0c0407035a10450354455a2110031154003c400c680c840c00440e95280e5640b00038002c0d540810003440003e03403070382498841d0a202c0c0380c02c500180b41e10f0842c00450058801c050240d5180c1d4043c1711804101c8000401c0340030b0700c140c80f80c1e40305260303041280d81c100018003600c0a1544290407042c401491000c0e2050300c0c606490700000b2200c2035440304104100200000f0000030310401c0500400500c0e990018080c01d0302c0a030944061086410b00d650329821108854064008104003400034003450600d070540391f01c0081048 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 730203471 1250 730202221 730202233
    0x6060907031a0a080f0d030507020a1127070909150611070305120c0724181802091905031e070b0c0d0f0302160b1e18012403080a02 58
    0x20403d004540d8000400c1a4400d00031070303401040c1080034407000d004c0c41c0f6041000d400e00c2c090003519000d01e204003030074250000303039000a03076500e00f4007d4a907042c0079012021032400c2c12100e4a04410111580c5000c40c43d00f000010308640c06002d01015100307074141c20b509c02d505054054407000411000d0b02d9035407080759030100015000300103001102c007003032203170680703c03150646843d00d400c4143e000312184862030000c8804c00c1d00464403407200394444c2d080c103010003a01400d1a60b1854003550042c101015401c0190450403242d500030402000141c40750040e011224070f040c0d40910b41c600c01c0300d402d9440f59000314010b45d58410304c0d14080ca003510a8502c05507030b6543c552000d0f084015410000e801103280c1c03450f001c2d040036205164544908003581855403200d0200020207500101401a480160000d400800700c01c1c00c21003440b4031560903d00600300b18000c0700b02d410071240c03c04215031808140f00001c02000302c3e1500f06108414045180a0440ea24180280c221070001425440740c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 730204721 1250 730203471 730203521
    0x903090b03150d0b1506090a0b1b0a061505040e07061b080d0b0306071805010507020d05060f010f080c090c07020319030c06050f15101b0609140606090703 68
    0x40f00c5010b68540075000300307082c82c00d104c00290380020000d820948510030030451414191500007800e0120741c0b100b480076442d00c0c401000c00b1400e020060320803c40780100b00d26041027001903408511481146010356582a0700e40d0103100403550054218001c039070100c070081005603c18002428215800794072081c034105181e54921325174001c104d807420080d0f00d444d050b84190504018640e40421203140420380c17681900c0071360400c40174600686041010008001c010354840d00c4500d00c100740d000040358020720f000e022481803003e003801036046a00c00364000082160700016040210100200001d0850703c4880e000b901c19440340e5012178041c020840d0070044a4442c0355495445800703516080000d07003117883c0400403503134028020080020004184143d0485200403007030000d109031600803c0405603581541e121032044102049100c0d0345000d0010041d03203404c14800107104200b504444050b0041c529240d030411115180c1001d144000980355900c2030704000d0743c030520050380000740b51030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 730205971 1250 730204721 730204729
    0x1106130b0a0608031821150f04030801140a030c09020a030608070b04060e04060e0403020607030c090608010b0901030f06170c03030703170c040302030d0e0315090c28090903120903090b0315 83
    0x18513246c1843e80291804400c2000341413801540000040318131501803400ea540940204018092081c0030070160284c030405844103100e0034041d40d0890100240943d8800094006e03500018181e0b002a0410500040000000456500385d0744d68024041c149400c0540c215842c447c503501541e8450703143e00c0c1c00a0281c20008120340941c3c0280c1c00340429141c80140070b0240e88211544c08200908101c00f084401d0f40100307042d0540790510000783d41c50f608000102c1c040c100e04404d05a0691400100054641c400c0b00d00051b601c3c001800c0c0c9040a40c1e80d007c158a034010341c0c4014000c40c000b080000070002c0c0048503140c4c04401c07860000e0400740c8a4011a00c0c01034404400e07408079010b88a8640380b80340400c4000030150781c0a40d41e165500d1700e0347d149501c40d5113030340d0203a008101c402294000012209001500400001c1b000e10a03207903980070b50b40190034210401d80204001002c5214103010034064031503615050788034142c03464a060760241055000a1500c180ca00744482d98024641d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 730207221 1250 730205971 730206019
    0xb061308030702181911071a07020c09090309240f07020909010e0d050f040e090303010617010e04020d08040510110f010618020a1106130b0a06080318 66
    0x34042000310340b114998814000104c4514100c1505500c08a0400810050b10228564003604c0c10301c1c00315480c013101101600b071b07004940c4020a1606a10811601840b8150450303102e05850703403c035007600a6074010b00010401c250341c0001240c00c204004121424039041e058420001400903203650801307107840c0c003025040690f000360078013000600ca40961500b0004160805003040c000c0045100c9452043c1d910401d1071418024040089511196601c80c00160380062801c01440000c500d052541c1d5a180d074024003e000c0031a0080303401800c0c4240c3e03510224145e8980100003801c0b52503907003c11480680803103040316000800c10021803180c41d804a460070703050320750303d0f49140c0444000034182400440d03c18070700c0b41d81c03405d41c00304203800c82e0680c0b8901000c2030340300043e07485085140488101005800780c0d2024170444007803260012081210344499401241446c0c1c03c0d868507401107080d40c003140b044441603441849420480003000e8800040c0344030042c285107010903151a01d05680c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 730208471 1250 730207221 730207229
    0x20613060806030c15070b0a1d030909070309050718110c01050411011409060d0b101106010905100509090c041a09010b090105042606151f120b0613 65
    0x90100010b0009a04080102c0b007142141155440d9002c4900c544004080c01481c034080c2444c81d410002c242410384541c032035820009500301c41818640c0350b82103103903030b83d11500d41540a25040c0000030801c921074820000c1d6150701c0400b421a4601e42001200c02d0703c0c007191198207550f502c40c0500c00b09020b013002022441ca000307001088528150411501c0785418800440c1400724081003925105414011148440412204140c940c246e5490041c01003075070840340b6070003000000320701c03117050381149074805111598011905180c0c0c0302e403446001e90b1000ea540b902c0f008034060050085103440c0c0a06540700104408171154040d6000001b030070b44a0b440c0f2000b0a4100b040b040a5807030800d440300c00e000d000d10311062460700e0440400200306206a10400b080d01c40d800485035804041c8038010051100e001088920701d0030445180e640c0d0200d0010f115129004030300d900c00c402c0741061010000ca01d001e13107890720b0082218600c4805410240d80c0d9070b50015041001035031400010418070003030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 730209721 1250 730208471 730208477
    0x90106080c13060f181802070309080a030e0a1a0d020702060d0617070f0f09090201051306080109060501020c0d080915040b03010812030c160f060f0903080115020303040f02061306 79
    0x10500d074804c05000d00414020340d941d80554818144140200980d9a100102c403040b0016960003803800d080740c0c91034080d00070380260f0080b840f048045c190302c401440d000381c6040320954415641c1d609140c650720b649c002c2046e0b01240c01c0c4a00080c0c07407040d9028141a80c006001185001d08140040044a14680150300340ea00000b0207404502c80800082000d0b1180c03001e00b416503420404008103032049032040031032281e22410080e046904ca00140ca2064558844070084e8640ba0440074000310310900501c09440d1400c8030001d44c9602c0000c244000d0440507010420070320f81e9881e100416400b03c9155500014020160901a03443d24014801803400c0304000d0703200e505005000341030203071001030321142001c24418040048030b50000c40d10240c01203080220b506c00c071440c0ca804102d40c0c01401602c1039180c030301d1108030759046802200c0c43c10301c00e076141100350381c841c40c1d58031800400310105001a0720620000e4000303034001540d017805070300080400d414a40751400704209070120b90000e40c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 730210971 1250 730209721 730209737
    0x3200d0c0308060102070807050d02060408060f0118050402330c10050108060103050d05030403020c151b16090e2e0b0603060607060c090503011b02070f05090106080c1306 75
    0xa060b400381015802c18000d20141c65181c1c6400c0c07400c4d40c2c6031114042d20b40700d6055a64144119510581104d00501440d000c4d03886074501022404401002403280c1c7e010041841c800c2c3e840c00203d07108681c425a401480f0b4001c2480190301a030480d070412a207804a1a915010142070b8120b5a0240661070f1402c80140360b00202e201c40e02c41070300c0044e848412140e104900501c000752002c554100c02c03503610301d811600c3e80c1c2e0380d0408070300d0102d2900519800c0201444c002214010030401006148003200400c601c0071402603040341d58240d240d00e84500c1000300c0c201803201c40b4007034201d0201a14800216420403e00714103104490940796809030314100000881d80c042c42d0180500294420119501c6045181170030101c0c2d46441106001001960340d95032022506000d210304401512001d00200034500c0450500c0d508000e22809204c00341c8607040340060240700d084012800d845025040c010702e0b92030304e14196050000680486c60804080c070490b035141c8000001c0d080202961307668994 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 730212221 1250 730210971 730210973
    0x51b04090b04110406051603170f0f07090501020c0d06022106130b0607060203091e030c19051513080f0405040f090515071715010311070c0303200d0c 66
    0xca54042403034800d0ba09044c00200441900700c0156045000c07a00019040b1203c0b900e01141e00500e42a114031001e840c0c03400317001e1400c80700300c801441640d0200030a0460b0325144419600c00480d4400c0c0c5005a01050450000381800c0300d10010040c030400c0302600f403034410b2154800d0740d010310041c80341149011042000c180f401c3c03540c50070f10aa00d0401081280c0e20b0401240c1a80f05000010b04426000004a01c84590400040c1c0070340f848401e451840000d1201d0417a00e941c0401480e0f00d0320310075403134599480150040a105400c0e4020000c10b003c0e22680840c3c06001d00042540c411100180c8001d000f24184030001c2608106444c00c40341d43c2d40c1008100021a40c03d080d02c42c100a1500841c2e2000410010791028059401c40185140d036a4640c0d088a41c070b000100c1082100c082741c814424a02d43d011850081100262021300c90701c030900c025001180100c0101402008004c0800c002290040404000d01c7c911400070103055000c0714407440c0350500160b4881b001034203a0000314 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 730213471 1250 730212221 730212229
    0x11180f010c0605180d05040305070911040b0703020a06061502060a090c05060a090612020304030c020f280510020307080a0503060114070b0702060c0301050f011215060903030212070b0109051b04090b 87
    0x2810017a50400d1030500b070440d00d48a65030b600a01860707203065034640403001004001d4040d640101440b034802c0d683d84001d0701d80251991703c0c0300c00072100d05040c2800401d0b03030049928190805a0320307900a144030741d00c0728414005080100c8042d2402145540701041d241c03a540d00804604040344ca500b50420b240010003040c031012452913981c0c1620510520000030f5011499001141d01210140004084140046c443d030341607402c0f110002c0120010180a520204030782c00803640c08403035020780351580c00d00990316441040303401040f0308801c000c80070440b8003071000755410490614129402042c00d100e44982a480b440044d108a02c85c0000c00010302c0e810010317190f02c0340108414038155403615000c10f45c2611190941030500c040f41880c0040b003a50341d40300001c04285c1005450041d6990003014028216a005c20b4005010b81494012000d004c0021180f030303e64044d003080c3d11a860101740800800002c1c00300100e40101c02400082200004041c10240c02590030010300c02c01048200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 730214721 1250 730213471 730213483
    0x61d01060816060f0e0f0a23030c060a05070210030b0303030103150c0207080d0518060301030f02090c07030503040b0c1b010609061a041401050c1c0311180f010c060518 74
    0xa203003088131501090800640c81007841d00110700c1610313494604038030200011440d01c001e0704425140d00094a81080d0007024400c0d500041b0015000e03142d041415201b800864451310a00c10007013501081641c005061031400b032000e00c55185000284080481c0009003036500c207920507580060202102c9102403400d2180009000e11800204110361070050a00e403500c803400075907001e101001c104103600c240b145091140c2c1541c003d1500ea42d1b5a1070346030080c90b0b010741c8203041c0d0182c0c18180001d00f0b06908a8100d440290b0151512400c580e52903039122030f00748005040c896060300500180c0b40c420884070031700549034512030000c0341041c2403080220455030540d001201c5060004224000b00b110709080f60265501e4110040c4440746400c0160340c0d600c11024184040e1180c11189070310090020551400f01d40740703079814001100c0030405071105028800101c61140c8014610006600c2c014024110a00701810320001c2648035484407070444108440400b01069180c00603882c010307040c0302d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 730215827 1106 730214721 730214729
    0x816090504110a02070501211a090405070320150c12071a0a0b0907030507021204030309030b012709030c0c06030b1503060d061d01060816 61
    0x30034501d600c22034003d0014010071402040d21741c410041d4011030940c44c1030000038001c4c1c0b040408000e25081c000068101000348070403140361180440103210301d00800c040c192452850802d82054541a00103c0c05d0504074454643c3e55590610002200c3c80200f03000e80d168150514481d1602c0c514030101c2c1c0c40d5401c049800400c00107071441c0c20644030041c1092302042d444842c07a0105640b41d48441c1032784000b40d0800903401d41d200e079001070380c043c03650302c115194010141c0072030030035501c2500180c3c00903020310800d0080c00f0110002c1401804401041c0c00d4032914940e41701203c0d0103410140000c251501d100c081414400c02c0c0d484c01d1703181c220010b20411591600007038010014040400c0c064481d0207001d00040700340e401560b10034003026160706451001c0f40e440b8401454140c20340d40d40141030944400014100340b15100207403011200070b041d41000d1708000071100006601c = true := by decide +kernel

theorem cover : BRFrame.Cov 730035971 730215827 := by
  have h0 := BRFrame.cov_init 730035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 730035971 ≤ n) (h2 : n < 730215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
