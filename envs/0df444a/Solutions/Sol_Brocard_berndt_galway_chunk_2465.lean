-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2465
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:45.255919+00:00
-- url     : https://prove2.me/submissions/187371cd-92c8-4963-ab66-37170de73856

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 443165467 ≤ n < 443345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 443166717 1250 443165467 443165483
    0x90f01140409020415062303070906030e0309130c1821020a0e010f09051602370f02040e0d050f093c010c020a030204020313141b010c 59
    0x640c0c401084000c01049400300e0300145c8030301601e101d100300060400b00402e0349485510400314035141c9000208034004005054180900c00c1c08801a03000000409584846c00c00088d221200b001d03062550180d0000150302401e200a2080300004542000d00f8400c40c07501d4180070440e0010007902e840080c0d000d4100441600c1081090b5440d07200341c00c070122030014040394030040c1c940301000d201c40f200341c00006100d14194800c22020b8264405e5036030285000c445414035200440000b91120170f0b080313006296200c412190746800a21164001d04018500c401c025451003c1c60181c90b50a4020416403090740360070000040c00802040e0305496000039a2003518148100030400129048030f012541c1188101070108000d1421010142c4020540452500c0348410140d008110341d450044a604010302c2a070b440f40140c841985650647c0d038112000b41c1c43c0d84e1210802142c44808200c003401895020210000060000c603024804c0d202c080070758251191141e00640712143e450fa00184290 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 443167967 1250 443166717 443166749
    0x9030403030e0415260c0f031f1b08060a0602010905030d09080f1c0614030d080a14041202061308070602031506030c130e090a2a03080405090f01 64
    0xc07070f240d030100049810f10315607032034619244e65038500c4010410070000003a02040c01d08180074601000302c0340d0190700c22550001c16600c00c80100341c4a82c8800d0206034400c2010214248058840e04030074017001040d2100803030903540050040403280290349040c0502110b0380041001441806802000c1d5008402585404000c061042c002c014100c01a01d405800380880300078860007030004c04107504030301501101c16505a52800031180160301403805510310f4036100c103058801181f25804980b060410791a5582d032009031001900d0845024600c3c0fa000c03a003007204100400313203280342d000216401c40b005a030311f0f072200d080503040c140400790041c10700340231201c00070b40590015a4041c49034117021009282c403c000ca5641d03001030f0b030441c20038003022584070030905200311500d0060001d00410340c0a4103204488548440e92244041e04501c155100100305a10304000c000b0070900c8800340c0f41400d031742c2c1d040c1100e085c1c0250181500c101880c6000c140048200c03200c65040e242090403040f000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 443169217 1250 443167967 443167969
    0xb01120b0c0a02030403020d061a040b090a091505070f0f03050c04050f120601270b090c0a110a0602030115030209010905040203150616060507260c0906030a06090509030403030e 78
    0x650080790402e01140301c00c0102000589996200d098114802e05001c50b180c4100c08664170510b0018a071103002d940340c001040003580d0b400f41041e42180e200301001a4000050800b07c000107401008201c0301e81c00e10041c00310031030740040181c1c0305001c01d40d00d220400d5102003048040d1003060320310541d0058140030500043c54002821390003070b04001c00d445656042003090a051034800d030b01c08242c05d41000c2d9450391b503003050100388500b4022020200141c0c541003001440c3c1040281c00d010401c074020908602d8640103055064101d0b803100c0403034840700007914003880030b54002d00070541040702075000b13000703110300038001c0d989500016140c03221070707900f05010300000350001082d20040d455010000c48098458100070a800d000303005041c4c00c500f07210304003c41500c80c040c002c00100070820410b081c89107203901c2c802e4010791091038130801646800202a00074052062803603446030300041404070b402c0c04c46d407080c02240c40d819818416591f41c0e8000c02d40307900843c40041c0c04161044000191 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 443170467 1250 443169217 443169241
    0x3020f0901291902060711070302031e01090816021801050607021003020415021b010906090b090f0909010504050f0c030d110307080415020606190303030b0103090605090a0b01120b 79
    0x14a9581e841d003c0c10561096681420342180e4440440541c00041c00e100d400c0d41c0c0101c203903e0309040c0b00c00528010785141c0c0445d5682c803069862202c101c2e6552107034055854213401c140c44598000190980b64504980750320b00858204004901c51101c00341500c1e041a00c500101d03040700c900515050030201c9907028810b20f40c44813001c100070141d080001080966001003100041d5080382d000700214a41c40240d60085080d1041c0d42c1e061080c213000801500340e02c241e080e0160348100c00569100d81c030400114214a6580c4426607018210108003c10340314158401d0303100d20f014104403140030701000681610340d8586400d0382e4164010402c0850000c0c06140d07441c001000e5842200d142c2910b40d02e540306260400c0c0c004210300d45c2e2070b0309610311941e810044a070300030100b207800c440b0694503403904440b4500140300003010706448181c2c019203607020b0341c4071042c81d581140043c041d03843d002c5001a2a0718030014102d5071403441400118510f6050071250008550040c07504903241c40300514041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 443171717 1250 443170467 443170529
    0x1a060304020a080f0a03090b030f01031407080102280c050303070309050a020909010510060302090a060f0314040813080609070e04021923060a09210803010b030103020f0901 76
    0x40c11041e070b00c00c00034646104002c0c3e0003180780c001c40a0003c244480c07034010a8425681c2c05148100030074001d11403500082c075000e50440ea480182c0361031a250403500541031110651040c11994404121895030120010140c03035424200504c3e01100b105c07491054170b030b4840845001e000e0b68028000a00c200e806540000002d5000e40c0c00c0366264000c550028021900454030703189103035100c00c2441064482c0c0c07040c5802402c01c50800f0b5041c1313442c070808a4592800c2e032059800304a40340e03400c216010301070362058401e41280d40032504d41d4902030610100a40c0300502c00000c04880440000d40c0190114000380941c009902516045240c9030b00a102081c01500991380180d5980c0304040d500300003520080188402944102c400c2660002794203551200010180103010400070007003110f0f84880d04c001500c0840f103e408074040f00034105081c42c0c03c2c0800082c01c691000001103003040d080f0000c0c6048a00c2110200c550b60452000d00034810000e114690030300c800c2a81d20503c20001c010011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 443172967 1250 443171717 443171719
    0x10c09050f0409140f1908030601050a03141e16080a05100803120912120f0a110d090605180703060b2b1104020c0d11010b040204060513091a06030402 66
    0x4203c3c0c0c1c4140c0c0b03561500d00602d5001950036130280c5211010b000b401c0c032141c0c881d464100c4040340228031544030101d461000812490400000241c2d920f1307042e02030b0780007061043d000c00c4c00102500c0c009801034240c9140b0b4903941003500300d8000081c000c458066030141c05403041d658031155a1259190b040c003070140505000d02e24000c00c100031660000410152a079140c0700c1130098440c1c01d110707000030308184044c040c2000d00302c0700304101d0800c0c00d07403081c80079041040741c2401c105a59030564000e0003014038880140e20a6800a0550360402c0399401a40032140218410043c40d10303200628411190084e5524443d500104010800720340c00303a000403030080c0c025040d4118052602d11503200d516041100c8880c40440001d140e0034001c162002424402090f90700314034040303420250513039031005890b6140070000c500708001c4005c8401c0d04140300303586000d8019900c564403600081c001c2c0d000007404240240782140c0000b0f07113415034061740c131240800a1150541141e154207104075030b41300401c26 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 443174217 1250 443172967 443172971
    0x2040e0c03120d141e0112030516020a2409080304080705060309030913020711100519090506070507050108130b0406091e0b011401110705371502010c09050f04 70
    0x702c213103940c544148901c2491346071403120358102c0a0700000902001030704249110394403030030306e13500003600081200c2401b1b00c503443c40d8000030b00510000748000e1094202c0342218505045007842c0d0710035985040c100c440a5110410f0030740d202e03031000d40e40f4061171045030042e5001101c10041401e1100003550001d9211091f6840d100848002c20040c840380041c6840050f400036240c41030043c02074180460443c1101d011560588851009003940102d8011000b600c500103248e01140e802a0500002000d01400c1c01b070700c4100b0343c20b1544c2c41d4001c81c402c540c04550200c0000701210308082c10892050740c0411030344920f4640d0303151040140b271001d8080314051000a039101e5661641400b4007105840386048074540d60404020303040040010f06401e05103c2c01035604000c118010030804107540d000d642c4c480032518101d0341c4072800c032003c045a0300326005c0c0001c1001d085201040b89001d50f82c2405400070001c442c000102d0898580c3d02900b0000741001c10140090326001301c41c52a003407001400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 443175467 1250 443174217 443174231
    0x81b070801020c03070314070b0f060303041a070c1d01060f0903020414040309050604050d0b04020607080a0f1709100507030e191104020a2a0b1302040e0c03120d 71
    0x480c0c1d0890380b165684520540c004601003040541c0403840f1056485100042c40c2000074a41e114200000c001d4510101d200424000507402c2d00d080060b14018250100c01170480c2c0c680e44580380c4941e1000d0405c0d607103d6500800400c0010309031040141e540c5811810341e00d16807030540c0407203d00307851003805020020046000400341c0d0b150b0240e94142c2200c4002c00d815400c140c540545071003016403100d40a08800d01003040a681e0f42c0d035110510360b40116500200d41d440d407001810900c03412400030b00510f03010034403002c40ca50041c10314040c00c41a48a1001c1e140320300c401d0100c460f208a0ba11102e0f5071180980656800041e00456007145080c180880c0703d03011440c0c071a091808209040d10741500c12042c40b428440f4a00c2003800002c0c0070745003145405001072005020040c4c04105018030902c2824201c050082c0591034070103035801805003503160030010300001c0c08246820090744224108800403104000c041120b02008000500812041c0a03480207010070f5080240900720460303543e01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 443176717 1250 443175467 443175479
    0x30c0d1e0215040b0d0e010b13050604110408030301080601050306100302011d10050c0118080a0f140a09050112050609060d0615060201090212060603030702152a07080a081b07 77
    0x800303000a131410700c1000392644460700d1184c003260440b4144100580c1009003a80d000e8682107595298684105001708240c1c2e03500011030017074008a50300b0003501c0300c00540017944007000b00140d81030311090800c1e60400e9903034504060343c845041c0d41000c2c0e05a40c80900308010341c050b03020300000413800b000b40000301d0700c1c2400041c184084800003001240c00010210ba44003402e2056581d40010200301d49081411501c0f050f0f018007901c101344086c0015541f92000d4603005100207122858410249507550325180f0004114a10ba1301c00d0f980403030905640c0030b41546180c018284200d0b00586803101c030381d4880e07042110508a120701620145d940e80d41d2040d003900c0c241e15107400380c400ad0700085100303089441400042d0202d4061110507802c404280062540c000c0300b1030b00e2040d011186c601c030380c4425042c2c80c3c02c64030415842d4001d10045c90250b01e8145000a86080259418000d9a12050b41d441106840e21034919006000d0642080f01c04520100c45e500b03000f200d00074008030391010792105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 443177967 1250 443176717 443176759
    0xb0f0705010b130e0f031e03070903050d0309020a050f13050a180506090d0f171e0f0103030e0f01091a130609090c1d0d1113060302030c0d1e02 63
    0x642d858001c1622070050413a4000304000c01014800345000441c50941c00d06141c980240300aa1600b03031444000001c10030700d92148111001440d00401660508880f0000140090001d028200d0040e001110000342030300d001c80d8070484036040035200d046140c0098000500902c3e008010902c0c05070340c0c000800703150200c040c5000009110340d0051000d4104140d80700d01e4101f0510100003000000c2030070340e0303a255100c01d80360040084c0410242154030786100e4210302000300c0182085084000c02048442145d11090904803806910340d0729000b4039540501ca40a1042e00101e4080b40c0f00803030400c03250918070116005032040807406c50614120314000107c002c81f9502120028082c010244104076a506c81c03440740005606180804020002e407240c0300c1d042c841c001a02c120000e0242005001421240210303070203000341302c075021322208809080244030301d0006038002d104003a58084242824000071004a03004095141411506080c99200a107036a4040341c2140c6141040c8806003108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 443179217 1250 443177967 443177989
    0x70312150909060e010b06030423070e09060718050f0105030a09080f041701020a0815011107060513080a03091a041d090d0c02060a0c03030b0a090c0f03060b0f0705010b 74
    0x2a030f40c0458138250381044c3c642074940503110746204080400c140000550844c41035840003240242e90021401d0040f115401d0215591014403d210b941c42007000c0207002059450ac11030050b19410301103d030030110056408018000c0d1500100901c650703070481c2d80118065540300c0d602c14004540f41a03541c2c0ca00415420440c0c220f0130740d200100342801003100111314843c400450324000c6080501c130501c002d10b042c034054050a408181c44110f14142c0e4441c20328a84401000703c11908065a03464000741113030300c2100b60300755045404002051074503010840c0103590742c05030b4034884503500705004848009107034a03954814030790400c80014100c010781c0800c02c001c001d0005800b29071903d210050304120b0030341d0800c401c00040305000001643d034042030718490061841d0004503251340d490258002c02c200c51580340e000216560000f40700d910384c0c101602003000c0d6641d0780601c4488100c05d5059813060301420b15a071006120300380f040c043e80d001406c180c901078400415001000c03c00315000e00c0d0340c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 443180467 1250 443179217 443179223
    0x403120806100c0203072c010e100504091205030c0d0608033001140303090d05070911190e0f0d11031b0d110102070b121b070312150909 60
    0x21408010440c0b40941160740000440d0030090810081c0ea40041d48a000d140508002d6045610b0007200340c410420726011f04180030f00301d000c0d09584956000c200140e0440350009600b018410115450030300380a1590b01e103500c0410b5038142c1c080c1403810b8400e9040100440c1d80954180501488a01c9034014100100012805150f4980110f070240c241c1029643c1c91039000750149011024100d240b001c1d0504442d006c40c0c1070841030079520002130a510500c04060352104030f21050704103105001c198202140c030400c10400044449445504040c002d0440d0450884107034070352050003030b000c1d05c000e50700d00c0c100521180d0341c0c1401350f0001f4404030988505840141481441149509003040704d80e60745404d03030b400c43d20411100400140801c591440c01044000da0101c2003d1a074020021040604140c14481d5145d6041c8030300020b1815003107a040100c080d0801120b05605540310481d40343d55095139480201414056140026089006150f540c58010b0200056000220b01c0b48110b40c40c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 443181717 1250 443180467 443180477
    0x50a0804030809030d050a021b04060503150a0b0f1c052119080c0901030b06040506041221090302060304170c0a060f0203060640050108100b1b03040312 67
    0x240c44400c0c5440d00c48103900c40005c1c44400c00450780f501d41c00080724527000e40d801d1496856030b11000c0106010700340d40e030b00c02901446030044450a048110700090310400d1200d0f0100114081d1a003005412010102801d4020748d000702c8904510f8020314014060500503002c4030305600c1000d020303580812490404110104001c103080480360f040e0030f040d00640f00b02d40340c400c099040512043e0b040703128020b005814181d960403021556265401590300505c1f0080030207031910b0740e83c0e1502d0000710baa000c2c2110070900d1000c040da8881d11421001e0440ba070341b80c0e40da03000c45040d5400d20000364000b0308260f446108445082d0300c000061001407403501d00b003174040c203001c0742d480c070700030040d12203021040c800750f4010310810040d9104c0c542030758a100802442c1015290104501142a0710a45c1515061048000c96a0b41d10900c84212504a40d002c4c2e80340d10780350391031810442c03244540b030044244c4500100b043c1c40c00b006a04031546823a8590304c040d00c0c6025541c0d03035004103041c204001100464 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 443182967 1250 443181717 443181727
    0x31903020606010201050f010902130f080c0a1a120c090a080d0f030612020616080d05100e0402090601180803130303080906070516030e041404050d022404050a08040308 74
    0x65050003055003001084c0028009414220341d2115014814010380213a15800304001c0c43c000351000c030020040c80c48080e8000004e445681a680b14001d80c20350500690360141c0c00243c2c080e01242200c5400c240c6802c00b800d1070200c0c3c0d007032107030000c0141c1074985900041c4540070320b590702c40c80b4500c010310124004290450400002074159045d209070a4203240c6410b03c02c1103400c007541f00f00380316168101c039201c3d61650445602c0500c021050806406130102003200c80141c42d0130340c401401041b40d6004890001d9549c0920449108101d50083d0050001008920154020a00442c2c1045004205c044454680c0c43c0180f45400680099030215070307021080003855000f2031056000004000a403020345489000034040d40b261031402544180b000311400d0038584903c012044e007100050042c0550003444032440004a000d031400e5031240203400c8001c0819000041001c402c000c021002e45080780b40c580740342c0581000410544081c0142400c090010303801030001c0c40510311981816440f1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 443184217 1250 443182967 443182973
    0x60f2d09240801030b070c1509110402040302211c031a1804030522080f060106030501180213031b081902091602010e1e01140103020607021e0319 64
    0xa1011111076050700794044416040c0c95001802c14103417504065000c20039200c0c1d0348115080d000000c0094110300350240d180b40046001d0f0400002035010784005080481030a04100481c40b680c1300003580705890b031901c207007000344840009200b40039070302c2a6401401e110000380102c202d40404600040d640390b6210155020034884a000e00609541c03501a040d100ca20458410300d0280000e418014085800300c225980262090f1407100c501c031445550555650106a66045a02c101031040c09124008500c261084c4241030481e9804e6550b003d082c24440035900080d400604050b403a0b05c80c007800031000c1403082c2c0f100d1400c0c58440f80305a294514007803410b8140024840c0030840b803010000400b0150303440102c6260011136243c948182400900c1c2d0130303030041c03e840003108064010700d410310710505041c0005c4004400160001e11501240c0808400b080e00c0c240002940001d052018802505110300ca10002c94844073704000e444c1e00550000b4500320140540c4a0a500c08200c01c13010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 443185467 1250 443184217 443184239
    0x31b010810030b070507060204210605090d090b0901050c0a0b01230105031909020310020d060501091d090316050d14030f0a0b030a0602220f060f2d09 66
    0x22004a01c1018800503085654402c40840040c0c40c410400c6000700b001000e0041e0341e4102d80c01002c0400e00550a917072000700301103609200c02001d0324010310740400241219800b0442c8206401d103980e844054034100140d02480390012600076040210510280d46101c0341000900c0c20140210003c021542c5403d10703558880e02c44844003604000c01840c00104e9980040649401100b0348400c200d0520421a00d41e0060100a402035454440c3c50100c2c1c0081c0f520b94000e00c840c40e0491414050592910300549005507680304094403144822081e504030300d8040d0f90355030448004410380f840d19890549140d4512040707002658030f50041c02c481440160040303d03028110b043e04028600314036062040d000b00701c80061610001310740392211507803e9501440841c9100381e108104548070200c0f400e413401e00d840d0c1001c4090342c9144100000c100f20256203002d0301210300d541c0d11078510102d00701c800c840032074200740c46000b201c035000c040340359503a50f200c0d03c3da88810640e521500118500460915 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 443186717 1250 443185467 443185471
    0x31103271203040f03150f0504150513080301051e0d050c0a1211121e0604110d0209070e0409061a04050c0f0702061804060e011a03151c02031b0108 65
    0x5142c0d07104200810900075500b03912030440f60859880c3c3c4a111a2100e040050302c840c10704102034624250410040101d20240d030b1200c5c84400c2010840daa80c5d800c42c8000c05a40414090040360301800101310724600034500080e0b5030746450440310300a54003400b20b06004551602240d1a41001d040040740e41030200700c0a006111800c0184180c0f50030f61611080006159421801403410303400107030254400b000b05d00e140a80842244038001a1b500805840d02416101118190705500074241c2c1454103200000400c0d40041a00125889403c41501c402000e061110f4001d62070f105182c0c041101846111580104407a201800c6a0500204406c07104000c0c10244440801c0c0007100195260100361211113505076403203950744c00283c214200711480c1042e1658001c2c2003001c0815103401d0465100e040745e031540c2c80b0100341d500c1c6603c074140c0d03408212404007004444040c850850706d40080303900b42600cae081c0201c0c3c208110540100e41029104a0781101d20074410654000395680011490303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 443187967 1250 443186717 443186749
    0x609081e0f0901032417071205031204030c02130507080907080d140f040b0c0d020109020f10050c06150a0501030b0609210607080124020a03110327 65
    0x51034020072040c0900d07280101403885040550b1042a0ba410766a100740310540c5060000d8800ea149607070301c41d100c8401e025203220b40841e000300c04c030014a50b44001c00041250740d1105c091810701d0b0504e01c800380301c00c0c0000c1040d41004600300100001d600e41c038480403a4003000d0710700400c2c0b40c94122805045804050700d965803030b0b4420f20003001031343c00205040500201c245042c1503520030800d803000e43c03030281d01582e04001c0c4000400143c5942e81c00e00804034882010180c40011070b08150580c202c901546c4081c0d040061f400940340c46207030040b07080e0303100c1c842400d00d90304003000074910620701041191107440b44552036140100624240e02c055004103400d203424462140c0d0000424030f07034065140024014100400450f400840c5564091607800035002283c6242c81d0500307000340b41240038070684840140b2000700307105001d00e003a055121001a50010803003000140d40c12a03020000c0c003004000749c0400d10808031a0100742441c09044901c03003504c130001c0c114240801c8018480302800c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 443189217 1250 443187967 443188027
    0x1204090c08060f0a0312051209070305070b0315040c030e0105040507060315050303041502031603180527060114070c050f01181419030b10050a050315040f060908 71
    0x9000140d444004c0481541c3d0b0041ca9000400074500c1c094440380161402400d4030314a100400c400148001828400c07280a1022901d8580c0d07100703004986440160f5004c00c1c1c2402500220806003450f0700419131071800c500d400aa504c80c100c44590840c0c20a4400f116603400180080000e182d05014960782c00074003035142100d0918010010b590b030300c03035440f4500c014406000c500300a00c1c000c1c010794494003070f05954501c07496140d280080c00c4400300641304158084035a0003143c941072003000f00c8220309455010114402d940101e2600044000300315504010100d0010203d1804460181601301d20455404490500301001c0140b5100310801450400225002c40d8a4801e40c81c08014212089002c45122008444010545800c072004101c804400090030001c00c01504011140c424010000ea02d00c0507600e84080190b4000320b0701c1003e61550028110002242d02e0260094101d445440a1501c0c1603050380c0d050700740e070041d52003500c0418020800d40103030009442c3c200c032038041e54a54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 443190467 1250 443189217 443189239
    0x12020907030c0537050310090203010302062203080412050601080a02091f0f03030807032901050f070f050304051206010303140c03071b0501140c0604030309051204090c0806 76
    0x80c50390042030f8040001082060a00c0828a052280246604400007800c0020050301c000540300e903001f03486c94550400e00c0700380010040d110303109913810303a5401444245000001000c04007065880b444450030b507540740c0000400603200d000280010041c0d030403c00090340e21400d055040420591000c2d0560300060300810050381c840c0d031301c0d540c001001c051801100c102c0c40004200d01c0d07440d401c8001c000c6880384010042c150844101da100341165a024043c1e20414081e008002d00404001181c00742d000c2108032031503002d000a043c2c04080c840105003404001c0c1c48000c40100846010f40e200c0d000000c06010900700041400c801010b40d200810b103a51450b54010405c46c05090a51a550030102d51008128018811076075016003220710503c403c088051441d0300402240b0440d03011850b03070348842081c980c8050070b50744018460801f41c002603450352410b030050401d94004032464080c490300744561107180c1006c2c0c4040d10910f840000e0300b88000002510592020780418070032500c0200e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 443191717 1250 443190467 443190491
    0x6042006031e130f0c050405160906030f0b03030409060303090f030804091d01090506150414150a030b0a021e0408031c020d0e0a120806060301030303180602041202090703 75
    0x100700c20303001c94070800d02c4070710703952a881e040c091001030300020550a061810307042400700030207000c4150752003180c2c100704c0c0341c48503459003240c058540c80034800b01d07500081c100025402a88080201e9406000101c2c0c030a11001c0080e003160b1198000700c8420343c2d0340809000b85540321030200c7c09849011030713a14801d800c0d504c410600b402a4420001c6290300c410170b01509103408c00c00000035004041c024840e41103507142090300e400c02100c00d060103030000360700c3c1043c0d40707070501441010b41e1b06003160a41a880c0d078141c401044440c200e03c40e81111203450000b0014a010305032521400025000503100d0300b200d40e0301e40c400700000707815852503003051105000903040442281d07440c044400c40d26410f48449411800a40500f06041d803581d40b604c02c02107215400810b1820205114841c01031208409020a0320044410349496400000c24001880024005e900860b0b03850011200744200c0c1d1000ea03a10340c2039034002e8000c1885070030140f00c45000c6007800303055160400c846060510000281c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 443192967 1250 443191717 443191741
    0x180f1005240105041203090504110304061a01050405040e07081606030f0902060d0903030608070f051306080a170c0d0e1003050c0a05160203010501090c12090f150e0604200603 77
    0x2029404004182d00000c170109070050314094000c0c01c0142081c8500141c400c0248603e400c01ca4084d103900c3d003002035441c050703404003460b01c00303400050311f4440c2807600f0b00007408010b004503903d84040d0712900c980440c00103003c00c252855180b00d1039064030b149040a00007001c0e0b40070ce514100516042c200e80c1001030340e607001035646103c5003010010701c4408905084003e030929034008801400354440c041540c8401c0000700c01034420580341d0303d030a032415142040454245200d601101d0701f100c07601c0800101b20003021205011001903031030810083d811040d00300b103030f40b0110b20b001c06da00d00252203141c1800c4800703500340c0ea49810108503626107032501030141d200d4040e44408010307001610780c50388180f0310050840c00360064000c000a68603110a0070003041c03000c1c264808264a8540d000401c0078a01455490f9581b2000b0848415200d40d0380a00444803605098a015262840e8005c0b880c405c10019120b0707402000c50083c0d00320900d52150341c4002c0c48514034007401c410401c001e0901101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 443194217 1250 443192967 443192969
    0x1020f0f06070509040b040c02010203061e0f0103020f0708040e100b07050c060904090b010b0714030a020c040c090302041a01110f1e120a050301031b060206180f100524010504 77
    0x260a0013a80d0300e0074080050000c142c010f9140c0e910900e0301c80030480039a81580a14400c060030307a0245030b0a0700c0c440d64480c4071086102248c0d4881c554040b21081d0b9403294014042500590b0441d030b060030210381e01c182142e009a000200001103000400c070071200183c58078070013491118030a07803900200c2d850362a00c40d101c4e070390014020100064800b013541c42d1903100c4070ba02500202d18a07840c0d61110101585a446030340c0036100e080b614025241908004412a40c0ea00490380051501c564807006010142c07404004220134800680400009030300c0e5402894003c0451540e8203144490302000504171050505224040340e10501c16100025000140c48410052181d020040309004206841c40e00820f01c3c02034001c075402007250700b81c035500b280103541a01d11408040d49030302070014032040c403294240f064000603400781d00400c803441101c0311610071070085a0140c1d503808011210491034200740d4208203440c42c0d5900100000c1d02503240400004402e090501c100f200d80d00d00c0028243e002d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 443195467 1250 443194217 443194231
    0x60e16020706030509030d0507140f0408070807181109120c040509030a090501050904061e080c1504030605130611090103051303050307120209041506030e212109070501020f0f06 78
    0x282c0c0700400c03001402b514494142d1000b05070100e60f181d680d86002d1449030064840d061081c482d41c040420100004550081900c0442ca502082f01d140003214102401d200c0a2582d200c8504214030112a150076200e018440720351402002090740440510003110f90090103500c054000713101c10543e099012100d0011203000b442c000b40c89002f140c0005000702099400760440043c5600454540c00c0240c0d107a200720380d04001038503d07084081007032012500d003814030542a00b600704004e200044041d8015504020001000418280396548020450b40c2e0728901c0d4508010105543e400d0751780c140680340c1e104888449003030048006039409400b500001c2c0202d8284503841e940301000300541e0b419215403082c000c000744042c0b05808000c203803c04482c004c4d0400a0b00b00880307410045800514007144041030070811705078a4400844c0d0360190440034110050b084500d0007060140e2182d0110740c05130004502401d44545000006480d042c5022803903c0c29420050320311020340070201c1c0896102e45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 443196717 1250 443195467 443195471
    0x6100302100e01020f010e15070504030c09020a110f01051915050405070c050111030403030c02010513080a0212040f08011409030f0d062c0a02070809060904060e16020706030509030d 80
    0xb010400503800c0c6117120200b210158641043d4009460001a00c050000c84500101603141c0f182c8400b26801c0c80b8600001c2c082d031000300f00800180c8080e41c000e0a090005241802c40880d080c2c101c0c6003800c0980300c24200307680d1194248904441c0800700d0491140150f1420003142100003811006401c80b4441c0c4c603c202d50303e800003001c0d40c1c00348480503d221f501000803c8040c1582c0c07440d184542003a034080d80003e01c4c00c031100712180d00507c140342c069542121040c0050a0301e44d1340107141e0340505282011400b03120524626420204040e001402c640c901c0a1215418040303154212a2444620048500400c0510040c0e00c4048201c81090030800e4a580c0d403038a0f040d004202518142e4081102c10002e070341d00d91002c82c4041c0300801c0350b5203e164000f070291900d0325010140c0c080d41d0005081d8440c02c121200c42450030000818609001400100d82c60741d8079100071010301c808861a01003944200c00880002d54180020b2002c0d0111307007420042c0d4240116076603528002c01d904014419 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 443197967 1250 443196717 443196737
    0x10e100f02040b07030503041101030608191401060b1908040c09051003021807021501060e09090708010905030a020c010207031a06040b031002070201021b1f030f0c050703020610030210 81
    0x51054040314040c00e003140e14a60b480491703140080c000d40c800c80c2c040d60300c40c0040070782403450341c401e01a0208407482040102105441c81d03480683c1007101322400c640f0001110700c01c00010f4801e0007032400800c0c0c4400c84507112806035183c080201c1c2d50a00d4417007041888002c0200041c1d440c1800000d0b11039070f64002980355560a086601c20515410195011030110003c002d005030b000301082c858a21a82550302c105040344080132070130000e00a88003c1054800600304508103014a50307403205001e0111070900303948000080c00c6541c00101a0341c0f07600000b5001980d25010422022a00c0c000c1c402016418610348410182c1c20f030301c1d50b21484960410003c101190740e2504200c1c0d42038030060035a000401e115031540002c3d2301c007002c22405030041c442201f00102c0c1050b0304203070070500580418102c140c0d01000c1070488428100ca60289030f652004d44d074803000b061140e0249209141c407584c2e0740c0e810508000c2d207001e400500480701c1007800c0d001840140c452940020007103c941c10441651 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 443199217 1250 443197967 443197991
    0x1e081501170a050a060f0e1f09020328021503060109031709041d0c030a0f030c0f15090b1602251d010e1e010e04020609092502010e10 59
    0x4514898805030444c030804032400103100744da40c0000c0000c28030003030400c8045c1c0302c00d9800340c80360850032840d460358074035124074440b6178001d8000800c403910042c1664189d48203400b5400010407454200c803000308101c81101c0440c00c1400c3c4490300c0710303500303081caa0440c13038140d000804040071408000c06040149080241040c001c005442401c40020814040851480c1541a007600140c604031400d20525500b845103003400f0410648480d04041c10700d1061005840948840c4d003d0a4121068140445d100d001324000a8400e542c010240e07101158041c02760600b00c80b01d50028150b00100d21443e0400401d154001818002440c0300000440300e0664401d442d500201450b0300c200807120010304105040b035600484c084c140c0303442c001d02d62010b843c3c550009001f200c2c040c041c980c0b00118a0018048422040701c1103a0192008103082d290404150200d00715210584a24045124650340084500440400e10400740c07007601c001c1010b039040624181e500c10304c1c00070203510603a982c1c0c01c03003442c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 443200467 1250 443199217 443199223
    0x8010e03280507240b010e01022808030c07020a06080f040f0c090c020a1505040807061109150304020307061107030b1902040b0c0d05030c04031211071e08150117 71
    0x410344d0088140303405070301c028a24001c3c28042440d601c460f0b51030105014400d41c000c60303400c44440e0045c3d0080204a5440010b444990b0040c104522108035203450301c0300040c031401c011481804d0320703030b1040d071104034500c14058000392a4008405003c80a13040050050300c1d065569440b41c0c001c54244032103405428450b4502440f42c101400190030070410000742a00019000307a003d10814540c070440c2c201c0b02c103250803070301b06403001003641b0410001c0001003181ca0b0880c25000000c0c034259458403010000103002c1041045140a444102000700015854203020200080c403003818840400c022400105880350740c070b40802130000080358082011050b03685c0182c0d100041000c011966661203602c041c80a4201282c04a0584619111042c0d6180310b039060301d0042c0c421052481c10309003075a65a003100550102e8001c2042040100c1e1a110a000c1000000804403086000e19080f120034031030490b08015009401c03070368420b10781202005000f02c0325604440c01c1c00c030340c0800c983c81a0f002d541 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 443201717 1250 443200467 443200477
    0x7020d02041a15090307060f030216030c1412030601031508070305030408071a070f0614040c06090b09030604121e02010b041a0310052208030108010e032805 69
    0x50407900d010804500000881d40d804020340c41190140ba060700748460a95044c40361104098040d00007a008120340c03405030210f00c4941d0407604016091040c1e10180c0140040e68102c1500003a228603d04018080c2165248020641d07180c0585070445000318074400912000d4129410541c1d034425840300b00e088184c841e4054080e10003907032101d6070b403401c200b55240c015025a001c0e5000c0e900e00042c440079444242420804014075641c01c043c042d071200300312861b411409851664640340c1d00007000c00900b000a1080784a0444003010a09040c802462035019420000110301c041102c060790b0b60700050741d294010703404460000844a001401c072800e5134110700003800c42096442e0310007410b406403c101035070b04056074100014044c0f41c40019031708040c440341c0d54060300102c2500e885140281c000340d501c503c5e4054110381c13820700715000c4200c14007140001d9610761004001401134030420701802c4540004c100041d07052410181030f840000802c1300c900410f2030300084051403400e000c0e8041e20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 443202967 1250 443201717 443201719
    0x403200307050105060307060219060f0b220f06050117180a0c030b0c04050907031a0a030609110d152c010504140706050f091311041806030809010507020d02 69
    0x207407201054540345004c3c103002e403030381c6110307010b980c50100710240300113107003603103041c80651944810003562182c00040015810081440da1241c1c800c402d1a03d4a07070030795400c14581035401d500030001c3c460207000c4402d03100040011509014040240760b90001d60442e1340b41088013040141d8a8a05000300c0d100c4909888404900417160800c082c020760141e9542160b0182c0c0001c402503503403c0550080b482640511603010030101c0120740c40c68800e5101c0030002200c00f845090750b03600540014402d4240b81d008482858603074036110100121090000701e03480d811354030f03146501f900340d0b04c03082187c94185403449141d5071413180c030b11749058810100303046075000c212a41d02211600161400ba000464040d00da100e8043c09580b14044000b80d020102d40c0140c0d01d460409009040040f210340c0488507413640003904000a0105402c544101138128580940700d56480b864010b4080c0c482014038840d80c0e2481c035126041010801410031a2001036091030201d035244001d00c000707442010001006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 443204217 1250 443202967 443202973
    0xb06120c0301031e0215160b0c1b0c0123120c0301061e05030112020109050a090212010603060501090e0a020c010e011d24060102030d110d0b030c0108040320 69
    0x100040e0301419008606a034040d81094201c040604024079070300801080007900150f540c0e20882e10821050054005e80c070190303614001c2c802958849001d5a4070940d0041c180200c00150100c080c00c081d40c601c0e05504c610405444481f2840001a0815a00303000824002c0151040802d0b80c0400714100c4442e00010220081907007800b18101c034498009009100c0418000c030301e6181e8180e070310804c1048058203580d40e245540c0c00e01c0321a500d44401000100d0501c0031007403020500d80c1e148009000a00001800181c483d895441c9110204070b069004a040c1840c0c08014461a41d00543e514203440d413800d1204c00c6030f210140341c10028455842c400096510340241c0e914203d074190070000741c0403180a01d0003480007951a80523210b02c204404618156041061898180300b001780e156444a01401a40d09010581c60b125042d1142e00d0302d80c9540010005401e0b0884109200303051007418198020564a80ca02001803d0b0101c042c10180070300003801100f4042005603030320b03e5416007450060b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 443205467 1250 443204217 443204221
    0x1c090311120319030b040b01030b0d02040f02071a090706050408060a2c0a02010e0a1410020f03030703060f0e090c010c080c030c070e01210b0a0609090312060803030702100b0612 78
    0x3c01401441c2c03804d5001e114078285a6416190341c030a000c3c4801e0564000c003000c548005603030030080242450810380c01001c0d000d001c8000811201e6049061642c0350f030b1201c0c40c3c42d103060321800342440d0f41500210207108050100340512580001c1c05580000346040c005000c0764824945100d001c078102400b00d030718203540060380400001203a50803510b4400e032030704503540c01170108100406401e405090003050340710385501d03100d05c0c060030b0114002c0f611303006444001d201c0c00c02c1d0310700b95030040b12954082500c0f0401005003440020310310f4020403e00007141a1400c01d0002140c4411504040604004010fa400782c107002c1c01c80704031546e201035038040326581d0f06600301268a95405201301c9140340031300c500000702030281d0100c546ca1340c000302c103820b0001d8180b603036031001207100500700884c090380d14000807038002403034860010018080d0700da84902d0140340d1400b40540d00d41d0742204400342c2090041c4102d131900040e40c0c401080c01d0010104907000c0d013401080302c0340145925148080500c4003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 443206717 1250 443205467 443205517
    0xd0b0705071502030c070303050c21041109070e120c100e040506040926090306010e0406051806061018120c090908030f0903070609051c0903111203 65
    0x401080740511a00d03565195600a050307001c101e010450b984280d0f00300030080c20000a00c40c0c1d0090341e01c8100d0855243c103011596000104100d000c10507002500035010920040c400650704c01c0f01010b4085a14004500e442e11f002440c0c07868010040e40034421503030050081c040180006264003e01070310192a8400c3e50303500030450184245803a000c0c2d4685804034896007040d010301514150480c09110b1907005040c00c86d41041305003c100005c0e02c60a1000610301da07401e0100c140204000d10b07020301581010304010049820180c040354040315600a00d10805d030020844a601c035100329080610840c100400740d94a0282c010b041814101d401e0380880c082860115502c03d0f140204842c0803181d448604100403501565400340520f5420b20018a1032141640300da6400042c0070309403820010280e80b00c0094500c0481c0840c2c064018814401c49100907100d80c20300c03a441450711840c010b185031204d14001f1084800c1c43d0042807082e00b02107107007030100111140078880841003400c200c0380721 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 443207967 1250 443206717 443206727
    0xa17070806181308091504121e021f0e04090c031211060c0d09050109120e1e040b01181203090905010501050a0c0203010e010f02090307060203070f080304020d0b07 72
    0x10340c0207200701e64101001d0102c220400d4403d125400c0110144400031443e101c1100d84d8111070b40c49a4810007000007919502c0c00c01380500700401d80925a1040c000070380c603003241320401c80071810351b4034400c05110700050b94481910082407101c0c6c002e405520440c80d002190750b46010000c40e9002420704e84038501f00420070b4415000c0328040d07a11481d1440c60316000b00c034084201d00c040074543d8030070400700b103020701c25400620744101d00c0303080080c240404d82d50b054251004140d05560683c143c6100d6100309800428800040c8422294101e10076042850203492080b2240c01600403555218010b03000d900802e50400c4000902c1c0c6108543e0b1790b40c00c2288200350314400101c0004032601c0c03000840550364041e441c1682d1050b1620350610000b0340044132071301c2002d001a68192b480e1016807540700400e10640048004207040540e842030f0300002d2600e004c1491b40808119401082101c0110303c00000568031a9031000180390313603485900000c0c000c00c0400c81e02901e05580c0c041440300e03183e049 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 443209217 1250 443207967 443207971
    0x8040906080714060304030527100201020319180b062407150207021f3b09010b0301051309230610031211122109060103020607080a170708 61
    0x4030920442d0007030361009204013800243c4000b004940d041c0001c0654520064950122709182042c8808003a16040026440c0c0d40c0c1d00c40c1040541d500000307000f0b105590740c812010002e80e04000384070915200b2601e04210300295000f400c20016403011030099520340302000d0040c1240c80d1035104244280b00042c00301d07881000110344050b440f8501600012840c000d40300311a400034201c44005c1c4900d03410004900003c20120b040007000402e565070040c40c4801c405070600e00da81c1c1c035036003024009074010910781300194881c401e01101c001081182070700800c50381503880076101e01d0180c1c0e1402c2140030141c240848010003085c085598900c5851441c0c180800100d8010b080304c14949400b150341403040c140340409070440701030300501e000160188080c03030346403002c2c0001c44031b00704141550b05880350000155821002184c1014498880030045096005030308a000351000b545550f000031070340d110b16000205401c0c0081001540e10b4010281c0383c03911081404218454542418010980401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 443210467 1250 443209217 443209229
    0x203011508090c01030c05190e24040909020604081c0909090b061905150306091602071203090b031e0c1c0203061f090608061c0b04080409060807 64
    0x4080c4056416600c10140d150082c8080b4000e822402c0c1c18000450181c0170210050060103000c00080000203030304da0a0104000407030392900e60210176030302000001d103102144c20106801603240303d4403d081c034004450844a0311040012401b0651010610500480e40b0074011030180621680503a43d0410010007a003c1c1c598544011039200c00031001100c0c41000094488142c000c000390756420034401003418000c0b9011034000540d40c1d0030000d92801036590b001c0724068008014040319040c6401c03140d800441440d0080034001e0b00c10f100075a1b0700102c2c130525807050030600444c000d25006220f41000340a440010a56901e0592412101030b45140c402c0704c82c2c0c403040380004050010080980d105600c003015070000c00301e40025140081e40024120783d511500c0b03040d0012145004400e10040c0400a07103461700c1d42c1c2d2400a000d0609038004004074014180c002c3c0280f4080803000103400e24550000d014007040d02c0d40e040194160045c0e81250702424902000400da17014002484401c65807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 443211717 1250 443210467 443210489
    0x3081b19021f0207050a2709082a0a080909101a0706060e01090219020d02070b0304050705040509100e071a0309120c15060a3503030705040e06010206060604170a080a03020301 77
    0xc1c84c94001d008172010084081c1182c002802010200740cac045003031250034036440ca1301102c8034500c40f11540c20800200401c031000e03140000d80c000e884c02c18030510f0360300040d500c4408108926107640c1d41d83c2c4c4000401900038a01c00003c181c8200080c40d40440080c000b138060a1002d5030310b40745940025806410248030010a904000380424800a01c400e0002d04a50242190301d28080c10402c1d01d8101a00448050083c144003003003075180c9100e050711800300344004020a00501c1c2411048441d401c039034030700640183c88240f02d0f207400d48031714101240951502580d2640c52008003030420414100c1134000c81d0340003414004064000408030041c400445c80032544d6141c28003000340a442c0b82c45003900540c10b1680d0445006403000c200c0d01442d080d0343c0500c403104001064a0b0466000f110b80780003242002c6820702015400c1c0201e0b40c0c0c00b071030031700040c140c1342000ca000850302d000701e107d448110016110005107055040c001c003c2000d03841402943c803920b1001000d006500240038200c0860703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 443212967 1250 443211717 443211779
    0x4060905010f06171b010e030a08160224090603130b0726090a080c070308040306020414180f070306081005250c0602090a03081b19021f0207050a 64
    0x9400315805491110201c0d82c280658150fa0054a03401d0040710048d50600481601341b001c03a040d1001440414455076040c4482c56080c810400c4044040c40780c5103000d000c2d86204801c0a020a080f58142002128116244d503100d42d03400c0b0042c03103041c4000b8442c502450500039400d4128040c0c1880c1ca20003400240b103a408101d808012060849000c2c8035640003030103060106400b00000c000400e544016100001d1301e90310b0742640c0b40d016a00889082e41d00003020887d08074840109a03c0410495541c0380700000001c9400130f614000d400d104d03035141c0700b00114000074060341c0008001c0582e002912080c42240c2c0105000300340481d10240e038445008034150060340400030003a07103101140c0740d10b607141c0c80985901c002500041501138100501c000048003050742d42e00603004c41082201d5040c4513400e03082019080c1029500610a82c001c00c5a030807006030b40300e041e0603061203000c000c0c082c41b000003048200d280c41c0c11030340a04d0300f1440781ca101141221a804564926220182414000d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 443214217 1250 443212967 443213009
    0x60303080606090d1104061a07060c080112061e0e0c0f09090307031409060705010b1e06120a0603120c060c050f04030321110a030b06040e0f04060905010f06 69
    0xc0c0c4910f80896901a0721a040e103800690580b00c801a40702014000041c41a00d60800d4100041c200c0c1d022500310402003070300020030a4500810071707005014038000b001540f510b003207200308058103140181010748995400181d84001c410302611022450014082840000c00058803400c1081170640559a00301e200c1d4140d08012801e24017810791030b001545003650544040b640e5040c80100180d404404016076001d640e10280a020705600800000545103014410003141d6a441b4908c40a031403e49183c0d104180d885c0701c01d80e180c0041a01c080c11144c1d03a20780742c10000340b07441d400003040c401c1d40c030065103034ad240d00c00010208070388610803c00401c2c106c0c4c0415079980c0500814031115401c2017209000007071003841640c007000902800b09103d4240d000d981415600850084e1111130b0010801d048031580c54060807030300301c4068414620b060700701091034140d410300038508a0030302f0080011904014003035200c400c1658000000300003510040861002030102c52140c8604108861021001e07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 443215467 1250 443214217 443214229
    0xa0501050d0308090703020301060e07180e01152606100e0607081b060901150605090609060708121501090602010209031e03090a0308040f080a081c060302060d0603030806 75
    0x16120300500840040c05160b504940000b001080c5a285001c1c40e44000010785090080310007030418480d41c41034600c0c0485000f001c801c8219004c102a40c0149010000f40380ca8903901c6041d150184410440303103050120540302a56801d0009850000c0c6000512201e220740c011140505030444600c1040a4440e20071145548554003155200404001c01c0d800165000010083c41801114400401848280207400c065044401c41c00c1a51560f050801c0d00703d84140c0c91000e0f28003410042d042112200c081003440c01100d041c58000c0c0c40004103002844580400c1c0ca0a80d4205c10304540189414160300d001e030b610388a000c0d408a909100045281401070090314120303200603000b012282050f00d04130700e5038140503030540454001002140400e0b1070300750341d207030155000b40c0325190b03110324000c044000200150301c4070031150824041007002580141c101e400c50103013850219103884d0640880780080c0081ea0000303620101c00230700342c1000c2c0f4654100364100c90184d1560041a0341310814044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 443216717 1250 443215467 443215469
    0x209180f01050402071505040f0209011e09020d0b030304060e031005071e0504051503042114031b04080a02191202041112040c08190b0f060112020d020409050a0501 72
    0x3502040d000050000f070038240e024000850181d9035032000d4007003040d0f02504440013900d040e00c9590160240c0c0c000c0d0300b0101805801002b550080c140341000080c0b4004071000705000d020078258000074182021030054000360a940f400805480e80e669581d080a0482e0748030b590324074040d01a4003d83c1c40e031200c55204140c4076100ba620351035440a051400408050a459551400d000e4148801310b1217855050502c0c1403003d184110304c1da40d00b0071f0304020001c406007544481495a038511044d00282c0d0080c1c0c8041401c4940c0c41c400d0726030b01c510500f0302000c1b0b07000b8055071141130041400152400c00040383d00829009a400d0200006c00a11043c0000309502800302555000d040000c014149540b2880c68060325801507801e01e0130000b20380c8500c000c1910181ca035070b0b28807001405010000c0c004440010044a28040c821409980c0c00e500c446004007001e01c031700e003074200240c00750740905051018190940d1085541d507000c05060303402074006000718002c491a040001c0c111119031b20490b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 443217967 1250 443216717 443216731
    0x303040605070f1e0c15060e090a1a0711120d0b0a05150a09090204090c110303190e0c12010e0d05090307031118010608161b0b1810020918 61
    0x100014802c0c10701314000c00030302c0d106441005189179040e008510ba51802c070b40d06964021000c11040d1038491140c0ca00c520151100c4125000300d010b07140012000ca1119892032515416043c00e5910108191809100000b821465000b40c96041d0140c0050740c0c024000d1140c2540704102446c011300c02e01c02d40c200c0030300489070000d507000c480346a00d24891002d030a007040c03949004049286c40e075a1080680e04140c0c04285107075110f4070311101594201c43c21450121508000f5421440d10b1700f04154030080849030b980660740d40700c0b40d141c10000144400c2001d50400783c000c0000c1d00c0c401c1010360080600c804910f0603801440544584144298200c81c0503102c02002400711904544510100c2c40a01102c994822150802400314440003010b4038000c02032030322480301d0781c03a0000306082c8079854000c1c0d44040101c007007408801c14003445205c00310b90f42c0254100e000c0b0f581c0c20728800c3c05100051000e401074031688031321301148103064004120016003900d003030f9500b503d030006030040e80303009860034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 443219217 1250 443217967 443217977
    0x603061e214707083601061509050d0c03051b0114070b1906052206050103020304020913020402160623010b0f0d020f03150f1c0602070602040806090303040605070f 72
    0x800c40310f42c800e507001d9070801104840d0000c80c00505003034035840000303085003507190240d070741c042c4141d03410038418070006154030802102c4c02c010b003200003403003140c2e10301500307126000c400205014030001d581c0d9a0003039944502103806851f003602c0d00380110020303010b420b8005a004854200061091410b0300e582551100d40b481680d11042024104080011703034015081d0741d209000540d13980d525100c0708005400c2804246000841d0040f08251a01030300014103040c010001e110041e01d490024942c4100007150701c04468070b96100040c080e204040501040203400c80e22082806442d03400400f59460344890001e44812010030902d0001c5c003445403028414040c041c0e180c029445200600740c0c600300a80052500744101c0441d030303654205030340901c3c006024842043c024200170203080000c140c112030300700d8030601e284031031900d10310400c0e00204450f801060300c2c01046010340685000d407419078180c41e054030f0400400d03592500203c900380c581c00e08203000f00340c1160043e1020b00c0d40c070006680e2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 443220467 1250 443219217 443219221
    0x4060c020d020f0a150306081f020c15010f080606030118031407060606030f2004091e06080a170702180426040603061e2147 55
    0x1c00a80460310740080e07810580420320521295594500180503144103418500b07034600920700101282c025402440e103950200304010030100303e00544000082c1198005651003800c1c1410508114010820113200c0e15000b00210360589100000c000351411102183c1e66075aa5400305400d0300c40030354a40c0d1104038640d8204001c24468040241c3c6903080680c85842d000465955508440040d4081e8001a030b4950005880380043d01034240e0b10380302403003016080315034090070182901c16803203000c0c042903035031010f400c808020204110b0010035441c010049140e0701d5180d962154080441200c16901041002c40e10b55050b0382500c040c6070300500301c2e00c50000300c10402c400c142c8002d803086e6512840684107059190b000e60381030001c125044011a00d0798a4801d01509441c11500315080e60307440322407c45c0f2401c1c034150700c0394102c0e02c4502542070b00b01e40900900346101c1d90341c1d20140c1400607000840603941e0340010140c810105684404211030f4411110312410102e150140c4054101500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 443221717 1250 443220467 443220469
    0xb030120030714030c040f05060324040609020c0a12090e07030b06120702070f05031f020901031e020a230d09050c1002160b0a02120d18030e040c020304060c02 70
    0x41d5610100e40d082400000341006089841600120713003202c12450006001c1c0525044041c00600030101521640e0a41c180743d1804002c60042d1a078020714841000e1600d20580d440e500180c0040c41c1d4840704541d100342e4200003948405003000c0559886644901c400000c0d4031501400c000c550500740708580640f40c91804070040d0100d0100c03240d00103018000740301d40d150b01c601e101d03010b6280c4c0d400501e1902e02c0c025040d00143e1943d0310062082d00050854001c50300e000350316140c55030a55100503a54002940140c004040b250b00030349940149403400c4001c91100d27230013011245510340f11040b1898149100020a4404695295203e4401e1200080c00c280c550030032054035105005640c06007000c040403d0342c4000e5000340300d0059005030142c10200d00340081d6040a80a0340c3c1c1094075105080001940c0c1d030300d01502c0550721160005925820403110307413181580c00240408541481600d05009001d103880e00d4030b81d84954038000309041254000800c5604607107454840b00445802ca130 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 443222967 1250 443221717 443221781
    0xc0307060507030f0203072001080105010f021018080f0c010510181d01050901021b0f0c0d05070305060a09030216231203040608040c170337120b0301 66
    0x1010106606c0b0600403000000d2080541c204120319040d0b00c42c62901082000600f0008103134492410702410f0300003050081e07801700340a400c8070070029000c81c40e10660310359000000313095240640303605000300b01d542075810440000c207040a0a03a00a115645420b4a003c0340d402c040c2c41429005400034101080008003900032401c010108500542444101c4006a003516421603030540142d50004848800041944c5040140c0a001005101c40c00a00e00c107990780d00d1002c03501c107204142180941c81000030410a03c0051513022066900504014105901070120020120090b008030300c0d00001701590819014101d40a0028020031001c103403100c5001860b032110499008190380411303c527148410001000200180c0c3e4881410b0310345070500c0c0c1082e40041e0803146500da82807810420340c0c0000010342d241c41e9140c540482456076464403c541d00649400f14040e1119207281c4013455541040562690074491070050000150043c201400c03a81c08841016101a015900018040d030300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 443224217 1250 443222967 443222987
    0x4030e011b1401110412080906190306031e0b01090e030c160e061518120d0c0501061707120f0510020405030d0905060901080627090c030706050703 65
    0x103050106040000100500c00741c07154030300c01e03580d0040e46040c5040d2030500b48600c0300040303a40e01020341000d04051451803034089001c40600b000b9404982204541e51340c1044500c0440d5416001c40c0c401386005014024001c944000d4420140324580360b020742e641030351064001a481801b003480c50382450000002030010381c20b01e00f420f21090001d0f926102c0d0070091307150400f200113880f6244625110720000400e400800442c0103410748a20503449007144026294968140344a80040014600c0415805201c0001d040103503c188410100e5841d00003004546540c0114024070441d40c071042d1a80754aa00c560085e03900c0e43c45488200081c4034101c0078840148d119030782c000035030001500c44501d81310280c0d130b080c1456640000c04010a107010002d9601071000c074101941600c0c60280001c01500822081c079042c48012400603105507a11002145005094030743c0c0200c008113030541c0c54010a046445684e40d2151800503016071800103620b40440e41950781b202c2c0b0780410750358112045444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 443225467 1250 443224217 443224219
    0xc0317070908161a040303080403081b1908070206100302120708120a0f03050708071d130f0f090206070201050c2a030c190902070c080a0b06030f060f04030e 69
    0x844071000c96000b409100962590b01000c40ca00001070403c0c035103181d0b131581000d8050003220104420030003e0341000f1000d80c0540c06061460440d522070742210181500c40d1104400324a00064611442e8204204003000c859280d1b0342d50302d6640c5005003680d441d403043c2c6040d013080b005a001040186400d1426041c0083ca02054850042c2d40e030038078510300307010b51a0142e4909030204011311682c1c2d01c26451180c2120f145020300590400107800f40180c080604140c00b00214031411210340440c80311002d0201401410b0150b0603020360b135201005140c1250003891080c00c2c0100d0480e0754115000704265590010040d61510040e6030054403142c0c003009065005006200e000d841500c815090040200101441c082100e015141010b003441c040c40c04c4d19116080383c00f81181040b80003a00241903980030003005035103060030300380b040100485910814075480341010f66000c014001c141c1c1800303100190212842e40d803036980155260001105c181c0a08515100000e020038400e5149042400e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 443226717 1250 443225467 443225477
    0x6320d090f0804080a02030d030204060e04050601030e07030605012102180421120606051201050f0a0810020405040501060f020d0804230a0b09121e160c03020307060c031707 76
    0x1074a9a42140c0e64000d41d20140c1550040f003459419420244043d5404036940d190451800342401e001401c590240c5601c0d40c0115503510000f40564003a90100740f0b200280400c0752111903407850404040c10090058911000b0100403500d00f490a02caa210101640217100c43c0c40e00e00740c2c90305c6100a500060041e40c9406001d502e001c2d620110061a42c84410030b944c44e61490a55680008103807010b540c011401c2140822001d50941e001000d1941503032000c171040e000d5600000002a120f00e40b45e007242c445800f60b0107142d50218001d03030080c001c49109940902103682d95280689035100c0d07040140703001d030b0000310b0042d40b45807003844142e40c0544203600800602c01c140150b0707204602c4541104446034030280300d80342404041c1d00d0340c42d032100c1c0d00b00060080300c40d0220044038902616280c01004070800200300101126401952041c07110111284200b1942c0e0400c0318500305e0900c820383c0280101c450105106120390000748880d41c144d1118400c18584046103a03410384000c0118040003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 443227967 1250 443226717 443226743
    0xc06090c030803013506160519050414030102161502210601020f0d090501080a02090d052109010912030909180c0e3303010606320d09 59
    0x5000840607501804500c0d020a002c00f03449000745455141e00d03d20040107044200517050300081c00070720150700507104805440300d43c1c1d00a000352120300610042425181d4040811110a83e2102c0074004407100e0096a13440d816094050500300e200790b0f040104250208140c00c00820455110508100d001c07002c01403414100c0c1d40d04084150324501841181ca02c010240900c940c6d04200701d20910003454003401d00703031141060262004d045485100d06001c4900001551403215606860540c080a0300144c61104189050b070b0f103401d8000c144001e040f24000e1380225103001001601c54194040c0c50f0303140078034244044000680e81202c1c080303080041c030f007a002c600c400650103204000d03220400c10904030b070031a01e069125141203030008246480058200180300c8851254100164041c000c8460072103410207000c40312104c064046a05503081030400900c803544610010758883d284100552008840c421480503141e1441c6402000b003403e20502c0c41c1c82003a9406001d509201c3d040d400221 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 443229217 1250 443227967 443227973
    0xa1a0f190c14150a18021527030a0204090501180b060f0d020915011e051801021f1107060e010e06010b0304051b1329010f0c06090c03 59
    0x2485000c9400d0001140301008408000311021514040d10806000d040c070500311036406200040001c01d0040d6141d00c49030b05503e00541100008100e64028100c9081110024480e41310396002545045d640c1c100c910300c200a070710490544d2618010000c01030002c5039455000c20001e4202c05100b91419507884928480f41500480040c004a110300c03168201889c254041040b803e070308915150013849041c500100607030f5a0b0810343c0e8401c2d01342c643d84403c1071040c0b00403100403507564513404212080b030f26090351b2a034200d000382038401402094210800d056000498903071142403c0e2499130350205441035410203054000c240d600040e501c3c900c0c10550315448000581e400200542c010365558041701589200500c150350146c406480d01038a035042c42d03034640303070307202038200c002213400181e00e88003211680c440400d07001c0c1c9806d013002403110207540c240204a000104841c0510141a5619407940394010b0207801400c074580e4451014102c5942c90b0320300900301c0100304580790b84e048030f804800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 443230467 1250 443229217 443229247
    0x4021005190e040b040903050f0c21180f0609040e010f1109030f060103020d06021602040f0b0406050a081b0303040b0406020f01050a0203060d080901110304080a110a1a0f 75
    0x100c20324030703a00d07039064140b0342041c4070844009000c0580a01e00382001d071408260040708403580d0b48122002c10759a10b082c05009814843d440b20341d0400040750300c6c002d51039451030720701900582185000c00c4c251070350502e00708000c82c9948030b100f039000007042c00460128a400d5026003c08200600081584500401c80504030303500f007141c0000f207010200d02c024141c01c3c02c120708405584041c00500c65941144c0000c0c000300c5600d14010b00986d0000f40c03060f180031000f400318282c203134003900900600c0b40c4015070002400070401c5040c0a2450641c00050500c0c1c601c40e00070454080001825520710b01030f00600d2202080341c912078151004000016025942200a05c010006a8040c14500e0700c0000b2440c00d4400180020242d02d0040c0103000301c6a0b41c851034214500e82c802c40c0260b5941d018030060710f074901003404609042c0808100050391450200c2e400220520034008020361142502c01c2041d07140950048491440302d0761400c9801000301c800400c600190040c803281421418100110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 443231717 1250 443230467 443230507
    0x5040509070305060c0a020304031e0c060c06050a0b060f090a030b010e09070602011a09270303180a0b0105010f110a060c11010b0d11040204050d050309121504021005 73
    0x50350348500d20400600001340040e80d009102e020740b0343d10301034031120003e54074000d03408050040032034842c1d42440b410100584003441640190001c100f0341c1d4580c0060f0552174200c01c00d80e01c450824000400400081c840c0080300a00200002d00b0950000301e0040c26800074105c454000c00504004404607110240450003011a284220414a090f400b10343c148507195215400f503a06044a5504549010b1030020401505a038a02d0090355005000140c182c10001c0c0713000b521440d103000441c0072102000071481342d4031103595040c001e45125a10386c2d407680c040002500c600150710041c40b42d5803103002001000385141c54641681c0300c440a11a080003094041195420b41c0e40d501c1070b18094001903007030170030b0301818001c20402500002180307400c0710014008080d01440d68010341c50b0b03602c3d43c0c16500070303280c0174288221208c01858559a02d0780304180e41485040c2d01300e2260f23800c21001810390180842941c0001c1c2c0da0701c2e01d40c01d006e900044569001e042c04000e10403800b00d130003a0b00d4a02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 443232967 1250 443231717 443231731
    0x3030108010f06060809030d0c091203020f1606080a0e01090b07020f01110c1c05160803060f041803140906161205030c041202060f0703020717031206011107050405 72
    0x18440842501d40c03403c44035a90301190034080711404015081c038011064500c6080240e0011500300380784402107922000d150411040a00c10204480516078000b41500c0e04c8114401114007152003081d040d0350319030461060400162020001440030100c43d045403921942d114004103141a1030340d103020754154101c0d100340061740300d0254040e9905003401184042e519200d9150f1030410041b04150303c420301c1d030038405170b400c0d00144401c05142c450003c503407500005035034411748504c40d071400d031080ea030090fa800c80c42030348010382412851402e07105140070b410a1102100c00c8102c143c0c1d0a0382c4414040d007500440b11f20511009903983c40c0c0d0f1000f02001240380707a00d6a84544903203064124207a02d0380e04c0b0400c200017407007000700003c032a0085800791181642096800c1c0190720001d0340b80e10980034000440c10703012914100f05900060f000e001d55154418484649502054240e902c0c00b0700808040101181d501140311035003d0400b84250140ba0825900055260700215003641d4003601c007a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 443234217 1250 443232967 443232971
    0x14061314010e030a050c010b04061406030601020705030f070611070b0901080a140c0304060c172701020f030609090a020a050f060c07230d020d14070905011e06020c0108070503060a080303010801 85
    0x6c040010020301c03440d039040070115401c01240d802d0508500c8045c203034414040c0110800008950ba5a000300b0008000348001811101e0940c201e5401030380f9503a5610485000c90420201c44120800c081804d405403880034881c1030910305403400440c1c4001d0003a00f00d0161a0303039024091084800c01145074402d0050424155880c10303d0328004c02100d40b20844441000501e40d071841802c04014070040e08000e841c440310041410000703441488440d264012661503100240c104140030304e91014500c1100b088506001d103590392544280c90f22540c03c2c0007503001c10121024400c503d40389552103070000001d40054203003001c50300243d1a0468a420034100d207040c40102186c42102041c0c4881040002d4960f03140340c01460703002c9200f5450540006042803810311100744600006c011060081c26118828815541c1d82c00411940703400880079684413100c070440114802d400007a112850341010380d2607465940e030b00f81e011541070308042c1040340c0c445032100c0700240c000c00c00c1020b580070341303400400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 443235467 1250 443234217 443234227
    0x10090803030405010c17041502030705120a09120f02031210080f010504200f06030406021201090603020a050d120305060424051c020109090902030a0b0106080414061314010e030a05 79
    0x400340c01200346d030301c117a100102c42c42e0070400010083e41182c0860302c2c9100d4096280d844240007034079076000d1a483c1c18482c101500400c2000e00e003581102c0a1140203142030880303041110f0007200e07038507008100711002d64020402414a005075803002a4000d01c43c1442c004262307111505a82480c88814031003805a4440381488148007049240104074040060040704115810000ca00168124400390b03200d1400030000a00f4461140c040300d01e80c0c086a4840c03074042d0303140c1600c00300a09086c00141e014903408400481d0900300005c10080098000a007460054100c0c00214040d00c4020320654100c0d89135440101c2011002d02e44840b4103906040c0f03540481d0800c0107000020340300400c44c50030f04514410140140c4d81010311481030b1100f80101240c8440b007400844d26001c150240101340c02000800041e5441d80038070a540500c0c82400942c1142d001d685400d80d075401c045d2507444003a04029660400148200400003150407458000301740302c0f0380429441d05540120407000c001c00d50010b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 443236717 1250 443235467 443235491
    0x40611030405010e1b100c0c030606120507060e0607021018060f030b0d020a0e0a0605031b10020d020d050c1006121a091024260114061009080303040501 67
    0xc402c00c00105c1d0200c44a02a500058070b010401d0101d4800c0c842c0740ba41010500841044040103507400c01c07010311200c1d036682c51103c10407080385000d0320640508100412031030701c40c442000c49910020102408c1a140380c080158650203a000701c018401d101c43c140b00c0b24505500c0030340c010412500c0d200d4004022030f1010301901c071030048241c403032000050507a00590710303101554248c888a040c4020655100041000144a00d8014640c1880f400001c0c0f2260f06002003400764408042d180104441000303c01a43d9540016100e07a025070401c80b00712070300300c0c8540c015012486503a42120000981e811005003140c0b856000b03400c4140f03800308000c09000d08210b050030072403d405235880140c035082c000d01d910303003101e40080100b4584820751348440c20b001c82c020303800410102131990201503443c0408940e815240c5c0c6901c0c0c5525080b1140407000006124007a203061070f4000c2801c003643c42504118150808103000b0050110344e00740030800650400c0510306c25841880001103410781c1c0302c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 443237967 1250 443236717 443236723
    0x9060e0c1801030f110307030f0b010f0504090b1b13030b091213060305060607120801091a0306160215090601030c0f181104181a040e15040611030405010e 68
    0x202a14080c035070000010000150043c034154040707a0041c4d480a02403c804002904040543c1c0c006803110702c985020100f486400c6481d54100c414041805540991340c5050005a03014140098200c45440303000501150f1142c1080c510b600300310281030320b4100d889050782400c1d0342c0c3e5002501e44807402c0080015105003048440440c002092400b402d090600b459035034044d40a000c2c0c0810141c560001c18034603200c9206840c071865114421518801003c8002460b03244240319880c08141041129036120040d00511700d14403002034040c3c11290703036a803040410004400388640440c4100104a11603510840c0380d0740c020f05043d0040e150701c0d455070400154444241d048540c01800030f080c1041190401036610a090308103950210304074440e00b4528070744d0700a07a403060000d01240220800811010b9200d1403803082c150544040c5500c05405200440e0300130240203100383d10101840d803980180041d1985d00501c00c000200b14004200b05500325900700b66011074560b9101d004807c10550b0078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 443239217 1250 443237967 443237989
    0x3020405041e0501080f0613080909090c03100b0607020402032a0a2d08060d0b07180e07210b0618120a0309060c030509030d1709060f01030b0a09060e0c 67
    0x2410410311b46010b40b521182c028000c51924400300400c1410803030700400341c4031401001011081f8600d0b10031415070f260f00583ca18a4440d0203035400c0482200114440c0c402c00d0200035010310308001c3c099080c00700941c4050803410003080801c1103903940e100d4800300148000b02c048001a01d13a5540540078040402c500c7d10003030414032170140b40b940c000b081150a0f08a40181c07038a100c0a48804021842c03154000d48080d02c82c0c000c3c0700410101a81016030200c0e5140b964840200b502d940d581c100c101e035801620164002030149031903101030ba030b0042c0072034448000c1c59030006807010f800300002d8440d80505074800c20f00100700808070782468900440e034210312401b00135080c0c03543d8554000340111020700034042803000816280382071500c00c80035602c15072400703002c40f001e0400c0c04102420345610b01d0038423506a1209000654050030100d04940201d00c0d10301c40c100603909580e90710039409801421154029920005800420200d00880304101100350140941e820100c2c148041055a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 443240467 1250 443239217 443239229
    0x14090301020d0e1c030204030f11060d06170d081e1807090f0b060c070b0a05120c07050129062104030c06050c09010e0d02010903050604210c0807020d0303020405041e0501 75
    0x8180070400120309c0c0180403540f42ca030700c55101601807042c400010360f14011300e00000b0440c2d2800c4400304030310f80b03800300040000d82244c040700c800c0c0c030b1100d004840d80c10f001c1760031580c03050780302803000203030b8000c0c01e040da80001c1561a1050044242e02011745450040e0b40040d2406031203041150704440d00784268002c2060070360300706142c092034415290303540700c107841f61303030a100c03400a100780007035100b80c050360100003ca40070b4a105083c202025045600511000c0d03c095180003030800d01e036610a0303102d0010031405c105a11410f05a001041469000300c401400860329450300340c030302e40410481d0b50f840b81e4800c0c0c480148540440c00e085048540042c8500c000081c10840b4000760707038001428504800302102d01c1855625944012103181d510307a0f000070841d100d40b00030710003007229004413040034666207200c1c03222035a081181282d40300c003001000b81214008126290140c24040c160701e21060282c02c0251619030b40d00042001c4403559281b91000d13010296209400c1c5599010329801405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 443241717 1250 443240467 443240471
    0x80a030c05160210030e1e0105090105010f0605090126040323041202030a021203120906010509070309051501060c03090503010b010e1003060306090309150c0314090301020d0e1c03 79
    0x8100c0e00b100c0b02c070818540c0030f032060443d103066003e07041c42a00149000000c880c2a5170701d000e440092941d441d200702e5482d2140f5428140001c2c502c55052250354102e6900c011001850703807501e001550306901c07418101e8100100d001c44540c0035004441c0088144103c1c501400d044e00d40b505004002c03020110141c409d2412000d260110204e0340016070707060303071009268200300300642e00c00a4545066914000d42010031200c01c0b4511140200182c01e0141007030f420901c0b0b82c0d440011003138403240c00340281540030201401045000d4440e52029044a01c84e80417160b80c00a0003c2d00720304880240e00000005209150505c00c0561044200c0020401640248002d01a00002a0100c210030702e509025030000307180b408400e8869003201008540114040005100034200200310304020b000b05040007844030121340b0f00500c40c80a02c0c1e031540e019a03541c0145c1d4656100c80460b68001d00c0400e50644d0240a880c0c0141d02e1441150505509000180008011550000e1450010700c3d05001494 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 443242967 1250 443241717 443241727
    0xf021801030308010506130f0f06080c030112030c0f0605041b23120a080f09040606020f0d050c0109021201060303020d0203070c060804032f0f01230c0412080a030c05 73
    0xf6004200541503070b000b01c030340603111420074144031002007a130b038461351700381c5180840000c100034862500000e503489991100844d54940410050302d00c020312850020103603c40c100c1010030311985982d402c1c140300d4240019072445a403201006d1b80c0c8181c80945601e607030080c10364156004003001c040104002e01000d45040c5c3c1d03a400c0d210f40c4181e1b0114240c05400b0818222500300e40c18040d2060141d0b00851043e141c01c143ca100b150f490304050b00305406289000c201207216400050103a0b84118010010a03c02a50050072a0720703070002031038030300b40b507498142c1200142d494841c8082c2800703802c0d0000941c00d2a50070003e161601213002d00083d508100302d17103804215500065400e490441c100840e82e038941307180c103c2e10052009801755004501c11030801c80c07a00041003034600034074018225800c0d038a00030355880c01c80316001441d000358075116151242c0c804180d007142e81c0c81400c9961003800c0070366400505480c0140c00c20301310360710000080c3d01800b4036010710030504030300c000d89011410a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 443244217 1250 443242967 443242973
    0x6180b030c0d020312030a092019050913050f10050603071e0303050a09051003021308010c05180a030204051609080619201c1d0607050d0b0306040f02180103 69
    0xc400840c940a17121400200045401c52250800410350b03501c880000310b2a40300c0c0380682c00656180c44003521070241500d40b5103017a501360800c0310a40382d00400c07440c80c40e250b0126020000500d224101c5290080c0300d0791781907881c002d1280c40e80c8400c9410000c50a841c1207010582012025084006040407403186601e01c00200c40e6541e003034a40c54142182d842c41c0302e8034280d92202c80c40e071110742d0203081006d40d403401aa064028000200031400c0c1c0f510300036148d440c014266100e0059032800600d0a00070b40d44c40da81d0212035691005c0300a03040140c90307a01c03038002c20180c4204030340c8400c5c8088680b525920455000b82114001d05280024102e241000300c0c00c0c0ca0390440e03403d04820b44a1701c40c2c483d0f00302c41c01143d42c074580c2031055003070309980ca00c00c0c00c0390501810301642906446a1910210140312240e0010000070003071814080e10403a84c0e80b460603030701c030b030002c81034003070b034240d035100a1b481d103480400c0042c2c012030040702c240a6401c1d079841008040b5014107145800900e00400400c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 443245467 1250 443244217 443244223
    0x12090203071d0a0501030f0b0c090d0f0b090625050c0303010b041d0705070b041b080607030b0402040803091012090b0412050903060f090316080409180c03060f06180b030c0d0203 78
    0x7c0c599004040c0856500c651640b1200d0307014142c06968032000d009040d10802546e01c2c2c9451742a48201106003242e40c1c4c0e001c040b500c91072b08503040c4188840140840000b04000100c03d150b100342c90402500b8840c00e460001d01d9034209070402c0710100f10006040c08545a645402d509010781d046060150307240070b4400620360301948400800c05c075100008101041160080c41444603003415a0b00515550b40312480d0755000c082e110782c00800d1400c11842100e06003402254141e0713640d14004c0d4500b0b400801404004020103040c0420443c0206c2101d00583c070500039100a02e0055000c00c405003842d061451b500c658400203401070000400c10341c1c400e83c0303002c12099882142c5021900c0c06542c0d400c0701d2410740c4241c8072062984040018014208078040d0701505c2552000c2e5820405024550401201210200400380081c4000e51040000561940204905c45040c0c080440c4166a4030f201c0840014601281421240c03240e14200280c20204400c1444030720840da0060030a4254001c01c2e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 443246717 1250 443245467 443245493
    0x7020c060307020c0f2d010f110a020d06020c0d0c060b0405130b180a08040f050603101502030f0406030906050604050c07032304060914061912090203071d0a050103 72
    0x1000d1441850100d8596490031b0007902902c040410030071010700144240c024071080728030310a000c42d01c03003404909001e219a001800801440004100750701d00741d001c01001a128490446155400300640c11281e4402d001f06640d81103603880d000c208881030310b001d0043e44c0c4810001809a4500000c0016801a807242c1031440e9030030545400007504d51a4046500b54070f4545021700a20511004004124001c001041240c0004081038034540c2c8400801c80b00b888103940704400038840300e02c2841103c0702d070350014445800600441c1d1a20300815520209504590300c40c4001c26036800203101801614010680d2107101260200018500303642e075481e40c0d00403c01c0280410884814044540c1c0142d0041040e81003005220b54490307648070001000d141403030144080c021441c01010702a41050407d07206001d1043d080f0020780c0c800c810701103e100c80b2800a9610554558142d64003680f0300784a504054960b40560418101c0a01340941002402824940813079250100400c085100300845003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 443247967 1250 443246717 443246719
    0x507140309060301033005090f12060402061318050f06010c03020d050a12050f072c0f1c0506101403030426010c120e011a0603130501020408030307020c060307020c 72
    0x100317450b90010201412070302071442d484c506d082c020280036541d58004010b00744440044428030300c015004c000341b21000d400310800c040035502a0000c04d0051a08070081c00c1c103403c500402000c0e046c1d44a8000515944513220109501d07070325003d00181c01c0e40b410000d07500640a00b0302c007a03504196900203656101c1d400c0750004200001c105000c42c07500c201010308144007001014840da080c60b0407801c41c8a04191003003008038210740708200c1c07100d44540d040c0d010564560302c015901c01c1d690003400701c40314644a00039845494546400792041306140340c000d100340a07000414607460414001c01d84224250000c06034145051301c0c1c4002035a00104a4096800708410100702550420101110210344100700000d54200703400781d2182c2c1c1d4440d40380400c294000e0414003c1c040d686c0c0d90b4600301d83c0b608038440b40b01840807100d02c0460504500440d0445414018060f000b1181d469490881c0c0041c3c1002c1a00c2d003001091001e469410090049004004c0329018510701781590085d560b840000911 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443249217 1250 443247967 443247983
    0x140c2b0315030204020307050408240f01030818060f0c060a0b120604080c0a0f03050706060b07020d03080402031c2d020615030c04090321020406120905030d0606050714030906030103 80
    0x412088c072401c20380c0e00401c100070403640d484d903004031500341c0d80784004c0d4118038402016002520544594030124100e13030708a20111320b0b0000c40040c5140881440c00a660405000c1202d2140100460001e10b503160580c40a40800e0918180300070a64000f10140ea11503a030400c0081d62080010400380c0d0800d501c6819182d070b40c4c41d601d03562400c0c50400180640751800094983e014107400c0001448002d2103400200101a180c001509490040c400060341041c0c5050340200064090300195411a000070b0803900c0d41c2c40c01c1e40e80c0d15104400e180100c8001207055550503031061f00040752102041007415100b040d000c4a05000303540b10b80040038000c401592404062031a1014407218503415000b07802032080010504007d80b080d01d0003040303240d105491040f1301c030100e04240301740c60030398005649000345120305145000c080c0c029084241e8013804104406c1c2000441e9204600090035a41c85064a80d43e15003044100d400402000d40d4880c0c004002d485c500c0d54600f41101e0540fa804615 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 443250467 1250 443249217 443249221
    0xb0a0605031e041704080303070f1b0f0302010b130c0311090f0d0f020a090e0f0106150c150e0a0519051e100606030b04060f1203140c2b03150302040203 67
    0x20460722080204c1c0c0b0b00d130188005400b042c070310b80100046200d202987c5811040100c640800c8481070b01807400c12048009005a00300012620000d04034007600a01c00804e01c84140d00001e410f801074000e0781005140d1383d8a0302010b03a90140100036602200302d502070705280a12000c9681402c0d910b41c3c3e24825811803501c4000c0112088240030903070703000f8211352041522003400a0040026074206043c1e44a03c0300890310702d00e014000c1600341d502901e01d0342d90400d65800190703114108600c040707500014a202c13482166640c0d2294048003210040100324441090414a0401104a110381141c00c0c0500030540411000100000403000704000c5c1a151111030040c641003400d0300000040103401e141001611503031507089281c0740401182d003004a641e58009420030840c880c403d1114180e03403030b201c050200340112400f1707404401078884546040208002c8905040c0c642003102e00401c2c2c0c0916802650301050f6504c00750300c0141c1020170003600015030140c04a111840000d12490300040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 443251717 1250 443250467 443250473
    0x9030f0613112b020a08030a0c0b070c06020f03040218040809220920011106010905060103020c070315050c0a1706132f0a141303080403060b0a0605031e04 68
    0x15403400c3e030302540f03a201031903515002d020303242c10811405038400ea00407040480d44d0f91012003100c42400081e02c8a1603580501e030741d2094014801496141030021403001c04c004265280000c010b1103ca0801842e03403031405204000701400b00012010203004010104030000303020204413050584d0803105090010a410000306426810066510030b143c14540d81400308030500864114102074030760b03080141e201c45401110015001520041726601c034000400007124141d0269030800380c185805032a020020100078600f4505501c211410700385001c5000c0c0196241c80340c0c50300210103c14441c50650000b90050042c205020b1811411221502107810f65560310032001c1c1c0501c04000a0102112411249900f034001d03800702c1240c82c0c0840110514044042d080750700280d216147c0340b04030907284d00100a04e42203520610410078540c080440891480c3c4094401180b1400d030118511240005116800c162540840c0c10700c403041c41031021400f07055241c02403090258040b0252030342d480c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 443252967 1250 443251717 443251729
    0x90902150d0c090e07050703110a08030708010f0504060f060807090906170c09060a0b0a0c05031215030615010e1f03090c0806071e05120a0209030f061311 68
    0xa88522080400103400882900c654100b070607052003035211191920707595554580b032010b08540c001d000a2081154000081c02860054001941232084410480881d9614025588240ca5440208050500422041c4425016200a0f0509035003d108003450000700c000b80c080c150240700c2c00d01c50001e001844036882111b20304000c000c0a00d00340401036a44030360343c40c40304003031040c0a110b0240d4401032000e070030f001031264000d0501500c0c28521500c1c142d01440b00da0414070310f80c81008400004000451400c002400c00308445180e903000701d0811005180841c01083d030307020300a030401c40421a81905291040304410f02c2803c0840d4544e00c4074000812021030341d0b002c450000c0c00200c69140013540b43e800f41881c10710455000f0801c07910307400e00307682c1e54000b21102400214100d1700d0000c050109190442c401581c1d0901d01c0c281066503003010040f10702107440c0da2800d03901142c80400c5107010450b013500440d6681c003525403405c1030a0354210518265001070300c200481194600704e51a11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 443254217 1250 443252967 443252989
    0x8040212070806040b0c070f03080114121002030702250e010501170711031b1509070f0b09011214190c0507021e03190218011d040606050a0303021c18090902 69
    0x455150503070f03088c1034600034100103401e0181e149005400c0d907040c949400c0444c01c003080c482118005200d190102c8604201a51008020608601900c0c01448113500c00c0d07102400038039107d65001088038104840c40d02e0b24003050307000c113042140164110600c00c00590311a50060744900e030404568100e5010949544a035035502800e4110b0301a140001c1c0b6008140700c2408010310320044d0b805e03101c1d64111951031016000b0f02c40e1148035440704000e044052001000541410b0401650150300045524210b0b844446a00f2000fa10705041008004401c2c000f0104c0100d046000c20940d003010b40c0c020210b02408000a00410306a503000170340b13120455140204180040807a9202c4000740310507103e900740e02d40224002e8030140c00414410020405440c1a50f15411128420b10220556540c02400c00b0300305940d142c1d950040030405848d000408005580a500204a03a074070140714213420031040410714040102c8401103080301084120503004890aa0702c02055400003800003848200d06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 443255467 1250 443254217 443254223
    0x50402062208010e0c010504060309020a0e04060518070609050622060c051005151e03070b131403032d04090b01030c030b0604120302100c08040212070806040b0c07 72
    0x24001440107044080c010203010b8642c004000d20401004000c00c950701c0800d4100140807901c01d00042c07240070b01c60b44c0101c48460004040d624030b15998030681c3e40d00e0340107840541307080e515601000401d01c4003503000c0010740180001442c495141c0b8900401d041c41c18081c40c2e200e02c000050100c00c0c0c4182182070b40034020100460882c4607601c010140c01c0d010210700448150040c4600f127940e201481c0f003020721803040c0d00348079946041048100b10510040e401044103086c0c004519004c55107040180401a01035080720075920150490a05000c1041e90300a0070717040c90a01458a054030702009583c45402650444801e0180242410110b110030007201d01d00e1180c0070400240000c42d94204034201402a01c0c00c001e1070b80540c0048080d00c905207144c503004081044204000f4414200d2007201a01900c182c8480d614a50b2047d070a0b1403101680500041c0c90b50b06000542c54403840d08641d4000d100000c010803440c20a0b660385039000107201034400c0c145840040c07807100549044440d120782c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 443256717 1250 443255467 443255497
    0x1605030619090b15090106140a03090807140c011112090609030a1b06030c0302130b09010e04050f0f0105011b0b040f1a0a05060a030305070602250b09010b150a0305040206 75
    0x58080700c0021240b10080c2e01c4c0740319401400001402600038071000c01c08400301c003003080c90204604c000340d004d021461011682a542004142e0100d00304a041c0000050b01201030122518004001051070805182034101d40e08040c21419001415104171000b034001554150388412030300700080d08064115038060b10041111034168141c0700d40241040903501d00341c40401c490110310070200c0403030103030012021211405940a0201c021400c02030000d03848145041e50f0306a03160b4021a003078800175100c00076207204071070038000d071300015a0707506024100a19121861048000c41c914071080b00754070280c640d004000110b03040c4508180c464146076044100420001d22402c0d4a0501c401c0c01c0306d0141c01c2d0b614280c0415018500340c10b220048130b0709961201c0c00c2080d40e40b20308000b944000c003009001b1403c2e1812190103402c0c1b248000b0101d02446c110f41807450301360320b450b081d50a00fa0f1400c0c412030741d00c4a600b0100b4505070035204003a40515001465688510102d043c51041907822203040c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 443257967 1250 443256717 443256721
    0xc0d02040605102f19230105090d0203070c062f06180105160302031008060103150b01030c120c02070512010c02010e0307020109030b0702070b0a050901021605030619090b 75
    0x15000006844900712010750580704c01d880c08200407815400c5000d184ea142c00841e10282c2d0801640c002103541d9024246003a020895940c0d0380b00c0e00d0011260090007a5100e0007001510003041c069110198001c0c00918034203203c030f99407015213000c640511070a21203000e12000180c191940030401c545030084484200010a80b0202c0e55031104555a4282241c4c000e001142610180a664043d2500c0149000001c0f103001d810b40203904020500082c50a03004070000b605e500803c9a0f500a50060090880d00341d01c004602c82518582003450b07050600300001c7c4081142c0c0080305148004907000001108140c0c40300403400c00e08690302c8a6801031005c0c2c00301b2801001940404800c4906030020015181501e18031912401461006804101948170820110310000a80303a40404070344142e880707954560f50450000c3d005104c4800000c0c41c041400412940c041080b002c0501c1283c0c0c0c1c480c0c03410301c0c00c400241e4501c0e0040030004a07103006000d000c0d090841d9040020170f59403101305540b583c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 443259217 1250 443257967 443257999
    0x71b0804030f200d080d022203030e090705030f04020d1a010627120318030503031006120b10121409150610050a1b0b0a05010504060b0c0c0d02040605 66
    0x40f0540424a5044568004041c451a045620361429544041c45600b005580d48680300290000c03204d84107035010004001c1c80640a400201020b540b00b501d84c0502100300314188401003000810342024041d081040c0004503920b5115164003550440f420f2851145a1800901000071504c7d14161402c04070000726143e6008407c2080503c02c0c1da2101007442c4e01e44841b070740400c145101b02740c1c80c5d00b10b02c034801c030200388280241002301c180d50b1480320700903a981e174500d4656030044800305085080107205015040d0b00c01d609032480c4125040500503010000d001409680b514140300043c01071250314003200007155004040110200c5101d0320b55854408603940d220918003400030b0022100d180001c3d00362602181d404001c50199444501300a2090b40070345a000450103108081031020311a000001d8482c001188114400308011030b0342d501d000306110640f6856000030481c5101804070010344000000c201d006000222040706140603140040741c0140030903045542c10a10002e520029 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 443260467 1250 443259217 443259233
    0x30f050f070f1814130c020d11120405060f09030a03051801080613090318060908060a05100e06030a060c03020c1c2304080106060512060f09011517131406071b0804030f 74
    0xd223034582c2c1ca4258400d400e5a0146072a0942108880240030040c8010b111500780740d00604501015600c1d0145801c1d05540004e2400810000c1203000420000e40703511170001385901034403c40070a0802e901d00d802d00500081002c0c0d48540d2490700c3c90b42c0d801682d010706d407159032031070006c107190059800401d40703c0d030006080403014090b485d01e51043e90049071041038144a20bc0c0b1800007030b070034084c0d402d0401c50840e04010303014001c10790610036010110080340c554402c40051107400d460040c0e0300d000182d855400e01e5504003034405c4020403c582c1081c003d81002d5454510400305002891700c1491450201107170160b6000040c0380d6282c15004100e041e0400d00800031300707185d003c1800c640d0390345000704580d1029114403503802040e00f80041042d10b101f007080882c0000a410209206402e00c0c03002c0804803411070380d003100c48900c01d26450502289a1480c102045035101400c2245404031002d0200000303c80d08800304144400c010003070101c00c0064901550380400b0101c2400760134182101c4c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 443261717 1250 443260467 443260483
    0x18030c1207060207080303070504170a061109030c030a1709040e07091e0209311104090e03160b040c03062405040b0d060c030f050f070f1814130c02 65
    0x152082c02d1300460304000000a4a229039043d50380c1d24a0141051920000c100b80c100d070750f0800c3d20840b90f45d440050400c0c010002d075194954185c2c0d4072031a0202c20503140c8088000202e010b034002003500f1021882590040c0032180440c6180d60303541541a020600401c1c207810741900350b0042c2e40d0085a4882070b900b1240070030390a0000e00c0b0268070a07500040c01c03841140c1c511580310400c0f20074190b2048000440400a44030b01e600406050008101d000c10f035a084038075202600c20004007481415010b104d215541c520303400040d420000314030fa107402c00b40340348007000d8100c2c0c2c401e900003000c2141c1c04029002a40d400b0f80c0522083c4040e0003503070800d04820a00c14448109a64041750b0381c2030921417940304c004010684944412203881307101c000c100e1414040300b0992a400c840c011145603005a0f40101c00c03202210399580f03022072000b001922055030312003c00411b981c201d0640031f40c0c8100300d800d840d8070501e80d601c18804000000c0800c0204145000d110b41404018102d0640216001e5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 443262967 1250 443261717 443261729
    0x40e0a02030106081b0d08040803071406090106030809040b0607051002070201030b060f12190606050403060606110a0b092b0206010e01080d0c0204020c0115030c0e010b18030c1207 79
    0x446051345035100c0d81e031500c022440c0c01340b0b202d80100c0443d0240c5440348041000b580201c01162405403103030740c02d0b4107507805044107403400480b03881b0320060380c24100900340e8800c1c500d41c02003040c0b07815540c40148601c90228075502c21607c8245440482d030b40d07035085503040390f482001c503400c0c8140391140da40030350010348080e8003103880c00e40c80c001c460070114100c446000c902841946000003108850219103405000608602494403400f14840c10612543c40502030984620b0707162450341c98000180e8038250044000c01c42c2007a101014a00300081c16070742d565005048807060f42c0c0301c0d2859031412071b2540f0302404018007425030104a410410088418003020b80c00d0350701700ea03203803010301079005000e110b40c2055510544849410920811030724403110702c01000945428400c244140c00e480d1030344905642000340c050304008004004200000905403450340c4500343d854490450000d00500c030410303d9900710f00e121b079000e0f51b405020380d5a06403801400c3c1d02c89071001d8100a9642c1d04030f40248 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 443264217 1250 443262967 443262971
    0x80d02131d0601020a020d1203110d0f05150a12080708040902090906041104060c081611030f0d080103060b060913021c0b030c060903031b010504021c0b01050f0f040e0a020301 77
    0x1140543d44003040100816401501c10818000307103030307100384112000c0d40c01074040556442c00c5082c01d0b41c1440c020129a20f00076000f14540030303c940c620040b5440035103520a40c0c0ba00034a0307a403054440c003c0070070071145d004189032502400c03820030310581c1c0701b0301000402d14a00042c0100d00e007007465000c1c0c00d08200c10742d01c2c81482e0f500c5005200454100503080c600b516018002080b01034440e00000d00300c603102e0b0380d03800c1c2404909d00702080980520241110b141e90721017465200740c10100300e031041001d864001030040c0594604081c00b001c506000c040c00030741d145c0c00225402d80780c80b0103c813803070000601354808078081c8407400e0000390030170075141154022200c0c13007100c0e11046002c1d403068075400030007900d80c0c0d1401c0420000c90b83d00c42440d09805010510044860310301e040c1c40036095260810012980d481d15104004800340706070a00030b80b0041ca181280c6c0460124140141914000c0c0d8012172b010400384000f5600c04100b070042c0d64464100311500e0859031004c6162040b0f24400c2e802 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 443265467 1250 443264217 443264221
    0x30804030b060409030e0f0a03020d05071e0e0115030608030c0604030801051219030c0b07020f120301060f030c02100221010f03150f0f1404031701050d080d02131d 72
    0x2044251014039070041c000031081c6c076014005140a007002d99200c01c0042050040c00e660760b002c54010380125200751280d800104c81009014040c2c002800400d00d9580d20041d6141480c803524800801801241421943e040100710114000d600507000743c0604001c0b26190704003142180d5031108201d900b18005562070f00002040c0c00d121003d041c0803d11070740500b000d441740c20100c5420000c014825420401018502404610f50800c03aa01034a0541e010b407110a00e00310b055486c0914841d40070201d268100010042c0c1988491411105441c62402240480c84002c003240b41074a05003802440d148000b41401c00b202d182480c0058a2081048061b00350380c0c0c403045112080b0480c0710151241101c1a91034003e048954003990041c1b68001c4c0004902c100400c01c002120030030342d42d01c4c03080e51144040c070041c15004450b1040d00785648040100e950f041101003041d18140c0d9000502c1d850b0045160f000c0e03030000d50180c840200e01c114900d070741c16940710500a405040780c03007a980d0307086901c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 443266717 1250 443265467 443265469
    0x7020c1c1e0609200d1403090904080c070806040f0209041104060f1806030506130807120306030308090705030c12070e0c0a1209051b06070b07110c0103140c071a01030804030b06 78
    0x1da1314554900041542d001c1c1c0149813582c6d040780d402401c4481b000d0000700241c11656450014550140707000f00c030046d86904401c00030300d207416000d4000440319800181044001001c9100e08882c0c1941512010030a454510f0710806049019070407580c41410414041141003801e88031104072010070710152160f10400c85070388100ca81c6070002801303a07040200003440958070010344e28212485800c1203444c084541d19602601e11075210386000013078981c1420014907034007003101c81c0c0200c141009440c02c50714050001c1e43d9600d48051103270007200400c01e425580781007400303084000d00f01400c00e40313160300d0608405913159000d051000d010400320300c0c01d030800c1c1c800d5214480b15a64071100401c030380c081d0004c4800290440c41512940300404110000000f1000c8042d01c1c060340807030b11504650009803a41500300901c040c00c441c1011324000200083c40321000c44550400d000a284d10364400d820300b40107821208a280c002c001c004a00700002c204100c410090044078066040401e003519420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 443267967 1250 443266717 443266763
    0x204091b0f0e0a020a020a0c0f180516120e010509010501031703160c0f0203100b0a090b0105071205090a1d01060e0609010f0306050d030809010507020c1c1e0609 71
    0x400740001d81800140001d0100503d81d008150a180c0c500443e03a0303204081e52001040303985604400103a012018040000c42150326041d081c078100020140510301d030207071480c4a00581490000100000500c80814541d0a43d00c40b000c1e01a600c002442186414140d1074042d040c02e00c030403200c5442c00a90700540000e000140c4c0d010380c5190000f2002c210381c85200f265512044082a02c4096900e105000107075810488410300070a812404a0560b00181c20031024425030707403084818508001070011140ea03c4802c8580d0994030058039520001240003c80b0701d402090075040c1c004100c00004110742a03160180005e4584c1920b8103500d6a0300c0300b0007242c104020840003500004141b0002e120366000314004004100c05140000b00380340e0383c0d4000785401c543e4a1056021a0b00e01c400d00c24221030038090a544069a400244051800705010462484481051710403c000150f00b03082089146e0000900441e81d02001082d59030040c03d1450043ca44c06408880b07050340441a070710760000038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 443269217 1250 443267967 443267969
    0x50d0905060405061b03010611100f0e0111040b0d02030c0c0a080301150315030b04030c060c050706110f03060919021801020f0f060a090804080a2102190f0f0204091b0f 74
    0x210100a0861741323052402c1d02d00809500381e0000c540242c5070b0b4030103c500180320700d11340c480303200c030010882d07207107800c905821114040b16451260a08000174003644c02820102c60740340121810040e44d0350355464ac0b0025034003400c0f209043c140036006156080c00302001c050750507a50300071444d10100c40d0b072581c20f50031030703610003505549480012410408100c61546099219020342414a407511442d41c5800032a0030f1001420081007000c00d0b03c00038000d4902c43c80024901c2e0030605440e142d06a904108076000c020701c1c1034030403594500080c0300c0c03001ea40f000c4482441041d00c00d40d00e41d683e03d00c24030030400d00e20300428011b118900c51001c07a01e40000352101210202d0002d8a039a407a014802406040744000030313120079101300800030f403502e820054540c5403401210300c1030401d24842c860105044888076080c0c11940005240400b60441000701c000041d4024070700781e81801103142c9003550900d21600658400c0c0b40070030072401d101070811042c00e0f2107819403480324025101c1282c0c03e43d103121 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 443270467 1250 443269217 443269261
    0x303030e0d0507050c09180708010515010908060a0203090f06010902030105011b1505060105130803040807061e05161e02090912030f1e0106030f0c050406051207050d090506040506 79
    0x407284d43e00341d00c0c3c101800d06c580c10032003101c0f80345810213110408910348405030340109820b80d540c0003003007441c0c07002c203078010b543c2d440034a0a03900907803034943c00541c1c0344800340229200a0303001012415401e0100b00c00851b4107585400d5450540e550200c0d00c00940091003090701146508000a0360f03c03400440f0f18042e10781c0098a8100068500300364001484000c20050501400300701e1a0030f40d180f03a0206a0090203584000c542d601c1c00d005286003441943d500c18024041c84a004a502204005051031841c60a1801070b49507150001d0400c0c05003010400506540d514050100007040b800059408050090300c47d11100c1d00ca50800303a82d03030001101711041c0084c007407004c2080c85041001c0c59400107100030b50040001c0c80354000f0f1004a40a034490404a81d881620b01e400c0440c600a03a00d1001990a00500307091408002504511544106080300c4084c4e4000500c0e490040043c0c03800c2103c3d81e241089215400d2802940d210000d40b0f05a03000d00c00d800010300b036806e800c0261901e07000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 443271717 1250 443270467 443270473
    0x51f060906200a1104060b0408010506100203070f080f0d020d1b0206091b04060503030f0a020613080f0c07180f0b0604051f0302222303070b0c070308040303030e0d050705 75
    0x100030713240c4000d16440d104407164000c2e20f5801c001400e07601b040c041c1c0301030400d0800015003070074144108021300b50103039040020354005000070000700351100c0301140e110b030300051115981d2448659080007481041c0c0c0c1c11403083e10118101080031170550080d45c00e000380c1e0b8550410058a681c069030b55080441c0d00c4c00e110f40c4a5031140c800c00013414560929144041d001048840c2c8400000b811500300e01c0c55241d20042c081000300d50f80d981045007a03000022440182c08101141d2521011445003d11114100400251001c00d140c2c01300051001444141114074501c481e007408c2101070006030400714426420440c00e05624505002210b044075002040b450070341640810340f41050018035154018161b0038801900d404910844510b00f051112400401450a00355030411013100c000d804094004098021304041d10002803070300645200f82c15054940016900d42e619013551a000104032a0010600101305505030b085608a0040d00301600c801d84410346d070840740750060282c00b0340203038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 443272967 1250 443271717 443271733
    0xa14090f0601050118080106060806131a060306120a0804050301060902030c07030309020a1a12010905070e12120f0d0b010f140307030f0203040f020f040902030709051f06090620 78
    0x98080c3d0040310082050b10b1990785d0f019610444942107460540c482e40100b440c1504104680c980b0a0114030306070b1000400700304004100140035030310214012818011040000443d640c0d50318000303440b01801103201101c400b600d29141c510303010740042c85094013030341c02c2c010041403e40d882c1c02a83d12449801e44041d00300b8080ea24110007512003510141d0b0010000c1070003103040040d0a62400040500b039a0196444503030b40815134050905074403a140462405c028400c030280d0000c07103c2d00e1582c044a0f01f40144000803d264245042c4101c00058000c1c00120031800b00480c1c07015080c0d90718503007010004030070040010760b0104800c6180a00041c400c1040805041014000d1600400180750000d070b000425604039040303a0040d1003d64114051600d140c0c11458586c41c1c03842590780c02d6800b401482c2c81980483e076251254061559040e450b04001510b44008824415601d4000007155030b260fa643c000150005949000d1200060304040100800c880c0c040480070142500c030380104030b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 443274217 1250 443272967 443272969
    0x7051204060c030b040b1c08040b030109020a020c060f0d0e0106081b09090606030a03120f020706020c10061202120a0602120406060b04030c03030e03100c020d032403170906030a14090f060105 84
    0x80020040c0423a110001400041512206500a076010348070346800140d9071030740240044e140240100c0b03c0d6124160400c415450701c0c1c50f0342c0c140c0c0d5240c002407101145d510270441115015081a400c6518103224500d001ea0556107101684020310a050f1001100b0383c54040d901e90700c4500460f11190154803000543c0c001034403848503401a20088070001800441c8001c51105aa205803819100301d500030a0b121035540c3c0610002c500141050350421507140750111201404c68200c0c80680324020161896200c07200c00e00540072044e80c401ca08654070f0508940140c041d1b4004c1c0e4060b100a4900817000ca42000e071241200c00b504c0d080b0b502003540354959501143d0b60024604659014000c3c01c501112a142600a0a214040b160058446400055402401c480f0492450851045404529002544c1c041c0070002600d82060081260300400e8480305024800d0b01013440c4c100e8000030800104a071f03c1c1c1e204000c010303050144095a62200001c01daa143d404d80c0030f42c5e40c81d4103c3c200421903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 443275467 1250 443274217 443274259
    0xe100207020f18070f180e010509090607020c040209030c130203180309011b0201020a021012200a0c032d0f02010504020907030506190b040504050117100507051204060c030b040b 78
    0x103051003844c003510f06111040900031031b040e00e94414843c1c03014140040c06030b40381240340346a10031020f078021321a42c58a103000940c2c4840b03607480c4074041c9a0010f079654030343c0ca0a01281803100005408015180d00c1110004004e501c1101c50000c8140030440c041c15588000c0100c600740b00b41691842c030360441c2a00c08094a0240c450204e05610071000e00301c00581ba0b074138052a4400940d02e82074000d240c100c4000c800c0d190010b0000c078414643c41103103204030242e8419141c04400c9440c0c1500c15212902e019103100d01c0e00c148070351000b143d40c1207e150440713031004410740346812592103000c0303c41d103008240c0c00ea03401924001d44c8001c4910000b0007181c031039030040380e206400030032503d9400509060000054115000711501640004041c801810300d0f0184e076005000c401c110805158a4403148c030713100c40101c00307508030b07181c5c41d071000c29111032141c0282c0303025019440301d0b003a0504040c9801b0005021b1070202001003410400340c000249070030b100b180385004015201400240140c60342c022 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 443276717 1250 443275467 443275487
    0xf0807020705061c1b1e090b03090f0703050c19031a040c05040c03320411030a0c27020906040605160b01030b0403180f0b0a030e100207020f1807 64
    0x40312000e90000d4400c110038000c00455402c40d1741c03003c500c081d041030300601000280b50354100407100e1040e6100070691048442080f9290102c0e400d8403034031082c008071f00b8442c000111110a02c01c03001d01105120012500d0700001c00211803503078900b06040c03000b2120003118480a40007000c459000061070540c41ca8050340a849003244000d6544c64000140440700403003183d0000030740d5004a65500000c45851034000c518800d400e611601c40c402445c1c1818500600007442d0413461464155991420418504842c2e0300070302e8440c0c155180c40000003002e0890b86440c031020501d4041005980711842100c1030001d001d08031518182c204135003a1010783c098141000c0941c50002ea42010800380080390b40610700c51601e04281e41440c0c10014036041c2003401c0d4005a83c242c140c1002448024910700044500088500d40c803814035107016001049040c0e0046650301829044400030040c0742d0060203550300c01c5512484a019010602107043d032408022195407109101046030a4010540d0310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 443277967 1250 443276717 443276737
    0x2d02070201110706200a0503070813050a0605070312050108120c0c090406050412020606030d0e0d060c09080f031e070c08100501090c022a2805010f080702070506 71
    0xc01c81010010b141031034012203034406400100b11590704041c0c1060b2010300b4440d030541100901c2d04d001c1c662120361316031103480c1d80244200c4000a817440a8198860220f0042c50001c29084d5203541c2c520000c2d0190784410b400f00d00264604001840540c59480780c6810703905000010a0340c004c441d0b00306149940020182511441518013202c2540c0c1c94880281c41030f4420344012801f824a4901100c0d000040f207200c01c00d40d00b01d902049004c3d1400900420014101d28000616140100104802d410f4400d0081e155a0400a107c0d140703642110340081160710755021641d020003d801030300d443e40248580c000d1010300300c00d0b06484482e9100d0160400743d0044032064011555440c01a20b019240114503034031a86501c010000380100d07200302d0900d92402d0016145100700064000300c3d50f1816440d00e0041c003486400645580c485a9118484420152014201c00004440c4442e050b0152040500252140311241c2c00c542c401c1c1d0340540508429002054401e04000c100222a00550303010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 443279217 1250 443277967 443277977
    0x6030714070501091407030b06060307030e010923030708030c09040209060705070501091208091210020d09050d050c07120312051302150310050103050a0615122d02070201 75
    0x14100050311100504000c2e10900001540e10503d00c0c1081524108082110759600078400030004a00b4a86590354020421986140da03541c0b03c54055005200d500641c0d00c0035803800131044200003507504901f1000001c1c0520000304c2540c0303a110f036501e1091400c000c0400c0802d0000c1104bc1c1d800300c0150038900402440136050440f83c5001c141d06070802c2800362036a5114180c100034075604a00b410010f0400c000c9601d074820200e4880d00701d41d10407540c1c8213000b4240c14ac1d016942c81d5003440001070800c4004804e41d0303200c4205200c0c50103049c0c054410794450045640b03845049000340129602c1d400300002810840e898000100d00442111005405005185000703200c02d2080b44602403103044517800301241c122480c0140413a500c0d100c030110032200410018000b00344400c0c00b102040b02d00c02d10340030039150355103407c41e409050341c2c0d480354950250500c0c00e0300b801078000781140250429444100a040040500900209501c41c2050040661140031008a06168000300502d50042c140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 443280467 1250 443279217 443279237
    0x807050f0a080706140403091e0b0c010c0905040905060423060c1206040605240d020708030912030103110d230f071d07081306050702011b080f0402060307 68
    0x458101884948210ba03480300014261082003191321480500729115014492030340751950340035290b0300d902d0050100c04208082c000c2d00700d8440440c030101516109200035260340350202c0e864084c20b41c1c100600c0108410140120341e0307040a1207030b661450b400500800040d1615152040d911000040307000112030210016079031000700300311140c0501210303402240e4a0b007649410b900d0802000d0050340c45141085020403c1c5d980b0051000102e0326000854204403d1746401c907102c9103d18a4a12440e40c004260b07034042c0321003100550710400c1c000c02620000740c00f81402441d288401d02006142c0d03071241601145500b0806003007803480e40f00380c2000030440700260200303401c5c4110125400e01d9134403070314580030100c200744800743c01000c00c00380b1041d80302006801d8100c4801c000345014108404840001d2000301d410401c5445d15401c5a02005107040c030610090291119500e5505a01041440741104621412409119400700310303003a00341da21143d080111030b9101415a030704201c14590 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 443281717 1250 443280467 443280493
    0x170c1c02010519050a030b09070c030e01210b040c05031b0319090b04051204030c05041112040f0c050a080a030806060d0e0321060d030507031b030513050603070c080705 74
    0x440c0000d41c0c2554413403684601d0000310060a5440916045010b840384405010380c40e600122164440c03549800c0c00b114078004440120390341407002901040d24180400411160f880d154801c080201c01983e00348a004411202030319148804d0703408641100001440d5075081104c50003548e003188010710842030061002c0c8514003034420000050304d00710241401c0c081040700401143c0d00e012204602181450300d1900c42c1c0018242034850741d13000b50340762a00c00409038005000c0300e408041d100fa2202c09824035041485411a081c202100c1c00b00c5203000c04107140c0383c05003000e41216044401082c0c0144155030450749200b0282030183c000a00b44000c4030180781c23034041c446c02c0e40040d400640d01d40f001c16000000400c8008021842524030000340728250b165000280c60407030f0141000c03641c602c520324044410340900b01e10201c100c4000c182d55800c01d40d205008010200161b0760002c00c1544940070002588002e6072454041216010021300003070301c0d607018103512401281030380d18042c1001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 443282967 1250 443281717 443281747
    0x6031e030306090f060d0b0c0c03040609170a022b050715080c030402030c0108090a0813172805010908030f09070806151e031006170c1c020105 63
    0x61110066000801042103a0910b440f20701c0d4840c0c135240200c60103041060103c1d1820000300c03800382884250030000b41d580c40e122011512a10301d004103c1c0e0380d40f940c405008240c08018040c10480e1038400e107001c000c0200018a00081c95002000201e180443d50ba400c9410240c4401e0f44012640101508010a0050202000030500000030100c12400d2102c004c01a0380014654080c42034144180409610009640760b88807100f820716644503216684954940481004024024100011580c108001d20410700040f03d80201c0e5004103c0c00d4500c07069101e204c82520301989981c445003100f0007058100b000e5402501900c00001c4494980e22111003690085a03d0f034084840f40c03040c00ba800c0b45c10010b020003088800d000c6c1500d4185049200c50740f000d401c05041c851a190013096076402d03a0031001d61170103072004049404c3c0e8414000218003811881c03003099100d050040d0140c4040e180800c0c0200c01070402418841503070404190070003040b1700e03504161b0400c0418004622010003003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 443284217 1250 443282967 443283013
    0x3010b0d03030605130501080c10020a06050a0605120d08071d0a08070f0506040305100f0e010c020604120e09130c03020a03150f0c02101d03120f0c130b030603 70
    0x30394001c502e8504013400d0184550240380c0c0343c0300c0e4074030f4000100620307400444c11402204049a8039110301a0740340c0100c2c50403512a801600f0607103404d007840485421a400841100c1c01994103c46204c000d0034101d40340c03108141c040300403689250000301542c0c410310718a182c40d41e00040100d0300c5501907000c02c2d03800c442c0d504481e071194800c10317081c0641600700144030010700040718000e2415007103a4404c2c0c2c4500c8a91012440a1f03201c07440c42c61030b0341c80340d007100c105100194003c00c54a000000c0095803404250345c1541c100859603081c601c42d610a81044c41c2100000d0581b541c15200c504c82415500c02411040d104000011404001603079840700b43c400860082031805016030b030b0320004100315031151a1040b040b40c9480300d41d070b80864003c40c900c00c150491010000340e186544010846507502c0ca0a55000e60000140c142072103007007480c3c0940035a9030b030301440e10243e40d0801c0300c012611442c1030b0078555004a40041140c445220000c650000025060715011607203240c2980902e40c03e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 443285467 1250 443284217 443284223
    0x61605180904022d090108190602130302061810020606031510030c0e041119060516050607110c0405130b090c0d030302040501020105070c031209020105160803010509090d140903010b0d 81
    0x880a4030500d4582840740501401f0814050286040740503015207405008038170080c80d064001c40d8990100070031481c070800861300507008582d501c0c0109e00760901001d40c284142c0c410030358482c1400450707100043d030034800c0c02c020340100b456200c00000d966207072400411301419040e00510100006e5102c4031303d04010030b540c40d21034019041604d40880e0400d00c1c484400d0003280d60170040800b001402d120b40e01102c0407420041ea541c185448a90400030080c8005003a520505050103040d55211500102d08690342040d41c104020850401090302d4041e01c859480e0103602e1000d201050b0f170100d1094020201c00d08540c4030304e64040c0415207441000c0c006401203903010804120658082c040c1990284080c600515105015075001d40315004500341d01e480655284842411039000344c2c1110310051800390300300090f00b80c41c6407810f080e501c00d014050050740031601103003d0510024101043c400c560710b4040201d24042c4d050750054201c5a01160315649410742140075071546001c1c00319040c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 443286717 1250 443285467 443285539
    0xb0a0906110409140109020c0c0607060e0a051006120b0406110c1b12031c1a030601140f01020f0a0201030506040b060309060a0c0f0507110105120906160518090402 72
    0x24004442100e1307440c05074400d1610a0040014910089000c82c05c94460340c070480b0074a84411040c2440402020600740c40742092040326001d006012001410003050f079481c820a00a060325901e100399060070182c0000c003100b4401001c01c0000340c49800a1b01d0360041c5401c11810b000700300c0085c5140c24065072504610305040c0001508034180a0072110102400000441c5048101c60940070540300080403102c46c03e40d0780803800c0650140041403075100c3d80003004caa00301d507141e03c521450300703032084451403068200800300003180d40042620800003013260060800a5020340064000c0d04004080b581d1080d82c543c51f402c5c1980d074034030207180108540d80c02018a8a000d2456101b1501c1e40c0c0448424021250050100d9903131260445072450360240c0203d42c0c460807500141c80034065104022184403424003041255000042c09a22500e03901d00804040040140d0944003803081c0c03118500d4075605c070101c90384a81850413000c0c1d00a440980042c503a4021302d000200284891030010450340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 443287967 1250 443286717 443286731
    0x315090a0c141204030c03021204090e15040b010603020c1905010218010305061309151b02210304060c0207030618050c03070e0f07090f061205130b0a0906110409 71
    0x15901c0241c45103102e03080d40c1003500d8640f50340207160640714010402010003880120140c00c140c030a00030f4407212400010101d440d40c1d00e41503080054000c180d81c20080344140045200e8a5000620450041c1d800200000b440e07401c00c203080300030b98400032100c07400340300300d01d40010000204042c040005000700001a216038203040c14062007001d92201a04042c18042485a5a6203001d810070964006407000100818203180510f40307204210b25003805140391406007146400c50001c40e04644000364241d8118045070340078807200304480043c0120440040c4001800102c866126520b600320300d0049480007983d981d12601a030b9080c18000c20080d060090440400404000c290f4005e1000c40c0500302c0e41d401e051408a990300d004100e50b440b02c071000041000d0b2800789040402900d10703c0d8140140c01d488040240189405150070643e031850440025900394505031200d2500d68080231008242d00d560005c075010300141e04050399020780e00c2c5007030214503140c00c0c02000103284c1004046110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 443289217 1250 443287967 443287991
    0x30515040b0610020601140f0d08070b0117030901140c010c20070806041e120305040c0605190302090303121009061703070609140a052104050a09020315090a 69
    0xd480c0030b094035001d07400000600100e03e801155050550700001c8408118030181000607030000c600b50789003508080d0621014052100c480000c0507039a004400c00780c403d981c2c5041c000404c28a0b82e000d088150028003003142c096108054044124408800860034030150065032821941d082e82c144011032940d044d20720410301c1e44276030841015080701c080c042c5540340c4404107072a0040184028400d07a20080c001403041140070f414007070540c01402c1d20080b90590ba101a0050806039405d458000d5001d0000841602c10b001700d070302c0c3c107050301541c542c14101440e007a400ba400c0659400e9150200303100d1b0700706030249508514031499103008440c3d03d66140001c4401140e14540115591231003c03402030740c041c4000070442e010035501010004e140c6919051800c5880c4245006095034098442040c051100001c3c1c62000032818440840c0307a0549004800120701c1140329580d0401280101003000340000e038080c3d07034042c0c00000041c3d01c414500c000958801e5088802c401c54558451140201c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 443290467 1250 443289217 443289233
    0xc07030611040501080a0902030a2112050603031204050c060f120703061d0c07080c1006080f0d050d0633050f0f07020301090506150f062803020403051504 68
    0x5598007500c1500e18041c10440000e000c0d01c0000d24650071244c4589107801151002c01c00c0d104c4040c0c10405814021054916902074100a9000c0301e000410014008020f800ba51045074020240200150319142c60503102c1c02c080c4c0001481907540303006010030411a078a515004202e5001090030301a920107841c604040003810161105040502c0e00c00107200080401240400115913000710b0b211a903074070408850984138040d801040030f0b401007000003103040005495030100b04640014416252210842c90b500e0300403902c2c1080a41c4214203414015000700002c00310080000000316009481d4001e50b000700c0b14650000c4816118a48030801902d114542c01c1100500ba140c11840c000e03401c040714019024640344d80124100001d8043d045590951040540641c00b00541d8214506010100400312000c0301c0b00d4040e90040c2c00d40c08252610710304803241c0309420f11003072121000c04405200d04a940448507003d05501308008008903000300320b4007a140f1051103a60362107160030301e4032440c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 443291717 1250 443290467 443290481
    0x709030204150f05010c0501020d060b07052a0402070f0203070803130905310b01081e030705030a270902090f0d030801060e190f030b07090f12060e030c070306 70
    0x185040c4404001d00c2900d05001031003080f80e801b46045103141d42e05007480c034020b02c43d15010600c1149041d00018164401c0405000e03858040e00980e29500d8108032081c02d0b1640e031224110300380451f4146900540b03401d602500419006001c0c9030901c030803543c086854160180c1001e244c0c2c0c3d002207506d00901c00c050a00c880030305540c200c103203c6401c001156400000c13006800000f0036003005a00c00d0110340f010500312900d03412004440079560765440c2213450340341003000000e07046043c011242140200108541800d6441002545800c065000c00c4400701407080c80c0050003000030114250031505c51070a8001b4103000c11006940c3d050b030404125a025a060905000d00400a0820042034220340d0050440d0310344e044c4290320101d0107001444c9030b00601d094490300c40309410046440d8201c4154001a2813180300c084050b03032518141134510312178612070b00c058464000010312003640c0104508240a00c61180418224158121241103400240d0400c40f0307544000e008200340907241c0903181c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 443292967 1250 443291717 443291741
    0x30406060f06080a0c03020c0d0c290a050402180403020607080f0f0a0b06130803041a031b0d090821011e06111002070f06060b1303060e150709030204 66
    0x31194607005003d02482001801c0c044890b0b9109405d44603035000c1c0d0111030b030341c03103186007581d85400c3c2c0303140040d0011000c000142d038808030342c03183c126000414000000300c0c0500c0c0501c146a40c1d0f5103000650140c100240126048401c407080c0c0c008148540c00c000707000e00d2194000e400740d8030f00404001c00082000300303c0100007900509109402e010341003240d42100000e000494038446100104c0d0b030611800e0003442d18094007200002d00080d0200140064074000c4a1030f200d03008000b050f049480c0800d903030951a1070300c030399030340542c00c00010000c4c24000d5005901140d55002a1500a1150001c20284c09281d11240500c041c50f0b03140030115014051a444444030003084401001e0202c480740030b420148261003409203003003401008a41a91403407148159034a056924003203d20300c0c01c2100031508541441000714175035400c0310565400060091071b4021191442d00c030100541184240d6200344e002d0701d071612856250300b0f101d00341705407510303111f01c807266166205200860315604c00c52 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 443294217 1250 443292967 443292989
    0x301060605070803040309033810050607032d02010c02011a010e0d080721050a1b110a0602031e09033301082404050a060e07180203040606 61
    0xd000c040e8024003600e01080d00401000e44035519450262040340298002402c00602c039004220110040c8001070359100803038031826119403000310140c004c1901a0740222080021500074005402c101c4041c00005000c0e10f4000034200e1090032580d4030591611042001840d00310600c1491038090061903480300861000f00030700c8609410300341410040300382141c100219440703035200550390b0030401c2501e56045440f0030359420161030314103d1400a030440040d00101e980f0a05100e900030340c2500e6000d0181d07107a0300503030543d00c00c072486409221001203c5845003644c44120780d40310010484083c2c4040d400560f07075040800c44085001000d008441c003603020070001515981c40c046140c0c10140480c81c2c0e0070314038120840d4908180c1d108c5040b02c5220b811008000120400001081e40e0102100041c8000044500500c2549500112401340441d030059840b6000621258045150140c40b8815541507584a101420714034001800030342d00b60303402100380b10a200852041c0001030600c0824 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 443295467 1250 443294217 443294219
    0x30c09060b07170a03021e0a0201050c04080d030b0103230604051b040b03090f190b070807051206061c09110a0303020a0b0402040b040c050a180b0418020706090b15030106 75
    0x25014102d40c43c54116400b60501003400b0354824001d40688100390000003030000c0341d180304d800b0101c1541003064090300543c2004007040011042c1c4003241c1c16181c2c01d1024140c144003015007075002d003180b0101c4d9410183e9030309a030038400c034043c294884858696031192607a410088100801d48034003600440301345003a0040004060311050031241102d40220045482c0d40d00c0b800340c58146480745040320346a0191010407000080c61074030b10750b030892140b44083d280d238594810865281e01c0884411700820410080840b85c503982d11140759000000070a941d140c04600030096429110081354080e0040c1c44155a40c10814020941c1c00c61141c140c80f220792040c6181c4000f03640e0700a00c2009407401c85404003090654803241c100b916038840c050030600c585440e8030350007442a80840c90f00400190380f0861400b0300010f08121804a40003011802d0405050001c0102d0400c50100800c00c203540c20012a0009000c1e80121007680d409209001d44d01d140c00b03005c0005070400b50601c0f0f403082e458054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 443296717 1250 443295467 443295473
    0x7110604060819020a0c06050907210b0703050c031305070f0f08011a030a0b040804120c08100b0307060e0d05250b0405010206040b090307050a061a04110a0f09090204030c09060b07 79
    0x6c2c9841035001000414941ca13100c00d280c0c02c1030a5a0488080381c0c00b405040d036600c00c0210b03414602d080c458002c05540350f48815080b01140d000b038500280811081011075680d103a118060364070507000f24107a9100039540c040e030701e401c1c440b203a1220040d4040150100b00310b00081c450360780000303800511101c3da0311010340065140c0c048007000038044400c00d004070301448511001e0304c020303002080d10140800c8544c104074000c000e481c404c0a01038820103003020b2100c5c0303460044480c2c3c1c0601400900506042080548004039107054498102440c0e685003804540104500004001c0809003040254040c0e10001e40f14400342d040300d0a800c0c0204800c200b41e0741d0000e20039a00a421901c00e400603100d41c4501c508620030141e020b0824440ca0a904c4240411a84452400005401844140056407041c48155072008001d149200c03010f10650300864001c210b00403090b0214034104d0103171900d850810040340c02a420603074036081d132004140030181d010710614000c0d042c2c1005503410f03c515a9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 443297967 1250 443296717 443296727
    0x6050f0a08071101151517070807030b0415030507050105041d0c09090702070504050129090f03070621020f0702190503010603030309110f01050a0507110604060819020a 74
    0xc0000402072650009814907110350f0f52001e180c0340f403600900c405042d0224218201085000b0342000d035844c903000e10302290103000103c56403500300c002c1d08074581d5000301c1644e80d1807005040c00c0901d6102c540c0103030640c0d141d1047c0303c0140031115090581609605040d80b40542680056040c404108420320684810001c0380f0b8044c0c10b2881103000c80d540380c0b0140c03c2e06019192010b6005100042440307201c0d0340220b0b1071000e0b154191410000c0b680c1ea841c00a10030740000300348403854140040e40041c4c100c0050002c210403000604084981449140401c1c03400c0126032064001030009814840f501c480703034080d9003000404142c158200005090503d010388501c9070020311860104030003883d4200442000001000020b00030840c03130742c1d281400360260549800444103103284030903d0801e85005082140e04803411ba40311420801c242c8400d6400d82d0100d0801e0794207010100d29600c5503916103008202420b4107580300003d9040c0116150b54000f10080c81e070440a0060250b8070306a40c3c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 443299217 1250 443297967 443297977
    0x1b0a170729030a1e050c0d0f11040e1e09030705060709050f06090414010b0a020c0607030507020d2f13110a141306020d081e010b07051c03060f06050f 66
    0xd000184d0b911580148070030030700c2c002c07500c0300c00d941001c0070011080c409002070700020003201c40c1401a1000300c01d4110884460003054000080144020701804002c50440303580044020302104881246006944510768201c442c9400d96000044070b404002e0280a0305030050164100140d40c542058009442c0d225040802409414085281c240954407074109500806081c160100c0e06d50f1070741c001701c1080e03000010300e00240c8540d151021050034500700702c40f0b40d517070180d45882c1011b40d26400c1105901d940201034807100f640754215680390904000d418840b03500c1010500c242c20384802031040c0705202c650301561641c541110040c1e441020303000c40d0080d98075864141c02c00305044002003a21300440000c440c0d90203164001140403a00010403140c58816174880389056034494110040003080315004c880300030303c08001000301c10f80110180810f03502c214203440e070200c0d05110f032503221071203219081c0000791103030401c2002005070800000a0001490498908103100032100341c2480340b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 443300467 1250 443299217 443299231
    0x130f0603060e07030c021630170c120d0f050a020a020705100233010e31060c0305061309020607020d0314030a0c030501050906031b0a17072903 63
    0x45080124049100b1b2110030040d41030521f00446254030b07116090311310a56540942d000342c2e0590300c003050100584205006066012000e00b0340780c41c2d2204015010303045000030843c14030801244a02002e01280501044a614580018114001041c2009071a070203000810b03480d00c1000714008107980403800f4030030344005032841229030945040c12840d03c0c42001401c0c06208420f0b2075064501d1918130300624451f4041c00304078031070f629510b0340390552800361911400c440c00c0c521114401e5502030700741142440c2500d00800000340030384510781035854440d0b160b0000b07903560040001c82d20340048001d50290041a040049240300e5002c20028403800320064801d47da108401703420140b04034042d045248840388400e03241e040c01c40d03400025240840c00304011034104000410745090080c1450720450004000300100391a4460001d244c204603801940c000c0c51000c0e000c00d80c1d80d043c1480828030300c4410010b0002a03d0207800b80041220b80c0300c0903103141d59403d640d005510b02d1000b52070300031031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 443301717 1250 443300467 443300471
    0xc0e030c09060a1208040302281401170702010b10110a030e040608010608100c0f051902010617030d0e030304031e031e0f14010b0d020901110102130f0603060e0703 72
    0x2106000140d0001440d03000c4202521341d420341c0801c1001c81405003003200c0c800d8a4103004000160001c1107442000c00460a8040b4080c104002d04584401090f03a83c030b00c1810072102494504200602568040342e1010150b91121119002da090510380207040086a02c0c01d2103c80340280840394a41c1c0d484500a4101311103d0031320300d9a5503071030780088000c00b5100020000e45540740152600c80708280d80b400461440d2041010ac480c1c083d41003000c40404c0d40e03450360300d000d46a40005100c10401c060341011596210303070110710416980b0750240f61505400c008c684407418030300c503142a40c00d1551990401c0d0000d10a000009405c04c80e4480a21807041c070001141c001c000c0e0840082401a1030052030900e40101041544060781c051000c40070640014072246040c418101808070082c4550313840c0340310401400c0e01c2c28070a5800ba0401c00e4051419488100340c200740a42a038008910340485140a550300b0821807010050b89001013042c0d040c00d011652030a0841644608000d084e01c041c03507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 443302967 1250 443301717 443301721
    0xf021902030f0d0e12010903051e0c07170708160302042403060204140102060601120c02010b030a050d03240501080406020702190303110a0503041e0512060a0c0e030c09 74
    0x355052001d82c0c4680b482000320f400034494054010700b01d16030301c1c5120b40615440d006168030300c0810b015140140f81c0580300d05180c5000098003c40038450413000e040c1d003207001d006c19540301d882488110000c084c5255600c002c0b0240c15039403070070005941d03c44403213544000d82540c000700b00a22004110707030301200c000455401e41ca18454640d1803c00c03455080c0e4200420120801220358080c201f43c82107803100302071001c03c050069988500503684580844d04050004805d50b6983d04000e281030490b02c0042462104100032915060780020200e030145c008144800a09904d4441d25004040b001000c1e0341405803004075a410041700d01842d8104000000010b0600105070101c0e103103181e0240c840f00f1aa0701c000110801500076000403000903492109600751650700007100c4004580020245143c54079042c20050260b0141d0307170311100058034038000503403079441c0d4030b80c2c07500d440c0010040d00c123502c2e19281d24000c0383c2640000340c4c244200b2402840d40340d1400034003600030007001e5034109110307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 443304217 1250 443302967 443302969
    0x40f052406070b13170c0714060703022a03030a0e03010509010504030804170405090a09030305011a0d151a04060806010c030807120b0402160b22150b1f0f0f021902 72
    0x145c58020303400c10151400051003950b05800091a0341202c070b104218020145024080201138800d1100c0070300180d00080802c1c403007802040306a00101414080a02600025400310b42190800c140c40d10128543e0440940355040a0081c194080b40010081120b4541554068100c14014101800c80110700c91002c6900d8416422030300a404004c2240505107007a400200142c01030381011400281003000003c0c613191025440064000184030041c100700b12445464010300c00e81d5840707140302e90400c0380043d516184030340c8841141c0d402121980e6130707402e08502808107240503201e513040001061380d00c2d0100e0f17804115207030071456618000c02904030041c3d074040584440035409074410720000c2c036464000c103100c044290b041d01c1610941216030b9407814006990021403601e4880300200c0b0103242c0011a000c881c00011688140b000440c61805000300d112003140030301c14443c48031446500d0340c002d0742040780901450700514021211450b00d039030094903400110309130b5241c4c5044510352021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 443305467 1250 443304217 443304233
    0x90906071d03070b0309011b0f05090a0302101e02030403320f1e0c0319150f0b0a050405060d030e120a0605061903030f0509040f052406070b13 63
    0x7801c04000c0880d00c0740c3c2e0304d80029031210b0740705452142c000d6180005540100401d5444180da0000e0754454107001050322105540c80d81c0b184030441e611020f09000440181d8074020300c22000380032551410b0302c20200b0ba400480b1212100f00c004150751080c0b0003040019444550b400c00048020702815800c82c203036940e10900c04181942c071040d0b026555014260000010300388a0814540c10384030452100b00c003e05e51181000424182c140d0407540300c41c080904a440700b03c40c2584200414500c20f02044041022541400c85503000b498980c06441c440e4608135032050003403e03088500300002c1c00c200002568000d1900c0005083c41241c00c1d04800640d9152010310022213098151201582c0d50b20340280207280460f250b074407640ca44103486640b0702c4100f40480a40e80d140e11030805043c0d0705401030319650401401a64016107a288803d203d1026010b000c0c0117000400b0700e208560290b034204111101d04560013070040e10140326090200740030a084030340118400c0035920b4030034520305200c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 443306717 1250 443305467 443305517
    0xb0406080a0f111909051803160201090e0c180303211006020303010303020a0818060c0f0d2a050a021008040b0105041a09070e27010509090607 63
    0x3210701441ca4901c1c14801841d6082000314810000001c5201c464020818030040f81083c921818003a0002071080c1c0600354840e58010b202502c0c0040c0800c1c40e100e07010724660101c1035000c036070301080700f040d421940c208403920090074801c581d12155291a209480c0103014400300b8004c1a414040302c403a842d10140210b0b0560041151091100380316060034010f214016919411210200d4400058841c030200990b4142c03503060f07020b0030714002c141c2c0f1285150f8000d0440c840102d5190f00e203084c00c40d41e4141c000c10a5a0580016044894910107268204005042454103119021100103401c1c4440d42c04000e205180e1141c41c1e0120070341781401c0c1c0c9000b0500344003c0d0846c5540d100c500440f034001c070705540301d00e2042c046c039040c0b40c2c2c03900d0920050700c1c080c071202d12820305401c40e18074142c81c00d403034041e0780b0140ca4603004041116100004041e0040540d0080c0340400c0d0b1210300001c085141a0a40500030a0b00c004180d810520a0a980c03082c1c0180200e0402200c800c46001ca00003e825904c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 443307967 1250 443306717 443306729
    0x71203120e01050c130902030628121211010b0109060c03030f0509070302100e030d0804030509180601090f0b0a051b031215030c011d010306081002070c05060301180b0406 75
    0x1005203003181280184c4c1c1d01000c00415240c0790400c0009621109008881c42500050100248485503400f040340004403030061080030406410042943c0400528841e01e00f4040c030316004440014120191440380d600104c040715034102402400a030360403400388011030302540340c03014007030b1544d0800300c006003180721964451074208010300c02d170314000003203500076680203c58040c5100c413042810b540200c030138072180e5015000500e5002890380078030503e0380d00030302074100f0502d458240d1000601c142445104000d100804406000d03003542d02a0400014180351411100707414148002e0151078020000880201320f8005800c0150a0000405805040c0001c0490740c880100350f0a49031102d4048031503c1c044003e030342e102085c9240010b2134000d100010784802e10001062801c000500c2d541c140388606054403544000b0b0712100400c8001d2044c0d0f5850390044e1286054940000c540546500c01d51160b2428401846511203050701c1c0c1001308100e4000141080390000414050a0745502803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 443309217 1250 443307967 443307971
    0x10b0109050613170703060b01080112080f0c161401090509041103031303060b01021204050d0627030309150501260a08070b0f011a040302060304020303070f031709071203120e01 78
    0x3084c0c022800142200540c0c0c400e2005003e10980762004503104182440f80100c0010f1800001c4003085055008224040d01d0202c0e680c0b602031161581c5240c100b46500607185060f505008000c0c403a0760440c101e41842e0b00740f07001e134807152800001031020507002e030000d00000820f0702d5140e41540e0030011221a02c8001003403070603459484c10300c0d4000300f4008500398058000d03180300a2400c4c000c10100d405030364000b0305420250b1520380b645001442241d0314841c0c6844200368801031201d035411900340c0f40740300f60b07008a6400030700d26054802c00b40e2821003820b081c1c205001440741954a800100001c0c000c0710a0482086030b62030307158900803c0344d901900107d4009070680501130503400881c410315201c844030600b6603891b031078880803e17106110741036030000512013400140380510043d600705000a04890402380c454984030408541c1107412000303d083c001c1907525601000a05a07071044140000d0030b0510314101c00d1440000110700c004080107071194803246181d41940c03140540c3c00c10f01c002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 443310467 1250 443309217 443309249
    0x1d15060a0e0d05120a0f0201060312030b0f040e0a150b011b030c150b120a0b0105010c0204090b0f01030201021006080c06071b06030605040b09011d061f030518010b0109050613 77
    0xa042517001d004c550001490170070102c03600500501459084030783c400b2140311081503a06045004109202d80c07a40c1c01110411143e101d95074500a00303020705946405050070000c07600d4101c1c0b10385070219010720041d04054862485a8100b0508002a030303c02d8446a5510f0244c581124001c0c01e8032401030650b50410302c540303010b6183d0744c8200d4030a8400e80e03918298445228900c3d540321030b120340050001480340014422548a59800c1c1c1903688054004205c171440e42d40d40f4503000d04100d450040b0104454010425913a04000b200b8055020000c10416107081140e8240c554511030180d0f4002d5900190700f0302000f0480c050215503080c1c00c2d040b2200243c075207000a001d4502403203202e100b1800c01102880300d20b000640241210001c0300080418008450000404040103203015885486050502010314400c01c1046400056035000a0341d841e02208000008056046d100c00aa00d000c80d000940e0b42c010f140346096520450350315450304c400100320f01c4440100d401c00031440001403c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 443311717 1250 443310467 443310493
    0xf041502071a0f040b070f090b0c01020903010c18090c0c0501020a020f071e050409064d16060b120309090109021603030f11041d15060a0e0d05 63
    0x40386699a0006180c0e400b2a0f464200e8807a50100098070041c001c0503010020030402ca020f00070075140c442040c107202e5041651440885501c3d00100817607070040e50002460a40e03072500380b092020040c1681400c0d2840d5480c0024000c220943d80035078001545c0e10a08200e01c0b07809080080f40080c0c0c400001d550340d0b070500704025100e008860004d6283d118005001c00d0030420902010365240700010300d403021038a000b0400010741851502540c8056503040740c040c12902c41c0301d403c500b02d003001c5030aa1021300340040c2c1b1213402070200400000414000204408890f0b80c0e4100d1740801d0708610044800301346410b10704000c190181c83d6591141c2070901280d02c3d1a00440600802201200c550f11580e90719400d0400360701c42d958000320001d09148a84c400640254440e1000034240c08000920b90303800c80d0f02d1032440d441508601540c2261400002501110b000b4582d031100060f4210506140301c1d40120303026015601044007441200400500350740c40e0000301d00810b40d00a4200e80707030484444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 443312967 1250 443311717 443311733
    0xa020706080c0f1b120f0d1509090c08070b04140108040212010510030b0a02122811030603100e0705040e1207060c110d02060106201b030106050103140f04150207 71
    0x103140c100c024005c4000c5103443c5100b4106031060341d24030070440c0e46015042c440c84c0c0010900c2040700c0880c88507800001c14510918030400030414841c00311821650704007a0f006245c2841b644c044011030900300b10510580b020603204100f0742c402820700c0301e00b540b664800100540800c001500d1207600e8082084141d1a0350035410044178050400c007441c3d62180807040c4280d204412012003504031130742c04103e1344200700c840700c0e1100c00c240359181182d4400c4104802a980c03411407017002e01c02c010040c4185450103200500340c4025144007008007500800c44141c070f98890307116a034821076446640383c22865090182440c0c0b000074404550b07843c2100d140403401071010440e440c0004406200f0034043c10780000302890320b0756443e0000c0c04140e10b020000c9075450349101c0000994140381902100801e0204440581000864001d030f040159201c00d15084480651005041505010314081003003410854281c20030180e0b4004200d0b69035604055100030b04c40407504010310710025041e81404221 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 443314217 1250 443312967 443313007
    0x60f091401020315090c0412050f0607020703030e0102010207170a09030615060e030d0c110a0518072705060d020f040605090301150312120b030307050a170a020706080c0f 75
    0x1601c800013610032000c00307001800100701e6050581840401c800c3c00301c0044240b204030000d11803400c0300c44800905d01c600381083c900f0b40c1c0040c090fa000550500405420004410b82104284021801e0000d90346515106c00840c1400040d0b00b1000106030000620440c0c0a034055034002c5001d0249104c031501410000c8100d20810340001da054802c0c8980d07180200d020502005a5544e800c48400c040c6c5600c04a400748080c032551105030071000003450388801c2040c10039032000c1f440740501480d0891340034101d24001030032a4a038544265014000b00484003050040c2c92043d5000754460320801c8596000384a00641c0b03250b50b6001080c0083c14070b5100c0014040b50000743e0080c0480107841000f4444200799000080240c4004c5824506241c410340c85161480c42c4c103000401c3d0302c00d009022a065074411001074079603400c546894014010103004103480c04d0310582d045441d203134101d00002d44511a40c0030b0701c0200000e50300030400c1c000c00703403050742e410b9030140b0f00841e07440c0d052509080d549006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 443315467 1250 443314217 443314231
    0x5060a110717060703020a0306170303090d0504050d032003121012110409020d170a0e18010501140f0a0c030e102717160f030f060f0914010203 63
    0x259900104052842c81c02205840c400341004100f65100c445040d0069042140701004240d17072a9000511f1841448407407201ea04803030091503480c02d1854140313003002002426a000e20100708410440d5407100484102034942505d4001101e4038013061121801106041e10980c40c0310100d00c00d85070155604029005000d501000c0b80b4041e0780300400420b24854503000303490a5401500e102d45414150030071402248000c0903600040b101c0e5441c42c0000e582d00303495498500c400f0802404003a00b1541104031720f417040b00c403031608000d11400e4010030300050080c10b040200b0b00201406060641060314420221640003648800000381c1c01800402110700540000c3c050703080c0e42d5004d01b4580081c0d118403035199165001240c600000d03000c3c250100340302c0b501d6180342c64800070b29040701d01800300c0c03060101d10150070840c5004003e8002101c1da071300007100d452545e0310b04000044c07000120507401540580c000c215240c14104101c01024030f60b101910a01c1c6c4a0318402c4004410340c000d51003418 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 443316717 1250 443315467 443315473
    0x3020f030109231e04050c030109050127020a0501050702120f0d1215051207090906230106020a0f0f02191502010216062004030b070801090902010e01031505060a11 72
    0x2034281000203004026642c891416006034680c2c0240c84504814a5205d40154200d03041450f00b140401d00711800280d040c7d030983d5580600030103440f0001044101d80c40b00410000c0d6140060300040c907800d0300c0d40709160500000050102c2107480d1405a102a4009141a51822000e401005d034461040300205400036086c0d440081c001800d5102c3c2e08480030001c00141400c50405003488a201c0603620042c0091040003c001005c0b51903000e50104503110340004114442958261104807070b01251002c40d0618400040c09503541c000b4040e5400c0b900b200403801035000741d08102d03400f80e01314100650030009050050303c146000320451411281103042200d000d58520b07204900700d025201504030022580701070940494502c1d001405100300a41c84444102d0b03102d8056007656215520031905030070034104126a082d0040e44250042c54900003e1000c1089540020115210070304c10798149980c50381d6101a031800b804000015001c081d210360341d131720702072000170f00342e18000800b011243c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 443317967 1250 443316717 443316761
    0x90b010e01031406190b04061d0a03030206070e0402070f08130f0812030415020313050705300f0d030902090903070507210614160905130c03020f030109 67
    0x54400c0c810042d078414010f10076601038a031001040500d454002e08100042c41c8290302064044180d4000c0008083c9a11800702c1e440f20000b165502451802801c0c0c802c00126608101281c0c001c138549501c601e4074981800f20111f0100080c1c001c3c000e64002030102801044a00d00f003018001c010b005a4103000d0034950340f60350765500104840d040f03003c0c03000150401d14400c080c0f941c42c000910b41203481502010030151120769031071300b00d070402c135130021880507140100400d111781400b8800207401c0944000d4034107294102038a051061030007000390050502c521070b00c5046c405005102400030650241c40b0084a0418024060010110207a104880304408500364030400011100b48551207005441c04038602841064043c4241080c3e02a000c584444000060243c0c407860030401c0e2a0a801641400c1050031760031030004004082003809400501440960390b6a048146201015000400c45c1d991019049020340200085c00c80300d41004400807030030300301c2500683c0e0302d400440c803555054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 443319217 1250 443317967 443317969
    0x20f040b0a18030809040f0902031203060a15020607050c010e01050f19020702100c03200a03080a0c0e04180819140a1b1703040302070e06120312040c030804090b010e 73
    0x15002c02d20000300000000c12500d103140c00c154206c44600203101900180e07050035038004c00d0500316449608442c0410000400a40e450300300814405458520420000c42c000440040e41c0c1c1d60018000c0d00c10300c50049080c100e2803030250170051001000c40c0090003142408071201d440e00a0035030702610106001d146144045003140700742c80540d5002806902c1d40a16540705851109036080140c0802032042e094038035560b0401c0c541e4403000d46150060610b07050504004141c1e510190030179003e1810000c4000c48141e0080100c15515000c0307400142194407001c148c0078400e03072440c0c0217124540201d003181d144600782100110b0440141c4480c040c4423004110000d461140411620214404100c40c8506401c1064030721445441022000714995801400704610b400486084005034070003601406102850b4103540d412034400c3c0c42110398400b64a0b0b02540724052500071480c41d01d08400054140003100d00c0d400021600840500d5503580c5881b039480161604642041c00325464000300601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 443320467 1250 443319217 443319257
    0x603181506010f0f022112090303150901030312050c0d15080132040602040b0d090302070b1608130306110c01050f010510051c0e0703020f04110a12020f040b0a 70
    0x1544d14550183c2807000030420310b42061148103025100c00340d8203000300c81c4010f0303100701070354024101b140c0110b40b03a2034004030401c400118000e4850003106c00c58010400030ba000660b0b010400708940d404a0281d44945a80e03015002c4d51010044c69818400d0344ca0702500c402c509201900d040304028403000210f2008111405900f00c4422484090030031100e81c3c08100300d51031500300703200d0400949000e41e11000b81110760440c24242160715617400302c12040503010099100101000c00429003001008144001512058440500f600c00002206918a0b841400c01c0b400f0b036901180400909035401902020344d00b050080000541c40e280108850003014039010381203d03801000d60004401c404d10403546074102c401140ca20004400300002500c19500500030743c140c0751001088410316600400080c051010440781c005c80c80c2c0f9081c644120b40c580c080740d510025908040d86032080c48a90080244500801d40c2c021803804500850004003801c0203042081d0740b50f640c0401039a01d10902c8030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 443321717 1250 443320467 443320487
    0x4050118060e06070f0c09051f0806070c170406031407030b03070302010f1b12020c060705060411010c0b010807090506010e0d03080601030608030c1c05030709050603181506010f 78
    0x8042042c0c201c4030081803400500601542d07110300090440383e01d00d03948911600260b40c003c00c40d1030341c549041240340382c0442e00000e05204c07021000b10840341382118032511040c000d0b0800302000036200c01e0105000d43d2010306a5a03000b0001c2c1c0c55030f110358800c0c0042c018282c081b900c58809a4a4000ca91964401c0c020390a8505004002e0050540b4540c01034500003010400d050a000d203141ca03119409603045a8042024080c040d0720444081d5408024108400b2200e042c2c8034043c00c1c445139002c9a0005400c80e0702ca94000041580116048010307500c000034080d00502c010009400420300e80c03000f10b5402d00300e412000c41030000f51075910054641c10214100c0c0c2d5001035441e40c01344080703449122500e0308008107050018096440310800380c19540f01c000e6412a550050580100400b2420210803810766649840c50841c1080c1c400141880035900c5001d10840e03012001c03901021201204814501480007241c070a2001c043c001081003c00302e0700b09000c101c81001c44600c840c0070366140d40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 443322967 1250 443321717 443321729
    0x60501090f05310c02240c071e0c050f0f0108150604090903022505063114090901110906030a14010618120b07030c030e1204050118 58
    0x40e801410041032140340c1c125982443c24014003c0c80301c150890306503003121a070001c4960045000b40d9089800303490415441c0b00d62071422844001241c01c80002c06a580c0c00110406600e40e480d5510700f4220001c56040101d050701091110441c001c0000e03100400c5c0c11254181d8409201100c544200044c1130104c03506240840c07060030002d0740c0c0b100351060712500743c007000340300310f05050b1280c2011045800e5440704401681c80705d403e80400c915800d08940640c0d2038140710b407080508180120380c1e00d004c0c1c1030241c02c1d4418508100f000a501540c02c2000104d00c80e060300710b40e0781ea200b030382e61505441c600c4c3c154080c0d0041c40c0805c0c000300741809840c0d5000c5540355900c1c50103000070103228003944002d11608900760b480c03a001d40802c005280302802814036658002a401384001298038000042c1e000300c1c10038803201d9989001407109105c190744144e55060020f0b156561880a9002c1d1030b60310761a140c0c0e03001d0448004202030f00f0401410a0341d1003a40c1d0035024186012a00700008614001d503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 443324217 1250 443322967 443322989
    0xf180e01050411120f100e0118020a1512020708030609070804051902011206090b03100207110d080c01060806010602012711180106050703140901080c1602090405010b0406050109 78
    0x8410350410710b5024240140c1d0b94211170128141d481803d003000d034034100381400076440e00400429401d0901451b5018224a0f95040200249500060043c8001e00c52030280e4041c0c400c8a0300361900444848180b410b9120f400c0d59540e6092505044a50049039643d1040b440d542c007055000340b090303415a12a680c454000e101c0004404120072003440c0c1a04102c0c1000700d648452428071034240203003402007010176000f0800c02014002c06040c007c0740144019040c1c4180b290202141300304d00800005601580d190a0034905801e00c21114412480030044960070080005100d2000066003812101340d94001c000044401c1c0301c44801d203d4200703a00f00c00341070b032a03414004104a50b8400440c1907000300b44030007807541d001040144240c00da00c484081400031078150b09142e040b805c084884224900d000e403520040781d0002c7e01d0324101520491840c0b002045029200022a080306452600141072103078500c0c09141c540e000c0c00c8208640d50045040000009007540039100131b5090752800280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 443325467 1250 443324217 443324243
    0xd0e0d240e033c0c010204080102070c0e06091e0a020903031612030218061b100501030b07050a081305120d0203040c05030c10030b030a020d0503270a03060b04060f180e010504 77
    0x305a0342a041300c40d901000d95820400013868410910040041da1b22800c14282c00030306d0013a4002100300c00608441c00341d0640703005c121014080325013000030315103003440d2428603032201a44a402405011000ca825100008503d900818000c00080e81244200041c49c91400c100c1070880503070045070404021040ca80d048030307546180c0803014014079202c80207001500303400d010b691460980c09104141c40543d841c001030080c854508075030340d409007550500358030704828004010711179100204030700d1842801001140070400d090203003800c542403481185484140b1500d08000031b40c02510110313001c64003072400040c83d00b030100b4425038088009101c240500282e0f07a05a0160040422031030b803500400e00d0800c01a5a4450102030040c012401161641110580c000307014224200281c0d01c0700b950210440c9030364501b0442001c0d01e070b0055010030012002000700380078100300d411042d002640b0303e1020135800f94440d40808481e00c224020700c000a4030b1010030382200c8003550041c0484401d000c3c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 443326717 1250 443325467 443325577
    0x9010e030f1b0c0405240415090509070e011e080712021e04060f260c010c06020c06010b1e070b0403111507030e0d0e0d240e03 56
    0x50071860038962032043d1005485101c1c001002c443c2d0454504081501c0300c81c1e0070f440ca4000341010b00200030f0944080000b08070340751038200c108419200702c80780ca41e150b44c00601c480c401401447c000f40075000708440156161209400c0e12007060a190520100f6544c2c0021110300010f195004c540b4485004020300000741c091120032404101901d42e005007201d00124546c5461080390020001c031504038442d24141052107180f40d40c00c1d2100006001c66104414081c1804620300369910024249800070800b075103001300181c000c40fa01482a07004c1c00000092034940c0d08002c1c1006c407490b0020f10b81d4030922400d00c280314003903510f024245414400005d0006401444d6806420601d20201d440d00010303607242c903010810496030440081e44804409d12070a0301004100188000c604040381c02000650210321450a21440030300000380f041403840c40c0f6100e05d404030841c2d004040c000e0002c00740049000741da0741c2c010302403c400c10740c2c42603070828528545900039070380301c940405906102000b80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 443327967 1250 443326717 443326747
    0x40513020310030c15030f091205160507140102070f03080a03020a03020903100f05092b05190804051006141201020c150a050105010906080f041112030309010e030f 72
    0x802c2c651190b1014807010012a01a10303d880c01450300d40b040300006070780312200400f9a652020641026814102048009211000f84000546c0189440742c0c07200304610b40c1d04420382d001d00d4043d0050081040c0800c181c610100c205180c10003e07008c860500c0e64501c0101602016807201605d0003406200894150344240c0041c004a40f00b0b10340542030203e1500081e05010042008132141c035940d40d01d0b00080903540c021103920815590144c00001501c11030942c0c2c8400c41d02980310201c0c604034040c2e01e0720740a0030603078003100e08041e500d540c000362144003d02041d4041ea0280c03880d03c00c440c1c0030038802140340180000d45000c171458085005120083c0301030171240e0307007102d801075409000003c10180c041002c07124244441000402c6802c0050034002141c00c1a0005410014202018403425410400407500b2103100c0c0003101007a030341c0f4203042c241e0b54900004039502003107401c9000b41110f400009140110007070700c001c02204081d5a40d5903a20720401d240191201c0003030080d460800703152 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 443329217 1250 443327967 443327971
    0x60102060606070b0c04090c200d05040504090c030507080d080f0115121416090f050f1c05100515040c2001060b1902070602070302061803010902040905210405130203 73
    0x205c0100782082e4403030700c00c0c40070b588040d0290030025251400001030b00e103100d0804240d18220320003501c0005502c007001000d40c82117000c1d0601550700c1e010040c08001c04040c4001c02540c104050f901c4642e12241901d858001c090031680000d0045004140d80900c0c82401d0390403154002c1d101c560581c80351030180c1e031a0790001944030744682c0e11000c01a2404807601124422150b01c0782d94a48011400005081c060342074001c1404144100c20a10894490482c0e8628180040380c62080d64201c0340c0300f2080c10111940020644c0c0142007003450610419081f0741d0284d004010740100202c0d202041c44101c80b1001402c00005440d0451481c0da8405444a00080c1c01d99800101e551902c42499245aa215070341c0518100300000c0d09030f10b41d65040c010180641918405070855514540008490f8015154244500307004082c40e03510326582503018248040e4050002e000381d2409040103601c5085000d02e030507060400d11a00403003900d03c0001c4406480b00103000d41141d40401140c04029000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 443330467 1250 443329217 443329231
    0x605030f131a040c18060b031b0f0f120606090a06111e0705030d020615010f09090c0c05061602060a150e010905070315030f14010b0607060f05060102060606070b 71
    0x40103119038102e061044481e01c203a0164101003901c41c81c1501c45c00c0c0e0b01010b002040b84140c076180003032209081803000c598101c540d04a80c0e1610b91341c0401d002e54144110034401d1074070100014402c40c00c5400d00c02401007850806e103a070300d0383c0d500d15061101c00d20600c2c5040d0b038407050f000c10a018880c0201102030441d9000d00403111400c58414521091808110070100142d101e018200401e01e4100701c41d06113840d107880036000c14113164401c01d08112900912506111203c5155031a951007215128018540c00005000c04000004040c180b4100b150040e00c0e140225800540d940c01070301202c01d05500158020200d650f28400480b0083c03203641025040003881c5400003030750640300c44c141030103020000710004150810700d4001c1d084a0b85c21440521105d042c1d08208003182c1658401d0050f160019402c0c00c800111943e0a0700412442c0d6410350300c2500404d40d081800a660b200d98218401c10f4401c11141d10781d50016030b60b45404840d003a078000001c1002c03000003182041c0391600016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 443331717 1250 443330467 443330483
    0x9050306070f2703020306060402040e0112020315012405030c070206160203030a1101060f0513050411120a0209010b07022b0213050603150709150203040b12060a0605030f13 76
    0xa403500103c150258035540d60342a0400d18070500a500d001c0c0403440e0440422981145814035004407d240c243c4141300b44180a0a0039203460155203061260100e42007070203400d05903540c0c660340140d80c0d06003d103424020701c041d454503a81c900b41c043d00440340114034420900e4244801a8208401c2c0e42c0310303c0c9800d0003c0440450100181c900b000600180002615030000044038041f1141c215851039003c01c850980b034003810045610364144000c00311054480205403641c5e07a04250807030351403114030182c20502583c10300e030a9503400715010031180d01c01c4920b14a00e907a034060035400c5000b00031001c0c0d4000d80400440c001400d0f100c2d0565441010450400380182690300021509005059800c440076214000c1214a280600800e41c4445165014581504021100801c00e4496000c0c4a91046400c40503814041c001c0040d00c6c0140075165100f96680300400c0f10300f080400079268240110fa9144e00450702e41d0284040d07030300c030342189081c98070580d032408401210503254460540d9504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 443332967 1250 443331717 443331737
    0x17030f0706140f10051c080d051807050105090d111e04150b03070315030f0c140603041a0603070f0f03031707050d02070303110c010e10021c090503040503030a0e030d09050306070f 79
    0x5800c1030090600c024408c84009000d05d03000d03240c5e0b80d00300e00d0061801083d030803a103000c0c4196a0817000340d6244030303000e40315490300d01210f15100d09186114200560310540300310b480e203a006401850560060f04c1074400f0b003d24100011400558500e0340921200013030f05100042c003241c403907030214000c885002071960000e9920b445901c40e0520400050302d88030714020003071100382c06c3c0300d44c103c82d940426130712540395142540b032303811003410100c4401c100008200b0104e038241d5002c00c448005001028411140290348001c00c6841342c003e4442100404c1d0703001c203c4603d2401c00462140b10705130940301c40d0314101c1040c0071840250f0013610704800f45965800c00c2c0c20b001c00d12002801c04c2c03d23285030002800044d5920000d1400d1170701940c0c548030600402c030b86a04200301da801c00130314945401000c25131075403900d0071b03500314060303504280d81620010130b51b5a0811390286841801c0003042d0252030303005050034421140d00f0300074003803550581c3c441c401051030f49118800038400c4c04868030300b82c01d0314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 443334217 1250 443332967 443332973
    0x27021c0804090603060606170708044b0203060408070507090c02011d07060c06020c0106030602030f010e06030601060f110c28091517030f0706140f10051c 68
    0x39030403a8012209690b981d5809004020140c41103401a0584c0d0420440c1c0b0402c1400000030403070018800c0041140348400f0908000c01c421504145410318961100c03602d9018551002410769901d2244c0e00316250301c400c1c50342c1e0548626103d40c4c0ea4016014003081d0f91152103101455104c040c040b40d49204070140010360204500c81c03a500143c950340007162941d5070f0311405018591081c1c5100345608201002c100c12a08195201a415440710001d81c80b415000c200d24010700c08c691000d0f181c940000200301013040b161030524180c035420500d00d4010784809090550703508090041c030f004180c40d00e40c41e188003401130318210107070381100040342d48110458001c103c404520482620115082886a141c00140020110f028040c011410002480d60240c2d5552a402d18890070003508000c820307404200d5014001c88a060b540c0d401c80599540b054980103005055080741c42800402e40004a440f002228100c01d0081208200c003148840c10502000303180082009000100700d0800c40c01400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 443335467 1250 443334217 443334233
    0x604030f08091011062811090405040807051204150c021215010f050409120f0215010311010806040207030f030b0105041a0901090f03120e0f030a0501090627021c 71
    0x110300c16580c64101c0c82500001314902100580400302808841440552084c1c10714440e003a031101845020034120140702581300c0381d22480e00351036003081c10402044140b01c00e000043c40118414401c0365072030500f6280804060040e8054014541700c4e2517103244449204001402c881400106411201f40c44407455900e480c00c6401c070000c810100400402014008190480c01010161424041c80c6980c0e40d82c00041c044e40e00d8dd16050001c1c008400a5552003008601f83d0601c08054582255840c0c1c2800302e4030100034100c40740015003400000c0c0c0d0a04140c000e56802c1689030312031054585500e40300790b02522040c40d20504202e070034000000d122a035024005416085003406564420401000500b034021301c1c0c01058400500399410000036030034244030001c1c40c6007440c02c91130500c2e1801c0080c0b45030b1070b41c88820743d1603c61010401c050100c10360050007102d1041408112404202c4400c002007220442e00f2402c03031090200c00405400c0041d1003030920180b10079103090041c1da80c2d65400b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 443336717 1250 443335467 443335489
    0xd02060c0f0c030717070b031b0a050c06070306030b0415020f0f07060e0c0a0e07140c030901080f011a07060e0102072603010b03011203111c080a0b0604030f0809 71
    0x8154401c4000b045241000c0c00003101421443e064400c440d10700300420780c0d81e04400d201d0404400c20010000304482c1c040c881104100010362140d960700c1500c7c0800804603000b62408448074001e55000c109894004e1017908200da1780040380841701d544a4889000c030174405a0380c0c184542d000c00072400c0c600060002032410010a0311142c0c1c0703407800e900780301c4112508150551880d900c000380400040da902d2500c8800c94588440c099007036590003030101d600c1040c4001000455070042061240d80e4008000703460400350a0b03036a90a99914203429100408080c8075030002034003441c03008114010260b000740400781c0585c1c2c01003030751001325440900720303444841e080d02c0c207e104c80280700d100340300192001b00c00301c10342c0c0c1071500719418820003040b14801032003402c05205803c92910700301402212990214a03085040d00c07054820010b038111702c00040060f03580085c910000054000c0741500c1450503072076001e800182030a040d0303682c42e01c1c00c804030f64003916808014440c0c00744544d04e8800f065 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 443337967 1250 443336717 443336743
    0x90f0e0316060b0405010e04120c02060a080103050c0a060e0f061210180c0207170a0b0703050901060602010e15060105130f051c050a11040f05011e061403060d02060c 73
    0x329458030365007800c030101c0d040707250480d1040f0b08017801041800aa481c40300c0d08107802010000303c01c00d81e0001690276040c4440025000f00c40818812a0542c100d01258100e0740034205a4851040d003008000c2948054020310010a2141c0b00d8079081d401c1042c00008410341c09040c642c64a100304a4200e51035000311080c500488290906221400413034a0840c5803001420081c0030040d025040a51907540c103000350005540da1801000c3c0e071600400c680f41d901c94001300748161500700300e200100a01000c0380c40781c07019030070403000065440c814460550781d4481e05014000e45260300c00102d64000340901498104101070150b0841840e414621400a00007041c4008400b0b20b0007050242c050701c0468000301c0c0304505100720003c07480100b9003000c080d601c03c19001c43c10841100140040003d404900050761810300003142003181c085881c980c80010012a140c40c540d5650202d92440011001800c071800603c003150700380c20081003023031400740b0040c8194107050303040400740e142c03041035a604 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 443339217 1250 443337967 443337997
    0x2210c030c0d0f02060f0a0507120e071703070c0e09030403021315091404061d0304030501060509060402070c120f0b0c0703030506030706020c0d020414041a0903030709090f0e03 78
    0x1110b1074005000c4002415035001078015840c4c140600303400400024079003540c042d00c44000071402403060410342d41d4141003800400040e24400301d00f135640c00319806a01354603118005101c1003030b00000240c0f94202c0c2d0042c00644e4044c10250201d0101802511000803407100b8000400140c1e074021504ca00ca40d080040002e4a0562008203405400250b0044068030b1600c120507001d2480c112616500079048000820a21020092445540740120400c5c03414040440c000c01040810b405c2081110f4046460002a480700c00401c001c0740f040c2d860081070301c095954108410380074008400d00050251a103040640e0703039903e40341e94440702101c2d0350510410020308101059094810207800503030640003406c1003418180041c1d0740c2c241c82040180300750056030410307045603116000203040c0094486040442e080500c0d085040007900540384101070b11141c0015118880007041d24401c280941c2c070008503d1400c0260401441c0a841c44801d907a1904109583d00c03000300002c1c85030244038119 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 443340467 1250 443339217 443339233
    0x180906090203150f0a0603080a0f12061d0c090303030412140f0a031503022b020409080702010f03090c12030c0c081b04050c09042d050a0e060702210c030c 68
    0x20032000400404a1707100c545480c0341071000ca000741040d60710809103814025000304030344034165044d008003d2800112030038a24007095800e09403180c80741c4500d100b40c442680342c45103004012240a5030010507007507441480014040342001c41c04000060150910500180084a8040d2250303c03854484038a21000140d0031429503152003000c02e00003901505522060a6900003803596035903e44130120170b010404000d00c840b4041c02c8054000703600401c03c0000c4100b6141c540c141d501304043c1640403802e0b51441070b075004d02902421120030b0340196103948117810420030b5140b414821000390300b00600a00c800c40040c00c41440a400380100e0801400d40c2207800c0701607804142034806241c000c82c101801d1108984c0340e0310640307240c400202d0300071801d400c0512084010020b0b8480d180042e21f005050316004842e00e5009901030286c1c2d41c03050201240c04407249035220741c240d0705500141e22030041c118000c44520606100120b103590303614600300784440c8051843e0440c401007521500702d505 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 443341717 1250 443340467 443340481
    0x11032101051c060209010e12010e071d130305071407150f02151f0906030204050a02090102030d2f030a06140d0602210a09050c030718090609020315 65
    0x1490340104000c44058011030030b05890b500401445200080c0350640205225000740e002d8002085d40600182246c3c20080e008500180a41800c4d002d07900317103000750080480c0d02030b03408902c83d0781003501068041c1d203600d800d555140740a003044c2c016000c016040c04030030b0010f800b0707800220807094260010004c1c282083c0400381100a00762003041030104020149001c2600454400e26994040400026640d50804884140200301e5aa00ba81e21401d002c049000742c400e40c024810381e802901d081001d0f81c0c2c2d25040c1c1e07040b4420300600a000d41e009003d9503121a600350008010130b46d80846441c07010004901006924040030701a101804000c010401014000d00ca040010443c444c81422041074560104521000d2114003038066900060316104100364500c0344881d41014141079500c91070b0a00ba000c00808040e50b0494081c000d01c071a02010f4940043c800e0296024030704025500400d000d40300c80217220300003003203400584031024400565414800c01415403c03810101c0c100e443d20034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 443342967 1250 443341717 443341777
    0x10207110f01300e06090708030909011401090e07021b0315130501022203050c04050603030307031a0a030506181605010305071e050d0605030a0807121103 68
    0x2150601800e550303006408182c3c1c0c04083c2c2605100c0762450300b005000148414a078268041c640c081e40c0c6420a0130080951400003500d602c41d03025081620000340e01c03001314a0f104d10924000701c0d80b0400384001840b038030fa1501141000104141070810382d107591034002d47c0031100704442d0400540c01048424052101c0d0540307046402c50110060080030f180e802c100030032103a0240542d141100c0c00e035902c40410400f5411180c6500594002002000758450802c0d0803207014013084030180140390072292182041c2c06810701800b4000c000e18150b0703031101000c4006002100103e640d55600131242c41c1203454001c40103014502071070103000301b0325017032500464151283c60303001c00d1039000082c841d8940e10b0484104040d12024030300801c842e1201d0900b10f4400c1024034240001c1c84600c4480c0950b035811000504a4001510b804c3c040c0039602d0040540b13401e103482d000f603c0b40c44200180c03400139035000310f8207900c031a0f076043c007043ca414006191495500005400e00308902032085103000a0513103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 443344217 1250 443342967 443342993
    0x106081b12060a2c070f05010305040b0115090306060f21030f0503060d121101110a020703060f020f0a1814010e0103151205030d0606030606020d0806060d0e010207 72
    0x40c1c449614a200d01450303103503501e5006001103482c0d1341e901c0e9204803404104907076030410244503c2844400d0340090010381c96203014462000c04030601107001803154006d00a0b51300c42ea03001618424103a28000d00c035040390000072041400c2009e172340c0380400042c0144c070a16019003208124142e105060000000384141c3c0c050001011820520542d000207a000144010303c0400746007558581d240e0304045116a501700c040203001b03170056900d42d00d641c1d5200c1c0c518070090340345074028001c00d400340450a420b0311858500d0030050700504401e102050080e0015480c0107080840145001064411004150000da06110009032180003c40240d0950072500b0090b040d2000d0b40324403000d20400203000307503610b0a004c0e81410784880000c1c840320280d8102e03000030131484a404109144030320b0496240d0f0b0001c110444140d02d408000310302c5d14441d2042100791142500200058146c11900350741c1c050b0020074866009800300040b01004070366015501c05050007400240c3c4401003460505451803030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 443345323 1106 443344217 443344219
    0x30303050609070906020a14240114040c09060e04060305030d150e07020a031d0307060c030e03060c0906070501110304030c1b050612180106081b 64
    0x5a000305110707803021034110b1081d80d1812000d42d640c200300d00900380140d00000f0100005107040c1c0990038407403100811035a40040d0f0301203840410203100c100501038021280100310607100e0800208030440100c038144003c0c800820010f0140c24030340b08810400074214501c43c010713141c0d130348000c01031508a0207480c1e64108501884024040c184554a000c0c070003004001461110202158003c01d0f00794040d00440d03016403070459032001c0c1042e1180301c68180114a07070155408010400c01804691a0080002c2460a0207003592428005240c0a5000401004151401d0340c0459030017440440d4203544800080c00c0490040a0121000c2481c1d10000244414190003c01303160009114880c011001801100704401d00381013841002e412040502a419003c01441400c680c01055480c0510903a51407800d0305007551250342c880d00141d00004680102c92814031801c503540d1038 = true := by decide +kernel

theorem cover : BRFrame.Cov 443165467 443345323 := by
  have h0 := BRFrame.cov_init 443165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 443165467 ≤ n) (h2 : n < 443345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
