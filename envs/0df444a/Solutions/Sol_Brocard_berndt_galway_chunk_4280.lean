-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4280
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:06:39.040057+00:00
-- url     : https://prove2.me/submissions/5e7c2fde-c0d1-440e-9280-e1490e51671b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 769604316 ≤ n < 769784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 769605566 1250 769604316 769604323
    0x904020d090c08101b020318060f220602010207200a09140703060b040b041412030307020607110102040f0612090b0a0b01020f2d0102090a030f0b13020102030d020c 72
    0x100a02c01c48020001041d07800000030600c2400020040411000301c1c007055040f000c150960b41100164000c118070042c031031464107411031b61100a00b000741016903000603400b00d81c02c06e181e19009000c6c42031801c140d0090380d200210040801c0d0000310324101e441d883d0003000c0401c000b44c600e41070700c903c10303500055110303484407900521301000700300040d20800d9007003e1342040c10b0320440c0010b410184d001c02c0d2074503148122021184010303085490580351010f40c1d00420035210440317511160000311809085400e0004503c210055400388c550f40c90603400291207062443e4803a1a542c0c410f103c10702c00400c5015136201034400b1824800200c8024440c000c0162640020081c240340142050214040c52a00250200c04090b000c1d030340d4281901001d260786052091603142148440700c0a401c00c0e5501002448140e10258009480c0c1107a01c008240c2a041c42c0d4002c844500d4480c890314140150004604d810060540801007440340c20740000395a030103100d441c03150b810350004130194a0003081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 769606816 1250 769605566 769605581
    0x105060721030b010e0f061c0e032803090206070221010f05010f050603040507090b0307080321010e0603150907031e0204150e011e081006051002010903050904020d 72
    0x1103040444103904039001005414014465400300c0d4810b0071082d803515080d0540403801c040a803a0b24200702030407800d042300c0706042940341075031503031020044451582880100701c00d00814111004216100d0b138200004591042340c80100f5280100c2c0000503a21241140e840a1301100e05501078106d1071b00486001501c55210306941d80307010704080700e4081c10f0300510304954140e00040b6a065503202404810301c811140144160020300c8240443e1685a110a10303041c4003a048448140d1101941031965001e810052681c909680d00b00410352020140701d40540100c550b581d0702d0f410114042941da0002c0700c0d06150042600c4001401075408011000085400070301e11101040c0012a0000d1002c00040580c013460503c800491030f0302d50400d000b400c031071520a06441e540e01e0f084052820b100c4040e00740d52044100b000024488a040200104921211030001030302d6103400d0410850b8090b42c982c8505590418000001194220301030300d41d00c2c0415200565201c000d411004002c2980c2c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 769608066 1250 769606816 769606853
    0x17010f0303030903140c0105070228060c020a021801091b020c0108042609040c080112080c031201060e03011526010902030d05070c12110409030e0a060f020c0405070801050607 77
    0x100f086d12040e5070541049018980c140c09544091000d01c002c009020071003101d5920b044d04144481c000515264007000b119115881942c001c01c9145c1e000400040d00a0892200c07a80c1c000014031810342503106141c00003070581d49080204444090203511b940c01000c6150501141d41d00240611050a81c0005044000c1401403481c0c09481d81d0780000c1e4001c10070007802039260550f08420b250042c014581030780c15241c9102040c440c107540d0b08045911140d0088441d002c103100342501c80104a070154081c0203161079808203203048805050841d0501080d0003041c510641d02081070b01e00881c0b40300003860001507030416040d010502c240c00b410020364000c3d058421503012002c26036101c0c0c05010124818450703105019507032031b9a40c094036580075018000304044d455603034503481d043e400820700c40e1107030401d08503c03c40c9800103502d00b04268094404124500740101120364144000c0d140704008440030006802c205c100100b89100c140681c60007001d00289900030b109200d014020754614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 769609316 1250 769608066 769608107
    0x50a031e300e031c0b0a050909030904090b180105041509050708160303080108070806150f0316150519030903020f01020d1b110a0602310617010f0303030903 69
    0xb02250207542eaa008022032990070300c0c6a501600303016594001d010340070400904007000c0c0f604082c10400151001380c07a40640d03100410026909484602036505124014216030307110f4078003940905a000540040c001c06a45001e0800c8005100c2c030300e10302d40c5149640c50002e0540e001d403170101d14050490304845154881e10f060309680418030104c100a4a2180c0d440143d281d03a100300d80caa0321070250003000444d80021340014001d0504001c0c00b031403c04006c280c05c04024081005c281400491210700300078004004041c020003000940b0780b20304c040c2500d01146403040f84a0314001c0074a4180c8800100340e00c80e2640000e040c030800c103810507140304000843d540c10044102100a2103103120150364214401d2003c0c0060b40200b1191154460000182003018550381d00c43d00258050f48101280414140c80300090403801c50000004c0300009a001580505285000d065003d4130b000c00408542c6900c0148001c0b01203804c5070040300d915081c003180700ea9040c941a91017040e11043c821007800d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 769610566 1250 769609316 769609331
    0x6030b01050c011a01020d0207141504120b0106140702010e06090406030b01090221092e0908090a090b01021c02030909090c010801211b050904050a031e30 68
    0x221100e40013107211400340c00725082c07110720385003d903160f2481d4820707141c924a600c000c0000c58180f4800060385001241e141502d0aa02c8034039604207031113245801d581150300240180026500480c15203040600c000001d400d20040e40d000a000341201009140102c3c404104501c06855a030080d4000e9a03000180d1809580c490402d84001e41004204050b10040032620b080005141e07107045000c3c124000180810810350074011040700741081c503410504e5002240c0196101c81d0f0300c5107540b41c1c0d11605030150360361041e1040010702803454001c02c01d1145009610702c0c150f81c0006000b0710a14001028038190f030340e0403074140e00f1805520366140c1c220900c0d5082040200e07001c6001140f800302601c604450307036280c5881c4440003000c640c40303a071110b40e09817010001c0b8040132240340002440d081100c81090f202c80215403031820990b012102640000052820182c10989407201001900c00790461400c1c1c640009040e8600c420080102c1c02501c0003610301d81192401c600942c2c40c0200040c401d01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 769611816 1250 769610566 769610591
    0xf0b06300103031e05040f060813052a040e0a0b070306150c0b070306081b190e010f0e04030804060506030a0506010e07030e0705060403020f1c0605040b0604051006030b01050c01 78
    0x103459602c80c074a41244c0c40140c08050051050360103555400d4407e940c0c1c58100324041e641d02d0009010300c1c00c1405004140d8001481c00c200c202c8a0710030201e180000c40c0009002d280d00c0700544070000b4840c0d81060b00c00d581d10380000031010b1200d0781082d503000743c0d9201c22005034000c2c04107411030403c0e0403a803000c40e10059001402088002c0c070802c0c00c101c041d80d0700d00c822011208a80a100143e030403281c0003007800c0c1854403900307075440380c0100142071a00e86007541c1140e00210b980310010600b02c0c3c000400561a1040b008030040c08404031007001450682d43c000c2c401500108018150355a03840840c0b040e032001c1041031540781d840411a2915610b0302800d4088501c21141d150000b82021072007a4810000f0030460100d4402400443c109401d41e400c0150020111081d1900714142120904d101d8644540000480e409644001000c0c2071908001502c060b008000c14000e50070302d818051a02a030850500807600315150000f00c07580b428004940710b202c0c0040040c42c80d0308044825060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 769613066 1250 769611816 769611827
    0x6240c140a05030a1d0a0509100803040905092b03050c0412050f010501050a060c0b090f1c1805010806040908040513060905010e102304180201030f0b0630010303 71
    0x14501941700c1078901542d640a0148540d16a80e44503000300945008002c1e508041a203160010701940359040541d442d42182c51a581190340190780c081e4540e401e112510006008611000400810503207141c00c05056080000307440e030941c041003559900c0060b40d4003c1c07000a80b0060002d4458003400250350b81451035980d04050218411540303008000100ca182c40031280c1c044500325210315030810500c2c0c83d030b0b125810005026004a018942034091019014001d006880f90b14a11103e0a0800480010028824031520110400503003030709006980e009800554070101c11180841c00310b04e0b900e010200c0c2d0140d075100d1500305070310703039641e9121008940254058524071981000260703602c600c00410f02c0c00c10b481d2003c5003500700034244000e201c10014010904e964201e8415a10020b2001c1021140c0790316141100e403008540c0a4110369042c01451211071101c84140300081c0d14200003440391241010241800c00c06800d4002c1d0013646081003942402031002c0c42c006580d607814007810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 769614316 1250 769613066 769613077
    0xf04060201023a090c030203302a0a06020f09030c031527030304080304151b03020904140108060108060c1c1a120f0106240c140a0503 59
    0xa100034180300501001c42200000c1042c401201d9160901d004000d079083c02807110030415140b1a00f03800c070100158404003c10341078514080d4105060f064082810400d06500102a042d100f00420544008025403641280c107504c007800c501445000c031800c00340c41e20890282c000c003080d001040465144200700040c107020b06c025020760381c0c480100350415490b240060030306480d11180c4d0303011404100d0000100141c0409042c4c04421040756013500c1031940c0c004940c11a01c800c400001c102c00c20000006054000c0c1c10844244907205c00002516080c6c3c1104412004041d408281d96203180d030385400140e000384140c400c1155558503030845c183c82c2c82d070034003801005104880114040800032000c44a4186414440b560402c1c402c4040b100a050401d00e120002c40600b02c00c5203055880a034061112880440108007410001e4040c47c2918025408070241000c80d40c0c1c0c0302e01032402c0181d01078000d40c4a01e003901a500e22843c0001403114580403000082c81011031401c200a130000043c40e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 769615566 1250 769614316 769614337
    0x80d260924040203030a05031b04030609030f080f0408030a060e0103060e19031b0204060302040f0c1d061803120a08040302060c070213110c03181503100e0403050f0406020102 77
    0x54548515460707150381801d58000b034250340208202c1c00350b184103901954000c200641d01a142e0204140300b0115608260070544225035600031500426412409080000c4180c0c1008880303880c210304d44402003c0010400b405d00c040001c001111340403a03500c040d01805984000c80c00c1c03943c507420b00310300500300a0004c40d5144581182000d500c901100c6004034280d1542d1941e907a00c40700f091400041c0a4940b04907000b64071b903040400166100c1c060303618040c124000c0080d20b540e2085004014800c200e80309449503080c01c2c40c1c490144c407404100c0c6c1880044c820402c10340d035500c030301203850032101074900762541c00085001c54600c0d900040d541d00a900917401c45220b40c0b03c100c0a48001c0c0b2078080c0c020761202c40c4040c60361800030070385c00a640343c4c0c2141c0512810480070303080b03840c00c0d80d1004150465003101035403003034401d2030052100110449115449410b40c40c000c518290a040107000c5c69001c00300b0303100080d08152043c0d044070a00e103010010b6685656403000064080e402149224 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 769616816 1250 769615566 769615603
    0x5030d05040b160203010b060706020904060608090312041115030106030c021b090a140c0706060902030f13170f0d1a0f04180b010602030703020f07080d2609 69
    0x4012803081050764250703400200b0031443d008855060845030250303154220f030555200c00380305902c0e5803104c1c0504038003800380f41e0150345c03200308000300000c85000340c1200007808150f03000d001c1210800400c0d500702808240c0035100680326070401c100c900058489080e1301640108201e58881021800b6604072403941c0ca0038001e80c0c01d588030036030311545220290607064072010620301076482c2c0703d10740030b030040000d0400180d200080da611446110086840e801c01c44000600081045490312541d030007030089001c11400d504080c041e50440d140064503615252440c46500740c03c4c042101642c506c01d101803a80d4542c1e602c02e50001c10741036007040058100f854504100c5500141c04c80c100c990303000b00c000701351817820342c6403100b00001001302c582c070442250031180030507001420800d82c09000c1c00054008503141d81c600d2800901d05260305100c020700c1d0300041c170200900034001500e44000ba0450074500310b034100e95031590100e81c0d43c40806a00030038145003400007001000c500c0c1049001d114005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 769618066 1250 769616816 769616833
    0xb070215070f1a041a0421031508011107060c1b03031d0307020307030b0a020405040f0608240f1819020f01030903090515070c180506090705090d080c01060b040503 72
    0x183e440c82803048601900380901512011a004103101d206a07000b403054405240a8071201148404808a072401d140800ea8170203400c0009501000d07072200800203a0003d00c500b00080003410030318018042c0080c40107880b0702002400c035000d1600c120305000c0d00e03003d402444000f401c00901818550099030500d04544240c1c00f580d1001004440000d078001e4003c015151941d5500d0655120045c91040000d509200200c1c3ca40d9460142081c0b00c80301180c007060040c14469500e0802050800d110700b501a040c2000d5800814a06180e920200d009080d5615581d01200f100c1000a0720444180034010b800c14598000090f9016003905402a12000c0444603004010b40032100e94110140115900f480100140d01c0c0c80070060424948110002d801c00c002d9a46029034110b280d00300602d03444641d240c2640e031400500ca0243e01a104544180c294244944041c0807403050340c04040c024010303900d00e0300600080c0812110580003800080082d5690b804031010960410f00410744a409030340c08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 769619316 1250 769618066 769618103
    0x9020a021c03200a0c0b06030c0d200619050715060320030105060d060b031e100f090b04030e0d080a0e0312030106091205120a080627010b070215070f 66
    0xd807034060004ea1100c581e00210b681b0b81c030828250041c8030903071500c1040e001d00c3c003544500f4880c001d510711441104441001914603207030b02d4159003a100c2e00800c42800b4030244110a2031489c1d8044a141c02d100ea44e52221341800101404800e4081d0102810440c0003c10070103040c152008012110b01d01c2c24080d01c03803804150907240300303541c3d00d54001010b84042c80440c0c40c1d030b803050f045540e008085070054100d004c101100140c000c4140205500141a00741404205004010032000101020020041076548035070741d10380e028002070f0402c2417510b03034007400b07850b1241c0034801241c014800a481d12001000200503003060340c200d500901070500603c1c0725031034403400c0c0d174180c2d0b07080d490b03520001c2d08101d443c0c4914024034030103640510801c0c06c1e4400c2003041b48000d14000d803c0f9503d2100030304d4285c06021040f107000303c01181558100c1140101d40c41494001070548001c4d0818039507c028500008001c031036090580440300d0800946001040b054242e070b03c840c02d108032040d219074405c040303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 769620566 1250 769619316 769619381
    0xb18130902090a0c17041110021203040b220605060f043c0203100311030a031e03150b0301051207210309090509060a050a020a020709020a021c03 64
    0x200070740002e00a00880d0114205800c0082d01140ca807812008110b07120700040e45080741964156a201007002140c0ca45042c030302e0290a41c03100c94001823440f500c1d80440130b240742c0b0005101501d014520f001040f1007410800c1e60304440a41c049648103109101d0600344020705042c0ca20a1142c1c5510703000c10403906160048000e022501c0142440b41c0300403804441010b000c011503003043c0b2040341c00005505615201450091070400503140000d821450a00382c0714500c01035040c441da000040b02d01c0040d80c003003030750f43c0014403e06000d01404101b400c150003601404007505903d4040a03408100d002c039072005103040794411610400b00781e24101c0940d4841c00b141c0101405d44880716406504210001440540c16200c0e103406010295070703180400c00c0b504191900c0129802020600c12a08603c1c010700d0303049221503500718641a89154080d540d01840d1141131151034001c02c070042c5d11402885526100c02c0c2c1440120401100703004d00400034102c10384414001844484c158203501c1c2ca04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 769621816 1250 769620566 769620581
    0x150807021903120b0609091501120524130204031401051003120833030c030d17090307060c0503070306060f0801050405090f0f03071406040c1a040b1813 67
    0x151210f103c1d401c101020703c000762419480344c0c0d8110340300300000842c6448040c645403180c84100e412040080f23004000500e6050b812110740440c60620050292421180c0c1012100280b988085241c4403810004030365401c55450b0003080e40d0340f0214001083c040c400016400c6502030f54007c0209a0f01c1c0b4884a00740c002a001c003a1400f03118840340000039000f00c101e07a4001034104410340400e83c410704100c0312a20700d100150b01915640740d590302e080c1802c100f900d180f4032080300a0007110000000007000310b4000510071118000e0302c408140343e040300340100d660f80c9420607028440d022011401822030303070007a501c4500080c80c2080c0005c07000d01c41c083d803a5900595a4070180d140e46400c04200107400c0241440c0101d0040103c02543c190080001ca840c001c0d141000c0c644419039410311000050030ba40441c9040e030003001c01c100001e003070f0074500700c15501c250018003004081340e00e101c0c502d0b010310340081c10300020003d0300203120a4003080c1c1c840d2180d0f0858090484e07804486840d400e039940c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 769623066 1250 769621816 769621823
    0x6030106050a1d040f02071109060f040b041e0c02060709030c05090a02280e150f07050f0d0917010b1003020f090306040f0606081c0f091508070219 65
    0xb84604160395105400c1210301d01020b44031502007002090000b01196110406410300c140d00003440e404003d1044900a4500002c94000701c0925003000071420713a101000005204542e074141c101015511548500a150051a081d03070840f580140104006c0c9000700051015200301c5000030000c9100c1c600c0f440c256a880b83c1e5618410746004240150034101820043d1801e40a1002148401100322024518018040a40707510500321101800e940c0403000c1443c001c1c00c016100500b0181100110f5002c0c42d0b00d0f10300180e4941c1241072403070030148514254136040c080c1c48a62000140c0c81032205003030f1003000d1081c01259500781d2006007201e01d070400d05034001e04501d4900c060980030f58050400c4003a6001d566292460500000341000c004071001c50701c1e400303a215a1001d00c000c501c030704409450080028018000528a602e8072030002c8850401001006c0c24030a0001c1c0c13080304907100078100c2c1908d50f42000c0b82c004008d00901c1c403c4540308018420030b03018100d01c041307240b9101540c580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 769624316 1250 769623066 769623077
    0x30b0609070c170702090702010b150c0303270f06010e070c03020a0f03090b0c030304110307030b0114130207061a03010615110304050a03031d06040b1204051e01060e0606030106 78
    0x51543c514003442080000c01980540a10030703100540c031210100c80c800c101c2d5500000711982c0380310410041c08600c40c0340c6002d452007401004840c20002040340d0f00240c0340d12058041e17000d60950b65901ca08661f40e1801e49e8000c014151074683e80015041d4183d8035040c110b0000e45d6500f210888407000310803070280059001d032201a0104101e50b44100000c4c2c000d00e4101209a180da500000075030211506491a0780004200014030046078000c00b02c0f0300007140603105051454881c1345c00d44030103000720700c902e000e2a40382e1035869460507400d4403140750400040d511001d0a0403d04020004124240034281d40040705a0a6150612421054420b20110349c5c8014540078801c40381e8010b2494082a40d100400c8049501d41d20680c44800179071103540c0b980b008803200401c012a030490345580310b000b10070901040c04003003030080035925014410380e80c0354000d5486080592604007801c0400c82c80d248100076400c905441034000a090b101d495015010a441d1541409141d200902c14880007d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 769625566 1250 769624316 769624337
    0x5010302090f060a12020a090e090708070509150301060f05011b0c1503062301110d050307030b010203070f0b01141e0105031b0307021006050303190f180e01030b060907 74
    0x40d214014100c80d813401e1401500b0702e0100e015120032640700b540810b000c41d40e014000c01c05250203140c0039a100511001a080851400180a940794194000e803032181e0100c0c4001120544c0b240a420303207000c0018003e011071980c600d60403200000f42d0040d00e000845010751480f44040d007401d0000020b5001e80b0744044546400084d0601c40000c101c8003007099100e11000030341b281002111100417480d60040300c1403061000c00500704a040c2082820781d0340242c626080204d401c0020380f0f61100e2a03040115a01d802840101c0c154415440014503c05011420302c5c107016040c3c1106040c0d603129414110802900800c0020404410342d8400000142289108665106101454010f1040c001004804401c0315074a0174980044606100503800000080c40f080e00754003c10f00180001da01561074420050011259000c4601e19075091114200d800900703a880b400c004405c00e11100b224003d00b03510341ca0a604120b8003884155044500a0040744a615207181c2e901d0007407541ea15480e1244 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 769626816 1250 769625566 769625569
    0x10b18031f0507030905011e18030f05072102160501030e1b030a0222050f01051c1110031d0d09030f0309150e120f10020d11040f06030605010302090f 66
    0x1084010003081c20135481e46405000035400f4016000c4000c802064803903021030340400b02081f44c1c0008001c0d009651111024000700c0d40042d556080e811240ca000d41d91b134019400d01014407480caa0340ca40c4000025801580e00380d40c0403034105100402c0e43d0141201c0c80d80e5000440076102d00031883d02213a0842c40d01440c54840200001001440280548828607515000540301107840303880076440600c84d040301c82c01c3c0b00241c81041d034800700a0410071003e5040c400031544411001c4074030700e40c00f140a107594003030000e800f502c1c2d6017451000302034072070225081c1d500402500580e03240800e0444107586120541c0e801080003c424102d66a40302e00c0289107803111100c40703a42000642c1404482c41011030a814600c0d0001c0e400021130b10b0f0062031050b01e50611a00000301410500c20341c000d0380c88001001c070046044c0144d0f00340500050384983c1e8065104005261044660440d08000100060001d1440d041c080c102c1e041a00c0800c440c56480d030041d403d83c414540e810354000030a000300c4005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 769628066 1250 769626816 769626821
    0x20c03090f030f120a0801050405040b04060905100e0f0601090c1b0f0602031e09060705190e060301060807020d090315110d06230609100c08070605010b18031f 70
    0x120000500302e5034440d42a0003120304011030011544c201090010700b0019454000501c0703401440103807400c110a18080d290034110000141000b03002c56140c413002c1c020300030b04101484454105560030040d00002e105155596449801c45010500800c4000940c9a03000d00c221940c44441d41c4420a08510340d1041d0079204012050440c1d10720a6484020041401032020318880c80c1410b010104040c2c4a206180048400030300050107a0702640410540fa54400c066a41c0c0a00b08410f1950140c0c407105d056075580358900055800840100000800b07951100001e03000d12180d400b42e40501d041d04000316035909590001074030700c4110f0b044a0007004060361241012580710380f41d0505100c001c007141026a04140d00c04940c41103214030050070802008650311402408584081c6841e140d10040392940c02c0c2d0700440b40500100e505890144070070001110002170b40310070300b0066581c4038284102c1c40e412a40300c0307000c003503c1c5440349607040c1000100c0c842982c4480500300036440d00c21704910003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 769629316 1250 769628066 769628089
    0x1505090a140303070c1206110901091703390d1704060f091113061d0a0b0619080c03040f240614100903021008150d050a05060a020c0309 60
    0xc00d84000c01c813001c04111007100340006045039004a00c001801814200c09641d10301c0780c01d8010301c500704403401203a03810401200450328121080110300003002002c0c1e0450181c15202010301c50a0a0380800300d00c0302c80703004601d1403009810385404143c01000b065071a0707038442c1400c02240781e00791800c40703903102e180c100c0340c1c024494540030070030060301c0c140001520340c11001105c20381c901001d600650700d0a5084165400520f140c104182c42c41c0203464000c4c03e03040520411802030b16804140644001e8120100581002d003469580701e690b003a07114102c0324041d5030600042e01880124408001450890340207907008090100070006a40f00c101000360203541d08114000c40e01c1184800745542c1c081c20008210030345040300c14452150510000c0da48070a205000c2010f071010600042ea20103001c20242006031030940b44580e102e44050094880c00400e5590102c0d412452804000b0b00040c004030740c40c807440036103015849460011059003e00500c0c0346a980040c4201107850400b03014004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 769630566 1250 769629316 769629319
    0x110a050c0328110607020c1203071b090507030b0f0103020a0309120f02071a1222320c0f030c0d03020c03060705250326011505090a14 59
    0x80c0380c601984004110215102000c01d00e400408082d806416003000c1c02c01d216980110180203149881c140085d00d6540044100b44203899030b6802407034000082040d541244c0c1d2104054500d050700c5101c109241c07006105500c0e101e810103000418851090103001c800c170b41c0250018140701a2100198007940040303040c0303010140d94a0500020032901c0800300003042c45134498003800151464020f040ca004d9802c90610a03005c0012070303c0d50100c19084600000542829803229121410580052003041e00c56001113491a05078a082c080740d441409081780101880035006c8520141e9404848904224031030207805c5070711841110b080400141c408079100909545079414003100280d00307807203030303040c1500141e11007050a82c00c0c2c202001082c0c0c00c112107040c01d6003081e0380c2d04082801043c1c141c5019546500800d140d008140c000c0d0400b90f40d9130508c840251b407504405001c48030481d024070a84500d501112044410319005030102c54440001030320503004113050800e2200482a00074185 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 769631816 1250 769630566 769630573
    0xb04020301021201091a0102011b140d05090c100813081308011d120408030414040e0f101a030a110102120309010e070b0a0e0907111504060f110a050c 66
    0x11440183e10511050203082040310001d8440d10305c60416402001c03d10109040d0384c50265800082440b50071541700782c822526240c2c030400000c000341001c030302402e40ca03448618140400c0c4000000c000c03888000c07005055808032980c01001e201119a00c42c19a260446894400d0300f420108603a4402440b003c2121300108210179540c0242c3e50031034680d4500070144901e42031042d81103200c248124241d03203814190003402c1c41c0c100070216451b8803842c8204005080000982880764803a80c01003004005e00034140c4014a460240464461008076503c0660500d4851700b1420000c1651860302c09a00140081c40e43e59800e030f07203640c0c40d85074403080c190552040da41421480640440114494288500041507134654442850702d420401d80004083c80c0c0300b0f00c181600140d10901c0d8644c1040d048416000c5030b103940340242e42e0481110005482401010421b0062002c40f010840c0114802d540130081c00c1c02101a540c02c46140c034441000c00b200400050071124495000b1f40b50442e600d5098 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 769633066 1250 769631816 769631827
    0x1d130905191407052205060a05090408030403021c12020c030d02030412030605030c010806010815060406091403031905030a0e07030c1401081012051f060321020a0b0402030102 77
    0x48550504582022141c04603440d49581d002c680900005005080a8400a40b505412000280e5400c210381c5560000760340d40000030201d9031850242001050086c200e040c0d5800c080c1400c0b03842b030340101c9056004d40304d2164840d000407030f801c800d4040c50f00c9641e906400c2c40020342000b4043e602c0080c02e40124803041c040030544100c1803000f035000340c1c8624843d088001c0c41c040c2c0034094038034542c0024440e4001c2030140009903081007065a00913001d20706443c81c1e6640d1048032034451451110141c10000210b40440c503d504655250191040480c1102812404104042e84d0384a02702841d104907a181c58800e803100c0c003c5002c0e41d044401c030303030740459000075164220b40b5004480c2d000352803401e0b014070f08101c080c0f0034081d010034148081c030b03041ca0149000c440c6910b00340321520404c1c1c4030029403a00c0c6000d2210130311120500f00b9a00c144a09440812039070100940001d000c181d90a00903042054100350900c0c143e601c01c0345154000d818150003589030384c2d084410042003660155001c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 769634316 1250 769633066 769633093
    0x201050d110f2802060f01090e0109050105040c05011107050d030305091e150a0e060408180301060909110303390d020601090f020903030906090409170702011d130905 73
    0x90035502010b02e820b02c0c941d55114051050043c600c0c102c0c0c000355001142881005014426410b0560f912007802117a07d07050400640e00600e000080500749520340790034001000f4a281c0b802c0125202607a03002d0029800f50030b0340303454a00c1c80c800c095000c95543c458200003801380d045540e10240d02c0043c1c034001d80e06001c100c070143c00f02c1c2c8442c101c1600594010140000a90101500011099801c2000498a03603c155440300c000c2d001800203140401d81580810b000500b801d01c0c00790280080c0596551072007504007a1030001c80c01c941324040c0c2c0860748000e081c0041a982c1e62650458080001c1c104010410355040e58007011155805000da03131074407075140c00c1200440e8400c40754010600c947c5042c141d03008550b4025011040b01c1e004000c030000725500041955490b800071280a40e8a44c081000903000b0594000300801104500c28040c480aa03064054034095000b03032101581813042143c0701c00141950241103900c104074100c48187c11000d9484000520710400440e50510000c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 769635566 1250 769634316 769634347
    0x1201090b1e120f1009050d030902282111030c010807030e0a140f0610080309060306120a0c080d1b080a090315020426070e040f0c06050703080609040201050d11 70
    0x1407408655190740c41e080c00c201040101800e10115440e081010000315070000c2c55280d002c00c0740340c1d8601cbc0300081d0248040c3e031780168030004003a4001c031004810f03212900403140c500e062800b07464500340c250185940d818007158244010700140d480e041c003591106d00c181c004010041d0340d07001d80e120b980401800209003040700086400814010000d034181e00458501c1c06c04000d2a0000180385a501002070807030010039222401d6088a515890341d5500c4003081072560189803046191180040900503c94042c080001b504e1413801602c152020108040e10109403038620740c00c0981804610b4408104440302918004c9540c0c6089031000b5a291500d003020981d070030007846030647c001000c00080080080c038021400018403025504070603441c03a83c0c0c688070303d44039140292280f0303400030b0304200e134841c1c84018140c4d02c286541ca2560721018010708c150008041100032803190000300c0c019142c144801e034402e56050b07482516011140004e1400380c8217084040030030706010b10a4010000556 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 769636816 1250 769635566 769635583
    0x120903020402030a0207120f050406050f0f070f03081f0e06030a0c091a0901030c17071205010c08090f071802130b03072c06070201141201090b1e120f 66
    0x42130250321200b580c1021a4400e0b07104e500340b0144400b014502030591b410805a03411070703010f81000307600c4480309110068a0320550081c03040d075060025468041000018090141d140640d40380d00403552540c5076001c2d0504003400d90140d110140d0300420184600c1000c15900640250030350b040c09850340d80d84458000326402002d0ba0540761a116610b070340024040341c1600f40c040728414080c1d491900c3e100c481e51014002d40c00f6480906541c41010441082410b004002074460071001e46c5031810003500814402d0541c0001a600d00702140100c1d600207065000c44070130f10043c02500d480c11400c000e020581040b04161140c09205500e41c20001015200081882000707803543d0f4a0064001800c0c5c10004030303000d030703400c00c4000446004c490800b04031004d144290381560340c5444a00050f0f9071001325842c2c05090103000254406d406101c103100301e04a903004102030043c0b80a4108010360315800c803854a00070103c40010745903a00d81404058074010000050740e1150301106c0e00e850600314803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 769638066 1250 769636816 769636831
    0x210207060516021306051e1201021213031809062c0a1e150e0a02030f072106080a030f0302180d0807060e0307030801050d03051902010e011b02060a110712090302040203 74
    0x1f00740c2e40c200303052012003041e50380030003402140b8011500c2c442c809404400b62280070014042c020020800d8060b4100600b088012400ca070900e554411515020700494060b03a0702c0d009460340d50181480380d04068200d0030700302c0348841c081c90340c1c0c41c01a20014482482019040d03110304e200003001440c203110b0030b01036407420303143c805005052220801c01510050b101f8035501e403040040203605228842410341003449442d0001d140010f0f000b01c683e01807606066034141e0703440e100001940b10400185102c150b84281c07a440c40c10000d11405908900402c5070302082200103a8040c07025203009501030b441e151242e0801c078280355894495104551109803499901c0d4070001d400c0080c15000310265004190072100c0c40c0b101c038034694000304240201c48000c0e1801114032000302c9158001e402080c0c100050074000c00c101d44040b84881300c20481d0044060240c003504005c20180300e064001d6207510b141d1903108621384240303503540c0c1544001901000003001009640800180d60b140001c50103807a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 769639316 1250 769638066 769638109
    0x6050a11041206110403052d01050f07170f070e060f030108031e0c0304052707020c1305160507020622030210030b090402090604060321020706051602130605 69
    0x7501e8100308440c2488100001d130b24081c0010030000f08002460424072018040c089452203007100c8611544070040c0c105070146d420101001004018031603084c0c8980309079510314800d100c0301d01074800d0201054980f0701c0500f29260001707401500901c1491000640545854500b4031021181c7c121030700280c0180b400d682000903518035440300195240040a10321248038070b008031807848113590740b080740f04541c0100300200800744014a42d40126010f514510341c5a001d51501581c000c0d16085040080d601c980308501004542c02e00500c02c0a10800c1c102c640f0324034043c4524400c1d101031f0004001203034001d0382003104210180c0d50060b41d112042c004011640c2480c01c520401c0700701c1c40c03030912543c1094030b440e0010100f03546041c0c6e101d0b0841c5d01590748880b203440700800714020340085d4001400780c1c2d421f42401802c0081c001c00c1600a010540d007034a010903220a0112010b11566200d00c020b00f0801c0c0d8980701502d03001ca080742c0c0001b1003200002d883c40d41c5c0c0001c036404d40303071004c601d41300804c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 769640566 1250 769639316 769639349
    0x3061107020909031e270f120a06051608190e19020406050f0d02010c260c010b01030b030a061505090901090303110a0c1403070614150904030c06050a1104 68
    0x10b201c802c0c0016806542500f460800700d5a41c00c03100540d0144111052860206e0804105610707030112044281c0c001034101d008055010481ea59100e01d0b61608440c110300d4040040d6500140c004041c00046d03071076a500d01e99450b10a141c0d20500080964002c0351550391041402a00080051b184000d60040e803070f0442505600400c801c691081d071089001e41c550310310a10003940d521140076021a824204687d1624050414014081c000c0d0540c0400781d001b0b8181c1072480c1940c102900c641805a00207001171904003004506a411803458190964840c6200800280301754000b181004844031441610640d40d9000039607030142a83e0311502a5529450b841c1450b6048c018040c20481280f4035901d4090310000040020000030030250a03040f0000800f50954400e00c03c840c44a6003040b024041d000c2840c11822206c4415140c0c3e00981d1541c00d03403801241001c480d5540b18070f426490b881d0103110142c072542c003d0403004105410403036076901030006900c003280c0600083c001c84814a402c88 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 769641816 1250 769640566 769640587
    0x10303080f090303160c0c05040f090c05060f0301030b22033b010f05130e16020718092303030a0608011e020a0212030a02070c0501030c02070306110702090903 70
    0x200005003a050080e0800c00411060b00404c0c0b9841d00c0201003494640350113a0300c0d040c800c07c040c6454100540c8203082c1810310024001f0341c0c00900805001d038480c0e0003103035658000c02049105804504510b007100740010804200a41c500303582c0716500000003d032000c1d90f01500c0c444071b00c180301c1c00c6001c030b818a401d107490703658078030400c09003000b034640c8980c42c158021100e074000a0f183e4100904201d804840011441e00c16815640c103401003403000750b0616114208468030803422a480b030034000401da4040c1c00c86100154840854506a40c0080e07100884001200504404130040d107200c5000390700d200d1902d40c41030f902c041e42c2e0410b8020710307101d080039075850040d41d10641c41103030b6036810080e86000251201e01d4207018100d421500582c0d41136100b1090381090b103144288082500c020003004103e0010350001c240042c8609a9071040b640c4520054003224034814400c001a070001e0820300000c0c0080d801040b081201c5d01c40719061800590014074080e5084810381d529400c041a00d1000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 769643066 1250 769641816 769641841
    0xc051501090b0904030914120f010e010b030d08040602070c05130c0806040b0906370510090e0402151c06080714010804030513091103060306150d11030c060301030308 73
    0x21001200c040f422410103450081111285002d4410060a04071400f0110758903000e040501950704000d440d0785008000341c1a0003001081090a081e500388161f040c0c1503e400f14014501c02c18940303c0d0b1010341c5880c2c403200d000790017000b412114815506001f1805a88030350800d595507034541c40118010001040c01050b0b9040509024081c0c0d00b00001202965140c50b1010751101e819038810758172100e8141042c181581c00a0a0f00103150150300e001405001c3c103010405480c07013524800b500441c5840101c0700d1001c1c0340316003c0d0303078089440414010301c1e00c80c40005041161600076418030803a10540000c160002182c0c0a1807640c518041007001da0070b0103048000d0855444110151583c10006008000010030013420003000041c1c0303003031800c00c5200c2c0f01c000e41601c5d01c0401070040b000f200907a043d881a21142e2280c0303e80f01c0010004840200014954800034280010399100b560303401e139041c09510708080e03040c0140510b1480c070340c5504c000b66000318001e5641484606050600805 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 769644316 1250 769643066 769643081
    0x4080601060c0f0803012310020307151b170906010f090e071a04030b15060f0c1513030e032b020102070b041a010e07020a12170901050a0b0d0b01030b04030c05150109 73
    0x88e802c440c0c2c0700a8964001c425204041e1b0070030a1000320100c501c0a040041c424101c081100b80c101086045550340c2c001f800c00010309001e40d540c1455241c520348a6a10502403259502281000500384100f21880d001000740384914030489031065115591744006d0240c0207000c41202c1804201001841303031344400960042c2c41042c2403030004808002003089403040c00241c94814400140a501c4400c0402200f00e0b401c02903020024a4140214031038140d0a487d01c054001800144441c00030b440c01040c0456182c0008850301c0007800320001d5504c0c00b840c4501082c003555030038804003000c80c11001140d4803a9114215102102d40e40390f10a0b801d00c0d00681011121000190030407400caa00040c090041c0391700402548003410044a08699040c640003410300c00b20720410a10013076003015000f003801000100802c0c014000741d48184005d00e4070700640600180703210401000401e0190a400c0d8100d8047e2030002503500c0d841d1a014544400030000c103055001c01c00c01002030714a944150123 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 769645566 1250 769644316 769644319
    0x11101a01141e0408010e030d06090c0f080a06051c020109150806090c0d0f0c031817030c09030a0309030b0c070f061d100b10030204080601060c0f08030123 68
    0x68104001c00608050103081c1c2d249a00c1c410348149000d0300410306003500e00504c1e401000340004e6240201440d1650800d88614045605040010032806140e000b021207c40c03865441400c0f540714a0002c807102c000103032030045059580c000114040d1114028070036000c40c840b159580c8207400d0301c001010b6500a40c0079803240300056140303e07000c3e80d000c0b290f00e130089812102d5500356200d0102c440b03818400c41030024415890b2021200c0008900d4010590107140c40c1c50801104030550000580c5a6012000501d02600c01a02c060400c103000080d41d0004000c01000d41002c0b02c03100403e107070000c043c0c010b41c04070b010090200104408004c105600280481407a0304005056513580d424881c8010024625603c48180d8207102443c00300303064407842c1440881d12480d180d4001d00700288210441d40d070284500640c280e041038080d0089800300c45104000308030580c648a82100c11001000041742e42d40c41c6401e09101065034600558081e01c4111181000003030b04100d04030300c8840c02c0013a035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 769646816 1250 769645566 769645577
    0x10804080c0d27060903060209030c061204022d0616080406021608011503021c15140f15011103120c0327100209010903050709020309060906060306150111101a01 71
    0x44c0301481e8414074180c122640030001503200d90010340007900f08007000340c0c1141c04c0751001c20130049214248100c10b00807402a0354180c0440300300c0c0d50345d400e1201001210382c00b0003540800b0044a062150040c003103002c81074100381c3c92503402d50303503030300c05500a50080005900010200080805812400c002000e1410003080410071280d460620041203101c080e11070740700341d42403000803a490051030841e03c3d4800d400b158000d050143c148024008004101c00c840081400a68900702c1f105c011400341e00200083d18229500c0340046500740d816018601c440e0009000050303c0200301501203001c0c1211441180d03c2e842e2006a0b01200d201240c015254040ca8400d08200c0c00d82c003050a4035008148500965103440d8200141c9a0240c154030003407180c03042c0c10002540710015400385002c0d11812043d58144e880e44068181c4d10001a01c10341e505402040110f4095411640113500d6140107040004915103601c00e014108020312103188070082d02c0c3d440340b04020142c510000d404070303003d003807a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 769648066 1250 769646816 769646819
    0x4031707141504120210060b040807080703084608130b0f0a200d110c03120711060f0103140f030d0f06031205120114010509010804080c0d27 62
    0x400728100000c1c10280c400b495410104c1c883c50310070300081d42c222403146410701c0700580d9600485843d500c24400d40050340514800132a00301d001050301d1341100d81103010a0305000080c1d01d0709070303c001c0d04a00d0540c1050144400003802000c041c0000309410b41c0544140c18140a10b005041c80c48002d002c403002c4924090400c00103080204103c0c1c2241d03404441440300e03550807041000401840c9104410258000080128011407000500d442155600280081c035030031805002d55005103035140c14035400912191080c1940400701c290700030440c0c60445101070009010701c0c1001c4081e140180c82e8460403006105003c0d0500d01c4001d520919002081c0c5080e6500809440e40035550b020950f0f1512000110400c070b10940040020307542002800300100482d00015146900580900c90024000f0000180085c07054561100c1d681040e16041c2c07400c001c00c00116150580184102c400d020305100160030070310f0800003000420410f840d1104e004040342e40003070010031800300030384d29448082d40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 769649316 1250 769648066 769648093
    0x4090c180e010e10030b0a05180307050102031f081e0705040e0606040e0d0516110604080d08072c0d0c0603020702040b030705033a0917010501030203060612030403170714 75
    0x2c040d1300400b0100000b4231a180c0d403502c0500f2290500c0c104d900384c4804105241400010f40c0154041e5100c1d0800b600e02c00b04800c1c2810407260a407050304142c0d001030085907000000e40300798210341590030096541c025210000036045554481c0101115441241041018180751184079080c00c06000102580c01c01032100921511802484800c1035901c06245020003070800d142c5120399034001c20450b01d40d602d036181c140c1c1d1240649640000144401c0200c0c800502811200142d02c50008030f0481c22080c40900c03e0400b00b001c0a03043d0014040c8100001040c20010a2009440d0a580159036005140104005d03615910a40c40c0b00347c100c000d00304015900003400101000c90401040e06c00107081410078011000d148071407610080000340c0381c072176650050f64402514040d41c0103803026008904450300721002408002d4040c0d01c04004144a407030700d0341d5210221040942104e10702070b125580c0364000c80164619580c0c1250100f506010440c810720102c00700e0611800400b8100b50026 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 769650566 1250 769649316 769649333
    0x13050306060901140f0a170a0203070b092416030e0312040f031101050d02180909160b0327010c030b03030a02030d090804050d0b0414030a0504090c180e010e1003 71
    0xd84c0c2d8821001401d40340016100c0c9807002005058004441c60441c05c440c0c0d845840f10617441040717200b8064940d01094924000c01995495000039091290005d260440e04040080c2c3c520300d0003200d4800d004610b4821001c0b10000852803007030b41ca16001500000c10301d0304c0c0407069062a010400d00341f1007404100080c0031824222500505032580f8450030100503203403886000603608440d030001511031042d005040341030481d1a030640350b041103640c41443c55903e4246400c04000d9094659100f04554003241c2c000d190010120440d0204034203940c642c0c1c3c0b000400c24211650f859456140950b0050740500ca95000c2c3c05081d00554948640080001d4982c4145c298078a00742c1e55441100c020700100500341c4002e0704010781250401d00303003070400f00100d000c111011504014001c580c4040b501010013515241e20442d00c3d9123007000d0030528014060110308012000700403922020107402d41c00041c404008002c3c1110802c040e5041130080d050403040105519012071a003201000081d2000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 769651816 1250 769650566 769650599
    0x1803110402030a020f0f04030201090504020c03090d0309080706031e090203150a020405060703030b090705090a03030c0203010f11040317040f0605030a1b0e120114041203060b13050306060901 84
    0x300d038016038039524888400024010039060300b5420030045540070540030b01200800c20389000340c0f03a030360742141e5407010001a4481d100c8030b6950b50b0000d06c900c0030a4184660703c64201e0f842814805031032030f100c0c000d003880c0c0045c035400340c5c00080c3c8550360803440903a0004c2c40c0046050f0343c0c00502040c111500031959541050221081ca4408500014080d503541d034103036409818014001d0b503a424040c140107020b400003401c4244250386844c0442c1a0301e000e00d04607800c00101618071000f072032441c1c50503120480d0f0480280e0300f40d500d40c9540d0b90b80c80c5107407142e281d22154030b510b0282c41c0c0d411800e00050303082d0181c400c0b0100b188100418071101281001030000c0740e100345401c1d40d5079030703d048043d00500840c0050725075807148802040c80b12900441ba44040e10f2081d01d1074000305000b140140d080e6182030480040021166001c9800710f07001040d1042143c4481c1008039025a841c28140740da5481074440c40d800300401c1d9000e10007840c0500500f500028112105903040d414001c04480b14642d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 769653066 1250 769651816 769651819
    0x316092408071e080402011d0a0b1804050405070e0f150d08070c08031c0908030103030e180f16030b0f1c020316080c0105030c370c03180311 62
    0xc000000c800521a07070b4880900f110340480d00c1850119981c0251048800f518200d01040c1990a028241c02e10350004544042d001410058541d02e00040c200e00c6070b002c1800c40e41d03261594154401a500c0e20300074107010742d1040d00207080e2603181c0302660800c04000351408044021803001d000340212104801081c0c0e4004403000c940c040c0c03031450134100f9889443d10040c031801e0b8000001401c401e0101c0584803500d014030100b200010050001401c66905d5240102880801e00052021138400d5102642061300a0300c1c2d80b41d480200030803805003840c2201c11480b910107020170000d800800b50040032030ba2003542001e10100e5070b0400000d00703000d07035503038854041c5015a4403900b194160709c044000864015081d02c0307602c5100100100300d480c0500a50007503109000d40d00c038941d403080046a1086014994082c20100c482099903c0154140d80c40c249601c0c46006c8040211400c281e0082e69072107039140c21403600c40524019100360313040c0c08404c09072481080108040f8141101e2421500700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 769654316 1250 769653066 769653077
    0x218190b06071217010506090a090b12060406050411060c060f040525030c050906130b04110f0304050606041a01030207140a0503070303051005060714070b03160924 72
    0x800d6008600c1c2401405070161541d0522400c525105812520b280d0540d04a41240c400b6a0b80f600140089403041054031500001e003180e003081000c84e030398003540c0746940c02004a002c2c1085103421514140003030310142c0340742c1e54440c28003042114064910040d04411398100d4108607010001603121480141a060800341000c000303410000309125400c02c24030502600200d40580d61520712084480d030100300c2d40540d8008000c90b0310700d0050041c502c40d001c020583c203405154101c4038005815500c0045030403a031180300c0c14903200400c6000e001d4130440703520100c1c1c4034501810300514008001e000c40b4000c9140000c6140308000440a481e40080d0a0070003680c0c4410074074210806038482d414007c1d1310301500305010304118001c002003c0450003540c05020300d8880314541e0124941505c9240e07030215040100c600058100c06070601850b8451080e2100e250ba0382e000c0403402e510494095098251b0804400046504216280d020701020088422020041401005c04201d003030801b88c240700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 769655566 1250 769654316 769654331
    0x31506090501351b03060109092406031a060112060602060a0e032802070b0406120f020702090f01180b0f010c0f24050c0313030f03111303021819 64
    0x1039400d01c1c4101c1d440300080303500b500d1204288030000d14007513640610a002d140c0c000591641c45000d030f02c00c041d410003100e81e040038041c5107018804881c4404410749507100d102c000003160040c4540e06441c50010004d13401898100c000500c01d90100c0490a0001c1c6084002d11141d43e00040c00c580c00f4206c19070001780203503038880292543c012a0201001c22000d9503c5015850300815040345d038503059001c80311843d0300e66640750942e0082e406980c00040000510301001d910b035401070f424031000300d14014908503440c1c0100d550b242c8112142407895120b10b0040211541604607150246481042044654440030001e942d181d0981c03020350400800c18900d500b0f0214600c0c1da8619254420203141c6881c070884000c0d50341c2030f1100140c0344680d140000080b000358a0b0301c12070340716000348000384120211690303060328000800c0300250308065480b042e0401c01140c0e13000400e0b40c14070004480c407425280d44104040e0300044002c50f42c1d414250340600c0302c004c000045901841c400380102040c80c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 769656816 1250 769655566 769655639
    0x1801080c0702041503050c0604030f1b1e030507150215060609030303070201090c06030504050c12010b03100f0f090f08071113140f07050f0919031506090501 69
    0x103005462020f0b5001e464a000180e0f11140902039a04aa200d1419038903e40c011104120f0a40500d02c8058001d600c0c800c850700c0000c01c002c9452924080710211070030002e4a400c1f01d006445500c000c0c01c011101c0d200002e0003030210070040c40005000001e03010803080ea644c1c100075180c2105890071803038144001c0c0400c0c03482e030741d900941c0e10b011000380407207440b890640d900a0103810140c4c020348688000340000b0400030b11a006491203160044000c03e44d6650b2001440240038006058524075540c502d00c44c01c1d00c2d501030000380d40d0811002c00200c0e0503545110b8200403208515030030403003240340000c540000303051412100392054004100645070308683c140b00b4078801d4140312055000401240c041c1085429038401e04903820480c201c11a159546158107000c203405031600000f0610a120303031045d04140c10010800c0200180075031512101e1600f00c2c820303515882d0001c6600e004000a19145000c00e0f20403800285040c8038144040d500d000803024040302c03c1041c0714042400c091414454 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 769658066 1250 769656816 769656841
    0xf0a0213030542060a051c150209010504031112121201080c030a03050c030d02030a090b07021f0b010c0b0403091701020406170a150e010513110415090801060305010b040c0302180108 80
    0x4001c003070000c1f404c51700100c03014604001003040c1100ca15141e0600807003081c00703d00c00d4510314101a182d842c90309013035446003043c840e140030450342d000d1002d43c28169110001d000304c1c030413005800202916020f4080f580c203800f040581190340154802c200d1a01c25540024549640300d415050603592004407902d064203510640c40c03501c414a0001080c0581e01000340d011180c0103000b2000c04c402504d8660049032220041c070f4010b00c08490f012144020b0004c1d0783e100c004e10000c1410a9600004240c0c0c914948240445e0141c010a0107101c040140b5101d141102c808205150b008500d0305007004c0d0050f00c0100806c1d91003501d4001d07040050380009841e48000c0c5170110251040152070307910b0004180350700090207098001c4180700804a407005450040c0300882c02d80f224610700301030070415005140c2051076203170403c1020394040064050020700c100c1c0040c5006500104c0d40d5002501800203543c8c40c1c6880314101481040348070070304099115076820226003460f00300e0841d01e4030000180b0303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 769659316 1250 769658066 769658069
    0xc071a04080f0c0f09190e03120925030302120d06090e0d030c17130f120809060c07050307030e03010e030a02160603020309060f0a0213030542060a 65
    0x2000c2c864503204141500e4000f4410b01d45010884013a505260001d061155042c025a41070013400400d5842030b6210303440e0f401c01c0c840d8000b04401c603030400c0b05281c0307a5451130f007059685112130b4010304240d03040581030b00303900e0300c0c08135446034180c2d0350300e1842da802599102503170582054401d021810b0300c4019216080b100091503100c809111540c2100c6505071900310101c1704c4000300e85012200d00726280601c910350f030100412413502e032003591021440d03c4800c140300c00c1184c1d1a484802040001359515810607580045c65841c0c1d14903190030414a03282c9200a004401940c4e0103201c4800041c500000300d812450703040c90012545000b02010901501d0f00f030b031078840b0500000c14038024050b800103c10208800350301a0080e020f035181401c2c0c08030300c03081d1150180c17a00140002103080070280407a40d0003d002100c0140740409115100c4e003614115002107445420103464840ca080c1201c0c1c000e2440c41c45041e501a519085540c0549400140141d030309048400000050552380d40225440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 769660566 1250 769659316 769659329
    0x48080c040e0c0d0f0e0c0f180717071e03020c1507031e060506042d0e0103020f01030e061303120501080606010f030e0a020d02120f030903010c050c071a04 68
    0x82407814207201d50401070708240e040c41e030a2890100096004c807418012580700e03020520140100032614000d000103d44c2460280e038025840030356014070070f040180a14407540e22650b4010f05604900050141004040c10b120304005c0104041e200034522a2244e44810401e800c006a035004246030f45410b041d000101c281d00024000104404035806810000d040310301e41c1101001200300012080031075901e4091b00c2d40040701840141714031074031708503000d0311a00c841c19504034400009008011218881d0854103121030600010411030900b91286050480c00342000d0041a02d418600781d9070340f00c0140599215030700b030542c0360280740c0501c039001c10b200c40240b0188410768540e088150341c2c10094454600081c241d2600031046442403107610742504841c0007170030301000c064080080c4d241203040280c5e03000b415034200b021600c41c02c004034000082e19001441d00c0d94134540815084461441e044002d0003001c2191799072000001c19600e0075070701c40052020300c2c107481c50414840c0e030080d60842e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 769661816 1250 769660566 769660589
    0x150a0b19080d09080619090c08030307030605090603031215010318080405030f06070210050615070c151d10050705060a0e070f031a07030b0448080c04 66
    0x401c40000108a225607036009440e85000700e951000e030300d9900c1208540074104400c91103010441500d45420010925004460107038102c0d480f139010904640c0309a0b03c220102c0d5554104000c00e04050800b141c0c070441c1100610704248120711007404281008000e88210006c078118842035030300950040b040c040781030140d10402e010910702080f0700e03800380c020203110340309075150300000680000d05c0c280729090780e5029080d501d00c0800b900001e450040e112540c0401d810028500801e45c00c030240160b01d000c1c1c01040f0889203400c078110204a0501c140f802000300300900c569140b02c509400b00c80c408d00649e9483c4c0001c90402044880d80111400280a0700a00d0240703c2003c6ca03a40141481803031484c10f0354595540d40b00079030680115480300030800214440c2d0031900d170707241100c52580510a418045819807240e40003034201c50718050f500486101c0c501c00e40e0310402ca981c0b030400741d04000d803005400c1a0030015001f1403829103280d200042000090000d903040350f441082d10010610031106 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 769663066 1250 769661816 769661819
    0xf070e0c0a410c070b0c0a060b01030b100201051e060f0105030907030204180b070f0c0f03140f0d051303050412080405031005150102072421020a020f150a0b19 70
    0x480b103554011542d0800c00e101d0301e01c001c10f06a0b621400c8411480d9200d005010030a10b5946000c09005044030141c181951081949003a40b10301565104131582503000044a20b003200101c104a0285204801191142030802005440302d50b5020760003c401d00380789482e583d8410400d1b2a021198000940145c1030501c102440c09585460200c203501c2824140070315605c038041228951750940c94000000c0803020118007141115000701e50290103481d20b20310301c10310400d00c0748984e80840101c0340703404d900249419100d5110301c00c4a820102540860051071001e840050030740c00745000d02c03821201100d400c407042014000c01ca40c000c0c203001c0c003a21640030310028071000400703017203900d0410580d1140b22200d4540c404107030082030f11424000c041d0904da8140070100c50f1015101203000380000d1323a2803104803018450079001781e01407405000d80d9460351424002d04080107036140d078401e544410b64004400d29402d102603404041404001072400310100020702100440040d1030900e0801c40c030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 769664316 1250 769663066 769663187
    0xe03090d0807020901120305030c0c0a020d0c2309150621060405010603090209040303051b190908060f011203050d14040b0c040b070b06010c050f070e0c0a 68
    0x58090b0900840d20b006260b81d03545d889603c2080503480c02400660100005200842d490002d04441032402c002c55030440c4496010850942c0c080b107040c0c4d1038281409041240386106000950711200741050906240744090100d188941d000c0d00c0644110310003801701001da01c0700c1040da0110880b10182600c50541041202d01000c01170394064010707400e240020800314024084d4480703590b405041340300e0640e0740e45c40880080030082c000444950500c80a0070810340d00901614070b00c1c8401030a116030903582c1d03001403c840c0032075002123040c1d08410208422414002901c904458079000780c0050181c05240c2203440703200784c29240441c81e180c0482d032542c2034800a00c0c24441e922510840c13483da11618075910302d40c0120b01c50040d81c003504100c64000600019202e90300000103061403040d032406a601c1030705240524400685540c8260380400113000c000101580182511f201985825840e03074005113a01400c50400074409080c0440315002c07694000403074401c1004005000340f5614401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 769665566 1250 769664316 769664333
    0x903390602060a2d090b2d07030f02070c0e01060806011e02191b08030f18060c0a0b150405040c0506071407060306030c1409071101090b01141f120e03090d 68
    0xb40549200c410300b800200800d40701e203e0301c80030354540e01407030b41a004c02083d207c03a0508000c208800309030711034090382c1640034140040c108151051810507181030414041c48000d4605901a1040016660501500307980043d102c202c8c2d404154003060760000105001d0f454001c0c2102c4420480c1d043d0b20b400b400b0705c1441016080e007221100b40e0000c01c80d03a1510500d559001d20881c1041242042000d648111030310810803120741c001501d26410b001d0040070b510300317000b070b15041900c40080700020009807103049010079030200c408070b4003040709040c00e855548008c2c40718042c1c11b008520004641d810720581c041340185031511041290107440c3c543c10002d0290006100444110f6011000415000440008842454000b0f00110b00f580c0c0c804804480b4030345950f83d140e4880d5a280282404030709c804050134041d010301070000210359181380a11507000350200201c2d101c074904559420405070300c81c034460340c05002a08086030b2800030f1010035055209008250b540060b104014808104809 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 769666816 1250 769665566 769665581
    0x40e0a0506040c2d030902030a06090b1b030c0703120504050c0f04060e0f1003050109030806120a0302100b19031109090712080a0903390602060a2d 65
    0x7030b9018851000c1ca014180e4800e08050740842600c070b6080790540c460921003201c000680e00c5450b011a4000c2140c0120341050a05241690441e495901c65001d009204503081c0d00f20f000031a10101201c1c8000c0a4100781c000a00396403842035001130070318203062003640302080a40441c8010000b80c281480c0c8517a070707110101041030103481640c3c100342140c94135103e10b41c125000c104d1041d00c5590354211483d0119001001c4005040b12000040081902440384d41150f621948581045040c1131007044200103940402c801258070000d903560000754085071604100c481c4031400f14840c503203580003809107070704200349002050600750300109000786800041000071040d01d0f01c14080d2294413060b600c40f1014082c030349113050703141c140c6400160400001c1050385000d1401a460700e850756102200031034030079180c40e40d8100044424111803a28411501c3d207400c0d035191401c40c2454000302a4480b600104400c1c40259290354006a0600c1e607000004044803045d80d503400400358404800040150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 769668066 1250 769666816 769666819
    0x91b030302010609151502031b010209030c0a0605090114091503040614010f031704030602042306041401121404050d0f030605150d1b0c0b0c03012108040e0a0506 71
    0xb070110003e9412034170b200d102007543e5160b0400070201d0a1a444844004c9665862004c51100300002d154070a0b40d400c2c40c00071410400000360313a45184800b01450300010f10385842c03242003140c004204030341d08a411100500c800b0b0030113400845c000e0642143e18000c800d15550031600066410190243c0c800065100d58442c000400c003904407511035141e4a83c0034002c02082012811080c030105002403003491391601144803080c505a10796072850241e81240e80905000d01900d0aa012061070b41ca0510300009015120141410f00e41003855060392440c4030682d0500c4035540707240d00c2403116034000070345015001702100700c241401c4c0b07045580e40b0500b03492007000070049014841c102d84240142c01c11910000c3c80345450703a008442c240c161f54030003070f40d40da401a60f41004c04d0f08a4a8040001048141070702c0b544401d14680c104044d0b1200f000780309860860b41000184000c40d03400341c0700b4020384050b01d2020480c2c40c051030f200b122403055820081040600c8820000020000d8019030320a840 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 769669316 1250 769668066 769668071
    0x3012306161a0718091a13021312021008040503090303070b0f09011401060507020a050a081f05060904030503060d12020616230c0a0503070f1505190c0e061c051f030b0a091b03030201 80
    0x152b40c00300c1d034100c030b4103800c1c000c0d4000c107904590156188103520040c0c105004500faa0700c0d000d5810006072071588121401c503600c0a03d03c04001c2c0c440b1542000c03641c412103440c002d22100e51040306e1240140014017464040c0300c004503a00081d529102e001c60301030480540440301c455100d0b0282c982e07543c0d403a80a54500182d0384c1d500f010b20341643c0502c0d401100060034178030782500d40d0f590945054000404031600440440803a0020440200c1c4c1c44412403a035401803e030f54180341000340303c228460f031003000c02c0c00f0ac4031910201d0750700e548404d03007e4901e940b00000c1e211602e840b20242070921101000d80700c4d08c4007180d0b64041c4652580fa45544034031913901d005c7c01110942c516020781e081102c04c1c040c04a000894140010490303001074100da907152400c108003194007000203082d6041603030542990040d0561003183c0401502c42e807034100003c08124103200760f5085440800d00d00c0b9010080c01315412502060024109400403900c10b9070280b07182e03558294241c40071030f00b01c1c00b0b880190015030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 769670566 1250 769669316 769669319
    0xb190b01051903020d0f14061302070f110109031a090c01030b030a17130b091c150c1e050d0b040203012306161a0718091a130213 57
    0x180501c080340c4603002d0030b96404641d00030b802c030140c1c001d4100c40000c440301d80d05c860100411041030300c1b50b507585170580d40c4003210600300070082c420b02003105a20a00c00d144104504008600030800d6090340390340c4640c0c1c4c030112580440040f6801c60341c581c40281510100350045031207001c0218400c1c4150104402c560051a44e4030045082d07652004000b03806030001d2200c44041400d2620940c601216036920a140846400603504c80410b1079000e405c101801050581551400c0c084100e62820380c000f440d141a0801c2c0c03540d2a41a2030701c044d4058580e0743e02e503141c907100d006442d00c0003010148502010a09a14a405040c5500c5031164043c040e25006020710343d0300d40362081d41d05031010410303400c00f40404c94003010030b601802142e1a40c412010b12507240303a5203404034000c11003481a40b440307600540104001d03015001c05000c000600016224910040c414100741c481211006400030640d541c055007030074950f0100c409001c1d0006c41a070036000400015400800000d05181015101203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 769671816 1250 769670566 769670569
    0x30a08070e0901060e06161e031403010311100207050a06050903010f05161407020a0f21050318042301061805060f0c16080a1a070c1209030b190b 64
    0x402e401d00400b0040b6400042c01d241506101c00a000d60b00c0b80d02200345400f42682c0c941d803a01e0400c40030089050b51b45450448201a0300c0f90316000c2ca43d403240c00e100e0855045a45d004078483c440b1401c940902e02da06141c5030550300c20020300780100400f5042c0b042503500c540d8001c10300ea01181c42940250708007201c1c0101104140304451007404003454074440d0103003001c41190000380300707000b12042c20410700c000805070391945407030300007081c1d0351124400051070508030a4100c80740d2201c08440030300903800308010440100880b0704d035000e5141a03d1031a2076020009000b0715091454682c85540003010b0900710580d000780505880460700c40d01ca01c06165520a05007600a02815821000501420b603080b9011307400f8118190701042910000326500b50032140300c031440d901442d100d030b0202c00ca0005000d80300d50030002401ca118134035a040d24104170007405c1d421445000070000300001001c3c0e8842840340d28120301440e0712a890580034184a00c20700501160400321128440c034000c2d46040c0c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 769673066 1250 769671816 769671829
    0x17010f090c0f080c0c1006080a03090518010614070b04030c03020c03010608030f0d060803180109060e0d0f02010e030a110406080a0c030605070203040f0303050703230d0b12030a08070e 81
    0x104000d60ba8030945580d828600500719002824a00446e20030503040110441050041c00041c144003402408842d0041c140104240515405680900c1101002c1c00d20000900c0c615030542d07480f420600505010300340c02d50500d200c2c0e03003405000c901129080c0001c050340031500c0a1160300130b07400c07903d42401d004101401c89465110300c211a60040012440003050322001e880300034424a00064110f944900f0a821603010071010558005540c1d152041c0d0b41e041010400541b5a5152160000c0d42c1800440d4011400200c0505208440c86052046a01c01e0700d000080900103800d551880a4610340984134a044080c1e144c8202c0c108070001c04c0000000804120968000341c4507200a480e5844034402004007401c0801180400c1001299440803490180003c502c07990382c21b81c1c0d913005420020100c0b60000c00c005110b161080e452040614000185c80c0e0903040301300b0000d0072180e114001500c2c048021303140c8036103020114505180c503030400760f503e114954903224500e04483d071a040050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 769674316 1250 769673066 769673087
    0x32104151a12030c0a05101415010c1b06031d151326120a0e1b040b04050c0c1209100804080904110c071a1917010f090c 53
    0x281d4038890703500c120900d08018032001c0309a00c1000c1c0d074a07000b1001c042900703207602d00205944551001498040d80e42ca2441014200190010035600504184801d040802e1030b140d12381c1d0410440c20458014030881d00b104030849031504948000b80b80d51414042c0c003425500402504552a00d00d007032030705003004a0301010044a50505400d0741d61220010703109524be45100b61080c030065040c0780c2c11210410b11440250401a4603e52250509050034604602c0202015540c4c0d0400300860240c030800600c1181003e4403c052000703d1991201240c0204041c080290340b05040c070f0300340b001a81106000f03200016014003964040c031402c0400e0291403244c084001d402c130060101c0841803c0c071944540740c02034400c060305803500081e40c0000b0169400c0403d450310580d030001c0c4031141000108494002052541c50102c8102440d0705c103441e0b14001c02512084914402095035441803161a400d0f200c0d041c2429030212958441c0c03102030400041d40604803445240818102501e40910850300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 769675566 1250 769674316 769674341
    0x10f0c0e030c010306030c03140f0703151d07030210020c041a030105160e041a0607050105182406190602010501060201111602012a0501050402030d090b03160203210415 74
    0x3401d4a9a902c1c0f01815400c03602d0108270f40900c100303c1e20340010070320810300114090f041c442c240242d00b421442c211200500c0d00500c040c54142a40501c2501207121401c40350100e1f0007007560341241b00160300740340c0c40540c03040c1d2003450850000d0982504500d5031b166100c042c2c6c0200903650f0341c0503d12007090348c0480407030007080072142c4080091078241c100306062209c075501041c141c0104c0011034856041240126103c1e51200c0400c504182400040751f41c000b40f100c000c0c480204603000800000901e2540e181010794054005001615144869102c40c4071484131000e1103583d0300c400034000e00e401c1c0152070044d400c002d05880001c114030300340d07642e990010603010340c14102c50340151110a41284c2c0c1d041c001c03801e6819250030b82a100408000a80920008111440e1601c1010300f44000e40428509000022100348050007014064079440348880074003561000b5100400c1e4594003d050300c6021101d0b9040f0080b8a40b150548224080c070700c1a0302c0e401c0c1441c0c1c540544015110918a02c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 769676816 1250 769675566 769675583
    0x20c0706050304050d050a08040602090d02331801030e0a05030f041e05061603021f02070311030f09010f090b07140d09051e010c02060d05070f0c030206040311010f0c0e030c01030603 80
    0x40c9c080341c003660007440751904c01440303c10345024aa004c0780c148031120b8480718000c8203ca04031640d00040240007958105036410880c0b4114512080300e4a401c21b254030300d4101031343d5405024101c02e0810800c00d00c6a002805c07603032160510a40d110056104c0e01521419075100300004480c50300340304091066600042146003044101a40481c443c45607020640451003090980b07520900c210020216211400e240565610a40e04010b48446503001c600c0f11907610030000c00c2d0044201c05c056861005e405d28110007103c0014000b1200345c1d01681000c078040000003001010840240c1d20040040c1a41d03060701c0b9500c0b220f01c2e042d2161840b600c200c5401150b00448032203014842e500803040b045050428000440260300440c68a03004420303041c00d030725a11b00601071103903045800705208034030390b1400200924183d81c0094842201800042c1030102c07044050305c0300c200c29000000b9898401c04104200c2c0c44208005200d03e80700c0c45464080c0c0070308182c086a41d4824051141602c0d00a01720 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 769678066 1250 769676816 769676821
    0x1703060307150206010b0319050a0c020708161a1905070204241412010603050304083307030e0a03170a11091e060310030201031107050619020c0706050304050d050a08 73
    0x1ba1071703547c0014040c0c0c2d1080d144880494805d0424458280604140fa07800139410781c0a00c0041d05d8140580c100c0d0700194441c91070f180c0100e401000f06401c1e071b0007500ca44039204110315409049030040c40300600e03506290600317452031541d20201070060300b40213b03810300404000359140b0780d129602d101c1c1c0001c0e03c4041d4109010380702030005140100003003d4140e6403c05082d030121400c40364160011182500300143c02c01ca0080c04000d00d00346110140882d80c0449021185000d6144641200f000d11002e9040040c2007113019500c4580d00b200048240c170740409007458000c2c00c016103c46080c10700e9400c007011820081543c4580d181c0c542000048a00d0a8007513001c002d0203903003114002e02500f0005400d0f0a00e9115200554060303210720010459060451001509a030907482540c103800300240002e01c0461000181d40b6000034481421000008075401070304080d12480100714a2449507020001d85954018015880b07107005005540c40c160008000300d0781c1d440340501410000352004003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 769679316 1250 769678066 769678079
    0x4091203050714070f0512030705070f02130f020a0f0203090d0b090f0703030504060207051801060507020d0618170a0e220c0c12030b010207120f170306030715020601 73
    0x1d41c000c41c01e0309041032425071510b03002e1a00c4e4400103013101ca0002808000c01000300410419940c810500c034000c1c254a08008000e0860051440c050070f0703c00182c0ca0074055403600d40301e924551908c0386081c01109502c0c102c100c0650301049c16034001500b0340c6400710b441031000c03040d100441c0e0300401c01c80c09a081c1c0c1d2504032403031001500d03a201c0da014800305e1280206003044440011480ba4a4058465281050203800c140c0301e81e00c0349001d0513942e00c0254200c01c4003c80107064070076906106488064a00110f00300c01d25000000b040709250441840c80c104a254511104a2148180314032a000310040c940141c0200300d510340104260034003425051811041c003260903800b842d81c164040c04401200c40c180c444a0030081c0c042804070480720180a0800d464800f40411400d051140840500000390344180074441c8202000000402a0130080c1140c1c0c07407010340341c104c0000d8041302c0c42d03d503512410fa070080c2c828030700c20311420000142c1d07125074151046050906d0780103806141c0c41c140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 769680566 1250 769679316 769679321
    0x51014040539210f06060a0f020102070f0c1406040308030c0a18270e061506040306020c01360609060207300912080a050918100504091203 61
    0x20400a0703108403015014200c00d55800900405911203401000d030400956003010440f10140400030040048001c0004589a220413100030302d075145084c641003645a40202d009000c2c120740202143d4480c1540780a00540001034030a5800000d05290742c404a0401c012042c400d61200a09908060001820421460300508a018014103050240d5418000800790914140d00000d1b07407219640c04c0050b2001950003180f210b549600300801503d182c200166036622002070480b680114260245091707521810141d40c003c50703000d031095442d40445201e690181c00014801c590340c00f291040d00c9c00d800d941660420554a070031082513a881f0141c0c903803e0207080311800988c0c01030b40822200000803401c01d48160350700089010f44c8500d1404c02d0030840f05000000e038035801c0150714081070280910306103244020680c003112080e680c8800d980b0586590040e41b0b24258001020074060300d200c83c20340c9680744034900286940c52150f407503104000031900f45200290103422055408200103000f079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 769681816 1250 769680566 769680631
    0xf0b01142713020604030c140607230708011103090f190303020306060f03010303030b03100507020c010e240d060f1505070f0210030212010f0b09150d0510140405 71
    0x400c1802c2d160045070007050043d406070b40200c5288501e154100201c14072045403039580141103c42c24603028440c1ca540702c0718170400358080c00400c8000c005c01c6503400304103d90030040411000a1104003142d0604458a0f041103446503c1d80c052034252400c01040401c3c020403819407441041400079131920200d00030341005207200c1d04807e007007100b4400c180c200f1000d540214403c2e5000700e5405101d03000d250800320030201d01000749041c01c1c248a200350300420040c1410f1020b00c0d1032010102100000742040c0700d10b4090510108c0c0b00d24600d80d110706a8002020145c00000c802d209035581d420002a04e07242c07901c5440916104a075140c40402c1c8910000c0511602894610f92080c0181c0c0000300402e401041c20301c0800c0c2e0001d45401d84800c3d00031a42c2c010021683c0e01c00d0a0fa2805070104400c0c0300380c441c120700c2003484030001c18505480c84240c41da1602c0e0742c801008a46040711511405c41c8244c01a40605e10040341610040d140c41d000d800d03c07604080382c40300c1d69111540f00d004d100350282c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 769683066 1250 769681816 769681831
    0xa0e07080a061d0108010b0108190c0e280605030108070611010b120c15030405060604050415140f010905130212120d0b120a0b040b10030f0b011427 65
    0x80b280002000f240d1101488403200a5a40c68141e0b5450300042034212102c2a010718180301c0400200714085000400507035144104080105800710401c030121140d03030700340908541c0440342c0340c00307030720521f05c180e0300890348401c80340b032001c426078903020107590500092080c1c81b0700d13a010035400d002080c441c0d0010718245044000100c1ea1380410710000ba92182054001c9010ba4001030403030400d4946420701c1081d040201d020b01e460341c00e0035100d090b110b15004140c0d500950300d550100d0101702c0e4201020b0400c1352806020401a0b41001c0c0f07401c2070f400c060b207c4100400d0001c0000c1034410f04c61042ca802090b0003214100c4c600982d40c06d201e103400800620240750300400303070451401a42d950007401c0e51115102d00044d0302c2d403100200310481c400c27102c40c8203040d03000150510003c0c10b2410803d40041c0c101e01c002c0745642d50720094041400e483c2d04002e1005013681741407000c004007800424140c61200c400b400003842c240040c013070544074008840c00d6904071054203504145142c40c1c4180c000340d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 769684316 1250 769683066 769683071
    0xc030f0f1b0f090a05100906050306160519050a02100e150402042702041b0c0f020409080a17011a0a2006042f180604060e07020d08060a0e07080a 64
    0x1544400600402e81c04c84041c1c0d03645450f07a040000c2c0c50542210440641059481003004508003404a643d6032401802c0c0a001c0000c07885d4070b20114007402c15601c404030f541c40607101f101d840b01001080d5070000400c41015202c1e1940725507880e00c0c6405900101c076002e4004103c6444460b003000f606240142042c0e03086603031091240100807070042907140303907500802610380305580c40c418881200c0e02c070321040020b80c2d64079801038152030340100a5007501f60010780040020f480c60000500528040000420000000555650301508100380c003410401107074856500d6030360782c1c4403640c05159040c0e8091041d00c1c10443c0c0e03c9c042c3d0254004420034145454018005c2120118080c42d0840030b8605031141018540b1001c600c442050b80310001b69811011055840e41100119014038000c104001c480801240014810380340c2d5071181005210700003c441c8103080800000c2d44800c24500d0700c900042c6c10200048031414201c0c1600100e0b549009039141341d946aa404554860f400307010380f280c1a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 769685566 1250 769684316 769684339
    0xc0a21021206070c1103010c080708042109050405090a0b0c0c010906140103020a080c0f040903020c1806030c0d0f060c021203040602120702011b180e01080c030f0f1b 73
    0x500b046042e102d0440b035120660031810f43d0911209986182102d14400d17818201303030200882e84202d5064001e04d141c241101035071110b250110002c5620418403e4109031600d100d10b0030303540280c40300d044030000d03101008540c4602c0c0d0042d8441018a001406460040d0b000c6440303246d840c40103105400ea00400084c0c0400d840d525941612a40b03a4140c1848102000603c29891b080d0811001000210000c01c21184104003250b254040001d603240b107181d546180c0001e0600070f12a451070f1100040a0346520580703851040100c0406940c214004c1c81583d42450140c2484640074180c07030340003840320560742c42c84e0382c491307001d02280c00245c002c5000d8034074481580c0030041c020310700641c480c0b40c01503221507a0030580a43c3e901c0050100e011a0305000d5000303130078802d520340307200584541d150074920303444000413800c00c90005034410f10b110790015000081030080817411418085c0c0490559036591a4052a40d84d0f540300f40b60350b00125080f221081c040c0e144941d140c144a424058114229107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 769686816 1250 769685566 769685599
    0x14070b0601260a09050c010f090605030402040e0303070305100603150b030c0f16031205040f0f0c0f0b0d05010b1309090f0f0f030e091003061a0a170c0a2102 69
    0x118003070300c0001c10f81d922200140b04011050180941c200003e28010716011104c000062100c4000d11072403061010000200e820754585401804a503600103007129982d040c001c4004006200440300601aa0b40851002c00e44500c40c1c01502144211549040416400c2c8843c0c51015072028000d40e8241000300711400208840e0300c080c1c140d0700b481142d480c0c040040e600300506212411000e00755a01e00e000d040000244041d00c1800d0f860340c0002100024240c00e10385034020450750303000741c00c04800395080000c140c0d840c0c0c8020030005640f0441401140da0701c0640c400940100110950060380082040c8070454560b4014500c49000e49888a4180803646502260000d420006d40c4c5010885c01100e007416005842c15291500c2a130341d58810f450000b84d00b480b80d441500008100680341c620f86007501400743c500c038100401c0141501d075401e9482c0140311456541c111001c00e0360281a004041ca890640701e040c0444081d42004821421081600d0801c01e0241c031007264002c0160001d010712 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 769688066 1250 769686816 769686887
    0x9011b0b0408070c0f0e150d0203070f030213061a0a090506070b0402030d09080d0c02041d01022101080309060d0f0e07060e03010b03070302010e011202030c0a14070b0601 75
    0x1c0d8050082e0a54a0780b460074005540c04668200c2070406044580411665001512156102c0c80d900c85030465044604001782081101ca02d0180d0700d44511007012a0744a510701812040340c2c421500c1c41070104100245030140c844501c20905551036a8002d5034150b2070890003010340b545989040200707580c0310307800a101c0340c1201409603007142400040008500b0104130040c0f46000c582042070449140a0180c1c4e43c0e43d0040c0c00c004200413902250f541151160307000303d980e03121000742d0a201c0803810440c1c207000307400213020041d0400710042000001802654a03505a0310284050b6142000e400c042c80410350103002c4100030681d40d140035a0111102c0d21032000e01074122809482440d15259004100c1500c41d510244284d1501070090080c1d030f000524802101e6082c00c00038607040040d0016a855240358140030811800003041003800c3c2406001001c0240c0c40b52500e00300c0f003401c0001040203016100c0010424420800464050742c01740c0c03428241c8451004200d10300d420000220f425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 769689316 1250 769688066 769688071
    0x60813060e071502031c15030c03050c0301230604110405040903120b0307050d0b06031905060f0106080606030f0c0c07030309080d030e070608090a0b1e0c040b09011b0b 74
    0x41c41d082204203000b41d020710100d01501e01c0c0c40748000c6040000d15510511049600344243e00c43d44d40e42d0881c5030001c205101660011500b0161116445540b4101a42c807400b001e03c149100b540303001111342c640ba1000c0c4c4403100c03600c01440072039526038502003440f0042c124003003078288000e0240300000e0035503076502130080315500c0707681c81ca0451120940751406a50071080c14038400d40200030b01b417003a0b0315241034140000740c2121b0b8503841c60700c602c001300b0b080c4242298118000440842c28030305000000a0550080b002e00b481014070342e0340c41604a4940130140c40780c962140d4100301041308520b4110800350003c0461900c10701d03040400240038980315003948101c0104101070010000498140a11021444281414441c042581d11240c5c4c0764280c0e401824207001d96000481c2c008241007054500150b80700000f4496401c1198400480c150b24548004900d0940d0380005c8062504409071000c031400c003114a07007030807486001902c0003882d00b0220007105200b051404082248000f10300d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 769690566 1250 769689316 769689341
    0x3020c15070203010f050c0d0b150301170c040b091f080d030e060a020c0a0f0503160606030b090a080a030914030a0806010207081c260108060a2406081306 68
    0x10741d50706191050500b920044101e911116244c4001c000d100c0c1300110854000068000700028080c66800020300070310100d038860740b420a00440007040041740390b04941855140c05040b81c070b1003c48041084152414454056004144600855040b140c681c0e0208580c0000c040d45812071625801c1581c0f404051014082c00a0b80300c0143c40c00404044c08450b0708100301078010346ca40925852955500c1c09400001820b11100c0508203051210034015909881d00a0b45080001d080c40d003010320150030301c0c2c00180c9128042ca004035541010006119840381c0e803045d4110b0030050003171001e40052910100075215a6501c2c4c0c1c0030000b600041c40100307118101500d03402070b07604103070000901c1d050f03246d0450305091b4450b02c445068040580b00d0b020106145280000707404415901040000ea0444401180d258111001042d07004010800318861003d00700104401c09130501b0000c80c1081c51b11050a0031001d5403800c0c0704d081c4c426460b155024044050000b0701d84025507a180884c1e04495030700303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 769691816 1250 769690566 769690609
    0x20609031209120c09061210240603050420040b211c021c031d070602010b010507110d0602250c0608010b09121f1a120a0b0403020c 58
    0x42d030390701e000712040c00340c4860300340204412001080412448000a00881e200700700500350081404070411201e2880441c00900b0720900c848007064200d00820481680c032004000c25002c580705100b4411648100d810040054100c160324409006028260740f0654000b6250000b0f0300541d11440d9800508406080c43d9000d455403c042840c00c10101c414030701413100480c0040c0001550009003403100c029100c000300c090031400e01c0c1c150000e00400c1c008240c0d5003908900110700c2103020803648100c642c1d42c0c000784180500c010045556114114000b070206e11381c42918481800d00c001d05048041c468400145003c540062620014408407000102644108503540030051520f004000030203090030324103110350400c00c03104d50900600c103005001d58107034481c03500350b000104050129460300026064503210f00743c20304800340c003002c4008420351300d240c2000e0110341000c502c4030000c4501d410250031766601e5942c03003a1800c40c1c00303001501144510090140d440d65011018824105074081702c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 769693066 1250 769691816 769691827
    0x100e040f1103060406080d051b0a14150c030c04030305090a0e010b1b192006030a020a09080a0201080115120501090207030f020109021c060204081002211603090206090312 75
    0x8000c2903445c1034120281c00e4211206240200703402c42c0a0b581c4103012030405808280310700300d0031407510b240e80101511400051040a45140c07000c580003070704440e10780c010701c403641e9150101d0300f00b4030058a4034540580c0400c41000400d100e00b02905041d100100074a010580d115151881c1c02c4080c2c0201c12000b40009141005103a501120a401a00e410152603070904000145504030102c12000d8009184003500103a00d1180c102c00c841078181c01402c10b40c0342c0c1400d244110003500107040701c0001c115140b0022504810010b04001c48c181d05035100000d980c00c000213a5580041c41c0182000d10803101200d04010030140900341c080c1031070342401078541c90303503003002060300440b01e02c100c0c1564940008140907880d82200130501058400c10354a51890601d40000284503a44c41081d0314001ea01144038698a5038006000411945090440d4480c208e1020303026442e06551a0303105800b8a0100b5141c14041d4001c040c1985c001000c1030304050079000400d0600b680302400680041f0001403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 769694316 1250 769693066 769693069
    0x1103010b0a1d01080f09100903110106060c020a210821070509100503090f0604050601030b09030309100911030a0f02090c0903030702130605100504030b0c09100e040f110306 76
    0xa2144103103050400c0c03942e40c2030481c0b00203449400d01420174484a2039940000300d0500d030411401c000d015406000308090195070800620b040600303020b54040b035007401e80001e5200e12600543c183c0c07a03002059490340c903180501c45041a200c0020b840c0704004542203420100c0c51840291000d4980c00c0c0300c0580700301061801000c40f1400078181014080705002c0c001044d2610503400c24042c0071400c0283d03884d12126441c03850090500c1c12007005220703035070402c0104000400c905048a1040c01922580d07140c00400380d8807800120b820100b00e511121403400001d020f42c1003100700382e0154041e8404c03061510046428103410303250964501014149850840c10814101c99204464042c03d90070a4049000652240324499020344901001151a0b0b10040c007a030006008100c010050601d04060650140040d0854402511201582e00003d40130001d41001c07681c9182c0c0c02005c0c2c015404d12010140c5200d58440c0d00c06400950b28112038550302c0e124427603007030a140c025454940300d00d051070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 769695566 1250 769694316 769694327
    0x30b04060204090f0501080a0f0204020d0f140f04030f2304062c0307030602180a0303080a151d041b06090f21080c100207080d0506010306050120011103010b0a 70
    0x25189140d149468010411f52a010401401e9a64040424400340d111070002a0180c09010101d8030558940b1245048054896103e0309032540001c00c142031503038a000014820040860300500803c6175010340e101442c0c8642c4980312080789581300403042c910035104c610b51503007003904940c02048144004241e605410061207060251040f0900c482c4201038011a44400d00c0b171000403d0325030041010052054811180c404041e8050940310519550f400e005100b0001a602c0101e010f1802031070081001003d004103084d144040010008a00300c45070301c2c2c0540310700600c1590240d2007004650030954032169440018445951090b100f1410401c01c101502107030751010100500700007041c00e039820800031144415402c50100e68403075104901c0c0c40c0c00c2c02101121100c1c003074030016280e000c000314800500031103100b03911700f0459907031040015000c071122800344a02103119100c014252070701300c0c2074a960070700403000003189602c009070003140c0c20381080e0400d60282401060543c90341c1e900a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 769696816 1250 769695566 769695581
    0x92505090f0f010f03020a02010e0d0314010e040221030c01090c0503070605030906220f03020d030b03010218040e0106050a080607081f0b1b10060e0115050906030709030b0406020409 80
    0x215000740002d14644006001c000810107401c0526401081307a030644c0d4000c4d403140d0703151900d1000f0f440c0c4400c001c100081c01001b61000c4407850b000e0b000000b0036490603030b8642502c160307400742c040c00e00094400e024200f00001a1036071403c0e132104000b0511081c2086c000c000c0400d03c01d000e8241d80c682010101400c0c00d9003900a2000c201c014400c0001d403110000c2c1c51900f285e20015030240c0601c40502e404190802c3d481c02034103460301c00d510070081580c001299140321181d0b9a04004000c1030100301400d170310415020509064081d081c40d420307441c156100d00500c0b4071480c000100103a481c0e000c9601822540c4c814070b0182c00074401c100a0076044040240e006181000007034210001c000c7c030442d051a217000701d040400000c20100c06114600804129800b05842280e82e00004100500e010705414000d00280c1020075000143d0f01c0c07070001580910340d91a0719401d0030515804284081504000e01140411045c2e032000408101000c41c0075001301e00411016070303120306110760801902c044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 769698066 1250 769696816 769696819
    0x12071406070c120c03051204090f020702011d01050903150103110301140117011d0c010f0305070c0b06041518140f07110f03030a0c080603030a0905092505090f 70
    0x700006000550391116020940d440340024612104407800d1140498109800c024642c0c40ba840a40d0526140340700644100d8004070303404e0001050b4030720703504168022214000e000c20407000c0041524200700d01d03d0341d00503e06140c19405c1580c89000245403005500300d902002d07036640e00500920801681c1d09180080580090052030405094564080f40c1403154122004040b41c0030748c0381d48000c2d001a46002051072200200b100151040380c1c403800e0511105011807489001000028000d0195a114807811303110384d4020b2032151980d4038040001040c0651007556240b0110150b0103001d0064050521804c1c10482c2040b6056024212905544000c1500c0d40f03d5041114600722817694640c04022403501400c4c9400050000c0c0c80d000340360203015842d01004c020405e1103c810f03848a040c10302d140c0c0e1000d44a131602020700d03482c3c2c840e4408010015038049004d000700e0509800311a0040e4052a680341b4810f44040070b2202112044080400184005000750691410741d6511002c85070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 769699316 1250 769698066 769698079
    0x41e09020310050405031b0a0c030606080d230c0a050304030506100f030506010611011d06070215011a09120604030e0a05061207030e0f0a0b0f010e0405101a120714 72
    0x800e0341740c040c1c1d280100c2c1b811190b120840122501240303c2408561480350340001c0c1500ba0366181c0c030707100019045500408440d84502030080207032500c501c10300c4c040c600405400d05c00000c0c982400c00c0036580800c80622040c412840c482000807000c1008100850041c0050109401c1010512407070344111783c028081c2c28004d405c14004620046180c5044440f0340c200454a41040203038140508150f80046401c06103451503101403440201f005807164421350300b0b4404210704150030b104444030a0140c10344001d031000e0816900548280245890680100924603011800b40c202e442c0c0386048034210b001030707480c2c0c20001c00c2d410702d2421100604011a95a410084c00e809034104510004003c2000c054035086140701e162024052001a6110740c41902e048800340c0c2008480e0420907109078412034800000061080c1c1301905060180d03034070201401c080800c5d845c0c00c03c040c0c003610301c8000e51881010b200110315502d42030305c120303a031a0328406010841c0c540790721001d08009151000c1e000e8003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 769700566 1250 769699316 769699321
    0x80315030d09092307020a0203011503050c0f01021c030204090f0212060103111c09020307120b04060c020705040609090b07031107060f0b061204060c02030f0f09041e0902031005 78
    0x90b000144078064408900002030250a0410400840060703450040a64060b100601481540c042140c10320140240c2c0240103515541c0c201164603006c6110152481c2c10400710f41c1c80038502140032040c3d1040c14411210b0074001860300c0c0001c1100020150080395000604001d1500c05000f4080d080c440303481c085040508260001c1c4203c070000b00383d94105a40c0c0c0800d2030001c242a000c0e0382600e03072078000c4e4443d4241403801c0c4000501e190242a0b00c03e100f01000001c4204081006682071030f07101c60480780710b485030399401d4041c100b00025a01035001c0d00c3c0c8041075545561066500030301c480d940c081141c1e00b160410389801800503140c441018205280c0e4501d4025090840717072400d5201e140001c0302d01c500c0300c20900030030301481000d51040c400a4214041c101c42a549801240100000c02490350180d00030780c0d0f680700c1c0010540800c0c409001243c42c924010000d040310507000b134404164103884c0c01d0300034640b45500720910b1483e43e81d00c0d01e07901941400c002e14400b0381e4040c0380402a50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 769701816 1250 769700566 769700593
    0x2040f0e13030519090b1303020a0801050103020102030a05180414010608070e100c0201030609020f09100e0319050c0a080304090c03020c12031e04050606010e0d0f170702030a08031503 81
    0x41c4503041c2c8004043e440d000c00b000c1054170508042c0010704414000e00e4079080d0180c003460341c00b94548400d900c10340c900940803036130180611607203040341c1d4160011440c1814040d400e80d040c0e0044900310622101140c21151f03540c5030390298034449450368101488035070604102800000000e0104030400a00401c0040b440d2a0308020014540e03240c03c00d9085030a0600c01280602856046001c0c1d007400800d07a51199560907018041c0030310125900f5004903c01b4108443c1c42c03d07070741c0d03400e40d05074080c0c85061280c50306030809140321030080c0143d9040007081d8001c0b600e450181d03800854140d2001038200310600040c803580513010320301d03e0103519108600b04d10f255103c1201d0b07103540c001c9200101080d840001d884130690401540c0040c0300462031f06003010740e20b50750122849804640700000720312061810b00240000316520184039207125000f40c84000040b03a2400103103500000c104500390140e50200481d00490b845180260755a2400010300a64140c0d200d0310306029500c90091030056 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 769703066 1250 769701816 769701827
    0x80901090320030f040b28020d081312110c0a0f0e1008100609050703021612110f0604050706080601050403080901031503061b051317030c0102040f0e1303 68
    0x210b08545041c10080a501034a0340c0c2507101d0b1422130810381100050001d0a80340100c00740101c07001203400c0c0c08030b2141c3d08007030110400c0c0159400d801600300010400100780075210060700040d5000700402c41e000140d45204e08803000480103800f043c00b5245903d5603400070071403107040082c1034070100281403611003000c00c212200c1c02060391030a00040000d900301080e008020040c1042011603440007110700c1c2942c000c00f102c2c0550344000f824000061a5a40603000303c0303951040746814030103074100700c0d15021141404001401c0c01c111010b481c00300c10b52010805400c42000902c09000281000d141440c940f00150b4404018001340d0020083e041e0303002002e4a0403030342c11104095075805542e004038000c026442c003d40109542c200c02000303220440c0e020205040607041c01d140804500c40068840d8010480010100340500c1c1042c001d402d800c001914000b050700f07040f02d09100b400702400342641c02981104090103910b010401c401002c2080003900510740e10b10302810a51240c40c010b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 769704316 1250 769703066 769703087
    0x8011505041b030f0e1504061a061c0623031e1203090a24180206091009120501090309090908030f061309030302040911090303070b130b10060809010903 67
    0x40c10f61341d070811319640303940e608030641d03d0f91194241c0351420402c40307085510b5003064400307680d86440c001c2a1a05c452100d48210400e45004103107600300720303135100c1c090303d040e42405145640a4072800009030394406075040300c1a07282c06030500c100c10640070060600d40308900001c03446212007010f0308040000c02091501c0305e00d44406515a69903a5000c2c3c0b02d01d03095094400815020101c401ca0140b5200091000b2035090508010f001c2450f030092031444000c15440c3c080c1d4016400c109180072407400c0080615500e18904107044450340e0b0300602212160702100548141c0d465142910405611403210f4000c2c10b0001e80400406105460714032480c00024250941c4506030001700c2e50310f40c2c1d003a0300c2040c8012001030a00154903c1e01d00103010b50000c0c8503408203581402100b00c80c1541c2542a101a248068001c4d810701035240c49040ca401c0c03000c4c110b260310348441018980415070410304144254500305800114038503225008205040051485030b607070b494003420740002603000b130104c007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 769705566 1250 769704316 769704371
    0x11040914100b0c030c0a080d0b01110c01080a0b0607080714031804020a1103283e1b012312040510020403060618060e2e0801150504 58
    0x10f40f40c003445404103140d40300d0712400d04102d104080c2003030100291903005000b02c084260b81031080362100030040d21004d1700b00c410684144c0200b01d4018a07544500ca4241c0d1101980708003040401420b00410800d40c442c210030786103010b00203061424804040f20003c0001e1240d0300662803e03e03240345100c08680502038240c4215000038a01c5d0000784200c58603010901c0b600d040d49d9607042c0d0310482c01c070000380e00f844150030398140c40c204115040c0240d450581440050500c0c09180e403d28120501031000141180d01700041004000a14407003009004101c80803818880100002c4074005088100000380c10940180c401c0c4060402c942e4180903902030002c0458115066103940ca40981410b40d14200c00428901c042400000d00000341c1010046400030070411b1040380c07500380070400307072900e6000f40c0c0090b04860010803401a6003c1440100c0e034446028140200c0d02411b4503209800c11742d0218406a441e1803003a0a64070b07000318114001c00707040b1820002107002a00c04050a00e0000110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 769706816 1250 769705566 769705589
    0xc0307080112020a0302061216022e0e061e10060507021003061a1201090b0a0302091807090e0609010c0e0607020a1a0a11010501030512030402131104091410 69
    0xd0111340b20146440f02071980180040d4840f501c00d120440084c90864a140882118000700c8085a00100d100c0e4850b501e40400b00d01c04c0046203210807102401c61050b84d00640c0d8443c010381c80c0745c0c1c2c2131011900412203a0400070495014400c0800d500d10050048056500c10700c1d0304004c3c40303400904448507240d06486c0112607100601065000b006141d1101e804e0789034501d03001303c88407481c0004003c0e11a00080780950fa0342c80300440c0b030031a090640400d0304140000b80600161406a0b0043e9101c0710b1080b07403802041614881c6800c00a2540c045d407400380c4c071510b1490712201b082c003071f4680c40395030f810003005205c8082d40020048401c1011450040c00001180015900d516800c1d90190103d080f8048001105038680c22444c1d21400303a41c5c0020355140c40b2182c2c00340060040038100ca80020040c186440010540521940b014101b260701000013101c00d01c0008450140740440c264076506142c85914040e200d0301039440c04150580c1d69540101000007074521110118151011800c44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 769708066 1250 769706816 769706849
    0x810060f020c030a03031e0510030f0f120504090c1b060f0605061204050606060c0607120914070e0c070c090209060f0d06091d060402010e032401030b0c03070801 71
    0x50307090050b500150b03a00350080c044030b9410325406411403c6c050000662401403c100a13010000300c4400b59809988481085410400708103900d040540c0c40340204d1000030b00783c40c2c9a50303861240d1100303024030022840100c0e0811141c1070500c00c1c0004140f0500703140c61242c4200130b02c80321040481900502d072640d00d6041d40c8880d0200d034441e9001d00400f0f001269242c1814503050b00e0328400702c4040f20640708a100041850a190050302e41c00c10a0707100400b0320781c6940100782c8413081c11110b00503100755143c02000100c0c954684a12498841c44042c20642c0e0034240c0d22002d801c2c0c0240140d041040401544001a4544482c003080720f2400b01c00603180c040f22000030300644100000b0321807140020400380c140c2d01d8039a05c160704462405108021920303c00302e0300c52002030104200502c9030014070002d0091b500403c0c40d003205000080907200c000d070002100c3c1c8402805080a0310302c500e460700040c010003942d071a41a401102e82c1e80ca6034210700d40404000e2951805003e0611400854a80f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 769709316 1250 769708066 769708097
    0x906060909063412060602011b0c080706020708091f0e091f03051b0414071809110c06090609060417070b0a0912080105060d0902060c1912081006 64
    0x140c0718004805000520005040c0c4200904c0040035070184080c0925115001500d03500503c036000d40e0308000303001604c503a200c000082d600c42d143c00c1010340c0d2000040045c840024094801804041e116000b90398462241202f84009219524050a03c20003141c01840005400c04079072450240c084640c0e1581d0380d42d83d503004010300c070f01b411800307042d051104001c820424003040002d011841c104010301d201d10100200800d9401c882d0302d0036122034802c004500e52900c102221680d200f800c06604031602d980d29145402c441d0388803d018500100492003050254050103120b0b008880f5400810150511000d0179840b600058001000a95410205080703100e200c0c060300c0784c0d560000c0c5500c8281c40c16400d1100a82440c25045401c404684041c0380c290340184190f506039100a003843d410800307000021401420075010a0341d100390b00f800310a620150800c900e031804400c04441000c8409946031400c9082480003420051100d41410031400c00050682c440450f1007614000b41c81d10308000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 769710566 1250 769709316 769709371
    0xc0906090512150412080c070309060825020303011a070c0b0a140c07050906040e10050c16060218090903030a0902010903060e06070207090b0d151401060305090606090906 75
    0x10320f009981d804030810001400308038658588540b105031642e801690b174038942100944036141004011032a40302092001c648904811640101062913100510b0b1003010170030341d03404038804418016400080140300880b02180d1011500e1000d010769030030043c584d60f4040141c2c0050140d0754140342c002c520103045c14458000f44005440003014141e0b14100e0105050704c40c1014060b8500030220040070420a042900c10303021440348601c064408200b002030b40d00040c003c00b40005070140c405100c100c2d01e017000c034603440c1c0505208020050b0740700741011414051301c4000e4401445100e0203030410210075008021a03910150790200090f40d00800d1006880300380c8030342c0010f841c9900e0309001140032640001e015004541d40e4080b01d060654920b0320341c003036030381c21041e06030002401d01c20040040c108541481881d0304100010071541e1100141c4441c1071003d92000d800a0384800604c6a41c000901040790004819105080c003480d02001c9030780e4032100540484240b00d514a0503017a01242c42 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 769711816 1250 769710566 769710583
    0x3020a0b09150313060b0108070f080721060504050108030a080f0613020d021b06011203081b0a1e18030f110312121e04080a0e03120d0c0906090512 65
    0xc0381543d442c4c0c141280902d00303c1d518900111441450110041065801042c03c00e01c60300311a074404117092103c0394121402d64001e003695050140303940c1401d02c007004598000ca669665030f0030008170103182104010545206901004d10754004126201c0099404410198050003c1c01c4040d01502c8003030104401c08044482c54240c0703072011902c0020700446400034000e60280c0100e280c044041034203000d032180001c0c030510340040140101940021b02542c0b2070780d84610280e1f014040e0f82c800000205c9264001c5a0340c0c07000600915210040000b055410360000d0200c1c078028000c1c00d840b6410310750f03403c81d0f400050054118100300404002e41c07282a40000324001c0d00386c4040022500142405070083c200e01d4080c841541c000480d00440490058942c40a40350400440e4a5544a06010742e2000010a08108400e40d10b00d01c00d803820420500c0c2c0c1061444d1856481100041744000c035217400d12000d04014040c48c0401c80560b102441034180c81c400c1781c48030035040071210502c1c03900152 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 769713066 1250 769711816 769711849
    0xd140114090c03070c05190318050a05040903030f0624090b0d110d0c081e040206030606070507030c0f0501140a020a03030c0e040f0203040b0609040812040c0b16050f0703020a0b09 79
    0x13007071041f41c0500c40c3c610004c00c07040c4c8640c550741f119040200c208a91742d55180a181d400621071135081000b80f405030400081c0034003d0400240f1000000e4907581030300d03281d40103210702c41808040441144c25415180001140074603003070003c82e09101c084c1d079480c403450130300604d01a1111000b00b5174250400880b0b6242e40046820840c2c48025940a00a0340c01211148000f0641c045000b000c0784041e01e140348541d038010840342c9166aa40f0410046402448c0191420304c030f21400440011801e510010142c50714100d2404254078000c0010003100e41111000d194071401d00c54200c441d9000261110200e038541404600c0e00303c0c1000071100359403107502140d4050300740115802c80e11003030750055003d00d005100580e000c0d59130000f4481080c405076170051421008000306000b01d41e81c803a203a504203125040301901640c3e00e60720034075260800d44401030301916007036019042150030880034072010200c41c090442c4500e1a000502ca400507840350b410046d1001403000b15956800b1814030b2070720035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 769714316 1250 769713066 769713073
    0xf03281403070201080c180f12011d010b01020f03071b03020d05012703020618030f0d1e140103030509032103100503010b03030901140405040c0203041404020f04050f0109030501020d140114090c03070c05 89
    0xaa40509105c100d152f46101c45a03500e0101c1c81c3c0d299510104419004000310401545401c1099070350582c414031502419062500d130440110050350760b4a42c00d580c40c0d00400c0041410700030603100301503075580305007034242c220038681c1c0c20b200283e004220158003030141d01c0700b2811155080e801c60b045101d6402d0900c11402c5c0000e09842c1c406443d400240c841c0b999a0b00d41e0700c042401d00c1d85100300c522041210110700d40d072000420000340300d8402402e84e950050152440e000c000000f14126400000c02042d0000e0040108000803102d20340510003000c00310000e015050240021035100d10608400904108401000c4140031005000322401080094000c01c2501030302c10000307441e50400c0c058620b0081206a0f0b4401629183c0207079105410420302643ca4949401e0411332804d05410b0514180142106c000000c50b00c02c4c800741900300200b2001090b44030b042d500c001c0040c14160040000015560f2024009484071030b01d1540c00114005940e03074039251b420041c0c40c0d0000c0c0341801041c510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 769715566 1250 769714316 769714331
    0x20a0c1a16080403031b090303090e012403090203070b0d0506040623060c06090d11014206051b0316020d02011106040c03030e0f03281403070201080c180f1201 70
    0x587c4007800204403070003a90394a200c0c548481c03841682060030b1141e455005000001c03128903500e405004d0002003014240000c056846a011034105065940179070316182020a20b007100e02120300070b566001104403001c10030203041c0300d0301450070000c0021051071100485120500c1d500c44000310707202444250700700d502e940b0307040324681c0d500c1194807510300004000115006840905001c0c441540708940e0781c050210210130350380150085001d02d010b0b805039800c10103200c091500104a00605034030307941d5954400e0519414031108645401501903a8020042c03d52044507440149c01001e604076081e01c400c070001d0004982c15815400c4e040c00c207010b42c4050104106005c0c102c1d4080703c6c4281c45814200035180108020145020450394140e08028071107010030058603030004a07c4010806403044003c43d0702d545030304203410f0503512015400090402d0035580c2003d5003641c0454203c400c145845281001c0c40307640c1142e0402140203542c00134001038943d8450b0814085040c08000070401351 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 769716816 1250 769715566 769715621
    0x706030b0d0b090f190c1202271501050c0307061805030307050c100b1c0303240515040501120c09030f0f02040b010206010f0b160204020a0c1a1608040303 68
    0x101e04138425403441c2d102d08034000b4500d0060f940341c8414160032243d075500349071910b02a42140789680000320b81c00444800e42c03e003074003007000400d45440500c0c0c1441c1c100f407900b0075070341440326900e50740d20381800030034400e04403504400070841e001d040c1e20250100e030790006404207100f92105440020400d01001c402c002410350f01001805808030042d04895820a800300b00008403280507510302c1d00030140204001004041c4014605410b00c03900d400202103000d4100c1008803285020044040c0403400e004110924042c0382da14240710030004000e1501c1d14000020f8005d82c01c001240c036801da10b40070300c2d404840c020320b0301c0001150040c50329041943d00d03203080000070400d81c0089210f46d2030004400071715440020713858180d4115481c91030a03103060024016017a0000303444140002c0200040d02d00617200c50000d04404d115640780c1c0399400100303240c1140e408040001b20400019804100b00c000d10755890055201c403030b0740c00c040560361071300c1c10124083c00d0138402100c049006c58841c0c807a031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 769718066 1250 769716816 769716823
    0x303070512120109050105090406020703021015030209090102040609060c0c0f2d030206180a0510020106060f0f1e12152d05100908060c1207050c0706030b0d0b09 71
    0x2034a8882403000e1050384c8907801c003030850301c0a003e01d50304031a40c980000e0000b85c482d030003080710728001d004807544807294100715416692002c0e00000d203060f500780c0410450412691250300081c0d20b40003941010705202004140064610130802002480711591060242031816907026168403404200c115031503421400300e4154a5602040042c0300464540d0104002000602940d5005080c145031081502c49035014000b440c041550182c481c00002425548080440d0120071590300040f81071440c000004e80700d002c042682d0030a00c424117403142100c0d58084c2152607002c0624688110811b076500048450350955060104a6854190300b0f1a424254000c4001116003000e151100031004003040039000c00c0c0c666503080c0200700c851090100e0300d040e26000608422a10388240c03e80c1e80c9a0707070a450302c81c007a07640d03101c82100020070b1201c44a48803400e640c003a0302c604005252034059140541d49d001548035010425903034102281e8a96109404044c903070f600140e0060301c50420a5a1545 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 769719316 1250 769718066 769718077
    0x118120c060c0c0e0a0b03010219030b1206130c0e10091a010c080c0102070503070303050108070605030f0a05091903090503100e0318130204260622020303070512 71
    0x5480600500c0011840d204241c0000706a50202c2e00d012204e10300030b4811840307100a0a0125201c0e140e111203201174400344003602c0040e10701c42c0c041b0030200d1602d9001c2c2c11501203140d05402821701c40520380a2a100244070f640124401c0040b80d403802890408152805003500407882144013101840340c200185a03200c82900c0b5500800c0101d0f00b00200c084200048611215002c14099500c2d40c01261600010348201540c8500242c07900071980d5a0600316488028110042903032440188400101009210301401040c1051491810100d1aa85074180d0040502c81941d0302c4100281840340c3c18024618503444181c4141054042031402400c0300f803031401107078064860b002c103030810103400d8050103034180740640c0a945402c6200d1090a41d518202c0c10042d003004410350b030400721150750f1006100500a100c0355020003030000404491808981307003141440e61084c1d090000140e41d1244d200400b03001d200301c0c0445810f051020908500a00320050428050b040c007108200074881c00618 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 769720566 1250 769719316 769719323
    0x6061d090601270f02070b010f0e0a0c0c0b090a0804090c030b15120403050f07080307113d020a02031b0a0809060708070c03151415060702011812 64
    0x10202ea03240e00c0d10f80e0507508803402001030710310b2118000484100c0c9512044008504580240c580240394455842d5107070f0030fa001829500d08030b1001c01250400c502e43e01d4001000d910180070081052200524406000d071016040584400c04100079000c10005101000d0384680444c0c1c0310740d92240c1c010010081601080c0c08030341000d07a1140070b450280c811851440c400e060042c00d0035100700d9521580003009204400f80003040159070980103542003c0c1c00c81610804c04190349281c0600000e200d81003814a000c4d440d840b0f0340c02d809141b01d0400d800042000138500c10401110074401d1b40f00001c1c403001185403814400114002d10983c048010503030941c0641023142004600038036a507070b81080301e102400d01032081c014000249042d5006001c03143c0241201401c042542d00ea0045e448080d601c00c0700d841ea032025070301c28130541c3ca004000f4020700c031580344c441c5c1345041c800c0c60000748030010401f40301e01c3e030018003807045a025084070710850341203195440400b619100c0000e2051844c42d020b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 769721816 1250 769720566 769720573
    0x3060b031605181b030901020a03060b032701020f12040b01050102030a050307051b0d1707031103010306020f07080711030624040c020f0109030503150f06040e0406061d09 75
    0x74055414200200450b003010300184444080092952468a406450401c1c0758401507040650542c001c40914001c40300a0001680c40d142c10317001508071009540700c038043c0f0a0a104005d04009801d205102c011117a00403058400d2450f820203009204291011149071808a9100c02003003c0950306031081d8070034000800b0990b201d1006980d20f000b0f032546072002400410000760582c0c07140002c0c0000c100000c201ca0480f04c125403440c1d04081d5009a450000360382d00345846200b9507408000761704000c00d414100022070307030f40c110294544014000601501c5d0001007400c0c907140440e040b031b0910341d04040c0058554001e482c2c0201c000311580104c40c0301e8030030000800c104005d030725459a021301c0d2003a81da01094100750103000c0039200c07450403202503019001108038016420b0081c0200f641c4681e4410b507992604103640d0402c0800540c0450140420364040700d51b60316404121802e48142e80483c1805035180c1c50190080d00b40c90f0891100c07507000513407140302c0701c400e21900741c000c82c0608142c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 769723066 1250 769721816 769721833
    0x90503070e011421191101020105061c03180602030711090c0405090402061b060a0605090c030402010804031e180f050d380a0c021501180608030a051309020c0703020103110c010603060b03 82
    0x12401e0303c0702550980e40c066540354103031000e0703081b0105143c1c8040c07003070070034030700306002e3b02c00860040321300e5809500075070000600e00b0204802402e001501003001c90700280726081988100d261801180201801503c10030081010b40d031303440c4c041e2900a20604c0f00010890041d0401c280c482002fa00e81d20344003814440003107030303600c0d10158140c491244280001d0446da603d07001103440000190090342400305815403005001b6903110310a410200503110301c55004044000508008550b5018202c41c100c442d600744010b941d03580101204c16004038410207038810074101d86070044e03001142d0498180d01110704105800c0d445401074404c55003074404200400811b20280c9e1102c071900300800d640c0c03454800601100501100101d02c44992040c0040c1060f10b50021920f507500401916001c180041014204200081202000741c0101c5400b9401c01d600da074142941c2e005507000080c14540c80748000e002520105003515042d0000394000e000982d80c034100708006001045540340139000b030946 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 769724316 1250 769723066 769723069
    0x3030c0c150512130f06200403080301032d060f050a1416020c0310090b060a030302150411100e12030c0619020405030607090503070e0114211911 64
    0x1940181076071545855207050149040040b60740f5000340800c1d0310380d180400c08400314021024000364a0300c140400034681340410810b09040303880341c8840303c41100c00c002c14000100c200098904403503006d22881c000c8413034243e19800f07803c0b845005840e0030103204501418496550441c810042501e00100b106c1c3e107e201384031003034504211108ca181e8420001060143e0070b02e103002201c00c0031700d1042e10f441c802c07181d0001e41031000c0b03049010100343e03d5070703008024481c0610000b50042030444011031a2440d41d540130303460ba10741c00862282c212044000506001c52140c0e82427114100510804808a28040182807003880c95599802010000340f0340051950000894141e02c0f100001080f19503a0b2248040d51000246003d2605580034080003a940d2000c10140740120310546429502504040c00e1501d0700200b903000c410300b0b0388440c0040100303d100541c8803040e080290f4007010002c200c40340d01004d02150052190340c6110f90310f514032540e8000012601064813404203140003411100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 769725566 1250 769724316 769724339
    0x307080f090c0d0302010f02120f06030312040b0402010507080c030a0206150604030605040c0801020c060a05060409210908063405031306090602070b0f090114010603110d020403030c0c 81
    0x22000c41050380003040c060a180307082c00c600d08a1604c01d20003c904810034803e040140d0b0000080c000da1000e50f0014001c6421154601507440003041d0021410001040284411403801410140c1003491845c00308055900c298200c0700120b4010240698411008280960702e0f800003180e00018007400001c83c0e07000d180301002004070003006081c242090b0039600c40340700a28018100b2189651110b030b001404603030038005844480034500103070000d89407004582041d5140101340303d12551624500100140384603078401c0c1600c10601c43c1d2007000050040680f00d40e401d0360072221803407180b18100300d1500007c6910089000c0503160f08240404011454004110130840160114605000080c0000165102c96150a014807804504920b0300d850349001ca03030001c81c0c2a2201c0561038200259a88010009604200382030000c1202401140c1c48080d00c0b60180120020191a00700c4880350200340720507074041c80f054040842d92141d503494041d2081c3c403d44411548008809400501d003000d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 769726816 1250 769725566 769725571
    0x908031917040510020d0e07080607120e06190e0f071503060810090c0b070f0605130209040b15031c090e0f0403051303050607030906050129070f050d03020307080f 72
    0x1001402e41000500070813019410601d02c0e03410707645d6070340340c0000490000c200800c002c1c4280070152155003400744d00203107945410340300c441c1c6803400c1c8884120940f00014800754046c00c480403800607400b42d40b00d04005490001c001010b180700c0c10150000304000419001c049501e42801c0c603110500c000010340558149210700c401a030003060341510500c00e16080150185c2c49080f4881050383c4455241c511600000400c0e11101810707400081001382e140700e201d80010201400a06034512079002943c84000100000c09004200010a8018841000503051070380c0040c02c6d240384141010f50500001d6007400b5072000190000710000e600d294141c071441c0210948120031800717540f00d4500381c42c503900c61151010340042411001003c10814801e9134050100e0340d078081000780306414000142c07801030300a907104a601d16900001c00c0101d103042d00c440034518140d1902d60006041203c05c1001c004400b40083c041c4003d101d06c126415801184180d565488541c89625044040c07220405c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 769728066 1250 769726816 769726823
    0x610120c05040c0912050d0f090b0702130f1d16080a030c210818010203010b09130605030304031b06030c0522050a14010e030105040308060907090803191704 69
    0x420340900641c10182c22400003074030141405140643e031074411000c1454890019105c9401c44070080f9030465110040d00c0e0321088a1400702c4c030813828207503244500d10803500c0003841075080070f450f607040d04641c1e00249070104004c07004100614901e54602d40404030481c0c4079005000d01a6180d04007001040400d081da0104001407a000080d0b54040d5048800c081042d100325207140428030344440044400e840140e42681c2e16041820f2000700018000308211011f001c0e80d005000600c403820004080c1c55101c1e1048400c405488891901503001f054a0f4202079054000018040181f0058080c9021010708903410764469654850b000c60895800c00140c800148042000c1440d4003040ea40148003105400c5070071000702c0c1d5900010384036012603031250407440d641070603e0b41c080d81c000c11401407980c8203900a0011385020350700202410300040c01903100350940408034034964402c24a017009840a03e04032a69124010071001c290000340750040c00044082d041c00300048a400d0115000315070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 769729316 1250 769728066 769728083
    0x902070803060907050721021912030b01110a0c030c0b0405090a0f02090919060816090c0c05030d02070c08030c0d05031503060a020a02010b03030c030a120b06030405061012 76
    0x8624080000001d0701a100c0004c0040c1403000001051800645411801c09448009041603c0c401c019040021000040e0000e45640452201150352b5660091190419180014070810342d40010303140b01e1031407940e2081c948035490003801044240044001501d0084c040e415203986c3c0c0320550f8506110341d0056a8100400002050b4656800c1e00f1100d03240e07080540150500c0e82001c041401e60004684032003864580c02e598082003041c9100d004081c04004015001041c2004580200341c0014032440c40e00d1950350050580341c602c41c0020016140d8040140c0e50760f800c0d0740745540040d41154000740c415154040001900300000000c031aa91600744000d00240242c1200c04e032910b8100410403d050189801d041000d0765060010500c10034820000584600b64036030000e085552032990140640e00c01c220b4201c0407036002095565151580c5040030300702411440d0742028044405480e500480d021040c00704009010540705d2117801318005444480b56108021075284440e0140601481c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 769730566 1250 769729316 769729321
    0x633010c0303060e1003021302041a070f14031e121521030310090c090e0a0b130b010e1c0b040203120a0f0207050a1a09032509060902070803 62
    0x50140d5414003109019080005000750340711440455a4003c803180501c000741d2100078421854041107000c0341c0145600218107150602c0343d46230901c0421800c8440c03840c404600c0404209614a1100340d403030f40200310b21014200059000c0d0703603070031840c820306424005034a0f4070007603000320003178030000c161401d8005226190240c00035903040c190b0031030070f81101c5001030401c10300343c0252041020302d010300c008642c3d0746030005650f000c100c0c95403c40ba252030304103041e00d134035190311100e95400d030f074265800c6042c161100480703080241030310074406420030b4801080d444903801542c04070094080c207890b400d554003281d4003003044055207040381c60b00303154020509034003190300764040344c0e030252016048a1010b001542d1510321030b0070003034045000038040c903449603070a90305100c43c0004160039524075401c02d04080d10f040d80c0c1000110100020440400c80c01c4580c0c1e0700300200d0082d6410f0101c0c4644c2c801c1101052680540705015209201c0c0c10310200054602c06842101e88054105180c0c60864 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 769731816 1250 769730566 769730569
    0xa050606041118030c0405340828060303080106180e010b070c03060501030c081207020d12031404261806030601090918060b0603070c1704030602030103050633 70
    0x11400f15440d802d40300d4140b040c03a1580341d030300c203007801000c0d03003e840b1700b1031170000c20640000a00d0085072085c884881d061105520380000300c042d080340c02083c542114042030307030025862541541c003600185081c100e00106040c2c10210703050507102c5954600c9a290082519400043c1092092500d031500240c010054155020041c0a2080c03141007800401075582e00c80714280c807001e8009641c406950441044107400400c240c00b14841d40020050503c8000d0700042c10b40d50784088054182001800c0e0303203207214400d42c402a03201010000c00350007810a4104058510180c0408020900002110500465541d001d8410000000b500500e071005040e06210060708081c02240c113112403000c011450101c1801146800003a2070f254900d002d11504001c0d05907902c07045801d002d00d2040052050700750344035600a6801e03420a6050002200f6902a240103210310760001d03107150b2022001008009001c82c400d805406140c150310a0304d202030f040f02c0140b209030135022081c10360404185000d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 769733066 1250 769731816 769731847
    0x903080306060c03030a06051c0305041814130506220206070c0e0c0c060c03070c02210f100516050d0c0e2e0914010305180706020a0506060411 63
    0x200e0000ba0120341002c650507032062441c0c0069600210300c41e22000240603504000b60340320f5000303500034203e00301c1c5400d944000d0650710903805802c0781c03100c1144140701e1009460300030303415249050a54107100e141510017150901c03084142100c8500070315010032481248000301e85692880c020059103200e8003a420802560710051040341c0ea280700e244000b500000c02031451703100c0d51034148821360362402030100ca403c0c410700801c03a00d401d40302407044c4000315521540c5010039039419590040040f050744291130000002058105080c805c013101034458100100b900040007075104c00a100031740352076140c1040c10b044100f08800203001070180f14210441e0f07030414500300303040e42040c8418940c1c401c04201c007195000c281c0d0500c1d0040b4a480080e007050100945411512403a182c8000d074145001c041401c052032001504040e01d0f14040750000c004140060b092507070020031200d0f02950384002039124081804103139518040c1d00700055007400c2a005000b0341161650f405880c100e10412501034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 769734316 1250 769733066 769733071
    0xa141804051003050f06010303020d0203040b2704020406200d2106030c030b0114010201090210050c0c040501080703031407030801121a09031e210402120a060b04051609030803 77
    0x41c0c2c01502c460000c0864800d010170443e540300d00b4041c003203e6041d1700700a03143c190f001d0059000c641c4200820441c3c80e180c4800c0d5040305c1510031030314894100c0c0c841c270310710b01d1501c0319011a8040e2001400050041d000710040f0b04442940344c0c199480b8041e90310841e00d4055855502021820440c10804a090550b07000043e48003110400660f0700d8880d2242c03407400700030707410841d030307540c03804e0014801c02602810400f1507100910007805040e40783d90116140d0304400184105100c030101c0d614003554410b104a1810a2014000300300d00e603511a2100d40e11840f0303100c1603011603039207061401c0d18035105045460040d01a166010540d01e020041d280e900340e0900182d0300c1018407042110003071003011246001300e0b0071500464960719440c8401081107018404c0d2201804100080f4006450040c2c40302d40d4500845140c0301165120b0020441c081e10760b401c0d12078240641464002000902d620000020505550401450b035030305144030040302c2e040300b401d004500c3d050010030008104100459 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 769735566 1250 769734316 769734331
    0x703030e100f020306121c08310c0506040308180607080d1b0905030a060209010e1201050411060711042d1e020f1b071a0a14180405 58
    0x7035090350540000011900800148809260000103000300c3d4500f582c020254400003002520340d00f40b0307c2c19010242121075524106000d0307424001640c840d4000484180c014404451003000c403265006c08490035540c55045681c01d0031180c2c00b168505000307095a050742c1e4003e01d100d181003980c10203038154000d01d00030705500190800c140400240f10304040c0400c2260182c020885500b0084000c000740043c80c0b52004000d860720003002160340006d282600c2907081040140d0300ca0796500100d640060f607000494004035002c1d8101140c01c4154400c40c0302394002c0307025406144446003044030500c212400581824560740700458103240650040c12440d0155a5480b0b2102012100e0780b12407181180310000300d82c0d80c5c40c0b072920107400c0b000b0344604032900610861502014210b444624019409a0029502e10550701c000008003004030704050400240d5280042d400040703c0c3c68554000602c5000103610240d03003040c2c00c1c05110940d83c640c00070540511f40310140d0000e001c0203050040070321 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 769736816 1250 769735566 769735573
    0x50616111c020901060305131b1205150105060f09090a060504180501050a020f16031b120e01020705132d0b180f040f0302100606030501090b01090b0703030e 69
    0x3040c00d0303624410785040400c081c00c01c80c07240c81c0c1c0c24010407405080590000d4107040c24001000050910b000317800f030195034445588243d038540383c0448070310081d41c1d410401680d1604881c00b020b000000651450b2000107001c2851280c1c0c0392001c2c448980500c4d246003000031018400c134134940c58890001a0b000300d91800000e095176540d00000c1c1a18259002860701607002d400100500070300b8020561b2090403224107501e42a51a41e101640e4864042e41292090b291000001010b104180a59040d922509026101152400c1802290145402a07030101e07004480c040029400455034004851004000c920b07012041e2007180060000f0001d16010003150401d00d14420041c1114010410700c8045c0c0000c441200c50180545060800c03424a1941da034241004900c500000d00161f0080e8050304000480080e8074090f481c00751110510601f003401e1403408a40385515500241c100c400018050080e581e400c001507414509500130714100000421000011a02035000314206200b1417089 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 769738066 1250 769736816 769736843
    0x8061311121f030624030b0604090c031a10120308071407060e0d080c1611060d09300816050f16210509300304051504050616 55
    0x2c44100d10440e00110340c42969110140c0140101e444071a01d0185e610000003055804d6407140c0419050003030826100e1500e644404041001d07406101e00250342c00848641c0e80c010545c0014120300c0e0841d0301b00d03050188082d0002d00b200040c441000304541588a84032942c5540c041100d801d000c0b1190302c20000303006c0200c5000a4502d100300e4480301d0800010b48982001010028401c6a01030104200e2403020300041202c1121050441d49155100e044240700d56400e0000c642d0501030314822400f19898011180c09100404041298100780c403094000000d56540440070a01c0608000d100012030580000700c0d034002810300070300182d82c18203019082c00c0c00720100084070340c01415101c00305a14041401d0402c20074040758005041c1900c0310840d180183d0500810601078415114401c41c101c0e1141300070003c0403026085c1c00b1055200301c200a00c00b902100303950764401c0c4a018014201181d00310340c03054a00041d60103441000b0100c6240c002c240102c41c10f20500c0c4002502d44090302c2d0708 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 769739316 1250 769738066 769738111
    0x70f11030c0304030b01060c05030f0a1814010e030f03071b0e0903040905060a15081003410d080a0f140402031005010e0109021303050307030806131112 67
    0x509a07545051004664440c00c42c9000e21850304181d00540a010001108030000786020069600410207113034660b442e40320f6641e08035454007090040c1c1416142d61000861150386150f01502001400e1720b4031598050003800381b60780d6044e80b0006500c140c2040c00382c2000140d507024020a00054018030754030544d00d0341d000c400301e920151508145540001810880c0000301d00070f059104a0440341906680c4c580b034000e48010018080c2ca4042250000004001c5081d1040003400780d5003160701c000c01c2d0450070070038451040c1801d9101c0c02050f4404040a211703981841c184280c00042000341010b401c00d8a0155120306000d401c0c1e4800390789079052024039609034418195200c40f60200c42d030140c241801490300f840e6a551a01190718103120040c03150345807840d00c5a045a80c5250010b9444200b5041c90003440d80b00c0d00002e0182c0000201c01c0305040d800f285e20b50042c40e084842c5c0341070b91240c10510084880e40f80c4083d580003000e000c0300d0180040c0d040091b600c1200e9118a00c1c081d4031000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 769740566 1250 769739316 769739323
    0x270605101d30010608010f060e07082701090f0302100b040203160327050604030e090405060708090304030f0609020f0603010f260613030206070207050906060a0c0c09050f1e070f11 79
    0x62504080c8d9182403c200d584030003028960028034a041c11183c2d400c0c9404080310040f00410145985104020300300e0028400358081d09030541c0100c2500000002e502e03000b0b449030403000782140d41a0400707500040070b181600c04c0b28001c9200321031072100c0d2810818190b0150803103030b11400010b481c4a4510000c04801c41c039400c0794902c280094500d41c90145000391983d91015880d074000c035212400c020024000040345038200c5002d0820105582e14500d5141ca18411031300002c2000c102c3c20b40c180100a40c541110b54002e200701c0c2d0710f40c03944030b4280901c50303180001d100b0b03090030011903141004032507507400d590507140e9007080f180074810a5801a0b14078080c0c05840f2081901c1c810650503052542c140071183e001000ca00c0a803e005103031100180400d180034000314401d060004400034003a000340d40e480d6090b54032640070020b1940d0b540782100145001c6500102c00d4100e2400032b510b43c0400413424002d222000b2401441c3d481d1982d00700c501d00d01200c801c01c2484281d18051281c8403040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 769741816 1250 769740566 769740581
    0x215040f081b010612020d140c030a050309030c03030a1e0509100c0228060516060c050a090e041a15220e0106270605101d3001060801 59
    0x4042c0c0c0a48114180d01c0d007102e040f035202406418840024000503650900034419458205c14000101100c0620150400d0301503e1032991621410090f08200f2402002a01d2444400c40980b4170103194207003403680302e21401050000064004080060040790004c10300405100d620b0040d08002c0104041130031543e10246100114a100c04d140b401c514003e0389910003451060f0740d4508038240214240f4418405002d18014008007007034980c20342c2550018640e0841d009041400048007a00c8050419131010b040c040024420700d401080382d640c500a024000d0381e11045248102941c0d0311001140b920190220340c903800b080491340c0d0030b03a849000d920700c52250211001c4511401d07000b130900b00d480c00c80341c1c82c10590400c8000c01605d02015411503180c030040e00c01c4c101c4004e02c020901c0c001c016070b0304555130041c1e9075035100300d089601079010b00c0000203142800c08010681d1082240d1100e24060f441d42d16405c80d40407000340d202440c4d00d02ea43c04c01130000420f68a44a46445003550002d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 769743066 1250 769741816 769741837
    0x1008090f03070f062003062b03030903090609060215190509030414180106030e150c040603110c060604020906041208090a050d0f110a0323010f0209010215040f08 71
    0x400c3d858410300c0030b980f00340004d441152071003003190301e24060a40482d000c010700780d40c030624004085888000c1c5000781031007107010114100110310f2143c43c0107002401032400590000e030003150081401e0340119061030982d03403250014050341c5a0303c0c0344011240e02c010000c1164860f0403078080d020700000d000304c46c0501d100101442d202c9080805d003c96580c1c101128a1181000d4200070341000350000c1d1590640d20217260100c0c882d00a0f881c42407400541d010220003040c004020007104021201c0a002500c3c050b56051251190024402c8524010f446028101f90080c601150403880c043c2d0091500c0840a04a80d00703103540d8041c07004107024592001d6901f80b00000e4842e40350315001d84200301400044030700204002150302c940b42541d801c1072004021018441e820410b90b610740e103043d0021a40070729103602006e625020549940403414840c450b66003055480f00714002c840c003d075245010103a00a0a11003907018070300401b080054010307110348070b090810300c0208038880010b1144162 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 769744316 1250 769743066 769743083
    0x3020f0f0316090c02120304022b0501020304030305071d0123180f03061003030c050102040b1b060a050930032a0304030c0f0c15020106080601080a021008090f0307 72
    0x43c28031501d0545520030002e400b10f400c040780e0070400c03001060940f5006034051302c91540d84000c04841c265002a00c0303480812074001100d110080220540040d0f00c118840ea40070300031034451010a9840110591a040701242d803903100580c1944121103680c0c0000f241482003400c201100c40405403a40055002c0c01c28102c0010b00c0b000ca401d2040301c248000303d064000304001d01d4140552484504140801810000650215030074003a094054802600d120055076540d414070144000084800341c96001182c0203190002c1c41d10940d0744901e503c00c075241e00103890315045008100360400c20b0b1740901c0c03a400740d2102580ca24070000398040d41c072a44600c0e0441000998500c40382c1803060360380c0020500f50030b08100300000a540100a0705000b5400181d4060300209442c0c241e4407100c240e0049065103101103038202229a05400040c121802c17002034510998a5192042d1030306808080a5003202c408902080e109202d035201c0350f848a132500a0b1898003158241c402d0555008420960759800c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 769745566 1250 769744316 769744319
    0xc06180b0c0f0405010c060e010f0204090f0504200a03060516020f0712080a051e030105040f0b0306070c0f120f080901020a0e0613180501030c080a03050403020f0f0316 74
    0x41030100d410341220441d4811400d1403400381500002d48180d0081c0b40c108a002000c0703004010340b6411a84107001440020f008824104290f00020340091140c144030300d00301a0740ba0342061481c0704541c0120703000341203444000a00302540d2807840940d542e0741e4116100c6040007001c00c2c210321940b8080c50300c100c0380c1c4a074804190402447d01012000101c595000003004009a030003009008442a5100c0706140e00c44450b00c1098540e4064101e1440707001d641d140c0101d44c80381c100d50081d4180c5004540c20841c5441001001c000c403450000815015800b03a000f0902681c02480303000380c1103100f602070b2040941160b1f41c1840030814011407a02042022075210f1400e84c20026041e40003298500071400e0201591008080d400c14040c0c0d1400b8180008101240020800c1d80c0b20107000002c106d20900f0f0400c0340340344000c0c0070900c000e98010058a0022031124000f20700340c1d06050b015560242054110740070041421083d030000d0b0f0b4482c06100300503c05450078003424243c1d441c40c0c81031031804ea = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 769746816 1250 769745566 769745573
    0xc0420040e011a0a0207032306091f11030a0b040608030d02070507061b1b15020c031923011b0e01020615210a0501020403080a0e150301060804030c0618 67
    0x2070b22900c40d0142d00c810078880d41c0d06051740001d10030304070398002e016202c503490005001c441e164910000e498a40c002c82c03041000704400000c900000d2954031a500400c0c101ca512900103c1d0401c012903502c0d8442000440c1000d94140c00054250302c0c001e10000d400303580c1c0c50714245076600400700141900c0d00464444240413060182c140100050309103003209402c2001e0401502c803546034010900d015150415406018551490b0050500701001808403074411b00065900c1c4010842548207114800103135540031600d8400310829035216084400d6407061301650307007440c0e0750010610025175071141803c4031a4800c0c00c52211103904d0352282010704c00d42d240028285000105502010031250a13010001d4480281c610600c011110100038902d00c100340c03041c04c2c1020943c01034503941c00840e0210030f00c080100107110b4441c198842c41c486040ea1028400b2a0000c0340c10890300000610040145a0203a200700b80d20522910700700c2004880c1e55a02d4089541c184000f070041320390f010042041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 769748066 1250 769746816 769746839
    0x62406090906050d230d050c061807061b0203060f0f070903050303060f030111030106090635060402070209390d110403060c1205180c0420040e01 64
    0x1e00101c0380300340000b83c01c06011840003035030720800802078440140520700305407009610399003081500702540c1c1e90840381c2400078410382110140042c07902564000c9046581092000301d0703942d0020014147d031918145c130a540c8204c491152100307403840200200010380d02805801e02c03401c800e0030a900e250400d8001000301d4180204010140120f4800030f20118000105403a0322140032529101600c20000119015125140300c0352401c5e080400085001f0380c003c0709074070545290b5520128800d5441003100c0c8804c000c0d403001c0f0260304040e0f040c044249240d50a5a40c004000744c00941381032255404521a400c4c11509141403c0c1100e1143e18131110700d418200d689198600c00b5140120903039803800d0988a036165401c2c01d982d9a20130241161200803d503002150031920803c000c5070040809012300710ba07200480c3e80d084c0341c000065040c050054005229480300ba0080114511001c1444000e082000d0560500001c0c8041000511000001000034200d940440e07043c40d490b2610103c035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 769749316 1250 769748066 769748069
    0x3010320011d0f03100b03060f010303050f1b060a0c08070203071a1e07080702070b0f18011b06060f090e060a09080f0313030f08011401080406240609 66
    0x128580aa012510030380e0707001041c1c2181e0000b00303003181c00802482c40051440660b4043c081d8140c000d0301e8213444035440603801414011002e400303880c000c3c1c1d14683d900045280901000340072610a200407651442071101a0941043d480307452070810910240d01c070f00d420001c82e05142c5403078503120480140c65000040a40000c9035000850400000303a44000040c00716400c00c119892002d40080c50a09035107450b0004c88902c29102d4000c0c0c20520401860202e04884600c09440707542000103800c807200c1c0c00c0342c50003c000c09625086c065000c4425412070148800c0038108240d1140c1d0708452050342010304040c51040e28000b401a2400c0114140c2c2c1145503c0350250a14008241001d103102080d030603445107000d54001003000862030f08005c680546e01c0346440104ac0401000031090090807914403641c02a102d0503120203110b082202e99072000d0040c00e03014907d0200c2c04640e03501888500d07401034407400c03020903c05640c4568400c1d405a0b0000040c0380703050b41e4410006a90884035400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 769750566 1250 769749316 769749353
    0x20a120203070807080c130605280506030609040201030b03012a080603030901171b0f04061e02100b01050903060a021c2f0909010e0a24050f0a090203090102030103 72
    0x4c4600e4402407540700c0c14004007050290703c810050080c481c00380e500c44030152400a001c01c1e012001e41d0240900d801074401e50403401d83d0a60004a018a401d6094034420720008050305450303503c590046000d403885680c00c0b41c2643d21941484200c0011124164800d91040d9035100c00241400d40200f034107002a1640340241c004004080c03103039900503040c040204080c00c941000e0380323462410300d800b04404203550744521804214440001480c1c001401191030b00e84e1143d00501d407400700314458440d411841e0380560320140a8189170300060300503032078840050611a003003038410404030781442070445000b010f480c0e0001c0c0c03940542c1c40104010300c1642d0130b02c1c820001020007000c100d07a001014001c01d4a00301d40440c1032030460911304101e6a40c030001034289511543d4030024202000e07815601d001185017043d40c00c9009200c410048180c41c221000c020314034514280130301100e0503407000038036080381091402003402402d60000b540201c0b0000c00040e92903145040c28038111030200d00c6071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 769751816 1250 769750566 769750573
    0x1406060a120503030a051b18010e041e0c030207061517030a050301140604090c090311240a05070c032a0e0a050a15060903060b06160609020409020a1202030708 70
    0x140490000004d5a03400b000c0d0040005490301c0c0c060030125404917059140c01120000a8802d00c1d0100000301c0d0080c2c24401e0722082d4079580401c1c20841901d00c0321700c00c1c9079440d600018013020351442e900310123072070922420010300d0000a40c035000c042c0d0706410400c10065154a00c100194020103100c1c9075404100800340d4200041e04800400c0ca202c18407802c0e00410a40d40440802e50320b02c02110300401110b80200241600c0c560007030f090390034901c401c0e10901d4010400716514101f000600c07240341e0000d51100700a0081c0400c100c4c0c190041071400d000c1140a0004d171001071640c4118001541c040c10b24004944900d0a104072140120810503841080b002c0c41000003a580052058000301811404503d540c1c501c200e5200030007070000c01103c0081e00c0307100010640c0e0888150000c0d40e02440301070241001c08824440c3c9481540d1401c0002c598040d0032402080340382d8000c2804034070013000480e03142400d8001071080c0c1004d802000380422a070600b94218a01004580c0007080c0d800081e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 769753066 1250 769751816 769751849
    0x51905030d030e0303151504081b0a060f050d0209090405030c06360a02031204230604060804240c02010b010801240302070b010e1e0906060d0f1406060a 67
    0xf082d202d01000d0103219260306030402824050f51428840a02c0107500c69005440d41d94540f40302e41d45001c0180b4518401c1580784128075182880c941d80c0060700c0345600d45080445100c00100c030a640141e2001072030f19401c0c0304260301691441e4480d4081c500400095031142030908040b03060100244c106a0000240034110b080c14000701c600560101440d0100c4c0c8220180c40c4a060820f8015000254180107135420710840c903400e207014005440044805640880c501048010111901da0429600c01d000748001c000b1140700c3d002e0a41c3c014801c00380c0207003000950141095286900030342c0c144154070f4083c2e030b41c1c10039424410440498002d180c43c825551400220000d82c00585c0d8008400501c054020880c45009804440301198402e05501c4650b07543c003100003079581b090ba1403420007045c0c401d50030000303070b002507140303009400d410b000d855191190010001a5001210b0480389203401c2407400000c80c20f142e603682c0c1034044507800791a0324540081007000c0138026810800303c1102c040078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 769754316 1250 769753066 769753091
    0xf1b0f0b0c070b0a050a091212060f0b0403060e0f0109050303150d0c0603050603031c061e1a1e0a08072007050607050312040c0503011d0a030315051905030d03 70
    0x1c1150400c0c4c085000003200e403180b1010901804c0d981030050000d004507000b401a0070360055800090380040001040310301d0321044052205c1c6a244265051140140401c3c800314040b80e00c12180f900c00041120182d0030100440c6007507c00405040e55950400301c00c120521208100003c001d00c41121000c55020080d0345844109189000300820907958000262090300c0030012a0b043e40000c48650080704014622400949840c3c0161040d80200c1e180390b40303069450101080944949000002c0c1c107400007913804900c1d401215070850303d1002010f2000c0c01007400c0c40140700c074a600365980d012910789540c0c080e00002d000a811141e600080060b40e001c40408100384050791402c90b01c0300d640e038180e402d296155002e0406641104980d100a03c0201302100c0c001c0006c85d101a0000d1000441c2c001071410322807501200e460450f000003225500092099014a52030310302507180480f42d03a114000308418401c1030b41040c102d50616035007400585020450486038003013914003407000c2030b1580c1c0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 769755566 1250 769754316 769754333
    0x90414090a0c17100c0e0a0807080d050a020a1202070306090809040e07080c06130f0609080c04060509070e040603080a02031803061005011d0603161706060a0f1b0f0b0c07 75
    0x154411304065880000000052051050112603000142604039290300ea01045071100d076140f1407000180300b03442c44c4901e810700401c107840c0254250b0300038040c082d020352600c00d880110340195504600a0007c0800014413510a0781081c5014a10f403584034000e1805110848241c104011000d83c40394804014491001840801c2c401e02a01c8507034844500c04859a001c540d9600304180288810b400400d6541c0d114030140100d402040840359262000003d00c021510316010b51600901c0030f4001420081c01482c4004606001034800150349540c0d45403021160030040401005800c0043e200426450285805803038040403800fa0040d800c006803046000c000f54801d40b4103016072050310b000805e034090b0700d079040d000d0058861940d9203002c0c040d00b05407111140d5203402240d40b041c000e02000050842d40d61141c03201034910b52900c501c560341030319951604490382081024213104406009804c41891016903c2051000407580c2e03a85020341c0b5040000340042d06044082c400500490b0160 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 769756816 1250 769755566 769755583
    0x5030a080306120a020a090e0c100c020a09090f060e15090c0a080f0304170718020405090c03070e010e0f040608150106020f2a0607110405010909050a0206090414090a0c17 75
    0x403a4001280e0207403001550038003102c01409d40d1700203a142c084c01e039000d81208203d00880c0c422104220003039214210780c1c04035041c0800280850141382d0201001a0ba40e9112820045003002210003200c40424480340f8107200700c0c1c409180b40c00c01a402042402d000345000d0240442c1405442c0c617140c0400d61035907900651280c0b200c1e50100c0d90104045c1001802020050920300400c010101d022844c090040e51080c0b045034010940c03103001a10301c0c890b0070180c6e8020401565000f1303036400c00d4030044400160071034400f0707880080c890b0304900030b03030f60b51250200900040f0044e10035040f83d042050b1042d2030503448034095400c0484468000310300422400c40040780c4522449250b40b14681d0b00d03002102c81103030a50440030018420042c090340401070b010b1410111814066030f030f01c41801c0401d44040c0c50006010342d000c0501d0100500d4010080c2c07400501c0038100003600b00704200440b072212804c2d81c04040d15008a110031040c0802d142013074015248200c02c0c0c00440c10420b0520b40e490420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 769758066 1250 769756816 769756829
    0x1404140f031213030903050706030506090105180a09140316060e160e0403120609090c24050c0f030a120608010507053108010e010f0522050705030a080306120a020a 72
    0x101d511010140075020001c060741d005000c40305900d8555200ae8010041074403003911680c07228000103514507103940a5407002d014502d5180c038036210420110068680039500321031005a854900404d0071040010740403d0120351780c03c00c103948585c02d000d812102c10800e035002c1034015019062a8034983c180b05c2d000c03641c02c1590b081d02a696410101e80969141410011075400d280001404542c15009412043d010740c18112509507104a0810312000d42ca00504e409102624152042e5020f003000c0c140104c42e510543c0d68902d0314000b2681103500c9001c50502160002040300094241031040c00003800e1844000c200500f07144101034034034003a070130711030010511310307944038014060a0b4413005c034800007c449a0030740341d02e441d046806000d007d8581f40c11036180040207601480301e802524040e0140790313460151100190301c14041c858580d60192a07a01c92588005050344081014947c090302600c280ba8030790600c1c8040200d0221142290b0036168021403100015958000c0c00c80d00704c448 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 769759316 1250 769758066 769758091
    0x5061e0d0609060c0e0f0d030e010f050714150a0e0613020415151412070f05040b03070c0606081c031802132f070f061404140f0312 58
    0x48514159002e4a41c011000307000c0c42c10910030036811a0880c40f80064040c04070340704500e00c8000ea060281c0c00b1400302024000130000d58510003194010303040c45000095601d0104e00d00041034458112601c003c03000e803d0710b51f01c10340c00b4951001a211540e90170038000d4105000501c00240c0035651032401605080c0036450016181c0c0440d51240d006807030b10182a1659549240e4441d04100c5070b00e410640d440100313581142e003c802d189510b0841d0f1110301c5202c01c3c0b10861322085400c070381580c4040814024840f0400002c00c00c0789459014501c12181030742c5500140515190a106860351a031240781c4130350210307103103680000340710148070900c5200c5d140c00203002500348403100707000391a044003940243c0c0c43d4180140f054a160401810004141180300744100501030f220800e00442c01800f01c8801e050100e0000140300c082c10100c01c9000390408a9100c5c1000180c0d0340c4000c0c00c0d2411185182c410900c403030115802e0050b03002d01d00d9044080c1d8100424884803250349100244460103104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 769760566 1250 769759316 769759339
    0x8040b0705090409050a030e0307061d0402040b18010f0e0f040b040f1820010206010b1e0c100501060302031e090a05010e03040602011505060a08061f0e0405061e 71
    0x900c501d065580c2014010001e220758103c1d418956140c041000081e80001ea600000410b07500300040c0b844111500c5a8400e401907580b00707103989003040d130000e4807035020f9001c00000504145100280c000000620242e602d9812001c0c005850813100e4402c401c2440000e540e0700400f40c1d00c00c001d410401d40b003920b000c1018240d02c40041c00070490030440030402450400402e01468101809003022481000511601180e107035500c9940b1480320782503401640400b00520100760300e45c0151404000c1c0c0045100001e54076014418181c200420540080d4003628801240b4902402424014041405d0440c03850502c110254001c01684c0c221510a80d14980440c01258041010308001d5800000030000d000070400d0387c80e140d52003407154a0042d0300340326660082c2c880400c1441c0848000410f040e1500750206419200000c008080d960302c03c0c00e03940501515651154180745511030382c1d44100300d07aa2400204402c480300034024a00a0a800714030502c40e0748c24045280c1c150400321501007094 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 769761816 1250 769760566 769760581
    0x20307020a0506130b0615031b130303080a0f0c0503060f15160b0a0216021e031005160903020319150204030807020a0504150e060105160b070f0f08040b 67
    0x1ca000240070307200c0e0104000c030614000038a40c050030b12070407040c07000d500d0754000c00c184540101c40c8030710142810004500c40e10000d0801c0c2d02031070384a9440900700111a220200c180003650320950216854030200004106c0b01d1290003501c109606040085c06954000100301c0c1c003006081e980181480d141c0100c0710b5554100f10031100c070014000329070b034205c601441e01c50700700c018200300d80142458000c83c1c440c8445009440d0240d1403400c000591840d2502003040c00400d203200003e801180e204404281d86091250308070800d07040c2da0108003800c090782e009901c940754460703950412080b07100c14001660040740c0300c2d56400c0d40c0c2c059004030641d079040034413240041d2580c07024024400240042009100c00c0500300c007071b008580c209130040d80d50090100342c5d00841014080610314880a00c1140b50050710a0381080c010314240e810180c2d442a080080d056502c429586004004204036007658450800051a941c0c5d0ce89014030540c1070320081c001c4280940300408208184000a488 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 769763066 1250 769761816 769761823
    0x190e120313060513060c021911040902040e010c090f03020604050d11030307032d05090d050f01090c030b07171605190512011703070f170c0d080105010206040c060302030702 76
    0x60b03812000410480c20324900e55034520b0310301c060031140701d8184080b030240e1a001145050078801c1c81010540c00468030303902c2403800590384062585c4a40e5030740520015848912a001c5211502000040d004985403006404800b607548100c0c11505a003109000613207881d070503a011070f54262903107001c030305091400005032a20b4a41d201d40503c0007085039014543d100381046d00c40030a0b40c030550403005e1594218900d10004044080110b00c040100d81e038a401d00030f1030088010300034002d448100100d12956402d50307032000c20030307100b622520380240248030810b55007680003203140c185445180104011a62007800003440c1501185810103a2680781c0d018404032004004440b6552107180c20b110b0300074200c2d40200184244c811032510010885020101d1070400381310140b0029410504550345280461f50085421a2029401c64000480b464080701515403d119031018081030041860700a1079210305034442c904540c88002840003146180c541c1c01c003503c1c01c1c2d24004d40d590341c2d0010268074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 769764316 1250 769763066 769763101
    0x2010e0307050d03080606091002030a0f14070f030210060b0d1a010c020112060f0603020703021006052101020f04080705030f01360c0b0c0c0d080f0a12060e190e1203 73
    0x108162515509c0c1d4006901100030200300f0165110643c0040035541c04446842da2100e038800004000c1018201103419121341c001118464811210703511070480c0030009465003039004507407052010541d100006454080c071100300c144000204c10181e2100d000030403ea08000000c1e046c009880380100001d019504220302800c600703035603428a07e036134280c02030096000d1031b029001400381d520719417056003107030140d00100d400c02008805045010304821016241c41e81000714159400c100c00000c455824020300300a00e4058007030180d035403500042c076081122001c11101d069161981059a025024000c070404075806d103c055400160788240d01201c68681c0c0001c3c0210f210800b0018660031110024400000031500307030349406400d4800c0c0200c4144840c0018542d100501140001c0b880d002d001d403d0301c0d080d5190601580c8040841101120744036007059001c05014410041007403401921910680722070b0342c08000080003000703e0b94030740c4007000d80141401c400002244000ba002900c0f030f031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 769765566 1250 769764316 769764319
    0xc0a0b1801050c0706230a020f090d050109171608070201141306021e030f0d021c0501150e100804022b02100206100902160b1302010e0307050d0308060609 68
    0x82c1030080040c0d040d134108042c222001410b10540103004c00c43c00c0001000d01056020b481c43c203884005400c0080d4011072045c04909800b40318040036944c3c0d18840d102158007035070000800000702c1c14030b05910100380760843c1000008020402076a48903c140e2001181c00034032098803100c00d0310049400704000421a01c1021000c210b40c214060010340d014100c4290b60221100401e44061780e80302c1007003c08140b111504241b0061a040d031422004013207003910210010320308090351560b06100c000e02500040500c1d9074200600c640501c0c2091041100c87e94100181c80c001e4034400215042c82c045c4002d42001078200c042021911074013044442e20250171900703040c1214240c40d02401c620884001c0c2d1051407880c6540c0070407070000ca031745801b40700c1c84005c1c1030ba00780c02c055401d800303944051280840140400101408107012400e294060b0300c044040030781c01e181e1400018062a9072148046c030079044540100316984d10061200201a0316092460240e624500010858020081060f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 769766816 1250 769765566 769765571
    0xe1b03190902090f250512101203110c03070b09061e0c0f070902030c03011203021002040f170c062205030a0506010e09011a0d050307050129060c0a0b1801 68
    0x40f00d00d180000c5144604a02101c00300569441e0301180035221a8110a81c04540d04210702c000404003614600d0f440707594040c41c8151240d031150990070101c0745070b0062b0006200c101c8841d100c18410700c00003144030400c0380100303682801d20304910a68400e200c65544070b1400002c601c030401060b0013440c52442400b040c6c0d1a2124500309002c8d131254203007000d002550141d003001041c0d9018504c280e0340900c5074000017600b544c3c205003540d0081b5060711001d90541c461400440a54001400144050645650034400152038450031108440040705041404c7e04075250f00469501d641080d00c0400340c00a601800d980e8102d901800c0c0c03c42070750030840c0c03d030003501c030480d0034004001b401e28121800c1c0b11041d0042c0d51004d005500303d411000d41085a601501e01104241c0b0741303001201d10b5107000350160303440d140c00c6903601c40c00c4940b0213500c044041e20180c170420400f005240c0c00e203050441035501c5482c10310700d00c1489032900d68000c402071882c8011030100f08180c80e01c5114001c9402004000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 769768066 1250 769766816 769766821
    0x91206190c17040305041a130308030709081605040b0d0b0a0b060d1b0e0d1101080a0f0e010506030c010201090b0f0711240112021806011107030308010e1b0319090209 73
    0x30f2a40d80030340191f18002c031142e0742a00f4014080c02c11101e0045100086450450070b640d5000726551014181d8400c1100c0c614002c282454103100112408100e01211204030385407405002c01d89084855803440f0700c0042c284000460070081e81c0980c8482424000a102d2141c0c2000804901038070b100310748010303d482c2c503421702c003101500111103003c001d4071001c0e0550404010031091020718100181400c000c0e0019107401e50140d10b5458100c03a1500003c105844440c0c0030038100c1d000ea0a403403200703030b44074400c0c010f82d81420302500c211100284028800d03038605444c2c0402c4c3d000c0190903000010704040001e0a914880d0717002d8590449181c1c19548252485018484d12000030300c1d03810501ca000d0000004d41d082c0385504995400d9010b4a41403620f11741c181940301036a0002d00080c1403081031040a54a0320702440000c0c0598480d072902002941000e5901040c0f0303000621400b500800c1305038981c43c0b0300140080d00e5204801104902c02d8044100180c0301500d4000b800035000a0b20105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 769769316 1250 769768066 769768073
    0x150302030f0105030607231c0f050a0e150c040503010e160501030b0a0b03040606030209070f0e06030f011a0c01020a0e18041502210705091206190c1704 67
    0x118000d460000038241e56036280c100701600c0d0075017681c00d0f0022468181e440c24081064001d401c20194481c0d0f1081d040c0700c03041c2030b5110840c440e281c03a040710680d08ca00980c554001c0e4881c0310b4010f0f14401c010081640c0398034203d69519941038402019960410000d2114980d8100b21030180070064004d00c42d881c081700041e030b034911601c003803030190340e40720300c404955035210744110808410300611400b082c3d0b2030041c82107800da0020b0401c0c3c032605d403540350100143c0c40b403010340f500514459403050b07240c16079030400030900311300e070310100c1c0c0b040208209101d58a09000591815224000030048100079030010910203417040c81d91060007540041100403100b0b80110000301500d03015111708004440d00c00b40c540e441ea0b01100c00826081808401c5420034407194040c1042540700d05141e048003c2d000c2c0800329175041115048001803000501c8040c0e420b01e10b01c009082a8240024403807420140744440021142c548080107403680c4020740e20740c07184a0001003003e000c44440308026810700c0e0a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 769770566 1250 769769316 769769321
    0x6060c0307060e1c0806030303070809010b04090b011e080a14191b0602030a0206010b030606040f0801020d1d0606040f0f091b06020c33030f040b0c040b090d03091503 73
    0x130011518282c190341e00d500c018080c403020303486814000d000e10b20b160340c2c0740300a446545006c0c0c40c1000c0c6650314850b0a0240d01c13140f240110079402281003440f25032404907070044107100034103481540c0740600340c01c101c0d4000c001030201207030b81d000c2d9500141c0c02e04070b40c54a20b40071a40c03000900d2114115030389010b00905204415038641c1220091171a15120300c41a43d685c440c10104000507400440100036035160400511340040b0014585440c007550f4851184810074250041a683c0c0d42c0001d0300b0a8102d0603100b0380c0e41020401203282003920102c580c5a0300d0746c00c010b1829018507103c94038803e40f180c0302d0303004440c040d203ca06c08100c00101410012113084101c0c511028494454001085080c000552101d150200403c5211910210340700c154901901030341012a08140d003080103030200c03100380614401c814007401c1a4061405050081c1d803500050186400404100002c0c012000303118200c0369111025901240100240e2804644450072944150303d481d0a561503c288180e254 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 769771816 1250 769770566 769770583
    0xc050412080f040b0d0b09040b04020d11060423030c06030705090604030614041101050c0c21152a040902090f090a1d0708060126060a0204081902060306060c0307060e 73
    0x251750030401607204030203101e440c450685001d00003403a06070006006182c0340300250b0005206124074280b040320070002c54400d030002d401c0304004041602140760218104508a83e800400f10010500e9280c844045003540c440501000100300700001d400c4890348800085500566000804105600d242c0700c01440240e4292000c031619140c0070b06501407588610284c80900380f40d03401400008005c0c1081140b58504502800c0d070001500e00400009101841160940801c20380800c034580760400218a0145810b400700100301c0e801410004000040400e4a050360344881c8011780d01c54044000a0f5003254528505034405001d01c204140d4040300c0c0c00400d40c000c00c225100194007110f040c000c0e150700c3c0a000e02146640042e004118070151000028000b41400c03000d0040303170b95020078540c05c0a004490481e005900003a04000c2030208111440181c0030903a81100c03010700c290b00240580c480039042034401c2c0d00c0030070840280c44050048414180d4018004c00919014451954588860707 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 769773066 1250 769771816 769771837
    0x70c1b0503072d03020907030207030e03030c0609101e0e010f0504050d030b0301020405130c1b050a0b0f06010c080d0b190e180a030c030c050d0801090501090c050412080f040b 77
    0x540110070007515626a00d03d0a503540203040c03001030717501e8541c01c034002d421040d01030303082001c0d5241829298906000402d000c6008401800244c90b000845929000100b00705141c0ba600d041c00e4001c03c3c03001c0b203d03401c1c1140c4400d240420f03070941418405000d000c5c1500401e90a40c40c04c1c090004120380082c2000048005440034404100402c0c1090f080340140c2c0b0a00741c1040c4999a0291004000c0d8040880d0100c00c1c00c2c0490302c080030750900b01c21802103070002c6400c0c1c0d0186184009111040341d4184e40f002a00310031102500d07012000808001840f0310040401e5400700c0c0407102c0c9206034000d1000100c0c054500240302c00c0340000c490070b15070305125000541c042140440c0300b40b040c8511502581d003849009207400310241e0b600b2951841011425010001601070300e000051003403102c01d500201d00e6548903040d504000c810780441e101a840003648614100f030100700103800c04203442c200c9001134078403a55119942001041c51150301d13407100001000180200e0f0b541100e0000d8040a0007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 769774316 1250 769773066 769773119
    0xe0d02033f0601020613030207030f020402040e090303060f04022104020111011a10080f0103150612060504051020031b07030c0311010507050f1b030307020a050c0306070c1b050307 79
    0xf106c2c02c44103180b180032000900181c000140901c0815091401844401c0c80070300014034043c0e40b6030018000030f6081e119009036400c000248404d03454052460581e086040b80c0451600810840f0640c544010711904c1d914130902200042c156070280702c46580c0000d1042c0240841b40340181c2c800310406001601c02c0c800c01c0d0144104110728070501e0030f0f5104080c801d0030f0304026400c54881240080e056802c02c01c2c00c03a11420042940f803614580640014484c103800705160a0031314109051003240d4100d51241e618086101220840702c0300440c10312041160801d6480d151301c8414031103855080400d000030b260010700c04007096801800c07120103d00a680c5c0c500158038901d82e02c2e00343c071b0f019100740002410a00206203091400030092044c003442d0b40c0010840414440058119002200c440c0f0150f04829070f41e009000c01440141083d2000314080e046520300350700090f090100c43c59014000ca11a95410035080e00c01040c06800390000900326a01199a016180403090075100d44612a50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 769775566 1250 769774316 769774321
    0x20a0306062c0d0c0f0b0405091609051c0f050309031b060703050a0c050706090504230c090d0b090a030e060a0207030611160807060e0d02033f06010206 67
    0x81140c221982c00011074141e80c4001e001c40308114490b514204155050100d0301c1d00090740604c1400e04000400c114018a51268038201c100480d209004210545500000d841d60320140d90040005081d030714110341092040213a61091911443e030f10200034030042c0560385c081c040c4040000548000e103011000c032000070f202c12140d2000301018109040d0001424001c48000038007810207088843c80e58030b407608103144503890700382c40e00c19190301820215118900034099420b1a00500d48120784018001000c05280c507001c400540004001c0ca000d03c0002c900425a5035407a8608401c050f0072521712000c60800c0040b003520754100320030880200b1208030240800d4200f000581340c450101d60040c00410f07245d500c50078040c0a1450044c180f0100402400a0300c400542c1c070484c04c0d6001d0001075443c1c2d0854134060040321010064038089030321454a41080d56400001c44141c0b6070111003003981b0b08042156402c3c3c210400c01d1265500c00090030162680d405175405500c185003da00720355698 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 769776816 1250 769775566 769775597
    0xe0604051018030f0c03030e011e27080c07170607090f0b09010804060605040c020a0b0702010605211c180506040609031403040b0a090609060806180712020a030606 72
    0x30507610b0001000308000340000c0036214003e501c64604603029050108114003c0003050342110491405c03006000f803a11070260303009007144104e1240000b000c00000c181d40ca91181d0a20300d00080000501c079100000e24011030600a1001400508030300034264900204540b5840d22036100316842e200144551000260101c000303a00389045880c140304281c5030000101c011a200d01c0028400e903806621041e0000c2c4588a900c0360558a071540e502070080c9070198034001070a1000540403d003103a042800034843c1c6d4be03400e50000e20850700f07502c0d000030700c05501c81e00d00d05104081030303002c858803041a252280c06030002e01c2c0058800c1b51032070409190b51501d08100e0240a00d014200004035498010710002e105124007140002004003102e0500380d90b5035500b03540d80d118202c0b4000250205c3d10801226401c03413000c0001c0c1c42d8900740342c041031500c80082600f0000045d59400c00840c43e03804035040d80e0094004280103008028155503074404410701a0103400c0305c1c4901400030700b0000020191 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 769778066 1250 769776816 769776851
    0x7110d080304120c4d210a081921020903251a07030203161505010b0a020712080d110d0c020601180c170a0e06040510 52
    0x540d100d1099800c60b2656100c20700c0c001d0b00011054140103140d160310307000c281e4011060440340311030640310000c2e00c0300c3c0c1d602c402c0744c070008003010448400004420310602d022034514208160f080d5101042c482030001c0c94450610000700e800d20500581100b6414044030b40d0007002005050300400011242020048640c100101012600034000c040e1a00fa070172000d4004008e60080202140c0710002d0301031070803a080300c0400c801000c640e00395500700100310f034203c8404550142c0403407160806160b524007a44902c40d031404480b06801d8525003400b0040f10303510b4030815440a40c003c02466860b2000c1200b03035444080100054440e0310000a120240841c030002040d42c0704038003034140440d0316404006051010800c1c400c001d4284800d2429000c1c5120b00d88a4044503402404c2030351410a400c282c882d4400105c0840343d09040010052640000380b030408003800510240144d51201c2c2034100400d00c04c030100300a03020b09d20500007840b400140c2d00c500b0f01c2009404104070990a03010001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 769779316 1250 769778066 769778089
    0xc030e010809030d0515090714072913030201182303120405070f050f01051206011101020c0c0411040806130317041a07080108030d05041a0403050711 66
    0xa559001105a503501c9584100e41210070241164200309440c5030034400d6480440703420040da0003407001d0441c1481c112000c15003018460801040310541e80003000014800c2d4a40039203103000100510039041c0b40402c1c0b0000281c01c070850071b02542014034003c00c034a031a40783c0c180c0040d801c1960f08004900070001c08405164014201d90f030400000590341c6c0756502d0040000241c0c001070001004540049280500c02c81c03040024112180c10200004128011034000b5801200c05800da4042c81c1d812400700c0702d44544048500100c0d94070000101c4009014505a05603540003158600301c503040000d03012038208089805120500542c070782c440b42e030b005520aa00700c03980300c50042220303100b824408606550103450565a164141041c40b000d8410549007203e80094602c00803c140e90002d0007a03400080514204580394549444d040da46d00400d896108420358a6002c2006c2008420701400e022009904901e02480e25080280c05034011003415524400c25010314281c034078005c0d01020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 769780566 1250 769779316 769779323
    0xe1e0106020307060c020705062a070b04030512090d0303180c0807090f09020d15020f040b040e070f020c04270b01080f030f042303010608010c1812030f05071202100b010c 75
    0xc2c20704041c030b840c0249441c0300e140c08202c00500e2b0510880740c4502440610040d014a0040b40d42d00d5142d8600580b41202c1c800c00d400e030396002441000c1392551110045006540c1500d00071070080386150046000011060340248010000c20001409080c0444c1450440d1a0100c003004103800c181c00304c0040d5480040002d500408140e50000010088000d0f5460300310a038034018100404178039034130a194460f401003168184046020400243e500010360741c488810301d48512100402c0b0b0010750b461618140c07581c442c64560b0b080d45016140400c00c0d110002d00c03032101078911451824403a805020070702502d512801030441d0b281010b10b000080b01c002d80111100589010301d4144810074481810819042d07222503440604890b6030b090080c000600680b500000301425000000f41003c500e002a0b541240b041d050200702c060340d068882e854544d0581000c85080007500c0c0d040311305128004000301900c000151000f8060350024450a00e028000d80c1080000040710054070120390001004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 769781816 1250 769780566 769780579
    0x706031a1c14100603032c01080c160f0f020a05030f03030c0a030f14010509070e0d0602030c070b10212a0b0f12010b0406090e1e0106020307060c020705 67
    0x903000107a11042100b5816424010303181000c07203400e41e04041e90002e41c0140d00042d905085041010900c0c201e20f04010761450346240c141c2101c00010b0526440144070400c0c0101c0404d00114030f10303441040c0242c0315400740780749002003154504021411001c96059000f0118460302046904001504544169900004508540d0303041c895440580c440200441056191042d03046048510300031108588007407200c5000540c186401c0c0281d4170f9000b0309600411030394091042d00ca4461207100345946401c80009030340c5e5a13542c00c01020314030401b540185080d00b03030702c1041203800d0410740a1003980c0d82c0703001105103004944c151148882c540c0074041c01618040d60380c14a62609501010480440c0058010685943e51411021900100c40c0704008410019000501e024600d4555016007840c0da807182c100307424010000c01f03520140c09207450300090346000c100324507010700c075681182509c518441d01a40c1c44043c001c0d12508031803000c680c880e041c104d030460911b001061074419224042d000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 769783066 1250 769781816 769781869
    0x6140a0c0203070813030b2d1003081806070b090c1027050603010f0512030408060403050706140a0b0108101a0f0c191b0b07020d050f0706031a 63
    0x8520b080d600020401c5e20840b1302c4d00c0000000b861100d201c52080c001001c0503500e0303200d0110904010040d411020300d11f9000d100401c401e450201407a50b050369000302c0026207035500c680c0d252032a2070002c40c2d038a030f0042c0041902010041e103a04018401c601000585000814900901681100c0c40075448045140d031603075120340e8035442e40740200c40d8041d40c1e00c01d000c1030745d10800b1401a03030003038001040e0043c668509020070b0804003c092840304d800c5008510340703440d0128850f100c02028000900300000000e20805003e550b0704013124a62403401e04210a04040781d0500c0145410207029000c03a1484c80090140c00a101c0e05004942442d42c0e007800c004030507404160b10b40c1c0400b50984c41800c040c0896812680100308108007680c142503040d1000b407003030810040c2221080941000c0d012029418070000b24484140c2d021582d0503614031034151564074020f428000410004400ca214001d800640c43d58150031510032210303d508103c02d1200c01109014a070079100124030765000c0c01c0f904 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 769784172 1106 769783066 769783073
    0x90f01020601030c06030e030f0408030306040506180f070315090605090c040f050402090f12060106030e0f150a021b03070203010f18140705040906140a0c020307 71
    0x1003800d0b62555848148201d02c60050004040e1215039005280500f00113582c05410120310755038480307485600d040c2c1c0e6034200b1987c0c68811400c00703005c200035080c030040c02d80003101e0010518403996588003091a511601a214608160362200000e6403070f003881c0d19040184c2078202010606e14030341410072100900244c0701d150b481000300300030042541400711040032500d06490150311004c0581c001400030980303544494110800215981d50860080b800c2c6043e1041a2410801e200e1400d200310b695019200c0400015030040c2c1c03000c5860070440b000d199010745010409450201d40c1c1090710312006004110b0302040c2e2020070a50114a000e0140103d98600c0d94000c0010005400c6006100ca00245014003410b44840e61294240c00c24030451003e0b0001410038007180c21503285c0030700140b82c1c03081404801110203010a240006902843e000d400041d4000c2d4213240701502c = true := by decide +kernel

theorem cover : BRFrame.Cov 769604316 769784172 := by
  have h0 := BRFrame.cov_init 769604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 769604316 ≤ n) (h2 : n < 769784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
