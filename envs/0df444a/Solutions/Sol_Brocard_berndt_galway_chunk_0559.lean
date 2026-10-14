-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0559
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:26:21.207958+00:00
-- url     : https://prove2.me/submissions/b21bcc24-bacb-4d57-bd8a-a95d7efdeffb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 100359712 ≤ n < 100539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 100360962 1250 100359712 100359719
    0x80903010f051305010b030c0d060507021606030c02010b06040e0c160b070804050606031c0c0c090603060204030c33110a05071e05060f0702030709020a12060603050f150307 76
    0x46001c0c0034042c140a00b8034040000f118580282180c2c60054918025009a00c140b0340c281e40c0c062400040b079030410700c082650342d56420102e00f04003100b20f130303516489e20709400403c0daa50b042d80400f60f21034a81d0002c0000c40900e004008841c011440b80c00181610038002030149030381c00300905141a9540031001a40030ba5903500091550211205030010354000704100030b1000030020700760007034816030250440b2002081d4500301c40c04040c0308001846094007101c1c0400450040940c010000c00000b0800f65840c0d140c480702a5015210a0701c0718040001c022071514800d8803004aa4a040710740740b0201603040d01c0c1111010990346d464014441100c1c5801001d075014020b00d070003540300744040d2504a0500411102c06104481130084500100344207001036103d11003280c000c004541400f6840740090300c0080e00e002c1c3d5640003842000d0001c2101501c0e160001c00489080d9145241440802e803980000c80880c0c008540e40b2105c412140c0200c2c0304800c2c406500d00700041c0203010b030f5201588 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 100362212 1250 100360962 100360991
    0x120307080d090b010510021b12061005040b0a08060721050a0c08070201020a02071e0305030a0306080c01080f280c050903010b01080405150a060f0803070506101208090301 75
    0x40305160701c03500da48440e00c0d501000100b4100d1801341400310364501c410358030500d000b569020000400f04a11504102c103000c580d81e0442c0301c01801c07130120202e40e01c030b24061000004c02c41e05840345501650030114068120f1804081ca9400e80e84003400603c0e4603514022308686101ca071030001c45115007002040d01030441a8081c0500c40c0c100e80c100414400c1c0320020040004000030060811039106000c0010304d9035010554074210b40b200c0c1192403d082d41c0c0c1a4103021084583d000030070354800010b404150340c0d010b80200d000ca61040040c1c0b010050b11030010344484404940c940051074442c8000b500c41c0e0003d000f10018030202281440701c6019800080c0c1c1100c03003105010000c140c012035240e0740e501d07090051103441c91007840c101c40141016a1401e540d01d81140c03a403140c00010381c0018140c0041f50384448000d1020305440c50084d5612007541780c481d03020f14829a254000d40c40012096841001b00b00100c5940c5e04500c2140040b40e210031403a60004a42241c5c19521748160300881c1c1d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 100363462 1250 100362212 100362217
    0xd0603030302031e010803070b04080f0c06070945020a02210a08010302090c090a0608060118050609040c020102041a1201060f0f050a030b120102031501030504020a0512030708 77
    0x103109890069803030030150b020045480710790824031030b200e5194005002680022003a03542550344159004031648880c508462103004003084c10814980c04030750380d884c8e42c1000540c5d03030194440e0b0b107036000b2140d203400741d500701c01984216100d09030650741218840c41501990b440e40d00010703620803400302010365200300203aa000408500041e48100c2c0402c14040c2843d65030094980c0341c0c807050703152080c500c0001e030025005200292040d003d80002641210040044800f1410020080c0355100d07141c074800303010b001080c2d9402e03001550130620030900c040f03030711032980940c2e20040032542014250000c22020f0f091024860085540070310000a00c001c41c0c0070426295040155403645a500703c041c5565542c3c41680680104088080921403035900081a4818001c0511f00b0aa4902c81c502e81500a0424005a01d030001c20001841e01c1000c810750145002d06a001c130080c0000b00501c1c011419917070241c6d000307076200402071003c214500c4c043c0320f03020b03c110122042e6804c14040b6100c139000354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 100364712 1250 100363462 100363469
    0x6011101050129070b1b0f04060309030e0603040c0b0903070f0b030a0e19020402090f10020a1b0501080109051f03050a05070b04140f060d02070c050901060c0210140d06 74
    0x110004a80500301044064039051511a451258103202c4c0030307103032035038102805007040a0030340385010358189201c00d150840e0005400d205140c0e6580340e0700c920081c014240588240c00280c0b20000789515460484110f0740519081114488103508002240140f0350000082d10380c18400c031940018000ea02086040080041b21310340e5482e4501403000405a03503401c4084405a00100c4e200000001c3c62803000191b2a016a1f0042c0c850005101117288000c40c41c1e8420740c0b00d15050107451809a0025000c0c20b50b500c210507003000c1301c6c800c005800031087c0b24021240400c60150061200360034a0b48130581c802c034110f903c50203c0c0c1c0d03c82c090071080b041c0764100707a4061300b20018200c1800b104021081c0100b80e074900700d9142c1071424407d5441c9080024106201cbd4000c41d6007e203a642ea4101900d00011042000310b598403918604500c0e5010244909030048007400000200e55010300c180380001500900311070019440541c0c101c847e5101106192420501032000c0d10069003284a001e015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 100365962 1250 100364712 100364729
    0x60303030a05060301021b07050f04021201090b031e0109110301050112020112091a0901050906060d080c010b0301060f0e0a200c15010f0303080609160e0d0f0807020a0602061e060111010501 83
    0xa69041105120ac004880120640502d00412000e800c0f6a840e44100741102c13560b040014508045a00081c18001c04050044a1100d110140c0000e840194003c6100f14410f030000c1940040c0e21003031500340c0d2024400c680071310303205441183c0554040c2c11050320b00380c50400001120080c5170b580c610010030340900c00f01141c030905c04100003443c0074440e41c0e8103c070004008120910301400003610300e41e24031800806c40b042c04900010190001d4102c0e2100c02c1c0c2c0100248280ca44401100180c00001d2041d0707c01c9248000100d640703444070380300718041100c01e08100c5c000307a40044030100300b0750b020341441440c610a6121003e5240302203a01203028000f144450800b242c40e60400428000300600010310038080c2d08280a600d031001800744000b06120700700384600c14900000580c1494500710090b2404018074038480c00c04c158207000340709207031003103928503552610740310203d0350f13070300122461103842c0500c1400c5020518039458003075010f101451b04070184581340d0042d6003076880a90041c0b06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 100367212 1250 100365962 100365973
    0x1a0408030a051213020915180c1309050f04030e0616030f1e0e01110106080105040f0c08031c0906060305010c030c020f0309061b0a0c03080406080c03060303030a05060301021b 77
    0x540015100f1964001004038086400000380f0b03000540c880d08082d010000d031400080410055445c0c44141d20001c5155072090000b500d022050000a40c3c8000a401e44114892101041c0012503209580c09040c0e24101d40016039510740d030035544800700b500340c0c0d40d104c4024011a19800740c2041c031031000d248603a80300180405180005060030180041d4024487d00c84803011400c241d002111185044092802245400341140c07040e00502d80c40e00720004a5003003008001c07e10480920b000e800c24410382615034199502c0c10000e44074080c1640410301d92030792034243da54000440d0000c210847c0158800260f079035507541c480d803c451000c069100829254181c0052958061100021442c000005940342401d85800101940701d4100c002e217a005240e40c500a05000c10000cae1810315512942110000380c4032b0501d20543e400500c0b070300700003a100300002188182640309036401164080d0080d8110388641c410b2401400000700150b030599424030840d02100100030440040200c034001500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 100368462 1250 100367212 100367227
    0x2010618020a180302060d091103011409160602072309041a06040b13020705011104030305031807030309051c02040609020c0c031902120a06060323010c091a0408030a05 74
    0xc03e9001e21410a40300060252010009a140e0704111004220000400555402c2c02c0c90700e42418050300406c82c0c4c1561800d000c01c0d66541c0048000b500a0200310221444000100d108505906107030040100503000580c2c01c0240b404a51248013120b84211640001c503a5070314041911742608880c191420510001611a040c8010040b10380001054400344183c61508000c506605840c042482c8407540c00640341c0309000c801e51158403901c41694046994513600e04000b403c83d001a200f502c584c1e103040085c9244503200080c0303a0300300e1b51302d40c9480c034003240303003c0400c111125401405c4da419103585510000580c3c03188181400380c808441d0060320b8003000e00c0001e1503c0d01e21803c8900035400440c00010038502c511210501950450324150a24401c00d0841e04000d1060f0009080504107917001c82040b600c6108100f03181440244212000741c80c071010b0b403e80c1c4175105040045403000e8004d1040088481202d468840c2c0042c1c468505591000c0144c07844d4055015600007800c0424440f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 100369712 1250 100368462 100368467
    0xf02030c0403140a02030d1202040807031109010906030b0601210c0f02010b0d0f0212070905100905061801030b07181706010b030108100b1216030b070518040504020102010618020a 79
    0x79043c100c003e500402c1c1c040d25960200c2c1d51003074802648400d00801420700d6100142603011038006c0c1c402c01098503c56580c80c500718a40380020182d00f44501162000803410390781c40e100d0303542181c3d0000c4030190390342c803040e0041d030304118121302c61440b504006c000844540154012074024140755a40c041561b080d40700d0013401c5a51030300c2c00c0d0b0b110388940d03c0c05202042d40203105081c0540c049991084500e480c164183c0b41c500c055101d4030300c1c182450f003040f03120240030711400200c81200c403092215a4840080000045140418028940c0f4103801030010070400c008050f07010019081c00d05400b030900511460461140d40320981681080c2c4001518400130b21203e40146200700f00d890965042ca5a00b0f030300e9039903040048014075652600c80f4650398441c0b1142440c048514256816541242204400d1105c580020740311112060081520303241f2850466403011041000e081c0340c1e0b50211700300005020b019000b64110340d00c03914041040c1803550000c20040211040050381d40e01c009101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 100370962 1250 100369712 100369733
    0x903060f0b100e091b071104020c1605031903020d0c030905060408100b0a1d06031e030903010501061e0825050a0f02070b040b160b07030b031002040f05090a0f02030c0403 75
    0x100c3c111550754030179103800e840741c0700380e45200e680240311814842c4910041002805002a82686071040002110050707030704c0e05482065031003e031309682e05c040c91190b9010745c420400b00c0050060b40b0201c04070400c00d221300e0010012030f00c46d140c82400e02daa548001415a0019003000704150040c4204a10054451058094030281500c0040c0e03030510703281c1000c500c00c032105d40810001c4100800203030715030340c10b120350108020302c404813207040b12024220035580c0d0824840140250300e02000803c035240a042d1704030000007040b000d0b90b8410300c6001c040f03401c1a405040600c800000381c0001c065040200e402c1c2038a4450b95850755160241e5000c010004c0202d048840709641100d6002e01c03100c00c50b8003c54064420240580d40d0300e091b07801307a819507281c0b1310780090070420410007440219503154204a0404a08404552001040c40b101104a10841c412003052107440b1204100d03d051000d19598030004400340066802c104031070300d034203aa008560035014610001018410001d0082c0c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 100372212 1250 100370962 100370971
    0x201060e0906130302190c030605150a09020a0504080d0c0b0115021203090a0510060f0b0310060806010c1203060e010801150905060f03010f091a04030903060f0b100e09 74
    0x51111003030074002002501c4080c007404000d1038076000100001410700030010030014003403421040d0340c81e185034200342402c0744250000701d8141e410200030401c10258055102c0148800412000c9402d203411190b0300203501282400c418080184400540d05006005021090415450708070645242d07190000d09032105801c084820311203e22200000ba41c0000e01c0c1c031004040e1a0025502d0700d401070103a28108080700010b01e10301c80d40700600020255500070104450201141c0d00143d9102d0050b24450f020031141800e261f03401c00f404001d42c40c80b90407000d8001d071041c100070f0714110342c540340d81c030407905200e06030f0b40842e40341e4108001c034680c0d2428407801030006000801c80008100301c3c495242d4504d03c90500303c1910342000c0780b0b0796624001110b03010a001402000103e44070500040075151400c029507140100d02c201f040c644001800c094411030f45aa200002141075984000080820714103200f5566036a200b000741c1038a45c8040b01c0380c20783c56500c0c0c00010420420810403282c0e0001c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 100373462 1250 100372212 100372229
    0x15051933080c031507080411060c0f070504060b0d0c0302040f03210f0503041202120a1d01030624030f050406050405100b0d0b040203030f030c281209020f0604080c01020106 76
    0x10250b07208012100e80f0315000b42c1d0030714051b0020341b00d0703041681e60500c1119149078004000203004042d54000240345c0340651300d08040e01e480c0382c1d40f10f00b04012105240301c3c01d401c1250402c25002c00b6840ac0e4042d6000d85454200141802c2d2101c6001300108401d81085540e0348100050f203c41a1b00d100e000c1d01c00c0c12552134407103864009060014004e000241c0020061445c2d001440d00300380c0213009402c00b1032081104643c0300c41a2110050130030903c56031403540c001c014801990154403034040c60003520030350546030700000340300503056030004000040c80c1d0401d5500c070394101c00303020345003c0c3c3c50040d8014580407501e070074181002400e1483e95030810360b0340c1e403900b0345254454648081481d9103d820001468055469002281c11803080702c40d203000210340082001042c60104000e80982d07180c2100c41c0c5144078010b00b6080c0584120500c510210300d801d196240c00344101d400612031544080d054030041c1280d03801082540d0400c4d001100ad5401404c0480050f590900c551130080c902e49 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 100374712 1250 100373462 100373473
    0x9080f010614040510090e0714030c060f0c01060306110703180e01060f020307050d17010e070212030405010902030a081b06010e0f04050f0609030715051933080c03 72
    0x39181c001d0301421403200b203000f60f4942c000905c8a99851401d04020f002d040c02c180844917002400d140ca031402d0340503d00300306d04c2104c002c803a1420006040c0c618080042d2015107010baa0242c031380082d0704050102c2a4039901c3d154040009122802221074902c1c0c00300d1440d45449091401820036501c940582c04280740070305c020007480030745440321070444000307040c1544e510b06100c40803811841000d1014005d0b114286066106541c0107064a45003016801d0b42c1080b41d8890310307581142002601c0c440010b030310510300e4680c601441d0b002540c00c2440740780006a40c40c4540e0100e03041c140c0d0a582035442810109510031840d1004090410000135400540700d0340d03050002100405201400c4202403046400001e03007040410010807468030001c800715115803900240080d41e13540108000c0f94a81c00f101e070fa00d004804107018a070f014000c00500c03000458080e800c80300c000c2451081c2c0d119100740100541117079101c03401d4030b42d1400405000140415040402e0549070041500f003543c002da001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 100375962 1250 100374712 100374719
    0x6030203061f1404080703020f090c040306050c0403020409140609010606021504080c0a11040b100206070c0318060c06060803090d062a05030f0106030c05042d030309080f0106 77
    0x20090020311400c51040b500c040703000c0c00c020880c1e4070100265410048000002d000c22910300000e4032000b201e00c05c460220300c02012a05000d200141959241743c01c0000340003c1c1b000401d250003441d03002e050985150301741756032500001c054400c140d6040c0d0b00034290343e243e241d9814080c040503a01000031002800170524140c3d00940e1803110584594010041348085010040d480c1c3c00c40e02c520400300d003100c03403983c200d0510490200c1240c0100c0d119901c1e068080e401d90910f4941c01104507001d030003500a0755176044041e6070005e0703145011410040360b41c150050009900300c150f03001d07104c0d581c1c0c1d0b1040c40c1c0041c0780c030004a80045d00115441d0b801480110016074580d600042324030f5100a000c58034604660801a422281c400113603000c44038075224120013540f04c40990303c114540141078031030380d90740d480950858104513450000100c08110901c2070170340c00070209100d90b0f64090b920080036980c0c1e200880e4540143c108400080e00c4010400255008105088840748007100800140c0d14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 100377212 1250 100375962 100375969
    0x80a020a0b071707020c0112050a110c03040807050a240c051603020f03010207121409040524041103010902090f040606051909050d0204090f0f03120c26060a0321090603020306 77
    0x502c0c10280f08d141e468000084400f100794202c2e1402001011185498800720620380d038507a08540941d0950388500c550001d039a2800e480240c04540c8415551aa00b103458521545540040030052084c00a82142c020010b40d0402c800f0181c407600c4000c0040090940c81041200c41d5003031031680c42a8010701c400e6000c50001705c1c50b000341c08143e0409003c0e1641e59903810303000d40a850903071a800b5181c0f4003000068100c07a070ba00c2134842c8450a14840000044081000311441e0400095001d48148010b11030203e80b0780c000c060390300740144100d00042d134030000a400d640c90354022034001038000c5849160b04080c02c1c0782006030905810054034079400d0130007003104c2c13048204010b4825a1503084e064180449007100303002840c1c01111201c0f4400c40380c14003400601366500e040f00801d18011002c450f0720310074840301c0b50381104011020826000c02a416080700e0015021076030103080e1000000004100700c440001502244820a88031a0100c2c400b510580c10703a880315041c1801001000361903034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 100378462 1250 100377212 100377227
    0x5030d02121210090f0c11010c0c0303111e2203050604031404030501020c0d0207050a0311130e0601031109070c0201120e01060f030c05040509150103080a020a0b071707020c01 77
    0x400d01d080315040c41c0d43d1a05180c04400c1150b00c001500c2d481c2c0035081c4110265501b110312181e51a07200e03e03c042c1764031001a401c907a202000100001e640101c54000030780b00360002030240252803005400c210408103400d140e83c074030302d9001682040006007160a115101c0c801000c14640c2d5421007082032468803995161100104014100608841118101c841c0541a6005186c020000319120a213b41c041641c808400800c08094030540400242038038003203880005807540080070680c0794012406000911120740e108000403520b6041d0240c000404000b00d41c021409240c000102c20160001d005211502078241ca00f00144c1e01042400360760854581c00300ca41400b6000074009041c20202401440b0980158612180240c4004213000000314030005885040b40d00f001a510740c2e88642e07aa5082e407040000071100e21400400c00314100c9005800005003900540d1900005a56040381c00042102d044002c0703001d80541001c010480d001480c0c1c84906400141003100c44500080c0550 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 100379712 1250 100378462 100378477
    0x91e0406020a02010f021909080105240a0503150106120507080f25050a1205070c0201050a03020d02040306020712020f0c1014120f100308160201030216060605030d0212 74
    0xda0000307071030000c0910035807055803100243c000c115110b000080001d03c041442001800c0010141400405ca64906100700c5028190040540b035019280403030071001841d040241903071040b030009000400352030034010000d26400d0400615050b42c14048083c180c4031030208040607141ca041c2c200490650000d0405821640f0300004a00c03554500c80c0c0500394403281030700d03180a40454021034480d2a00709010300902c0589840e070340211003500380b00904a610071140c60001915150101c40554051401080319a00f6072401520b00340d0740901d0a4141e03403050b030040710340540c0041c640051040c20b090300c048142e000d2003d000300002c0318011690b918008403501e407041140f0708088404a00902b0400ca9003c17284989039126082c0b2883c80c0c820000458480c2803101280c80000e00c3d40401c003102200352640565081d0034640a22002c1d500d240ca405401c1b0f0615a080000c0058160b0001014401c80d20a500110b495410b000502d400d01c0e4410000c03c056601015000913590003003401c6e00c084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 100380962 1250 100379712 100379723
    0x905060c1c06030b0a1406030a17040801050114120609150901060306090803070e030d021c140c0a0309050a060c061a06030a050103060c050a05031503030c0f0705091e04 74
    0x44480d440182008041c0090300741c1c11a500c2d04400000300300300710741564030414280b0070800c0300d41c04014404140745001c81c0c4099043d00403070071100000b070703c0c0e4880700c00f003498081005003400c0d00d5298240c02c5070401e8000144103000b030b000e11045c500e005a180b408140950029080d14100b0380340f0345998444064280301c8100c42c40e00083d80074442580110029900640309010b000d080e414042c0c0960300a95600d8001041705c00d1482075400c1c00125004401103940c001c100754000c20002000180c80d5a010fa000c000ca00f080d040300400701c41000d0304645000d0005402c00400c03601c3c01500c43c80c60b5a000030300648001c00304108c4250801c240c405610307000075000c00d49141000310076131805480d00b86039070f0001e40401800000b000a62065058900c42c40081280d81039081c019940fa01810b0324600004100300006003c044e0006e00c00c0142c0c0401408176070410031a00145c900380211b01b01c07481c1440c0c2c04040200f100d450091046908a10f80f0940802ca4500b40c003815426004001d002404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 100382212 1250 100380962 100380967
    0x80601030e0f0a0620030f0f04050307020a08030a0f0201050606161a040309090b0102070509060118030b0a09030206061e011d09010b07110f010f0c080d090b190905060c 74
    0x461042405002c071010700203402c0c2d840e5042c840c41c14074010004400f0448155021a04500301c001c0154101c1e40241500100390300b196075079525400041c10300601c1103400340402c2c400e00340140c54081248014002000145803500001a8001c0c5480484a24034045a0402040c05501d0311680c040300c800014101c4000e1084a81e801e080300750f901d81140001040260304200810302d035000d66440b090350340c02402403003907941900c01260344484500034203038481200008140590b0084100d449200b07030102d0340301136080d6251269000601c04944109038a42c5454102c000c0550610400387c0c01b5500316100340d50340801ca000da02d100c507010104030303042c4410903401740c6100b01c00908502c0a42d100400c0f00002c1d41c0c50f41400081504015400c40fa2a21003d01c1d224492800f5465041120410b944004107070f01d5141c000c48404240030800d84d0b040404014030b88590a40d40a83d90440d8048e141000b51410020070505020105298000001d4504115040044c2c00411440d8200e80d506c0031054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 100383462 1250 100382212 100382231
    0x70c020d080a03020406020706020106050a06110c1003020c010e070f09020f04170717010902010e0f04020c03030a0207031103040609060f0306180b0f0109050f090903090d03020606031c08060103 85
    0x940c0c00c0244603024124050226a606206515030000d2060711210350a90300380703942d101d0044c1e00340c0d040d6001c1d25520010080c42031081354410000d5000060710202190252011640400d20000100c2d1561000a40020b2036100d0b80d1024014100c6507642c200081c04101d1414100c0445801e0500032815910f8000540324122032443c01558050020000c5003039580c0b0128141581c0d5000d54800c10344104001109500c51240603c80c501c0b40175010b0719211603640d0f480003080084140354500d142e0280c0d0030b100080c0c4526080002c3c40c4100801e210050740c860780f6041c06032101045554000040e0320402c800d110140e1300805080480d400c608010314000c1d4241400d401500307241e004a041d401ea00c401c0d4007065a1160005400c00f2004d179402c0c2c129000790001110b90f980140292500404050046078541c00d05141a561100c03401098078200307180300d0005504044c07151002e4005a128070706010305403405121096071895020552060800880006400c61400802084c1810ba46403c42c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 100384712 1250 100383462 100383469
    0x50609100605091215010608190b010804110307090908220302030a0b0601090e0403050a090503010203090705120c0d0503041a07111c14030d0e12090d03030902210105070f08070c02 79
    0x10303048074904800d0891036031140c200407c2d4180485002000c9180c0302410081403403075102c3e84400d8ad0040c0d440050660300d6032901030b400c1d1840b18044d5054420176000281c0c4c40c0d1940b1a00700b00910602006a076041680b0345107190309424211400d09100c05002040180d9000802d12910b81d0b000f5a40c0e140d940d180c40042e500d6a2032980201c11f080c8680080104156202d4001c00d5485100d4668485a0f9204c6e004d060817030004036100022035000304800d110174030345101110007009200b070444203e04000c0005c1441c42c1c0b101c0c03100b11415071004c1810303c13002900781c0c0980d10500340450498107221751a01c0b82604240e070511900c0c001c8039400e011800300303400148011400c5812212003030901d44e04014103540c079480411600e0740245401200008600085280d2204c2c0310f603000300508007880076003000303c01035415408034145a80c81d032213540140c46d036101009030154141041100d48003015045825204010310759020082c003001c1060b9541d8004440540104461030840085081031020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 100385962 1250 100384712 100384723
    0xb09010f080a140414010f050c0a03110c0a0501021b0105040308040807030507021e031207050601030308130c060503040b06040b131806140105010e0d0503030c0a050910030506091006050912 83
    0x280f00c900c00c2c181c00c0100f0310000c0c0c003404c0000510309001f00540e82c41c0a1400d011100c0503510036580b010100000210541310350024100c800074003400914048180d003020b072030b01d1903851003102c2d165004100301803644a8883e20240d04954400240160314056500424415009000602c0904040b5000080c5480381c41642d804580c0686804180100b03012210340702c1100c3d2000750f00c240b140c19400b640c840102400d0340d103000c0c2c0c400b0041c54181d00351f0ba0306036003c40c002000107060460020030803021448803000c00e801031170300d601d0300e07540d0703081508000ea49940700a019a02581c142041c00b00280c1381c0c00b15251102d06400000120103040f02c25007003480e010b8180240c01103003050100c0340050450414281203c200344c8900342c0c0744103d54140f1172032003d4060050595001880022442150000100b54030f006c145803807031422a004000800d4006d03c80c08402c0042d503101c04010841c18800c200300d4001c65004000c0c14030a01e400c0d001015446840c43c20383c0501180e00d000520900c04100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 100387212 1250 100385962 100385981
    0x911070204051f05040e0307060902031203190b040b0f150d06090e0d03051003060b010903020607060e0105070e13020f04050306010e1504090f02090405070e0703020705070b09010f080a 81
    0x424405410048541d11125031a00403c4581102c101c1c400600b518052081c0008007401002942c10060030351140002452540ea060380c0500624080d00e0130240720000840c41602806200b40024078000920011110b4001c40a8092441d103103111a159880600083d013108040340d84d034011003850f030512082402200d4002c030403a4240701b40443d04c0c0c585904112690002081110184130044004034160b40b015118100400352211003440412903582000d00c0194042c10301e0104030b540d9a020a21a0344809802e403022a0b45100e902290b0348203005664008025103400c0c00c81501c020700041c6144810750680703903515400548070340d60300e50100c180c0b401014000d00751001580e44145c440310104040322024490700c45140300c00c641d45064070940c410143c02600031742142a20f0307400c4c404902e4001d0000e8486225840740020a603002d02a1280308808582c0d015840311242d182940c0b6080903a042844600000c0c07201c180ca599002c0225901901d0504c1c080016440f00026400100103841 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 100388462 1250 100387212 100387219
    0x3010b0c0c03030c07141509060a03061d1e01060207061805060a030203040b0109060308070602030c070c081605150904110c03040305030a080c0702030604020603090c09040b0a0e060c030109110702 86
    0x240104007000c000c0f0b10f4100715010840c0640741502d0000c100081200d14105050305007c00340400700084c24940094628255282400617000d501c40500d5940ca407072900045850b511403200b04050400880c40d045503050050303a28241c1541030440280d1108080e000d81300c10010074110300170145e06024800c400800018001c0c43d907901c9040340c010042c3d4000c45090340c00701c0c644800010345c59960700c2400f045a421005480c2807582aaa034071029500c09001e1024196040c0047c80100b1242d041200042499000502004100011584080c5400d510540c400c82c507543c102c403d1007203010110341d0f120300b04807800241c030b00440b448417140303018966010642e80710101d4080104100007008108851040d02c03040b0080d50340105200c0503126a60000390107401410100d0010b04108010316040141074081d1884410240041048410f0031202902c0d0160104140015a0118071030300d02004e0f40080680080d01c0d00c8280e004243c4010301c2166480b6507248034060085102406413482c240d8000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 100389712 1250 100388462 100388467
    0x100f17010801052502070605030720010f061a091519020d0e04060803090907051b010501090b0a060206041509080c0c0f0f0a1e0806090d0e010305070503010b0c0c0303 73
    0x28807205000385412200d920309940c000807001c00c1d00c1c2c81e1101034030784141d155004000007410a041180d485d0009003149082c00290911320b20503446801800c8001c0c0f06000000610803415030782c41c02031301d046d1b91105542000c40090100100c948000701d0b048520309a4481c00c441c1c0804e24084070b984101002c584020f9009206141c42c20743c08100144003640c07554400010070f10800030001121071610585449900820181c491428010315050740882181056030030000725190104503912503030400c0c0943c0e5990801030012103082d201e8005080c10542e20119143c2c100000a9502c060260000d411180c07200000c0c84800d074281c001055080c1c0c0320010300e4498076910141d50752010318501091140340001100081c0341050103014501000040038110990b1070010241d44540018034102c2900150050105583c501040f09500408003640100f414182c2e080000305121500051035040604100a100c030040c3e00109490541e801448820f1b90b91340146551440c24a2600d052034040c04003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 100390962 1250 100389712 100389719
    0x20604050d0b2a0a0e010903020604060203040e0109140f0c0c100606020f010911040b030120070b0903040e150d02030a050d0f050c030403061508030301030f02041a100f1701 76
    0x20002d159000740d06003e040c1c500107602d641201c034046551440c0002c034250030700100c0c3e200c034883c5030032a90741441814580b110b25240c1d000b0801c0c0750310940042c400759000140c10040030b1040f819807801441100400c20604000c2002010848406440405c030910690041078058150344111600c45000030110740c141030f0f40c6068400627052510404004d80135a0026135411030060083c004481e50200e5412840c02c00141080000c20700c0c0c010302c42c1c0644d41c59011000c1c3d580c500001007940075440b0030303441d00c40c112803600e2400c1920003800d403042500140400c00c10304114483d182d81006040101014201142e000704186110300e00c000381d031601c0b50443c10740503c840400d401803034040c00c1c4d8a010b201d1300394810694103071082c01c026003041d0b03004000400101d0050b03409036149079016080c1c0419103030307078420703c134078540007030b00300341c07070240e0692031500440c900f5201e4000d0080c00100000c42d0110580300051140c0d6110403108144406020400c03205071250403025425040e059001d1081c1d41c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 100392212 1250 100390962 100390973
    0x80a2c01030b3714030c01031e11041401050f0f0d090516080105240f040603170d14040b150402040f060c0614010308030a23010305030a03060f21020604050d 69
    0x21210034209021003025008105544001d2500b44d8010014004100e11104000110300038003025204080d809944031381840344040307500441c404003244044082d100c2d070030004c80301030280d0004981d0b8113000d010040c07940445200819200348002d60002c443d1a0f50208081c072000d44540c41d0010300b14010f520701c502000b005a5141d2082d200d60300020400707940c500c0c8a40c0781d401a040e000036100080c540c031038001860008e190f050030850140000c078044e9503a076980161240c0c1800040b05000010072a070001001c640304070400c0b000d5580d20f602950919441e0764031102006006014031107103400c00610300d511160100c400400034840c2c0145400d5440c40f00904c54440f48200711003460401050f01900c0b2440030b00c0c54140c80c0c1200c5001d1441d217820071040d0060080f000d091401031041804d03481844140028503000714000c1c1e025540d10600041c000b001c0b01c0294220410100406205006420003102c0025000380588006044c100181c00000c0041c01241c0c40240e01104640c0401c08108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 100393462 1250 100392212 100392289
    0x70c1505090601060e1509060910090305150403080c0a1404080d091d010b1b240718060509010509041505030d09030506060409060b090103080a2c01030b 67
    0x803441402c0e07400340d98a0b0441118003001000b0190350003d002c0da40d000240020100500c203a100080c80185040c0c460340c00326500410318140240400d480c001c4c04c0042c0071042c004132010b070003000d40720583c0d0310f010750b80a0100701c005400050300100c081009030340b060084c0e400e20169a810320900b03860303da0710b1700c030642c0d40d0f0441da1703803200003405100300003070302d0003100038030340c1c002008541d40300c2ea160700300022a080341e0002114a20100c403180d040b94074914045c4100c0e400441111441d8404100214499075404009002c40003040380a2650760006502e19a504040e80c05d81e1900075994201e1600494080c00f480328507560291902802c410704600c18001201203d00c00e80030344061001d010030540302d0140d80e11015000e60082800602d0918265200c2d074061807041d04001040da0900c0007007407004009800032500424001a00203a01b0340107117481307503014001840780142406005c0c00e0540001400180e6050503111003c0b11a0340d51008401100000040001c801c2d07401468111000c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 100394712 1250 100393462 100393471
    0x10c11030702060d3801030c0302041401080705071506031106070c06050c07082a0604210807140f100603020604050d05210a090506030708040b041e0b0a1805100203070c1505 76
    0xa182c00b43c2c00c4109800ae009540840b5040e0f840407503204500d20054a2108009080404014041006000180b04591444444021803a00065182c03c61400b41404124101820712850082c001140061040715410080e03e0780351802c5030320380a00c135280c1c1d40b038880560003074070340303400b0344889041505444500303440c503c0c40e481005075980301c1c0d6000740103441c480d07401381c600c0180e1080b0503401594901a80034541500c210009032400200d80c4848402d152a03541c030a4407508103800c3c414175400208850011211003400801615182d907001074164407482c4a0a401000c03d2010141400810300038100144c0c500080e001070740c40740141220803640200d00c4000403a200203000319181c20503405891094505449007001340c0c4036a15a11903100c8010001c940d25081690032264140031a40117060f031521a1a00005608040044505443d1003504646590f0101c0d03060030003017080002c503280001042900165280c6685004544c1c00d0148180a000c8880c5c24504040640059005600c80c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 100395962 1250 100394712 100394717
    0xd05040c0b07080d02030601120203070203090a170316050a050706111b0f12100f0f050a0b09040b0709050d1a090a02030709020f040e09010c11030702060d3801 70
    0x14035155050007407140140d50015080342d00603c1070301c124034121350041d600308105050429082c842c070b8411001b603034411208800160400f152040003810310344c816602800b030b400c90500c0c02862205200f039507802169040c4a02050b031842d460300703001007070254010281c0c006065035225921200003820307035003200207186154410031200714610b9038114000e00c83c60130700400a01d4400d00040030466002c01591501d5440e0040443c4542c00303580070b2003a2500382c0031400012170700210660704c41c0200d5000400200d00305081180000321a40d800381d145611503400921400b26484503030044860075041c1d044980c1000c0e103081790500340071161415051f200c40341081c1c01c0d001d5580000503034441121345e80094055015035170a000c44000d80c0c000e000d0074a01400640e00301683c803480a9440203082d0303000c0346580d640d00751154286500540d805d040340b4a1500661802c40c0c0c990103e0764034401c00d4403c0100940c1c0d10030041d8119101c102100c0034000d80e03a8282d621040f448045c079101030442a00501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 100397212 1250 100395962 100395983
    0x140301060f0f020613030f0201020d0c030608100501120b1009050106051213030c150b03031606050903030403080f040311150106020106060f020307140a0f0501060302010e06270f04020d0504 83
    0x1003d10008203e07214403031850003c9000103065030f064400c07400025007182595002c0c45826215010746c0b081e00d80c4131140356008a1503515003403000e400c4c40c1034407a01025580c101380041c880480d00c00c01e562601d9030301400c81601e0746c1c2d17100d49401501d02240c000000c0c850810000040303480e4400041c0c4040d4a07807410412440e11140b074020081d04403c28020082803800c00700c9030100e0116166282e0f42080d18001140320000c1500003421544024032940004510300c81d0b07402406821710525501005140c000e500d1414903841c00313801f6100c024405d034030259030800041c040522500ca1808180385100c11103d250b45030b21100400000f00b4010308005602c1d005000582a1150522484008054001d189441030b175403200341c240354420950350820303c982c113424400100c00c1d448021080d80541c0000502a0442c4001400100320341e01852040b90b0910122030700305200825049621121918181000e0b1030001051000d484001010342c00b600c0411494500c03011900400e02c00c610400d032072507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 100398462 1250 100397212 100397237
    0x801200a090506040f0f0510120f0b0a08030705010c230904060302180f090303070e041d031902060a0219031802041a2d0904030e030706030608010b180c0a140301060f 73
    0x80a000e80e2303001c0002d2074101c0354008094041e448503034110740011010520300110780100d0003903030b51a4885072040c0d00000f808000d010003842065079003000d5140ca044082c10b08403560a010140d01c0c03d02110302e500144810540d681c55201c43c1c02190301038500c0e04450030b0078808900181d001c490513140060004000b601d4500c0c08011207110326031580710004402c00c07101c1800000c3c45203040f6080030010794003c0344128803003000540951100a441d100a80075035160080c10706402610b02000280140070701c0d4854107030010f0802c16100d4629000625507408118108036000c6100e0194200e45402c4151540340307036500c0386c0500500180d03a0003032220120b00e1000040103441022410100c55036010000604e80b2814403030304940079217070614411081000007030801c4143c2c0d01c402c0100303a45a2080051840a0040003040c24048499900d503004001940d904403100070101080300c50000b17980c10820340035031940c0b40c0340c4042000c1c0b59140c0da1202405000f295020541e1004125a1141030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 100399712 1250 100398462 100398469
    0x7082b030903080c07050106030c03060b010f02010c0f140d11040f060e09010311150c0a060b101d060c150727030209060f0409030c0b010801200a090506040f0f05 71
    0x245240d0b0b2650383c085007130b42c1d01201c000311a080701030216415500da04001000c101c44c8012000607501905001032004801c00001d002d0030081040d01d000c0d641403241120a40344c00c41c0051895112504204412250f1045803070480d1103413124a108981c0347c4400c5414440b13145c40a002030726240085004980d8681d003087c0c410030107503044594421320711801400010101c1d80c0d100d01c45803020b0006001d0104440f00d04003a82c028001d040402d5002c03020752000c0c04064041c0900b0800c0581340701d40b0700c2e49692001401244003803203080d488510306000c245151900d5080307950110402082e94450000c080c90094403510540e0040002143e424400c000c1602074240e8140d80b61220200b0304100c0d2469080c001d000304010f16540d404583c802d01c0388400d440b03d0051040851080c0d0f144081d03080c3d01e01c3c4c403070038602d4181c21000d4a68585885070b16080c4031141c0c0040c8520f4817906154030341ca0303403e00031210501c1c260060340d048600494009032403d01000340c181030340e00b40c16000384420348078001d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 100400962 1250 100399712 100399721
    0xa060617030301140a0b03070806040515010519111509010b090903120402031216060c0e03190819050408120906160f05031615020c06010b0c07082b03 66
    0x240031064000304010000b6100340380360303010003441c041c0c03010350500d9555400344460340080340c006000c0703190b0008000302440c0921516600186180740d440031101d400c07000130158002c1400e0700d000544c10382e00000780c460080310341c014060011400c550040b00c107420b08001c5160156512444c660800344500050f00d0b20300860392141000400650800d5605a034001550a02801c16a00360007030001c11031107035074004010300c1c03041c1c500d00c102c0c100c00d2800e1074600700311200ca00b000300400c81e0840c030350461070b070b00030900040c0a120b240d285603192186043c0010540704109603603075100c041031002d64000e600400680308454444c0f003512903170109160302a00c64070139200030507800700080203140e082041812039141d00034010b0004458003059a520903185a001e040350211140e10381e50717040200b00308503200d41c00242d100d101c01d50408800106c150390343c2c00c040c0030b1110300190124648600280c1040060700605059044410084858002d122201075041c030301420480c02540c001074980c0030303005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 100402212 1250 100400962 100400999
    0xa0201050f030406060803031005190e1f05040e070503060705040308070b07110f0c0a06030603020d02040c0c0503280305040c1802041d07030e0f0c0603070306050d03020a0606 77
    0x403014a00741003014142101e41c002031003100c0301907680201044401c0d0800c042e40c4281c01b000240e0540c01d041a0401004108180950013099400903090003000e5214046607000300e103829050000f003000c0305003550300052075003000d80c00500d0401030003000c2d103001039404100c0f0415815a000c1391500700040320786118500000d42560001c1003d0b00000390741007440c80e8400d4591800000a1000c059518103200205480c0d0340664890014051289824900b03007000308414102004403a2035580801c601904540c4060b202c0d60b40c40003204040303400340c0042151142d110f01030720b9882c00c0040002c254550580c4113411103a0319509810f070f1840c005c1c80b035580a02c2d005950400810315201c07168100e41b0102c2e0081e0040e940920001680c80c0603c1c07001340d01e08000c1c0321401100d250080004085a0300300444811070f40c84000104000c490100d00c81080d0002a46c515503640d413102815800340035907070303c0550030104580d000014941e010600410092041c0740c14451035586407038884e0a21003c03007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 100403462 1250 100402212 100402217
    0x141b0a11101508071d0601260103110303090d06050411061204051902010c020f0102030c030d050105030c01030c0f0806190b09130e12091201020f0424050301140d020a08030d0506030a0201 82
    0xf600c0401e46011130b005c2c5901c1081403418425000c15a0940b0541d00742ca40340c4810b84020900062040140c0788a40000e0b00c5010340c004d60030084200c1c00180840310f10b440c06060380c1d544401050501c00c40641e040f01542028040c44da890820607001076800c0b000310380503540d82c0216a02c402e1000b0a0005880c1400d8050f545c12a4440068007002054481750b0010350540c4070810001100c841301340003900e40201002030000b140d6242200f8542440100b060301410140780103808290940c100c280703000700603100e00d0300303034a542c2d680004900b13151000418040d4a5201c0c1400180e1131007090018942102d0542d11040640756070b071300350025950410642e6200f41c0046004000c05924880603001460004105088484416880a0880c1d02c03546880c11402c00005003400503e25680e00302d80c0502c6219008603109000810040c850b02040c0202d000440402881c105950f640310809003106400500e15400940d5070035107107a03264003124100e05118201400541980350100c1d14040b0b003134040c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 100404712 1250 100403462 100403489
    0x120f0103020d060b01030902131a09010803040b0c1216031710090b060d0203010906080d0f1d0f0306090c04060e0906010b0304140105150103141b0a1110150807 70
    0x10783d0703140080c0a4056440e810507a03a0000040035a40d51144030781d0681c0104c0001420222950b40f91840c00064940b0710302490359100100f1031084000112422035918000351078a4461540300740381440036100d04203001c0c0c000850085403e4010892604160307200392a4240407181021140b010900212001c2c50803c1d07440400b00404041354210f5031203d1401803807203140c0404007072207004a070001e03005500200d5444609228402e4100003003415004030f400e201500310084400100030300c90a1400300c80f210b10000210385107880c0c580141d6140c003401026103090f4a00000038075a50380c0c2c036060703c620560810b0800101030000c80411405414110003414480e030030050104840da0020b4021501e0384200c80940701c81c04020b08c1380f075019840c10082d4406091811000400b40c940014402d001c406205003403182c0c048071260680c000104111440385c44110800d030503a250600003d4000c01c0d8090000406510f130f000398403103105a01070b0080c2c85030003525503050580d50070041c001c14100e860b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 100405962 1250 100404712 100404739
    0x11b030912081b03010810290f0d020303070b060103060504061404020a17010b0901030507080621031e0304020a09060501020622020a08011b0219020108250203120f010302 75
    0x204201c661110b80b400d00d18460301140d03080303515254400d0b80321606da504281259144c4101074059400451942e2140e00307142c450040140c1c003141c0610903410721442c11000c49050304e4403169400000c0c550000c090b41d440b5009814510008001124001d000901e40880070940349401d00c14203007915822420f07940318045000c207101c025400160b0080030320071080603a086124a10b0b00c00c1d40038040b400c0540340c403201c6400015040da403002e031a002c2400440b03001c0180f03540b01c20319840301c400c1500039172038001007205120782e055110b440e0348081c0e410000060016880100b80c011405648203458004580c0c1c0c1c1c450035141101c041c0c0c0201e42c0180c1080700800c02014100b1003c4043c004a40b1141508a01680c0015000c8a8a520146a5035159070820164030808070040b000e0003e0317400541300c07203911009028400118084000e041c00a290302040d100c00c6160000d116441d00780b56464010860150044c0d43c0fa00606503602c0d41c54020400500101464140e180c1200d40c09030003202c0342d210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 100407212 1250 100405962 100405967
    0xf030506060403020406230913030f0e030d110c19050105070606090c210b0102060714131202030f011109010c0204020d110919031e170a02011b030912 66
    0x201a00c0207512103014080880941e50b03902c5070400401201030459407040311509000b08410002220314411881c5008204a607401c030309420103003992614244d01d40c45000101543c407403002030200c9816220300040c082d0305e15049180b000514040300100c07500620a05c0400c1b08401e403117011140380c0c80700358104100380d5005102401030035110b40e80100325240c40345042c80c1180c00507081140040d44082002003042a0ba580e07481c1440b1030b900091005c0161200043c1d078034030001d028041082213004803ea400000103054980310a094000d481d1034a1342c40b2415104102e140109a01c0303402040c0315a070b403c040500c42c4400e042094410141808201001904c49000310141660003503020003640c004c404041c80b4940172160b4440d4542e4407400c10a05014215a858403081d2240101d40c0050010546540d100c80c601619032078044050811458400011450003068001103680071074205101d54064000e00d00e00e0741c6401581109410000044096844051010b401520b4a02d04041c0c083e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 100408462 1250 100407212 100407221
    0x10212090106090e010510031e0614180307110913050604050705031e0a03180b0310030c0506130302060304050a0c060c0204050f0103021f021207050709060b0a09090207030c02090708071701060f03 86
    0x10507849e440c665200140c8a5800b6104c0c800030008010920304100f10319030f00081403841820070000c0046003466a50361760b8504d060705090b01d20b8400c0d09400c0000d1182002c030a01c2858483e4840c080e5502e03801c0900e00756a0320315090040034468019080040490601000c1c401d0220509034024120070342c543c0c906440b52524203092411401c82c0070b078040baa031560000214010007000031803003c03413865810300c01d10044454100e05e2050740200800c5400d00701400601c4182c0350100d40d20395130b9480c0c07494180d203828104e11000302412000240010540d800282916040c2d000303880030b01940c3c1e90001001d0605209020007980a01d003035601c3d0030030380c1546013000d400c072803d40101d1f0f000b078040c42d545040c6600310010031525503101403014094050755024001c02010000320807420690121000b500120b0075000340001340354080f4a00c0241442501030071046034029005040a0820030001401f4401c11512503000c00c1c04401d20f80d0044d86104207407812128a50380d1a03201e0110802e0890203070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 100409712 1250 100408462 100408493
    0x140a0305070c021807080106050f0901120e0712060b04020306060d02030402011211071a01080c100c080417160614160b0a090b09030f07080a02010212090106090e01051003 75
    0x1104440d000050319110384504c080502c0d0040c0d041c113413821400003407500c0b105806c000f041140620040103413920325402d03110b42101c2420240f5400d020f00300301b80002d244000180c0700398803805100062216540c1003101e441c6010714020303c001400c000034481a03210540715103030011401c00141100030510b038040c540140c0305241c480310401050340a2804d0f5001d014007107108480000381d10702008140d000e1081040700401901241e5850040c90343d8541103849540c0e8016a002203074030820a1284071909400d55000301c680d51580d03180d0720f11490448009042141c68811105401c500b10440d90400003100c000b9520300f591030f1400c50f41c1c0c50064001c00e08030a0b41a20303003054000083d860300b00c0144190010840000c8420803802c018800c1d90002c0d010310101e030001c04c054505a00a00121603000341c001c8801c0e652034025640407802840358103e000170020b01134080c0413000700190054011202100710a1280558030700720035080703800580b859499101351082c01c00004d54401d4540404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 100410962 1250 100409712 100409717
    0x5010c0807060e070b0d0e0105100b03040c082b0309050a08090d060501080127080d020f120a09030801080c01050715020c0307050105060307120210110f012901140a030507 75
    0x903683c00075591850a40150841c480c0e8030004680e180c110185849881c4543c2c0301c0000a100b141030030302e0418005102406070b800c801c0c1c3e0003c000703814401d510f080c00d402403642c1c1003110464000034102c519210841c43d017103010021540c1008070428445c1c010b0306c091070381010191442429560b648039060f80481809600038902a00c4d86010684034881c49009013803420022a034080b126180402d03901c2000c1252041c0000585900b01060440c0c0980f65103078034203600140d0701c00360341031240d00328018000c5031051881020100510241c0540284104502c00e0301c4c0c003851640c880880396103034a050300e541d5002481c03d010a8001ca0310080c0c0d03030070060503e10401450b091100c940c0506550280e102940c1d40e0391101c00b40312007030600300140b90040c0040d00c100c00c0c00205560000f04086900954841000804203805002e00d10522051004942440003000745a00b120f52a0900a5480c9021725245452140e4501154020060524514447c2040c5850210088130603030040c00090140c004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 100412212 1250 100410962 100410971
    0x14040c0e04020406031d03030106020d0c030309060c0e0108070516060b0a080307030908150f040b280606120207020d080a12050103080414010f12090201050f1305150405010c080706 79
    0x340780c4840c401000540529034000c100f81d1403541180d00c6000b11210300741103540c01040100310345035020480c100445407500d080310010ba43c50904801406540001910551a00d0710b6020010307000240301251003000c1e25105038517600e0b41130076a0030780504118011103401c41110500000c80c164042001480000c1c40311445948885125246406c0004200c000c101c40240c24402c1500401100c6c1d01c4880d102031030030a51074201031400a010002d40010189501000420b4415000c00c0e8024002d00480f280540c0c6650804541c4000e03103018428003011400341c4e04080c1d0446140e008076243c0e01c0d0058010007150781d0300e595502050380000741c80010802140d0000c00708940c140520341c021400792074403e48590400485611103070314988401d040c440b0030f0003043e400c1a003000c00840c000d004540000340e1303503410b400141c600b03210b20401e00d20450400509510344100045d00d85007520300035180c03055040c0070001703569000d00c03581c001d142c0071400e41494040020b08881c010201d242c411600401c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 100413462 1250 100412212 100412237
    0xa03020c0d030b0a0b090a0909020d201207030b0f04030215040305090901080102070b041b05040e030301083307030b0301020c0a02030610050f09040809060c06070f0914040c 76
    0x6041c22544904100001d840b15280300691516502100180c881d80400710300d0002c182c0006141d203030091080243e080c1c0c64107401c02c29980c0c0c2e0804010060340061840000d40494141e40c050140e2100c14184140340724000c7d04400c40d000680390098a038003c02d4940503480d40c440a402500303000704110114841c0e00e03280d1564910000c8080d000300c0c800d441e62516040244204081544142c00c4108580c0c41449400c0206d0b11094009030450b07004040c1d089000c14249035200d07001445e821081d0040d04050001c58034020000041d8126003080c4142d0b001e1701070101c2505040c0d105007102c80e10305030440100c11420126440c5041d0002c146045c0040d01ca0308801c04242a80c0180700310b02c820303400405400003981414420b60707600c00d08001c04030002c242031000092001c50403043c07460107844110b0000b800c1102480458425800c028025901c0b0003004402d00e903141c80c125040000143c1045500103418042c14600342541ca02c1d4034160341240c0d003036042c80700401d50020310008103d01881145c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 100414712 1250 100413462 100413487
    0x4020a12030203090102060117060601030905031312021212030a05090705130905010b0a060c0b04020d0b010f080f03160615090f0c02010e161503090c0609030b0703090b0105060a0302 80
    0x1809081c0c429006035444d18492800a8148074059121010041e003140003250744440220b03100f64048000d0038005420701c0b5500709545507000340840c1c0072070590019004100d030901c9003d0308001e507108680010754450b103948520b454903c81610340484080a002181542141c1d800c001c7c1d001913150120b8804a903180001000d1004542034014516038032074810050040a000340c0c407070140705881d0703682c1192038108010031918081501034807900c601c0f404039003150f0340c84519044403a08191504c6a1713503100c40040b0170030840c621401c00c1600c1140014400f02030f000c801e642c020206440c2e40003c6042c5600d4040142c54480d64460302c03803018002c0842d910311b6900c500038020360800ea00042d190300d41e003806821103100c0c54444030107502c00055004594949030b00301c001c0e07500c0d03820400c004585601c41070780034203042540241258201d50002c40d02581c000c040d1411280aa01c51a084d521100c5c130580486643e41000362200b90484014015810031200034550140030385801440d2040c2c01d00782 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 100415962 1250 100414712 100414739
    0x6071b051c03050609090c0105220605040608070c020d02120109120e0414191d01020d2c061501020a081204112b290a050c07110904020a 60
    0x400c1050800000c07540300140d041c0300351a40720800b507810b0500d80c01c06280b126035802c468030449041040000380805440c0041c80c0b03008145c00d030480180d4100ba282c4201030082d420602130980000c00031000213020601c6200394400c3e254002d824502400803c0d001d010008240305248102076490b80c0c1c00c90005240c0071800c3c000914180c9d40c417000030002078100000d48407007030309ca10b11007904501441420883e00000404c82580303004001002425082c03c0348448100c0113041000d54030218203001031940503080694841d840102080c0c0344c003441104c01d5551074180c0147ca000b0b80c0a100042c0c51040508645607149a050040703804030311003079480202c50352004055000309080d190501c4200b100101c2e0000326450125109280c0b0911070740d003d2030803c40d0135011016192441c8056080c44008019401c903400c1104803582a0031011000d0f40440c2001d46030f4101c0d0500d004000f403444100c4800341c800c40c7e41d12007200082d290840c0100030580340003500690b0711441c3c4500000304405503806 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 100417212 1250 100415962 100415983
    0x2040522030e22051603110f0705070e090601090b040504030e151e1207020303040503220e070206060906040606140f2104050c0907140d06030c06050d110a0206071b05 73
    0x1008500c4e490041440f15403000510342c0c20040c98180005142e90300c520f40241d5002d528520b040e5500c42c021810310601e064826405000d0f102d40903804c1c060301420128403541601e01c016400c1c406881d42c9000c0c00100c400484026002a402c40c0749180320b80f41c14404803109070040112613003803001819903844603452255403041034120004180070308401c51100180e00c0720b81400030703500b03600c0c154850170f0701da1240703403a1308101480500c0224441051590b00d800a401d40410141440ca000c0202955641c01074443ca841403000c000011b41d01d01e45401030100b0b540302569100051840b1498210b0b443e08901c030010102c0c1001c0c400314001da1519051450107c0110408030007904141c14040d082c4860041c8160051148000b04010f03035401c050702c03151003c030072078015039215481c2d0795900003803c164000400001000d100041c080381d1140c080c203c40c004044c01048071040c10b0031044842c0c4605480000907070031500c000740381c080c060391581500f401c01031100300501c00380c0e0340c8443c1403088211 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 100418462 1250 100417212 100417279
    0x150402041508010f1a1c050711010b0306191e0905010203101208030f040f0507080106050310020c0c010c050f010c0903031101050403080a0e19050a02040522030e 71
    0x1040101a00d070b21030071103030041c203018400740d1485080050100394412002c00025142c1400a1441d40700c006500c0511004000d1400821440c2000440104102c502c501300e4891907090035a030700142d01d8081750580c060f0780301c46009004101e044514402a007900101608501031003084401c083d01d41c0d0164a91540c03146000503035a14140400900d10510f58200c8a400b4080401c3d42001445983c1100e41081801c1201c0002d42c0d85c2d403800448100fa4044021324038094031a000a4400054115509443c421002d48021240d0b5aa10004a0041c15007000345c50f07004441d191055409800d1400007140640142e0f4150b85080c40464217490704010f0301c100144503414208107241c0e019403003980d0141207600a00c42c074103054030b001301201c03c00b91401e02e42c165988054005030004008039820101070300e107000401c100c2360800d261103504140c1c0903406581081d00140151400141d0342105040400410180c4a100e4904890a5484107441904421418280811020640c2241c3d800b00c1105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 100419712 1250 100418462 100418489
    0x30403030801080a030210050a060302130506010e01020c0a030f03140a110717030304030f1e08011404050126070b030903090406080c18040812160914060901050315040204 75
    0x500d002000d01005a1025403150400c41034500000d038082240030035504000c20210322a11071090410040040d079100039413010088100300700220260300a46e115210036220380090034a5140103a07103c504000049500c440d00340018800944c43e0320020704107074041c0c174007450030741d40306a04c80080354820003510001c100440320f10282010b0820211000c0c0005036010349036030781a40300d2140c3d01c3c0405480200ae0105100d080016039100d601e81c4208002c0324250003100c0c0058280241441d0000e0140960703154152401149074103003405094101c0c0c001044060808540d440a40d039001d40c0b00040d40c645000e19140040c4500c00500614052240d000c06560b480406008110449017198440e80d03003a046849402d000359101440c2041da10070401d00039100d0b945500c1d14920b03c0c0b0070b0740c00d08000255150240581d04d103019944180c0e0b03440c65100d030410252600d8014804004601040707038000404c024440065114502958000b59496a84c52a80d00c55000107030607600290016080901c0c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 100420962 1250 100419712 100419719
    0x3010807081912020f191505040c0506250309050f0a14060a020109080705240f16120501030305031608010e0604020912030d0f0b060c0d0f110a050304 66
    0x51200e08001c1206000400d48884120000c003015069142e000e88500355100c8500d81e418002d02c101c0c15903d03500d005841a60104201ca000c454060500c01d4401c8240044215100b08480c0f14090169811040c00300d8958a4442040392075030100d8039840c44c900080c14a000c0440044c1c4c0040040b500c03a403204441941400180a00303508a040500e11074103102d0810841c010001402560b0a2000d07106580d03142c4205405038058000b80c03000501c52030f00000d0f40d001340305e00400c10b92111300e1445001800481c2c0f0706d00a00c403070702050b1030700d005444d410304c0400c01c1c0034542c81e0107060f4001d45041290744194000c10020032280c003648183e003c40d40000c20003000440444009180c10401c0c104080740d5410040c3c4407022090060165000702c0d8002031440590741d07440300081540a805046aaa84800c800540094410348082d1280c4909001071009246404403d5900544241c0c000784044480b1020486000c0042400a03043c040d190710102c0b003003141030042c000d81350300030401507a5840c603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 100422212 1250 100420962 100420979
    0x60b0f040b07021924031802040b030f07030809091014090a0f050a1a030f0a12030e0d020a0318050d0201080a0b03030406020318010c050307120203040504050a0e0c0102210c0a0602030c0301 83
    0x19170104c52401c0500d05040340501a241c504200e28007134040d10001400ea110001183c500403090807250302030310448200004020b929402040c1a000989003d0361035200e050084146d140580100420241d4400700152142810034416a2146151102198080b01c040011044881c02e07a2000030850b00d0707800e17003121032a414000700b1141ca010340c010503040d1052200746440d2485034500428441c03290b03078100b403024800c0d00f01c068201d84a900b51101c900d1304a1000c0d41c0e9244078a0f085000c1400d10031a001211100e11000c0e0494002030b02d041c03142c03c11a0700440301004014240d20000d550340120359444e8808101402c040d2040c0c1e0005c6944000c06c0181c580a041c10300b0015040045003041c5074009a400b10644a035158040d50381c1c0c0c1c0d107070364580c4164110b000d035402c282e400516140070415440100c0d000a00a00e4009051304d40c2d6030401d500490711050000182c402c3d00350110f4070070251050a1000f004017034207200c10f0700c010a100e0381e074400c185ea009640c401c00d02803000c00140150703074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 100423462 1250 100422212 100422269
    0x20d06090b041409070614090301022b050412050c10060803040e0f1005010f17070504090c0212090f060403020303180a06091508220c09060b0f040b070219 68
    0x10320200300b03d800c0c0d18003072a00a58a100d64000c2404216003045000c281510081c142c81291000400030764407400124240720b030301c0000350107107408400750710603400480003140b041c0d600807a000032508442540c0d40ca1b0580e2183c0c0214608005413240615010a6002034031a61010740414000f840d6120320f8465411000c0c403000d000c0120700e540320410b000c5104c1c91000c001c0201c2e4002e080c0301c0c07540c01110400759003071101c40c180c1d2a01c0703c20040c100080550b004004205854003080c040112900848040341d0717400e8220b0000c000110100a1404645070000e80c0034150071004180514180e225808241150020b0103151440c070042e0b041d0041c2d41c505818000052300140c980b46103064905040100507202500402d000e010b20341c1301050358a288450100503200944c0b84140007122541b42c41c584001c401e1040310b03030b56031030144003195103082c4c90100e608088442054038101420581aa441d6034050103003282d1001d10440690f1280114031040002003200350360804064840d0401c010509 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 100424712 1250 100423462 100423481
    0x301050411150903030a230d1407020120130f0e01141507080d060b030405060412090503100f06050d080406020709052e0812130609030206030f0604020d06090b04 71
    0x182c506020140c041d4600106070b03141c0d005103103041e00da40300d039000e11101980d0780f49481c0d1040b20f800003100c2c003054405800800840c5001c44800b1700c1035845450803800c0382d0004804440042d403044441701c1c01c3c0c081b48041d2620081c286155500985c0d54407081d62110055070011203458130b031b600108401c008140140b00c407040203981452088000c8a154400b43c80350301c10007884103802149044242441d81c0c0108080e0025041d074075a28206420700c00d81d10101141c00311000e000407840360803030034418440c00f421904003400800e03c506008003803501030011720324202c1c031865913094009120f66682209100c0f080c0103820707881da15418175000906114023900803950b0981020b003031180030301044d0b6005031040c982840403c0d42d505c980c80004155091940301d0380241c803076600880c030000c074a0402400c900d1340c401d404e600c42e03650303a00098494070828840a50b10960500005544503069100282d119070b00410052520b10141c0700f00701103c04942100d00f89940d24658413001d03050621415009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 100425962 1250 100424712 100424749
    0x6090902030d18211e06110f04030303050901020705070b1201090605010905060a0908060c04081509150406090506102310030b0102070315020c100212040f03020307020301050411 78
    0x5108a190520700200e00504c60a050700c10070300c0b01c02caa0641c8050b10b8480984e80300040020201d884040642d03481030b41e40080d20310f9850280b0012441403d43c1c2111101c0c0c01b010320345c0c2e050a186407010707002080c0050000f287e0355003c110070f0001542c00d100141c050012129001c1c2c9030b0a40d1040415190780c141c00802e24146091001e000c0346ea0819000710881d1800c9801617983d84046070300b20760300c0d9215440004580305000600000c0a0114068001d84a42000300c881810100c4240d02000300e00f41c5488240b600b161a80d0203d203260449615401801020b001c01c81d061a50358503464010102c90030440500d54900621146040341c91412024520109005101c41ca0100240000305400340c060149941c1d10180203590b4001c0c81044001c58004e40c01c81540402e0f002c00002075404440100a14056804801041003551007a01d005640b0b1400c1c1c0d0b620f07a52a640c2d46010000c1403c001d9040d0b02c400d021290040c1d03024042c0c81d203d40c2c07044080404110924041c408455840342c050b100c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 100427212 1250 100425962 100425977
    0xf080106090e0402010c0506010b040611070312180b04060e010806040b01020c060307030b12030703030c080c0706020702010309060203100305070f03021807050412050615040515041e06090902030d 86
    0x1006911080440030b40d01000c07480329003500e4500c01a07404004110000300a400340d5000041c1180c0b0220141c411a80c00d43c440c803084100c40c1402a840380003d000090000d1030480412080e144a084503480c242c881940204030a40c95009002c5590030a82c0505c00180c00d42039003c660356482054a60044429603040c010b403c90f40300080d484010206943e0b008140101c0040c40d058401c1d0040d410220000e0407003c1030115083d020390302c1e9408200c003a0042810b100900d0502d510071003513140700e10315106015007032114559510020b0b5100c0c0b04264101501c45103002c0c0130035898401540030b540075140b40c881d481d15600d000c0341810241d0b4030180c09041520b10400258886d1401d042c00aa4540c00c40720b103560301c0d14001d840d14050354009900a41030101000100303d400038a440c0105864449101103141d030340d041006481048400b2241c80ba046c1c000703500f06040642090807542040d101300c044004105c0f40540c200e070880d9101d440c45d0358a0340092025818141f060741c0800019190545 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 100428462 1250 100427212 100427219
    0x50d15180506130c0203191211040e15030a03140918090c0a06020a0303050a060b12041e020d0b13240506060901020a020909030d0f0209030d0c0201092607030609030f0801 75
    0x3520380c0914007c000c1303511100e0415000c0b030392047c8203503c4103e104000c200309850300300f030b400240c9404c02d01410421503070840105545140c0700001180c3c50000400400e4149055070b07089641a13500060741c8410302003070040140035581c902044403c440401c403184403c0c50540388580c9060340c07015002c1d02480c4940d0060108550102d181c80c0c000381c150501080301d88400d210b800040286074403440903400b010030303960a461a4500c5560003030303000d9450707200c0b64140c40d10001c4a078400a03400a520000c04805e8200050221003203541c05510403c03e0007a04000d40c40d41410105025842302c1041101c241551180001d80324890700010182e0380340382082d0349403002030741c1c403800414007900c20013800e00001c5405804000b00c0d0705080840500b440345100707080503180690028940d0034420f02032a001c500d41e40b031248540c105901d40594070070318610b00c0d084503020700d80801224545072001e01b614030141e0603001c204440c0111b100c1c1400180d4001c441c2801000c042803902400100b20a000040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 100429712 1250 100428462 100428467
    0xd050c19050c0f0319060209010f020d08010e0403020f06010311120303040218100b18011d010c03030b0a050d0b100b1305061c0504050c0f03070303050d15180506130c 73
    0x4080c1c0801c00d4904484076000a00040d00d0008100c100e080d0345d001003001c0000700003054001d480440340a0301d4038256030b414440300740d031251820a44c9100240c04000100100480b40482d02c1d00180207005840c2070a40c1c0115060a060090300309460210041d00c0300420703414484103015a00c500c03c0c020390b0a60a1660000e1410074080340304d980d009031007001107800c1c5840c01090400500010302403544d41c2c02e030101c4980b204910748001d43c0c082040078004203000c81d900ea45014100c03005940d03c501943e0f290780d069004000080359190446a5504080327001e88841d1381c00c801003800b07411548520314191110718410320310703504251043c1c4000e010080392130300070744620000d492003121000c1d210511840c083d50325441e030107170080d0722504120502061242c040344140c1510380513105115030899502c1496501c2d1001d10008000810800c580c10080c0d405a01111100212400400907107546050ba443c50040840031000541d580c2e1061180360b01e005116040c5d0402c1c1d0344028041c00441a801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 100430962 1250 100429712 100429723
    0x414120f04120c050604061706010c05060402240c030304060e07030503040902070303021e030a0509030f09150c12030a06090c08010311040f061d090a020d020d050f0d050c1905 77
    0x2031442c0240004000d1040201d90082000507101c040c08a94a07180d45400042203660364014125104040070040307042944511b200040d1250030000138086625551309000b2002c945150240303492071a0311400b18191f0b4918024100c40152000454a07403c1c24284001201c2030f2400c0c0000303d40c06820104001400807058404842403601c006803142c2d45418194084e1080500300503a10759a50f04641000401c02d0213103015a4100e40200017a80e5502d42c610f540f44160000d5801208061003000f01c0761820391b5511508911082100703060000c0080410b2600d100e03510740d204407020200801203108810722400008020805041c4900c2c0003a0340d02500309071060101a1071030f04042003074a615181c54001c2c820031110703c0130402c0056607400155920022188030048061000400320b00d04c042e000030040c1c250b03070f00245030030311404a90b030030454903054851040b03c860045031400114403030184000076500a032500d60316030f2900b5032180c160800440c00c0075600e00001100300e150114000184 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 100432212 1250 100430962 100430969
    0xf150f0103030503070221070516060806120a0609050a0302160303122403080d0c170a05070c06090302010c0e10080f0c0c0105040809040b091909020a0302090414120f04 74
    0x2c150341e583c5c0340c0f09812400c20721503182409148854440e84c600d003a100b4002010224054029144d4401c0f5402d18020030b0703005881100700140c541800704106150140303010b0b101200f194101c0e102001030344d9a01c019a54403401c00d59850b00400b50705003d06406100040450509540610313901c2d00710307980a00903592041140800d036a407010b01c5030780e50800c903048030b01c03c0d2400c8000c4c51300c3c00c1d601e2510f20456030104204801c21030514000424460250700740d0a2451668008010140c1e03030744181100030440144038004108107c803482010a1444c031801030424047e070700114128000b503038040c2600102c0c0031054010400030b021941300c1a442214641c12045842d0940c2aa1300e9184110140380610a04002654070302401d100c00c01c44948020b01480a05403001c0c030840020200304401c186086540d4400384c400c0010203072000c5181da128070b41e06440200580c4481d9100d401040344650300304c030b040382d509038108041c0303c1c01642006142040200b502920b8900303c49420746030124003c0b8070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 100433462 1250 100432212 100432217
    0x90c05071e030e0904140c030106140d050a1502070b0726071e0801140d030207060804030c060c0305060906094f12080106080103081e0c0f150f010303 66
    0x10034180c105480784040408100c001490031503107003402c0c140880c81c0414006c103203155205e4440d010a107410180540412100c03410403814906581c1410312903c020440300031651030062480c0d04001496218080f0618500c0c0400140c48020600d85a800350030054013900500500090170242d104460000030180b6aa244010f081034a60450940b21410401d4001c01750500e03003481c02002c10f0340084a54122030100b4540594510420148003044000e00c3c0080e005800c80071050005500400e10030741c000c1c2c440c2c50000110308250b107a1070200c8603d071200c1030010f51640305103c0c042c9404c4081c540c01071001c031200c2c070703440c01e02da600040107080003c403d0713003200e2440143d0b42152590011220268002c0340410900345c1403410120130b02010070808441c1040d03e5074150503c14070401125044c2e43c0280c40c0c80c1c81ea43d085845d03600709504a00180c082d00d5115400d000708509081d80a0101450701c40000c00103002050700316403c0c01d14032001e040c00310303190504005494101c050410f0440b81c060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 100434712 1250 100433462 100433513
    0x1a061804060b180108010e0601020d1d030a0602090324011802090901060206091204031e050a020409080a0e030604020d02040b0a0305060103080405040c020d08160522090c0507 77
    0x810041c00d2668429004a00003107010b400d8090b90800041000c0d2090ba5112040d0b82c9a0394480360452040d81c901d40168400b4568110540c0500701d0240204812804e811a810a20740001c1c9007a00054003165891380100b114051418100b155000f00c4495200e81076048001004c0070354a03100500c101c0d811403858010380c540151569040361550340d0080c1010401d580c4840001c0d40c2d5802c00c0d01c011105106540d04800c05a40f0417044e1000d0340c0d40000c0840041041a59500c00540221000c0e00d01e80203403c04a001070380c840c450044518400d20f03c05444540e06080982440039009050b4000c3e08a0750400005a84882c07030031103610780c1201c00140a20104000ca04032000a81008045115010011013408091000351045501c1154140840011020101e0322502003942c0e200114444a01203909001c20443c00c8104c500d0503c0c1c175a0070040500899840300b41890a51710544101300f90501100c0418003c4444865160074058035200c95559501513207a01c80c1c100c290184242c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 100435962 1250 100434712 100434757
    0x30c040c0c0605102904030b040c09090b0106080c0f03010504091e060f0515011d041b080a0e0c030a03030203090a0803070f0801090608071a040f030c091a06 69
    0x761840d07001080e00940c00300564075003094400c42621850244d000c866188025111403084400418100034851500c030600f803601e5652034031070030100540220341c0341f90110030115204205214869143e40610300b0303044254908070014041c8a005405902e200608000700050f13403a090701103034112001a030300000e4100311810602e2081440c04d4007007000c251030501c56024044241c0050303031020f08446080100344c6a44804d00041014501041c1c00b0840342d41610f03448100070511583e82840180c000b00300d2085062107100020210140000400c440340c0a011002c0510701c41c00c801c0401c000c000f064442c0310f005c006580c03080d0303a160040c109500000000c1100000340150000c05a01c031001036201d05095401800540042c03c1010000b604d681c0006000e00e128003030007040341c4440018250460030140904414960100b0003c51000208400543c9010064041d40218005d1030400e55180c106055a400c1e90200d00010101e642049071400f441c1c2d90345000ca894180660b01da000d0034500c2c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 100437212 1250 100435962 100435967
    0x315080a08131703040603060621090201030b09070c050705030106030c0b0d0b090406020d050604200f07050f0d020607020606060f0c010b040501170705030a11040506011107090c0914030c040c 84
    0x4070740c1c0003c0384807072201c844510942d0000010384140d40890700c0901101e500c42c0c03000c842001000d100540f0800703459000004481003a0710400c042e038010301d40400c8800c0c4041c00f0942c0158203444c0600000c15203803c990034440240554005420114004c1c041d0520b1074851400c400100c0c01034000700b072000140e241124503a036000708403100010b030a10085151504215000b90422941c034040107040200141032441d01d4482c0030500e01c0c0c01c808422582a2062080c001038000403d02103074103a041104401040040150215000540000b4000f0742e4a4500080c1801005044081594410410f1203003c0e6501826030b0142600040500e4550301d0311406070f0f014200a003c2035400c98946000460500b03400d980007803012030203604030f502190b0780d1702c00d040c0c2d156204c480181076001000c8031422140380039089590420014503010240007451090030381000c400f94408110306554000c10b06038aa08824050002d11078a501b000c1c1ca5503944010949954280d62500e200d5071340c3d044680c03003860 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 100438462 1250 100437212 100437247
    0x1172b050c0105040501141303090b090a0302030609030c0115031106070609080a0e01090f06050f03040f0b0a09021e090f190207030e0a09061a0c010b06030411010315080a08 76
    0x6968003d01072810603040281c000e10800c2e80048214003038400080354028070f00340d40481703650302da07640310442c91420300349240c640c000c045150ba010288190010140e0b074100295406a09440e01865540348100d1807a42101c101000c800b00290f0301840400102c0c0804070b0000700914292100d550311541d52030000010b11040380b00038003406010400382d0380c0c180e000311012003d04007a2120302d04240c88501444165895100e20400683c041003102e50800070b0601440c0c0003841508880d100d001c1b207031346215800354110b174401101581c85000c2019850092607003021440400050761200c0c8926010649907040205415164001900802c2451100c5050400b928810100c215128261850300814600180c103184d4031807103500602140c080b04501c562801c4455100c555464000c50400961240d08141364140c1c0555807370083c00800c2d200c240c020362003640f1074100300e0b41280e05c0200140840300c031018120032403c0d100009000805000034413641e16034010684a4980503059071032905030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 100439712 1250 100438462 100438477
    0x6040213030f0b0c18130905010c080709050d03080402041e0614011103040807150e030d03140a05040206090d21020307030f11070303030203070314010b0301172b05 72
    0x10340414000000c1c071085180c1c441d020340c414030341c40c0c00d103850340081140c40e0700904107800e204031012400d2150b18642548205003013010b401e8003181118560301e40a085403900d900b0381d00811400000c0000041e0703c00c6000d005481c007207600c6211014036840050038040f004000030b025075a164030503494440000411017402c1d461581c18000a40c440c3c288030064451490420302107041c01d2061724a049010040e90261560000108440740c03030700b00b8a50035807500c0c243d450306101c0c49480c880c240f40c82c00d20291000001d5034030f01241503901a80c0b02030030001d005000c0f0850924010a00c00103940b003108523181d5880444a5540c01200350514890300e07000c130701ca030075050325100605050301500440500301190003038036101c0e680c2c06191020380300c100070140103201d2508900c0003800003e00aa01440d0000c04901e000a403079810141d240e02118000e800134000000e010004211507aa400400145602e0190280000050404910600283d10b1511742003e4200c040800d01b40c620034016188003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 100440962 1250 100439712 100439737
    0x207120305070221100c05190507020613060305011505070203071a0f12040326040201030504030e06072a050d0b040609050a0b0403030b10020604150f0f0609050703060815060402 78
    0xc900142401329500d4440b40c1c00350110720708050106001a000c5c4d420741c2c1c5104101d03681c42140c200d009408075915030007403800300c2e07100300c080c00030302c01540c0013005035400340400781c4000681b0350416080c10002d0030103103110410807a0400c003c20040c1c4000c20088202d440d903072151040b0390005c03070304440240a66500b1000755a8080b074580e480c4d150741181540154080c2d10703040c1c05031100704440234207603180000140000507840089001544280d03c46640940a8a0000c10424500300041c440da4003552064031021088040d640004600c1d031170000090800d00304076007a0134904008038000107086403020b40642080b01c00a814000e0315040440340c0381e0b000c0e041d1002468280303440c4507590790030345054000900c0d020621505091050b203118215005030000c040c01c0c0d5442d6118000e41c048a1568120306456078814000c0940d1790017030080804036094041410f0341849807503011154014030303800400d418400200309006001c01d40c901c517000c070804d0a6010b541c4040118020340300c3c582c0e45046 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 100442212 1250 100440962 100441009
    0x60a0e010e1f020a1e0f0b060307090c050903060a02180d051603140f190209070c020a0605070317060105090607030c0b040f0201030b0910060c050a2009010602071203050702 76
    0x4110f0340031500c0404184502034003a05c99013180c541d00100c10071140002c080b4001c4d03c0901c40031590300b90015030b212030002c1c00c81e01000d4036250010191418961900041480801c1100e081c4c9000c0c0401a03100d481c2d4442141081c80b4803070303d600d10802200c9214003c40144039800700b444014080018550400d2542a0107141e403403a141d0b0b000400326907107507810301551803408030740c060204129103090074203415a814400a41c0802c05134520240441061240403890039005840c0c5070f84000041213541c5a031900c03101d02e41800b4012101d00080d40595000340317000c018150380c04c2070030782d07402c05c0082d02c449440b1541490166542002c0350406049609040e04100c01c01403594010202d00f4400c0e68148140c4841d034081c804074100c2620b07601c01803100c0c0c840078010144101503e200c503601802c100e4074040040c2c1c88108a9040661200c00d000001c1400320307071503042000102c2e004101500c000e21490340b4101d020318280c8041c0030b00604010000407400207654450074072507914000350701d03140c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 100443462 1250 100442212 100442269
    0x2040f06080610050a0e060f0903150603010b180c0309030c0f2112011e090e0a0606050612010b0a050408150105040c050708030f0604020f0c1506060a0e010e 69
    0xd01044045602ca0700c240045059070400b1031049003030320380d010100d440ba5064142403c080004542141403048201c0c0009e000c54512550b00b00402682c156441134004140c0c10f1000926003910022065540541d008240307052101d5801c00c201d0390b01000803114641c40f40c07034180b1030034158803a6000300c600c6031062880540260b0004946a10b002c0e10704130300000c0c2008960705240c400c0c0554001101044c1000c001003040750480101610303400300244101c4c1b00b254540c9e10f00c00c00c48481d000345d003941c0c3d032000520710704210303003481038801074001190224181845200d80881c0b1201c1409410168500800c1c1c2004560041c410b075406452100705503221418a003080c0c0d04c8451091040301d125500709217403034442d45d000302c0403640c2c000c0c0c111944030302d90340d13400c802c4400400c0003411880d00a80d0801c01c14802c5070142024050403000c0038007400075810030249000c000e4a01500141c030420080254240c0329400425580b4000400e0038041038240788000003a0b2020980b9696500b0040c4044050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 100444712 1250 100443462 100443467
    0xc02060105060313050604080c16050102030a0e040e0102070f1403040e0403052d07060b1203041a070f0f030906020115030204051009110405031002120c161b06110109031e0302040f06 80
    0x501009e541c1d0f2040790300d012961000d264002c1034030700c1024050380040010040d00741c0f00310031030022940050404650b82e0107803003401c1d003280c1c0702c91420f480080307040e08100100b00802c0102d10344480b03500015428a41804419001440003800007401d10030000b840c4610380030350b889400e54540c0c2d00626801c00043c00d0f8059191a071040f1001c68a0a00c4e0031340345040c0b85840c1c0220b44500e14098000d604103801c0107003480100411001d000031002040c0304920003d450854151101489401003914403151481d01a00e294002d41081040d079040810079000c0200405440742200c0c5c0450b404181502c81c4401106213640c640c11028809044c4480e50414075407690081040380d005034200d8103200c4015242000305c0c002c0318405601c500f0680e0214140c000e864020f40010440000c011070038800680d5001c03e40c1d900c4124506c0c1d1514403607020000150008138507400e0514450003400500e00581d00248065484031541030700c4600a18900b01c054426816a0301801c1c01c002c85c0b0301015100c3c40701 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 100445962 1250 100444712 100444717
    0x6091f030602091c0308071202040905040501020a090e0103020609091305060a02090f0f0a0b1308070f0504060e04050a032001050109051005010f0e040c050d1404060e010c0206010506031305060408 86
    0x100b1340604107600000444421800c2080c039000c0e0140d650039415100e22108440c0000003041c2c00700610b07000d00001c200303403c807071148a02682c443e03000180e5410000001504011941d030054035509120b400401c050b071192400c95110440440f078024607560b0303d1414022030a00f00e0b101402521030001044a540350550041c001c0c0001110390400e5240003100b0400002004805540c1000301103000f003003600409400303080c1c00d90038203040304041510b621800d8642a115172008041c000344000270061403c1c82e214500c0a032a02c031f25010700ccc0307281a844d2a9581c00c0b02400040c00c1140d240542520b00305003d40e82c4418211010080c4010359440c00c111015150a84061400e4103004200003001d42c0240310565494240f51901501115018104001460329880c500103003e030401524140998900c10360746c1e6a65480c3d10303580c80d82010704202040320350380185450180e1520b044003030302980001c5c1d4103045901c226810750f40d80c0d40e800002c0701110b01c0700074010614800c120500c400c001c4100e01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 100447212 1250 100445962 100445977
    0x4140a0b04050606160b100503030f040f050906010e010e030102091c0605070206042d020402041502120918100504020f03010315020415051b0d020a03110303060906091f030602 77
    0x81c00d000d01d4503110104034080c414604902418905200b040c000105e0040086521844940440b0001662840030a0841c7d000c0000f402c0315000008050184904503070070307040070300800d840e801054a42a00040c0c020380c040035106e41031280c01c00a0030195a07003501110300340d0001600c0a1008068001802a41840d0620845042e82085c0010748c04900c002030b200d100326000200040c40018520b058210101d84a499560003080d0b4004140540c5641c001000100782ca5280c1ca107001e043c941000307003400180a00b02d004030104100c1a10107554035080800007100040d4401c10316154914690780c0e86080764080c942040c00810712805462094001e54103e9004500358071a96810381d50306c0303080f480341d13001310440039101d0800f01c0d601c984a01c0c081c7c0040607c950302c00002510007001140f402103010607900069002c0e04a4a040581c0505000e4960062000031740c158104280000c450f03480052049020310031100c0040c0084403110604541a0b0040421003112512400c0c0a0081e511441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 100448462 1250 100447212 100447219
    0xf060503012d0207030e0d030302070501141e09060c0f07020a030f0312060506040909020112050f10060305010f050904080f12010302120f0a12030e0106080f010e06070210090204140a0b 81
    0xd240b68480c926000725002d040c1d05030b40350413080040707008010340b021040e00160704140c1d09100d00780028030240b0030020180381040320b10b1060701e0461483d50745024058070004a85c9001d200f440146040014659009020404816110745c1c0090084080780142c80c40650700034480c200000c148903500b245a01075501075a02ca030503da10009001c006e9a50a10800780c009000b0081000805947d901030801e4034030500d08841070300c0c5000000c030242e480c25642031185031419418401e13540800801c0f40018081d40c14244031962501ca40c1ca0103855880c400d003030090350000c0014041054503400c49032807809880045845505d90714041543c03003400d010072406400c0d0859101e5104038000b07028000500754030300400804038141d07225105011100780200030b168a54a01c0001c1880c01e000c5c220240c00403a00402d02070840e04003a07425682019410909600440f081c0004550b011850fa10542c0f405034003c2900c1c407061002c100180041a19007003881c00d000140001c0c3c2070181c100d14843c00c0c045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 100449712 1250 100448462 100448531
    0xa03080c0111040b0a230310140103180b180303070e01021b0d02190b040e0405060601082502100509100c0305010b0403020108040f050a0b0f0a0b0a090f06050301 71
    0x754031100b1648140c2c002d80c80d40304818441c401d485442001080d03440e120040341411940c809094124003900166000c044034410070400340001c41004e04500710070300003468103104c1c81c03100c0c54240c100d03108900b00240828480038001081301d81110340d407102e0074030f403042100c3d40c0303151660009050701040312000d401030141e03055444006030311100200241400078041e5550b9106c075030030055007503c03403843d802001e485890001441c1d81e138400904000c0c440c00f8102d8495103450300c1c10f5824204001c0c150703414460a6028819500b000410302c01c14250340345010f091000001000703a18001c11941c840310441d00785003c0107280b40c1d022030321007458581d501e8240402803151400751309454090041c640c602d0400c1c003081001d0341c070820104d60064080c000f40800291a038a980d42080300c80c1c04252420680c040034802c0304403103036001e164032484424080280001e014006101d19000e4400c03c46071684681840b909084203a102800030070005008214500c1212908002a41c8180d4201d0100e02d40c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 100450962 1250 100449712 100449731
    0x8040312050a17060604060e030c1009030204110f0906030c090a03030903021305150d11061201030b01120201080109020c01020c2e060b07030302073f030c08040602090f0a03080c01 79
    0x48021500404e0010911424941080c0c4100c500811884440f80d05100d8003450072503e883d001003400300c11742c0c0765984984c95411401031109680e00c40d8140200780709e08001d0702081d00140b00950320103a6086402a0340c03a12095408040360050400c85513002040d01e000004042c1c00c0041c150480788240d4508014402e90b118910464101b141c00d81e1180c000b804481d0305034640441a4400da602c6034940b94015604403022030500d8101c0c0c1214908400c000300144140801454a10b0040248030803c0c51150520343c0003c2a550042c818400742a03008140d03004509029011345070542000740458540a4120b000d030fa0310541a02c80001450144400c20315240000d8001c660588038140651807518407640c1d0114020f501080341a150181d1200b07140703112100c1a03003801134172007850005a45220542c40119080c005800170b540c185450034458002180d04941010b41c4142c00100c0141c0350b045031800f00c2d00a0407201d0600b54440392040c8084104060b100180c079207800070341e000f0842d0040307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 100452212 1250 100450962 100450997
    0x50a0c020a03081501050d0207060b041b050906031003020402030f010e060a03051f0e160f06030207230f030408150702070f030f08280e0901050d0f08040312050a 71
    0x400c0308000d0000740c2c140d00010801300d5020030f890700180040c94036500d84080340071032030101d0b0400c0f00111110750300c407e1408610324190041a08241a0038040d40d4041c1104001402c54803901400364050300000c4009002105498041401180c001c1d10a56591600c03101c4448801d500740180c181c0c01950340d002c80d00c281001050320303081d00d5100b40109203d00f006103032104060441c2e6215080961980c141c80f000035000d0080e4842018586404141d032330070032454000021854005204040c414000c6401040d014140544440c461a0f071f4005407210603814141070900c00c10004410303200010b40041e40c000009850410502031404524003a103503070108907201c8040744104450141300050510104800810492405105602852803c5d820450045120044605580c05100350900340c0e00b803030b9000680c1500d404406c60308000190f0500340082c2d1100002e010140007406210301d041e04111407002180c0155401480c00403070320040360002401070f1f01c80089a00000c112554600c94200b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 100453462 1250 100452212 100452223
    0x70c03080a17090304030803090f0a030c12020a0b070302070606051e0108130b070f0c0606060e01110d0206070f02030408030409021c06050f04020a0c23011109030705010c030c1401050a0c02 83
    0x1260f10300514034191543c1ca03065501e40020f4110483c0b0300400885001240082003c0d0041612945402d03502600c542810000f000700c00c1ca001047d90450102a00000c50f4141e03142d620006030304005132501e400b401d0060091a89411088d08401102d031601d0001c207004007200c0d50610300b6a01c860880d03840d544011001440c000c0010203450007175021505080c001c0100c50b501d80300b42e01d0040b69906450b05c440095034800e9200c40003003440b10b00d130b98043d5644240e0714017210340c6d400018110261000b078001e5131000300a2810080040340300031619000e00c02c3c401c032002800310500721307920380da20b86460b03100940c088502e9080e120f03002914806514054041c010403500010b04120010b03404505000280d031080c1c28110400226448180005107400d8200d001a042d4030b0141c510b21040c00092030031a04c6100c030741080150b041c001c030f14250f40d00081c92004d43d03c0030320308000000c40e00e14007902d00c3c9000f01d500400d403504440050b501c0034015848548282042c560070701040c0440f000a80e160f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 100454712 1250 100453462 100453471
    0xa060605090607020103050606120a2012150a030c0801320a020f0403020409030f020c0103060b0d020c011503300e040902120d03020405120303070c17070c03080a17 72
    0x41d40c03d00581016601130341c48280e0042010708a68542079942240c101407080072212004421340e10303038409000940368028000150ba02001047c034000e101640b090581e140100007481900014000013126140c602c080301c010355001e031501200c10340740c04140740645a81d074164202c9000341e500605001d013000403680a05004608442c07026241c4981510203540003d01c090f845440400c00040140c0380c078490405040e000ba56174a0f150322284000070f05110614a03000d04240c204542800038948030403c503450010300e00c00040c4e0358a01000a00d01601e10392581c00b051a0013102c0000602244c00c2800003440c035a1000b6864070000c240c5032010380000c03240c44500181d0740510200707c80c20198081140c03240001c0c881045000d01000080ca0014500000030020f030b004582049a401c00e14010318116203610055400d510706508014040e158150000d0601c2c014801003001c400da807102150545a002550310203076a80300e04040e405a404824104009540c069005400a000c501c03020f009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 100455962 1250 100454712 100454719
    0x2060603100c08190b1c0c09020a1d0d050f0f15010b0301050d05010905011104050f0603010e040b070306080a0b04030f0e01020715020c12011d0319031112040501050a06060509 77
    0x2c03034850804500c1c80c8035000080c0d10800f6528440306121b0f0352101c036480c032a410301d4000d10111004524004171f10f81540d030302ca00b21080c01440f00c0740c0815000b10328a86071602a0701200b42009590b00042c005100d1540003800500030120341d860440700c040b07100030b10301c86003208580c13110400698a2450590074407030410b02003000e0005003c00d00d42442c4c6070107414052070001c259600c0c951691400c49420210503c40c131840020100418144071204c0d02c000101120441d04540c5000c030700080040c1c0061001f0074200c105c2c13001840480c029031224018200940880301804601d281107502c039042501d003580415451500400d08600c00d00745075203a008180d01422226203070401c5c003030342d049078544114107601900c01b020700e4580b145808003000104810021580c940000b41d5042e442c04030180d41400c2d90010802c1651440c4c5a0791045004040d520300015900a071402d07141560085403400318083c24100148000c2c044150070039409001c9090040202c15a500300540340d41c80341e144803a81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 100457212 1250 100455962 100455977
    0x506100e06090a091b0501090906120b04020d0f05030703080f040c061227020a050607080909100801050a0e0d020a03020a060509010207020307031b05010903020f090a0b0a0602060603100c 82
    0x50500385510340300d4000c400501c010880070105d03926200909501c48502c100380c0c0c080b0304100540c0d81c1c003400c0c030b00003445400390405c0520b06040c2024420503007408041c0c0b041900d900800c04540302e028641e0460383d00701c082079041c1034880c90000d0b102d50184106500003134031680031605101c000d48034240607a61082d0209201c1d031910344151031410f0085503030f0b014140d0f5240b902820b0041c2d0b40481800104d234568450088150b48100180c14420b03410050090344240701d85000105240100c9250301070885500b0030580d10a10b16840801450b0424482c13542441c0600c040c401c4e0f070f500000d01102004099840680700c2101c1269264820342c4044c0040e88101d03080310104d619603000c2600854020005850002d003900828a07100f460b0f4000c84140c443c0007a2840d4011083e01c081d40605802d10700101d0b0b1500c0e40e00019100a01c1070345651103a9104c0340403c6054106030f2110346958800303041da07031141c0e540e00b0001e0b40350700c000c6a00501a0240d4039003d600e0300703000d00c14180c0c01c800ca61030b01e02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 100458462 1250 100457212 100457221
    0xf0c030108060703050a02040815040b01080106080d05090406031709030105090105060607030804050c060403030906090501030b010e01080a093203030c070b04030e0607060b10090501140a1b050a0506100e 89
    0x1d0181c0406004182429400c02001c9509c40042c0500d104507082903902000c1070900780307010605610140d0080500381d240913000d0004a20200b40d104100ea594a040d0751102107000009006081702d80c4010300c85440d511032486200e0300b010140003222404c80c0200710340d66844480324240d50301112641c3c2d002d0700030043c17140068000d80700d00b0340242c099001c84070361240e03032400f18010342c0c02908160b004c40c0034501c1c02c000440e4442e0070803002d0403003803900f03100c44481500081e148000d00001304d418811180700040302c402c129801200481d410004216041c14038003450449084000d00061594100c0074900700c1640d00041109d000c2c80454034505d10340011a110302041c1c40f8050300c100d082010504409805944903c040c00d480d034010b10340000e407060414100a990715100f13521109206580e081000346a8014800420060004e407480307030b84250090341250745c3e442c00701d01e10b146128000303011003e0010024000740071702d00c5a0304035401070301d803032010100b0b01c4218851004002440790005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100459712 1250 100458462 100458467
    0x12090501020d02040303080f0109150b0c1606050a0e0414010b03040206040b03070503070f020c33070b0702060c03090303240414070801050d110409080408030a080f0c0301080607 78
    0x4410640140001030525115030020000d9070b10540c419800900740d02c051001036045034030101d0040000c0c210800c941c0c0c024200d001c1e1041d502d032107080702414000c59108070a01d003c0c4114a0102000200758100c541c480c0c5000d07010790080c0785c01500241810780c212106041a1140e640901207041c1c00c068948c1c45e1210084103680000c0c4100d801c16020300c40003840c07030b103048003030f5018030341c0c0e502e0300ca0700c84c58880801442040700302381000031980002c0c0403841c251140d403102192036841802c0041049088030001c0c0c1c04040603410860400d1000503000c017800081c0240500444041e0700fa2602d6454112285a550001b03560803105174104101044280d044110524000380d60b002d80c1c414142c40c400006011203d580214a4104018108010507680d1000480c0d024203000c413031074107107080151234210601300b0011645015a5945140106110001d41034400528204d0704481e0380c1c01e94030000415200064440107001c0d074081c00480e900301d1a031419603040c2c0d4104402070490b036a554404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 100460962 1250 100459712 100459721
    0x6060e0906060d1407080406050c0403030e010f021603060e07090903090905151e0111010e0309330a030507021f0c0c08130314060106141b160503011a0112 68
    0x80030f0035941c0d41c2842d8402d0081071944a2041c1011b845032441460030782020410787d50020088003407421304003c02d20000e500249030343c45030a020300c2c0c403045000314040144d1130700042c0380c03000c048241c0580c0000100314081e001040039007d8072040d100150341d00c400344030a407040e0b44402000310322208020b00a59400c2d40c4036542c003811038020450b00c05446004911094603112074061303010400d10b0780c0c200d00d5030080720b14484a000c800080240e461210034960b128010381390507502c00c200030f2101940c00580910300b82044120502c0031000c090741d00944003102d521005440c1c02203030030040060390482c0041030000344480545c8100c41c0084174140100020106d043c280000d10003131010360350102e00490082c12200a2026054400908604003500f030343e66101c580e080c1d10f51000b40140042c0741d0091b2101101803040443c55210030003010f11201c2d4500c0048000094031810f560300d00000400c0307401074100c0708150002c004180c00d02440007020700103c221140440d10610711801d81604903800b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 100462212 1250 100460962 100460977
    0x7090b01030f0e2515030c1701050609040f0f0f14010812030a02030612010c0e010e060309031801020a0b090a030f02010c0e1c020316030204050105090103050d050a030b10090906060e090606 83
    0x82c1d040c01030300c8200043c030b05c0514030500000a070380d84041a40554003d00344800056002c0e0b0aa11950b250174001150341c818412420301541c4c50302100301801001c1e80040903c0c01c1481c0003406280b1100d05010010400c1c1a40010710084680c00028280808103000700f0341200d45500760b14507a02c4e074092101940c000740c0016001490100e066050307000a109007480e441c05680c95010060000000615148815001d10f11440b81003040c8908444000700b21120005519041001620f21500507820b101c1150740c00750070400f445040101115001c60066420703846a20798084088152000300c0c2240e0480010a01007184605c1211842c1307001404640190400782c8801c4050703131583c0c08030b07051140c01c00010094490f981e1041c1b003103107464f014035405481c0c25107e00d8110761554960513038801c00704800505015002800b40300151007074110203e044005040c3e07980c4044028130061911055100c0d60050618000c8041205031181d02c41d0500c0000003003402040361280c0c804c01071103600400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 100463462 1250 100462212 100462273
    0x1c03020a0807020a1203021006060504050d1101030b060f1905030402030d080907080106081b060c030301030f02061e03061005130e0a0f050f0a0c02060601080406091407090b01030f0e 80
    0x1100040c4050703505c80500b20341e44203074068a107030407805090380103840380c030b81061090040c02d01040c850b580f18448201100c1d5041007400380008503800c0140d00070104504015006080000e0000f20316140d47c000b04175400907031241050300e001c48841100c0c18081514000d5058100d00c031a821900e00c5020b58941118a00c0c0685610a94404d1000d007190041d074484a40e6400c156401110002002c0f035aa500782c1c0706450162a00b46221405a00c0b40b0050000415490041081e041951254019125030342c1c0c852482008000e01219070402d10741041b1440c0344110540c2981d403103d144984150b030250160ba1150883c03090a06c18020b030751050051041c49499940c001084a50007540545405192100c1c0fa401c26801c02c7d03003a0605071240c550040d02954401d03030905c041030b41e0201901c0d40c0550040c90002e448482ca00d4410b040e94080002401648185000030a4103241c82c1d004021420098804002c40c600390031203003007580c05882500001d0b811076502004078000541110a8819121 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 100464712 1250 100463462 100463479
    0x80a140a09030c050f0109030b0702030f0d0504060b041509020a0311070f05070e0403050d180507030c1409010e010905191401030c090b0f040b030304030812061c03020a080702 77
    0x10211a4295040680e03100001141404100144020308407084050a42510b11109035620b080010f88242d015110080900c05507000040c800d5100b48107661110241d100c14036600c42d071082441d0042d04042d03500741c0b00302d0b140c02c4140760030b807a1500c222074488075070300540414503140248460003500000000c00c281526a80300042c645220303801031905038410000228001d9141c206245000c2c6590881e40000c2c5814062002107504102514520342c3c1d5118041031300b00511a0007489028036450060540c8101c5502104100c00245408291104400700c0c08103400d07208200030707070a04280b1400000151050050040c3c90084e0451588a0761403415004940200c0100300116200f00c500207040515200041c130800032240f16460042803100000e0114118100001d4020224009000d100303030740c0d9480748080c544060084c0d40044d90042400c84c1c82e8a14065506001041200d150303104170008810301c0f02045c02d80000007200e41e003540c002e15a00d45940e903090070b5a803140000f40e81c0300c002d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 100465962 1250 100464712 100464737
    0x6100501210c0507020d0c1d100519080607021c021f05060111060c0405040b120613140d092c010e06031203190b0102010c12021804052818080a 63
    0x402e51401c0e50309101f00c0c410891940f0f011891280309103580209440754400906000010f20407084100650344e08407402c0719242c40c1700803d8240100b4561008103075024000c2042100f54003c2195490060400300300360000f07845c110126241e0300c8103c02606e0010010410101c10109507100591005041c141450308249540105107800c900315021004d040303000a0900090500307008400342c1c1202940d48200d441345400303103251101c80003018100010b00151050303050010145211070329003880c1c4240c03030f424864140300610390890b50081ca8008112645140c1c1ca08409100d500001010004841e181c0d90814800c0c407449d000c060103183d410310800d1446101391701a84003c501400d8a0100860607080e042c7c0d0381001e4480783c80a081c19640750500040341d06130045030041881125060040e6500781c1c48a143c60600062051960407a00e4107040049038030546030340b403e041050418a0440500c096182029562002d14005000c184e04c6500310000e02242c0140108161074208600c00214 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 100467212 1250 100465962 100465969
    0xa0308070b100603050f01061112042d030b0601140f0d021b011a10090f1401080108010216020f18040c0f060203090f0621010806100501210c050702 65
    0x40326206031010340586052040014100420200034022410140f1291800203103051200205202d518140980c2141000c07000d40c0c148840c003800c5c4121f82105072507940380c117485000280c00304002c40d0048010b005061013035841c012000d040780c1d401b0303096200c999214001106c0140c807105c2c10f19081582800351350b00c100301d44006046068010000141c80791104040f0a030325040c0c04c0700003500350345000302c050100851001803115044041e15810810960000211800300d91a88038034900c1c4201d28000c9031100c00100da0441c100026030358040e80e640c99013031550803807041258500d000a03e1208480c01420105285210444010444022458107501903c0ca03503500f200e00311801400307002e043c45543c002c000c1c104003802151005504286011020031402900062280e1140c84041010369000f0b071102200204000d02520440b10341d65252070245d9540c2c420380381040341c00c042000103e050b5100c0d206140c440148444108103111444407140000d041161030041040700401c0107102584 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 100468462 1250 100467212 100467217
    0x11010c0b07120507031503060c0504050a0b0a0806120606010c080708030a0b01091a180f1e01090614090111030d110d0c031112090106090903020c010806010f020a0b060a0308 76
    0x402a15001008000c0803902c408480c801000c42090624100c0008a1442d4904500c416240e02010000d000c800300802503495000f02c0e030069900816003900816201034443c00307000800501c1c0c42d010841c0c0c40d130500b0800901544121101a41e0050b030009503998450b801d06551907006809081c072b419955241c0d0940c90740100c55034400c6644a17420040c0551b40041884024020350804400c0c0a0300303140040900d125500c800e11903080014a141c50b0303980c0e40c6001980c2c07180700500d0741d84203c00b105945110903141d90b00240c04242d00013400541540219049a1140c10f00c030245850800c074000107480b80b849100740c40409110500001c80e464030750b880340400203402500140d4440350f92100500550b4441c140080406041200f192612070312001500c040c170748074612402c2d00e0340d100c0351801e0040803958040c4145074203004070841415000f05006042003400e03a500941d0307a032000300554070300c41d0840c41500141d005a80000200d108604040e410400061001180d690303207494102e0241c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 100469712 1250 100468462 100468471
    0x6091e381303090b0a170603190b07030509030406080c0705010e0708070806010b0f0304020111240603190203030901110703020a172b0804061e0e010b010201050c040311010c0b 77
    0x22200301007080c0038580c11042042c010581007220f68981a0340b0b850040c10030750218903880d104d5020350046945a581440003804440400c10500e81c0d1643c142005142c0c24810740b141c0c03002c240b8020206003200b0003c401c5030305848080d15070040c1c0d52100840300d8071542c040d00099885540c1c030308419440420500c5514000c06c90500200b520301e0a0180c8541805010303030000074100010803a5054021051040e00c0d489602401d040c081c50140343c50003424104401c4440c82d110520282d0001191040080607000340f505904507241241210f60400c030100c0c0131034001c1e606a109206403003032503100340c00941c41c548000d400d440980baa03030382c00b1522660141c0c00a41c2c80318a02d10081c81a02d0080000403030b010381820318040e4003282244d0104140c0b50343c4881f1010072000c1e40c001401c4c45070a400481c0d40302480010b11500c0101a05054000e00303002c512002c0303d50801c402078072558414001c2c00c3c00f82da429199035251600e543d8070038118109148030181030018003810b07a804078400710041c0d03106 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 100470962 1250 100469712 100469731
    0x702100905040f0b1f1806020703150504030c02060d020705120d05071806031a0603181212240d0f0308070807080f10050303040306091e38 61
    0x1810441004180c91000d0150564035182030010021390751901030700c0380007440005c005102014108412560070481000b110440080003d00140d01580024108200c0c0d00075130200100040494000e0280d9609860140c0091100303640300b00503280c40001006180c819050051800c1e08a030340d13603400c00400c2c000f0310700e00800215001012000038020164486803500d80300078424000400107845001d80c5c000c120405a0350100103504161044244e00c1100000300001c1d183d00e172180d420200320b1008a0886546d007e03480a00e011200c1c1d0105843c40f035416044c0c00700703944d40c441d40d10100c40c41018000204c2c2103103c202268994132400100c0700401e025401d900584225402c015041ca8005402902048944410400c44a03801041d03c3d030000300d800354028190f1150354105e41c651000f504200d070325000018002017000040d9020045652060381203072000b0043e980c84500303221400b035002c4c1c0340c052800c41424180c0030380e450301d0250440d108600316080407640700c12924088101e844101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 100472212 1250 100470962 100470977
    0x213080106030b090606031002070203070906030f03030c0f020a08090321030915190c0309050303010b18030601050a0315061d090f060919020d0204090308241c0206070210 75
    0xd126403443c003181e2084021001781550f013080b00c08240d9a040040038900b1143d4041116000c41d40c0520841e0000c3c01c11030301c248505501c1c0d04154150171401d003002c401007481d00052501c1c2034001e0881c440b0741182d50f0040c00491031a03458611907984030701c0c00303250705001c1c0444903004482c1e1500320041810a0203016500c2c1d18060548902e000034100c0e4002c064141c0208000da50784042001282000380e13610080b500e0524100c2c280e01031310320007100500324007002c4004a22002c0a4001d4103000c1e03a044154005d095442c0140354030f80d81d0038010340d5044100c04100b4004120121120888500d903503900080071b070b5a94042003181e0a00e50030701a68100c0ea981802805017040288254809150020782940c1c1403640304155503405408044148421103482c40c0195601c0c1034a038070103a42c020380203120103016481c0040400700e00301e0700f814040d484124406841030402c5004000701c01c014001c0300401c0c032842048000c240f02c0b02000c80e80f10504200c0c000060312640250030035209691288035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 100473462 1250 100472212 100472219
    0x9051618050903030c0706090b04110a050409020603040f08120907030b01060f0c060c03060315020d0c0c0c141f030e06060607020d080a0e0a032a230102010213080106 73
    0x40c0c50006124165003140c24041403100301c070000720450340c000071500c02c110f1b41c5040d245000d5019141d141d4000d801c0301c082e0300400c070511280b002e04040101c0e040350f02c3d0307080300d03107817020482110403034200a50400c10500015000030f20503505130300068040c0d400c0390300b010840f42c011560300e0021200014070b41c010250410420040d0780c402809044e442c2048002480340c880c00071b0072407280080c06429242c44070641841540a944034502031500700c1250011214400c40b880d010394800c10018040c1443c000106102d0752042614a0310580d004414490301391402120401569851209645c0158002c1c454003400f120301c054140144460345010541c0310222183c10308108008002d5805400c0400100300140d84440495a0640c0d02202041e240c003117100040341d81d000005540c6401c002e030700001000703008640c4042580ca04280e000308180c041e07001c05603420511140b10301e2120b05840203080244820007001050b2000062000604103050140350201c0c0314055480a02c85964440c000d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 100474712 1250 100473462 100473479
    0x206070c0f062f060402040b1c0c030b070906020307030809160905072304050118030f050a0627140c03010510050108010801020f03010501081b03180d080601091404090516 75
    0x104240041c64110000f0310009190b40300c99005000038403803950780c035040302c05a546a9601450340319081145441c12558a07211050301942d020507075451018500140459125503490010b4507040c0c0d0196052020b6698217907144240a440c01c4110701840900740031071b800d242d56240040805031000b2a2900305403c02401c1132902c2c6070f0081c0e203415010460815440300104a900302c0e4420720b40030111000803c5000f8083c561070304001e2090781c3d41c00212040c00b0780000d103a80c4c02409800100240400420032001c0d501ca44034000c4507141c842d40010b030209001800030315140580e4001d37502083d4072140000c0c2150301c21600e8440900c801e9000b40217550b4400800e60240c0070000c021481c0540910b1110000e010512a1604000644001070704001c2c50380043c0301c0070310816203a25201d040210701100c803550340030340009107403040c82026180c00e4840c5203041c4c05640181c607442105030078036009400640340e040002c1e400039118117024000a004000322403818541814042c001400d11104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 100475962 1250 100474712 100474757
    0x5040507050a0f0311040605130803160524010308030c0c06040b180a0c0b0c071a0d051311061608070c0e060607030f08131b050406150c0206070c0f06 66
    0x900007010300c5c284d408000d0301c04030b000301c4050310043c0c1845922004950000c01d481c5505800180700b502003ca802850040307440703c03d8800702d200d85d0a070380c9800d2190b50202250320076140c03080209020303a401000450f4100c40190f4000e50004421440c040510b03441c5403070702d07000380e0341204c10661281c100310007ca03d400300088607149800103030034101c12544034800744590038010b0099400b80050b800030052005c11522000301008811074604da110400480300540060490082e80e41c20301c8000fa2400c00c0036000b6980195020072011900b500e05820301c0096004400361440d4040381d203004501180e4250090300724580724030401e07071079541450a03d51031040d000d0070305400355806100e0b480010350000e00c1403101e10145e00d48080c1590740c4503001603902d003d50b90f000d003020119250418100740d49021803415a18181c809000160355403d4842c00d00150802002c00194502c0555006150141c001c0648901520641c4505a1904222450403106034003180204003030307004403036140407003000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 100477212 1250 100475962 100475987
    0x9030503120402030c0303120c090409020306010608070e0a0518070203040b070b0415050903070b0402010507060203040614060307060507060f060f06090608070207030308130f05030a0906090503070503071e05040507050a 96
    0xa1400c08d040a401c0c11468034002d0f08115607a60042540d0109407200d07400780034070940040443d00c103940d580724094004082513924100040491824181c107040c0489454120f40c405002090441402c01c100511008003500c06811070100b040001006000340018080c0b8502032028200581440d280c9655003002203100c01d013813030b03040c2030410841c403c0120a5400321078004a03414116500c610040350244180d440c0103145520200c18441480705550080e0b01003681c5600b80550b03a110041003507910b1000d44907c01c0042d40401400300092001d4111241c5620b841e10041800c5403141c0c840382c5e502841d40c01100005000c0201045201e50010103680c002600d8005000000d06603203009000e20740040c00d0241000700081c2c1c0f8020801040410b0104030b0300070007902d85859000400400305001c45c03145000007218a000814179107004580341040b102c3c0200140385983c038108650441c65003a510842c151590343d140051542c070750780610340c407406841d51041d503295001507010300740303904600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 100478462 1250 100477212 100477219
    0x1b14010201050f07050301031403040801050c191e030e01090f030201020a230d0506120d030b0307050102010509030d0e030403080a022a090106030b0d020a080303010f0e0f010b070309030503120402030c 88
    0x107000d1559041021a4150b035001089c41c039800c6000110b1070b03d0740c461030380181034941c41e0004209a030321050018003201070103400c0314005106001e20441d00050f800368900410f4000380c41ca84210750003a407050807260300700000411191480e4442c9120190048015030250f500003442c0703041c440d4091081c90340165400f03c3c8408010703a82d05040750500078400c280c1c40f0b4640d1030340820010394607a141540390384d440c041140d48125015100801030039082d00c1aa02910800c0b6000c81e140d80180200d51080040c200154142050001c142024004a11702c0042d940002c2101101282c880c00003022810090303002802c00b290ad0748510542201c403003080310038420071440601c04691b10407510504440b600c1c1b80100c0c030500e6450001d1440815401d00a43c00000c0c214001910b1a02001441c1229a2074a0340384901d5034034002e074150007404403010208900350340c0040c050414850003401409000b494440c0da160b442f555002c2c9980c1c00034000c1c4100d525140200421803030104400800340605a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 100479712 1250 100478462 100478491
    0xe0312090d080907030b0709030803040c080f01020c060f0403051903060509060609130f0209040c1e02030702010906050708040906060c02030f0f070b0c01200c0c0301180b041b1401020105 82
    0x208503a138803000d4900008015040703010219080c280b294865102070340e00a4003803962401e240c40c0808480140c0c1c0b04103100ba014080e400e008254061080e0341c00301a00c1c801130480780d130f241c8424550002009104a0038048240070000361100312114501c4031f000181c400140300d03410a000c0000c40d0800078115881400c04008480c62902c4600c4e04c090919200710780407640303019409451000c1d0080c2040796800c5460451842d0049a0049034005a100400001400401038003002ca0700c0344541c00303000c0d000c604001e0081081c584200001c10b4418068440c503400e080d1280514000c0e0f03400741c2e0003580000e6145105030709515051242d9406180504c004180300910540d60b242c445106104d0098426400b10310340501c60030a4100c2c600c01c410411444082881c081d200181582001c0410003551040c02e041c880242414071503401041c852904494954070940e413200080c0a004104848940a101d513441a029051420034060100480201c40d10f8201000090840350024685060b00259 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 100480962 1250 100479712 100479721
    0x31b010608070b180102122b11091c08070f1202060405070b0a090f0602060103170c030f0708070203060f1b040b0406030c020a05030406031e0b011e030e0312090d08 72
    0x550407940c45100001e4a0030010300844e0050741405680f013060100c540f00003455298888070081c04080450100044040801d60040c400d82113410900c5e021300c050f80d003006880e01600e001405a141640d01d540c20885845080d541d0b0281d0340c00c64901103c01110100b8031108011142d16054076424991008141d50f1503c0e4035425a0354056101d0222102c400144c1552040c0c030030f840d4034024040c0d0b580140d00403561407600a50305c01003480103860080f890001106034510200c211117924054200450812600b02d0000f0513951203880101c826003020090303900140c405011007407080200007140318061030004040c6641640e00c0c4600310243d01c0401041c0701a1404606440aa403080d140000300385015a00c01e07403400c2d440b19000340c0140b1000c41d0001705a40e050300041c5001c550300002c040d0760b0241c00d514400787c50300e8030003249c080380c40d41d405c18020600032060b0b9540c08605203004225202040402411580f000d101981d81e8400b0400f0480e03941c40c20483c43c0b031844282d20301089107140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 100482212 1250 100480962 100480979
    0x304020411120f090a0606031109010f030c0501030c0c020415030506090a0201090e060301151202010906090501020a06050901020d0c0e0901050f0102060403120b060c10050105010806060d0f020705031b01060807 92
    0x8000c1c403c502143c50100421200e0b5420044a4603080d48001d04000c02e6440c1d09045c04807101e8805503910540404002150004609403c2c500702c96001c50701403440c0341014015000317401040810010070008185242c0940d43d10f001302c5a00700700c03030340500643c1821800c0090030310000030040701055002c1498900140d0b13000311207004480d00c07201c10507031988071040064050070000c80d1102032848800e0012580089a0300900405031003602ea40d010302c0e56030308050702c4500c601d12901e070140e0018004080400e140790490f0381d00c0a4090001494244c6900041d011242e01c0c1d0f2544002941d83d00e8110541d00b8005842809008122a51240c0c0201003000032b42c0c400780180700030100f01c4e99000740122032481c3d400128a8090083c00b11391218401d8400c1c1d540d421200403900c00c41402d100c000241035006581050041c0c102400e46803404103402002400b41017070320306928200307601b0000d50003c1042800900308542400000104445450032041d082d03070351a4100365416000100c3c00c014104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 100483462 1250 100482212 100482247
    0x170d1109030309090402041d0706090905190f0b090a15080705091303021c0806030105160203043803010f08030c0a02040515030a080c070b03011404110f0705030304020411 75
    0x30040700c40540c959560f1007c240640f4500c0e42c4401500d40c0c6142c00c0d030250070301055810648485980b04091140d64070b8032101642c00c1a034074400514414000c404585403240c024140316084040c0224610007000085001c0000803110010318540d204207899400710280003600003442c44000070a5200d04200024103a41c80c05070441c801d07201ca030b91310101058028404400300728840e9112007100049140c0242c070304802142c4480c03080d440c0600069000722a41d0300d1214581d00c0e9402582040e040046170000544800d09484000c0d1800e0028040c02064600301c0e03504005126240e07481c0c3d4505146881d04410316001000c0e19007042c4100c14205100249903103000b901142c002ca82c41c0c440c2c4100303001012070816001d400d405443c0c01d09050100c0000103100103107520f02154181c650300c1c0b594800e940000c1c040c10080c3e400c01d400c008064580ba400201c0f1040101291030b1801005062040d16944400011102030300040108000d51030584212445a407001c0046032406502c070300c0ca00e0603035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 100484712 1250 100483462 100483477
    0x14010c05030f13090f021c0c021203060310020c0a110111060a1e05040609030e1020120307020c01022a090703061208040906060e06180d170d11090303 66
    0x207042c041031510308a42c42c11403110041c2800d2008002c95001c4250385406544501c1151151100c580074020b0149103138420070b07001101c00d501902c111107890282c45c031a580081c010790b0b4148602c4442500400c0148001c0811410b410014150042686020000740095441540c1400740030b1644000d21200030927243d911035a540b4001401407400070398079507050f50b06007540015902e810308000801c0300b10346c040b60380e0601070303100d050004241c41c00700401600040d85100015084142d010804083c580d19400b00c80c0400003138032a0724141d40403016081d01304850910040c5e0000b8851511540c05100100ca90307078456160009070f59800410403034000c50760090034080d0340e0820000d41c060307110341d01000c050800c107070b6041c00d120101d040c074840c260040d01400c89070500d0024001801801454042640c203406004542480c02084954030002040680c1c6034220818188240016111034103180d140030240010382e450740810120742c000c5840f0f0750140724904000300003c2400346da000040d00c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 100485962 1250 100484712 100484737
    0x306010608040b0c03090109082d031302041503240e0114070e030c0a0605070b0f0915130807063305130f110306010f1706010f0513080714010c0503 65
    0xb29103901b039410b030040058410140c04032201280030704142c070172880510042e42d000038221007800d0002402c502039102c2690071600d2040d40c3c000c100e005081c0740c0c0005e456025400010074125560340c03510102071100101d0007070f1200108007043d085241502c1414140d91400000b0810041c80d0845003148a1000e0512014055074851100407541c0810411280c0f00f400781110b42c210b9900c03100070300a0b401070a01140d0051444000544121804003840d00c114614002009010041c031504411080080c06401307070f1101881c5182d002c20581d10042c14500e10400300090261034800030034440b050044111b40070b03c80c14010b40013603103124021100503074508a50010f10100c180c891400208042c0040741c980900706902c010101101d0405113120360b1082c1c84844d01c000304410101c80c0d65140b006134540c519043d00c08908294491b010000182c0000e0400c60300d0310121555600c0d1050349035010344850f62003080c040c80038820310591440a1842030a149003000000c2e5109034890240a129440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 100487212 1250 100485962 100485967
    0x11a030702071a070c0605041a070804030b1009050c031801050603060403031a0904050f0609060c03011401090305100506040c050f030a0f1112091902060a03090302010b0a140306010608040b0c 84
    0x30002c070444d01c4c204e50002801c1c1440c0c1d035400001d0041d1300a40305041c05244d80451150092041000f141c0502d81c3c0500388034542400c0d5a1545410100a00001807984070013401241f102d5035445440c0c00348501640482c0c5a25001d0052802c0c483d090040d06881e90418040c42003585001030720981141c0c2c142000b0640d29424800024a5014048038652150051b0148018041c001c0f030b0800f114110380099031110354460701d0443e901d210a54295001e03000401c01005209484c0c601824407110516108000c3e980d42d440d00b80c40d203060f60b003003282c43d030380d6803028400e4624140c42060004459400c02e5810002d25110090140c00006e01a00900b512032074101c00008941e80100d4001030b54140c00d50301d401d030000d00c403c91a40211420b00c2c091180710004e5100c8c01ca81c1a005074595401081c803860000d880c0b40860241425400c120155900c41c55443c43c503984a40301100540381150f000b000c2003c0c20000c051030303c130069000c00309000360501400085403c0c0c40100da070001020a4071607 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 100488462 1250 100487212 100487249
    0x14030a11010315030c030203060a0e100c0302090d03050c0714012708070806090111030c040b0a200a0203210a0c080c070f090b030106050616020d0c0e011a03070207 72
    0x30080e00050888988400c03d00360040100b041240e04074080c2c90017a403c4440541c0c07160a000102d031304944900040b54071409001035410081d800c4040c108046140141c00c001701140840c803c4c03600c1c1c1c5002c80202c0d1000c50015076024042100d60001c0604100d80d010400356000040c207135030968a80aa01080c01c0715a080e0341c0300f402a00c0d80020402c07a0202c900f05a5079511a6441c2d00c410b0302c01c1e040ca0f500f842401080d2003016425640580d2000203160b107418a4840701c00401c1c4e20a0110700107011030008241c010701d030141c010202030940a4040c0564800501c10542050b24042c84a0500441c000210a0007003081d419600a074185040588004501e070614180c0c078021090815603900c9400b4004c9105101c4005d0310082320090390086c0500320380075040500b0780d045400380603000007040c40501000c10f04880700181d041d00151580401c0c3c1c90b5500c500b01c1003a03168100b92074689108004002140d826044660347c55109407605040d4181850000c2d1140700c43c0c400e03560022004940309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 100489712 1250 100488462 100488467
    0xc050102120109230405070504050915010305010606030b0312040512120a0f08010b0705100c0513080c24090f18040c03030e0a0f170313080105010e0114030a1101 71
    0x2141c00c141900c0c4540025a0b5440c0040040c1c004062040703401c03509420441e04000072844094080c59000e40941503550070901800000c00e4010120381141c803070351714400300300000048928080c5010308008210141003080c081d0948d808184200c5c0258041008074200c41c071741c11700759030680350202c481554a0780c403e02411310700600e0094502482200190850402e034010103200005051522041c45587e81c41001408601520001030141c0c0c105840c60401d56010350f12024110f11340b410301c6814100c000704046c804680c40d80250b5510342c00880902501d1801d9960684000c4028004000e1030440d6100740c0100d0003241040d80c041d0107a803e09080682c0c0303158016a211007007040303960151829082c6040f076080390b4481500880d042d111009440d003400c2c9200350581d6601506e5403503092412542450842c036541c00c000d0180010b009818030b01f001651240000c20b000000415603505107800700e203507942c042e4041103011400100480c0c00742c50100ea0003102c00d4000c544544030340c0401006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 100490962 1250 100489712 100489717
    0x90c0424050f030c0702091b0703030914030a050706060506070c030b0402010c0f06020a030e060c09010e180c18011e0305040c031202011a03010b0a0b0a050712050403110306060609010c050102 84
    0x40e40c0c0c842c0c048104842c0d4005203025010b401c1c0222500c0a060f207900003c0034441030b80790328403110407004009840110340a500003507540c1d441401d018440700410451281075800c840c041c0d90000385d00150380014040c2078000c1c5405000c0445002d0302d8003034690349140e42000303d0700c4001c00c0080c1d900c0c0000c00b96030003030f40c401017003036040f0303502400103407041c60f1400080d8000f0500b0004a0700e06003066402210009000c0d21840f120301e103040c0342c8075004005407580d50858003001d92207201800b581c1c0c1180b8110348200d028041c02050282c850054074508c090441040b9516810003c11040c2c00301852244014085c0041d0300c1e080000d1a83c0712414640561003541c0c00250030310490504e20320106034158031404802d0246a0202c0904490408241c26121b2100030b565110361046010b0004403c0c0c1c1c0e0003090003103000d0610f28a0003a260380d0343d80e072680003c95901d01045002c41d0400c18044503080e112902d000480280030686052400940d01d8000e1110550400201070706000421009604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 100492212 1250 100490962 100490977
    0x1503031103130902040e07020c060f090409020607030201022107050d0e0c0301090b0709090603020d0201081e041b0e09100203100503070305070611240705040320090c042405 76
    0x2000c0350042d803540f91040c081e42c810301c9241d24880c5080002998584042488202d4040040c401403500041408094071500b0102074158442d949000010050f910701004125980c800d8002580300c46182540c210783e003031002e800c490b90f03205400800c0f0b0840e5014086401d2004801000600909410315061401e02c0417203202e5015860400800b040c4100c0320303038a0b88500305668940d00070946a00011081c3c3e1513500c0002e41040311030500000541c01143d1a65002448007051070329400501d4100c0004107090350280c0300412000401c10000103805692809058400392104c081d003004000399660300444456600240e40c0413001c103140b02c0510700e204001303000c01800c40f0100e07912400d115485043c0c0e440350741c000c030b4402441d0740c001d05000701e030030030100d1120700328069600c602c3e20005581000c01402e074001c01408010100001e1160115400d0308680c0490150b0700250103401d00c040e000d4003402c044007061043c44100007501c00150452292075250110324014443d00c08151018081d00f207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 100493462 1250 100492212 100492237
    0x30b07020a080909071e03050f0c0901140304030e13060906060503040b04120e03010e06090609011404030c0807060e0c04050c0c0705190801051305010c0503060d2901170606041503031103 82
    0x250700c02e06c0a94141c10503400703528801c0b000c02c0f02d03840c2d05001c4000c610443e54002c2c04644488030750400c000e003001c051544a406400c0190641914000041810f85001509a84c050380c032074040c0400da61034455400a0241800d10500e1420180c0350383c1807405009000502c1d440c0031541d4100aa132007020441204800900240151000c04282a0321002c1c120b8240d0041d204080008000105c14013620703081160280b01c0c4401519192401c41c3d600318805030a44402030200074101c0003492910421115294000c09404c4a040500400054440c090107944041c00c0c1440a15058100071680008a400480720454001d00542c01122004590380c044a4194640010401003809104800840510607402001000368005096030140000c0d00c107a5040200c03640c0d0400010080111403503c8080a101c90051903480f01c045442d100007600039000c104066421500d8007441003045a0308980200c40074004210016640010344211b403102070b0411181c40340503007045c02d083c41103038201078005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 100494712 1250 100493462 100493507
    0x20f0d0e010e0f0a0303050f1303120204030818090a0b10030c180e0103141606110f10020d060801020f1206120106030503120f0907140613030c030b07020a08090907 72
    0x1c0252602c800c0290005d80220f810300001400d206a00348401d0f10444401850040b02c0c0490785049a002d00301518200c01f0710b5003004040f0200343c0d03401c0545405c52401499541004410041c44041000501001591360070480791400d10380d80c200d402e504062461074006200c3d44520800c4820207070703016940c0001070490301c0c049404606160201e050301d00070100028603101e00124070350794492810111220001008040c880c41c0d00c994404001c03000c1e040111202407518285c0380d4141240e610340d190720664000b54214180d502070240f2802400d0140007141842c1009072048054440c0000c641c0f000d6421000250f09980c1d00d030404406454180000c10942e81c43e450801d41e294400d058203411046203100041c1c103c214800c01c648a5404100030708150b5141a0340071194443c2d416000768441c4081c800865008036801007078004600401000f051107207107040070703d0158006440e2030115008000c0d690b000ca60b00104983c6201029614564140e880107811981d480600c03041311ba031160b10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 100495962 1250 100494712 100494733
    0x3010b09040c0306061a0d1806050a05010807060c030806061b060403170c0a021b13020a0306050a090207031416020a06080403030605010323150418060e01020f0d0e010e 74
    0x8059000090fa4400e100401c480364581ba00700c907140d40501442100060b082100700c40700f06060300904c49800f000e01c1c40900c00d01e02643c409040e035104450820002da03070385004001a85081001100501341c034104001011410f072002058400c00401d16070044c4c800040700c1301d0f035142c240c5c04800c5800d940c0064a00c1c60410385401000d2090408428180c079102502003426030714440c0407202c0000803a00102031b854a004e907581054165103603005e90181e8084600c01e2070400d00d000801e503240081c3d90010f14281850100407a01c60260024000c440c4148543d40020347c01c0003c92070850410740205d41c950342c2c0c0b06c40c4856603400c4c00300025001488003c001904d0b0b500241007500441c403a444c01c0c000e0700e440c1c0b4011801c0b101d4500310800c2c081c14100b08088419030350031005401030289010f0a40e108550f102041c02c0d5640a2a1030308800f2101d01c41c8014000148140e10790006204000e41c40d0042c50700302e1040900644510041e40c555500c0c5541040d0000d50040b402c2c0c003410070a44420700078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 100497212 1250 100495962 100495973
    0x30c040b040e0906010626130602030a14010e010305030a0503040c0504060303050702120a051b01020f070608010305072310030b130b030115120303050601021612110306060f040b03010b0904 83
    0xd50741d0f40d0b82c1d80700303000010403500d00074003001c110702c1d41c07005442d544102d8100300034203803030406449001c220303c1d584043d101284136800114414080404003041d01154850781c40e02c4050144e22142882c0106001440051000300846030054403078503160762a0348883c240414820390541c4026402450300d84000101a0444060440700b07000b00c0d100c2e04103450040b00c250300d4501e0902c00401c550132000c2d070360088140c0e40c110f40c1510030042c03048580e0310542d91500d07444e20b1850303041400410f05c40b200400c204903040010320060301c009000131662900c22400c1100f071b00c0030020003d03c2413010012502426110b0385c403014088400400c0b0b0080100c50b807083c400100322a011032800f0354201150000140482c0408104139061280c2d060a14092924220000c00000c1c080604501407454413203485e41040403120302900729070900081d07413030b41e604d4407408050382071400714040d4001500300001560b5400d0301c4144c0c12420354020071a01d04240c002801851070301a2158000d0883c410f0000340074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 100498462 1250 100497212 100497239
    0x2010209090a0504140a390608070315030506090105070203040819020d0b13021002030702130b030a0b01080105190908070b0c04051005070204061a030412030f051312080108070b030c040b04 83
    0x1403910a64460354025554421812051f83c2985a44c000306d0300c5042203202d1044c02d000e03600829030302d00040c8006007840e8403c020304280d40301341d0360780c0d0281c018840a200288540341d00440e80c0d00017546006d15200780113444006049036008004030f070007000015512010043c18400f5800810131003540303007402502c0a08054101d06901403030f4402c1002c82010300000440300410f4004003d40b1032242c0d00814440588841410207405014410784031001400c0c4400c1c040c017911010380003184c5460541c61468884c680380c5001d11405042c48a44004a200e403806c9070f108603008040b101080d614211102e04910856110a400c000c1541c020451544d0110160890503c00c4409000c5103648400900150208001d03200106408002180c0029034801c1d058140078454213011a440620195050480700103c4800c03120202004074042040000b03940c005c0301481c581054070b10f80d41800810790340ca1195005000d4a0300b800404a071104035400240c900a00d00400c81036520340d02c4060212501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 100499712 1250 100498462 100498493
    0x15120601031e2f01030509070b070204060f03080406110304060e040209010332010e010602120a03110d240305060a0e0f03030a0e07080304080a02060a030f06030605090c0102010209090a0504140a 85
    0xe600e86003c50600f58843d020b841d004610400c0207020442c240703280c02a0316804908200d03803150360b035500061f1341c2009554041c015801014a681c6481c5815005001d048810503c2d032a50f40040106000c4150011040c0441c000f09540041c0c4500c0301800580c0180000c1c04170803005210200b8050030079406801184210701e9420641c0183c0e6642c2c2c10940300d054082c0502c1c00941c0100d40d40f1440814051301030800e10b0340b58980401d0403581d083d20000998846072100c5a017540324480c0748208001e2603070b241086000c2060901d0014036546070b850b102d0b60302a0001103855241c01440d4140e100c2008400075105840040d290383c0d041c11210a4000d10042c2c40507049401100b02c001040341d0701200b65402c90b852400508001d00d403503802c001003907200110340c4052560310711b150521081c1070312825000d0743c17060000107018201002000e01d048000d041003811680100010046500d490358802d4014480e010089065103891525909a51178502007011a00c102c4039000d040c40031108501211 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 100500962 1250 100499712 100499783
    0x60f070309050f071d240a030c060810050603090a030809030403170904060501080709090c120c110c0a0f0512150901020d053304020405060c0615120601031e 69
    0x741c445d9180088065001200c00c0d00412079164118042c40c20883c0404814101c01070071090076a489079103686030480c0700c1c0c2080e000200918200068039115050b108003030b003011504581107150802d0083d9980d1624a0003c007008040070206d15019000c109643c080c503880200d010086240404d5103041c1d4001034038080c811800c200001403507501070907100340035000396650a019503040c802290040c0039400030b03820401c0858050300c00c03040c0281c4240300400c0060f607551a101c100000180d4a06075080c0ba80501c981d000341010800601c000c402c1c1c408464051b10011100441c0155680c2403500028456142c0b0000310108080150190b0060000725001c46080040b600c498050078081d041080030200e100321401c1da9030180b0130492244c40a00c610040c00546042d84901c0840d4141c1c11110002d40268011030900400d4001c2640180c000b40094501c807a41d5803981a82647d0740350306220161001401002030708000c0d902c000d03230b500307100d0704041c0016558032034a461544444001c41840c82c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 100502212 1250 100500962 100500989
    0x7050a060b04060b040e04080909040305210118090c03060603031e030c0e1903050f01090309080c011e03020d02030115031a010206011a070b04120807050903060f070309050f07 77
    0x3103850b0a2061006803910030021320301305410000422100c0e000a00140c820500078080800f140d81c681034010300c5079210340d0354aa140c034404110300d0701c41f81014407a1005480e20400500c5181030138070b6800b03140c80d0303603d0000c112150b541c100804400d01a40000d8a000d0900b0740100900d6040104403031280c20303d40641544c1d26100808904407005c00e13000c540054002003040d0f22a1404240403500c9828420040275076a641303990300307440d14074031015400700c1e80d440d846520305041d046000b43c80140850000781a144140100003094201040b0a007010b1407040e40d400880c0901c00c0c2e05644803601448800c554958440100c0f1070411024000e0400003420000e4111484800d0f042900d2110010380003002c40e0303420311000b5814010340032043c0c2103150091203604007252092090741e009901a100750007a181f034041004014000040413038040c0201001010b1244d140000c545038003070040024ac0c00c0d035448016045014207103403c40a000b520584080d504a02400b05141c811211403810546 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 100503462 1250 100502212 100502231
    0x201020d08010e0f0621010c0f0207080c060f0d06060519020d0c060e0f101406121b0a17070e060411030105090711060103051f05150d02041107050a06 66
    0x80e0310a20074040c407100c034682040444d2191010b4146550401001040407031510741d5140044150200c0200d20215a07454141d081203135600306104c094540180c0c401ba0204030704154405c5d0781c44c040704a8103809180d00290310202c24001805454413258003a0041c0840c9540b81d400030180c0d005110991020442038400c0e502031400080c1c1111140425180c921200d07030b103a11078800401c0d07034010f1610079004c2e491000111700c41c10300c50040c060b480340c00d002459400a010703c0c0c06032704e002003820703000305900c9000b10b01c090000150342c4013403005c0344168025130801c503011418a0455a000b071184510701c9031300003800407000c41c0c4c1c001039880403c00314840b42d44207402c10094666142c030803110381a0030801800700303050410419601690f80d050130f1a50140340e0030410305d0071100340c0c000c0e14607800440c0c0082503000340090760f03440e01107215010702c014280f80400440c141c011060f83c500ca030300a07110010840d100e5420150241546041c0c0c20348030b5142d820803071f454070080b10080702d40e1407410703607001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 100504712 1250 100503462 100503467
    0x8030115110604170c0a030909060e070c140106030b09010f0c0203030705090607260307091215090510020301060905040b180106050a03270605060d02092a0a020a0201020d 75
    0x902504800001800c00b903c494842c40c0c040031400c4450305540070b0420080d40000020000d80c0b400910070b0b610303c0aa580343c459024101c0710341e6000351103508009018046410380c00f891710800a0381007041d882e90803100c055120700500b0780d0380c80104509451020014144410f51015072102c01080041c010720b44004d0040340c0764801151100003040c418820100d1a04060303018014a610030004006084850803950b450301a04200c240e007456000002c01249580c4445031800800c504104405180915500c003400d44c1c201003400980240e450301e058050010410180b001c42500803000c650b00e50716214001c1000e02c0600410b4007071801c0a480501909100010070084a4980d40c011101d90030083c04032001d511a0324624205134036660030000508440001030b2440702c0e4101c0c6400981007518107003059500040806101d035102446141c050780b5003050707a95000c00300c2c1691659000110641b1040301905a590a0200c0c1d00882c820140c0c0341c000842d004498000d0b02103076440710509504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 100505962 1250 100504712 100504727
    0xa08070201050c160302010e1b0a080109030503012304090c080d090503031e1308030706050a0504050c0402160b010e070818100b01050702030102030a060905060a0b120402040603020d08030115 84
    0x1110f0040400c001400110b054110002c05041c444e00c0007141074440d601069251406807550f44244204070a080f10030317480c24445a00090080794001c0c442524903407000382c0140070500c140701c13000c820f2460110545008540c840c4900c030300208200402c00b014103210055056600501e01c1c1e511926000344003c42c010f0700710344108ca100030000c41ca408070b402c4071070b0040300010811803a8010144034065028120140381c0000c1d0544800546c0c446039142000300039540d018003200c5046140c1414040403c0002c941444603038420390f005079403035007506170140d031072010040301034482150000080341640c4168000b5010b142150344545040e10303003902c0007420049550007001c1903441412103035022039094009605040050401c20305015a40d00860309a03402200c040312081c0c0d890909001f02d50043c422282c01c100700f03840c010922424081081e50621440110a03441e4090000080c11991503400c80d102450f400b0307100451070251882c1c508031a40080c020481318488480f101a00d0354464642d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 100507212 1250 100505962 100505971
    0x309090f09110d02040b0a0b0703030501060f02030d0e19050c120606010c1b0b0f130602120403060b0402220e0a0902010801050105030709080106181a060306060c0709110a0807020105 80
    0x4440103103a02c0070403c0a240e80b10001281c20940b2964400030564900828030001d00520080581d0745001f46802070481e0300581200051001030520460700d00d50010a0301c52182180c0d200041050407600e0040c50311940012080d80f6030400b83e2110200034000c0343d5040600415140e064440c408050200e40b180003c41d60f5900180e8146580300200d50b8480103032a218403954190941c0769200c1481490303a07440003407422069070b00010003030410001e160046004107200e202a240380108410f001101e44107a2101808603520b85842c24403d503141d50440e410090480058074288076004e010703d5801199114031074620035520002002e401c00b600501d01c03050750594038080c550382020b005490580010340721000b00001e801e40483c0b409030921562002d820343c1110500071101960b020010b0b0752441f18144010303282e412145445071540420760307030071880407240c0c86d48866043c07030300e5440c01070258003556030301341445030203c0c0b1100144000c1405590641e5000422b50750050141d00b42da07002d82d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 100508462 1250 100507212 100507223
    0x191103040f1506050303070605010e0f0906360703031413060804050c0d11030c01170c07050f01020f030601030b0f030a0201050f0c120909090d080103020d020103090501090309090f09 80
    0x40a0344001826030702c124400700007140c40000d1050303c45001c6451074115040c1250003540d180e0040c041d0103c0300020780d41c008414920b551051425403510742d02c5100c068600ba885903000c842d4582600d0010044040d40c29503001c07d03000752003101410b035a480d006440140c000c0782d00058421044058001183d58921103030303588010a51a00504070745481e00180180c07041d0141c02c0c1c0000a0f540d4482e1304030741060052480002c80d0429004060a001000403298107005031040d02101c2138001c111200ea02011001e8600c0c0c8451850900c1030138881c0100540456510000d040c84402c12310308003840c0559001c4c0e03005c101c0300c421003050280f1407400202480e49503022070a00c400642c0715000400703030450a1a91507081946942615180600c44164191001404100074140b820100070890780400510300401d20b4025810010300341100600000c3d00982c6148590f009590107900140c09070355208000b040650700702e080c0140075045a0054040842c20551510341301100f034000d484980340c100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 100509712 1250 100508462 100508483
    0x504230c01050313080d0c020f0c030a0f0201020f0a1218030305090405040318081c0e1507030212160204060501030b03100f0603210e01020106140607050c0919110304 73
    0x203401594141c02c000c00321028441c0c00d001ca0b00004144001420304c01202100100e0030034003140c1e0203030900300c1d09030407038265501400d1801c2856400043d100803250b00100b6402c4004103d0004030b052200c24a0042d42e684074090f1928100007000380c142d846060103944440e081e168444c01d840f20701c030350340c0f0010f000a0030034010b110b4280b50550241e40c02600ca4241300d044c0d00c280c081e0342803c0315100d60149003150007071001c100e07809250f12485101d04405207490411f850403800000c2c2d90091303450082a00145c08190070b400c1600801603050f500440900060300c54000c041929208111480100c1c001e500384800000c541d4028040c031941590020b0150860b1000010101c0080603504d005500c203e4071004000301064851071594241c04805401351035a0303403c000d0180007070708541612030441e0314000b400c00c0000900c903210703da01e0030200c2d412603031150f072400d10380e1030700340a0034845510201c1c160a03c901092010400d40c0ca5070b0105000f8040e018802c012510070380004c480103030008610 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 100510962 1250 100509712 100509733
    0x606070317060d0c15170402150a050c0304091d010510090c05040e0703050105091305060109020306060912030d0e03040e1b0403120315080109032c1201050423 70
    0x598014070780c4180b000e0074054540f09140c40781c40030040030ba032101450b1154200021041d9034001e007925440d82c0a13460610081c20158041035003e09030f200440b90741c02001c1003203e0300921640032a204040d061f4122034490362a06940c400404185184001400010b10060a6035006008142c86108030101111030780b49011034a00144c00c03601000401c11204100115a81081840c0d05025401584e00002c0079810321040c44003501015100c1c50032800c00c11554400034100282450550349091000360700ca441c2e42002c681c15010700d0200c60391000d212144001075090002c09440d2401404005014010414440b10b440c0d01c142d00500704840000400540c00b9400e503a0034800094950005131718042d40ca4945d010032a12150310f28001a40719580740b404070300c013011703143c001d0b1107418003c0000e041c3e42d40d00a002c0c42c4640d03030072241072111003582044055054580100c4200040c200e89146045404183d00800089030116610501c4840d910140020104941889150f4600800d880c542 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 100512212 1250 100510962 100510997
    0x1080703091101110f0f100606050408030405040f0e030a0806130e0703020d0c0315020712090e0411040e07030b16031401091a0423010602010225050f030304030c030806060703 77
    0x80400502c01070780311350201e1003070301701c2c00300326510800c2801c401600d0707540e030080e00744000d442c01507118804003c020312080c800884003000300c80c00c4401c115000180c7d20038210381180030b018881c0868241d80408942030004680240c2d04920070402203c048198a140000c0b2004455400708101d580e980010000e0005081c46015070941c1401001f000030050b03504ea0b00c01051500350f0348142da9140c0c01280030400c002690390300400d0042682040d10403a8100750b2044075030a4010006007146400c40c00491781c0e41c445502202640c09140285c59a0303130307241d09125210301800e490744000003403003c02058009120b44176601d604c078050311001c0256481c1943d8100641100f0142c400e04011120088205980e03910070301c50070410000c0322042120000300c14000a14050b40540156401040b001c805244205110031000d885d541008140380c1c1c090030b0041c5050004201501c90f44400020711061540000345000c01d00d100742e8409005540705410703c1850b020340d203c0103010480c9581003500450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 100513462 1250 100512212 100512227
    0x1a0901080708010f1a07080307091503020712051e0a0906090905131407050307140111060f0c0d020f0301061808010c02030a0c060b15031906050f010807091d0601080703091101 77
    0x17480e01251420400769899110440e0300a84a48011a1240030104100300807031040f44148001400c08505052032901c8146c080010805440704010f0005001468138600340d84003007512242100413034842001c403401400320b000b43c2c010700f0b0210303800481c0094420f105008142c401c0390a80c0210310306030a695111b54030300c542c5064031360040c001c47d1408920b50300c0030081d41009100c5101260181042c40c4005003030f15105d4441084c0d00d41281081080c0c040500c030113550400103e0003103035a65603846003124020f018070200e044000100200000340b032680f080a0300003c00c00d01ca4514229640e4903041400c03a24080903c0740960030910414a13594050071500113900e0242501056400c503080000742c18955070345140745403c40100034004406442403c0006000710100c0c1001031170b0034800003524100b0318159180c10030031000c0000e070609120380c134081c00801c030b999440c040e07030520114483c1280e041261480d00186851001941c2c01e803203401982665034104260b01500d40c0d00070011207444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 100514712 1250 100513462 100513499
    0x115080307022106040c030303050606030403210207080f040602070e040c0902090d02060705010f0501051e060318060106031a01030b130522030504050f10020304060e0a1a0901080708010f 82
    0x8814498910108070f014071509114501c03404406200d141146000303001c0b560b02500c4a0701403101401000000307500240c840300301c121008000f4000400320350b00c4201910a00c0b0004181400c0030410f50500c21082d8081e1040d00e9041d001e40320b40d83e45403003401d80305400c1150050700c200380303500b0100a07900465000b00b00d28940a08143c4400e41160046920703607004c01401c85c4c842c3e44d644500c50850b0018810b680c05080101d6101456808907941c548880d03403070340f2034584603140001c080f034254401c81241c013024142142c1515204d60b50384034040c0050015140395142c6803004040e851203503100c0d1241100380c0c2c00060009136450740101a0300c0007441c00801d02c01c030ba16071014520034080b50065103c5005071281e5500d80e601d40c10300040c03000c038410001c02d41c1e00844100046600c1b090f00030003950161011442c18100d61aa410700007010705074160300c148030b20700c40703480880f100003001402080080713001e0f21140c2caa0b80300c90708102c40441092061200842c464001805a13801080c03001080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 100515962 1250 100514712 100514749
    0x106050f0a121503050c0a0806100315060905090307030206010e01050a03060f0608011811030f03030c070c030206190e030f10020901020c130903020601060f0206041103030d0603080309011508030702 87
    0x7074400200f60040b03010801d81003904c0e154022010f902c0300780b42040741400904a840040c00d158203040414904101842c00000c081440340b43c11202c080303201d60300c08030007040400424001820b081594070349a5001280c140c0050098000200e854015020f95034100c0d003026101c900b040745143c8800009185000d0100d00d0107480703c40000b000c610901801d819055485200d01446000707141c54030588501e0005e40e4040d800c07412140c40c2116010050760f91000d56000c0c031175640c140d6841c0c080c0b01502580c01c0294800c0000c1482c107180311700c00c210300c04550b08649441c1d00101c00c4804040c0e58626032042c800059201e007010007132001070754010f8a40c0e09410f004503881d80000301e00040c2c004c0483c01a4204195481c4002170616904120190041040c1c0c140741901c14942a00207440b510000c2018090a000b4403061602ea01d04008450480003c50010440c168480c41c08050b11303481580d80703203019828914500a402c0c0001070303000481c1d10440055140c049964240195030072514802c2c00d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 100517212 1250 100515962 100515971
    0x608130c0509071e02010b12070b09090c040e19050f040b040303110d050c09010212030c070803060112092102160e0606070807030908010c0305010e0f04051e0a0b0106050f0a12 77
    0x8644e1100703840c0d0240221a00082029241007040c0480e0354021100440d456215101c20010506498204d4103a01030a86000d004d0b9960007014230407510a0394841d20741080c5500810080140c2103000400f40743d12450b081c046034a0300f004070314080c4400c0c1da024024a4012000c140001d000341c5c0a5a17002c00c0034018181001402d0b101601103a03801c0342c0c640d20140002a064040d50782c1800740c440c04843e030707000d05070441c241580d4207005070041040086c02d0600010104855a00070503205a414445110511a0350842e00c0e12124003035008a101c031031a00800e10000c4081c0c008514803603140350307030004102c40c0d40c81e203102c407012400090041d0717030032040420052000c6051b40c401800d50500a8445004041c5480d615900b11030301c042c904410580340c0700060141c140220150340c0c002c0000000314810741c0752800d0150902d9640402c40c0303924110000c0f12100242c0214850710420302440d145401680e0b6107005a0b030030b206200f500d02880008110303800d10307907010302c3e030031295180c28420004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 100518462 1250 100517212 100517237
    0x5060a0503130201091a040302030706031503031202090a12020405091b0108040f050f0a0c050301111204020a0b1914070b04020d05030c120c0610030302030313080d0f05010608130c050907 82
    0x4030301b01c003c1504000044000541802035060800054000303010514040050341443c1600000b2600c150000504104499050000e4000503405035002c0840090080306000e40e40c04080030484040f8408070700072414140041d104000220b803000a40d5400e00c3c420500f03000c0b0740c004480c100c0000704121101d10001d41c52001041c82040b480725011505402000c40f146542810300d1a08450b5200501c01c1c1c0c188407a0b0110351200d0350a0318200000c07080c90b0b2000b80c9607031000a00407480c50b00701daa50000040713480350420f1161911441e40e00c902c0c0d290780a09880c50320561a69126820018201610000118006040018400c1c900702e0142040d00e0034006006c40c0b2604141c01200041c01040001c940a0101c91050000942100c0c8075411640c007185140c0c6c1c003079201e00000b032440b07403108540c810341e8080c411032000321406003100c004200b04030b42c800028040201006e02032040060184e00000e06500d2140d2944880347c3e42041594404620b000108030704000d0042404081050700070007031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 100519712 1250 100518462 100518479
    0x16090e070b030c07020a170a02060304060e060405160609030807110a1706010905060d05060a0506130221060105040b071113020d1a06280302090904050109020a05060a050313020109 79
    0x79809441c01210f820364401040c010000c0c107803140e0304140106036461001c104070038000101710600ca9419900c00f5246d948130b0a0160040c042d04120510318001c5000b0082085400b055000030894981d030081c3c46191280c4046821035003501008100303031070821411011801c0b40c41d0b040911300008101c1b846040c1c841400042882e152000c50799940e100c2d400600100600c0e0044a500140075a0b02c0c03401403c180d2151640d0f034201526807600c4560b10804905c07240c40740c1c0d040070702c1c03a920b0b258195501c0c2c80d92240441c41c00f1001c035079041081c86003004030704650300c901d00705c5048070b160342130f5141880e0b15a101c001200845040482d0b0100e401860320030700701c1050020701744004200e04c00251078000c000640340b62141400700719115070010060300c0d8040c2d5404510000e40000c1c040a00044116007000b40d0091140c035000319880704c0c000f0200000c001c0b054004044140c420340d8130845180c1c0d14800d100c100d000d00c02c04040030400a00008000b580e122140d481000d005240800c45c81c0d40d1640300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 100520962 1250 100519712 100519717
    0x20715060503060105041802040e01060b040602030414030106060203220e09060603100b0a0927120f05070c060c0c09020f0d15141005070506010902030a0e16090e070b 73
    0x561100d1003045549420300003d40104000d503018080301c4050001030b10101c081324070092060742d0310002076440000940c0404050288116101c0d0b0f5030784c0700c0c030b8041d40d250403503c149859030000310b1460100b810706002d48811600c0d103400035410004440c292181d486600006041c0307214910f000004c4008488804a00503422400540742600342030050509108800d008049010b04042d40c0ca401611541c8420341243c42e444000031300302010900c4515004803030f000d501c045036903c1d15100d051195201030000c01c08a603890b000714015800000380e5050207400b40280c8454221801040414003030104045018402c0000024031600c5400440c226007000502b007102c40300c080798850344d6120920480040881400c1107801d49442c059242c001d60501240890184143d00741d0340c104280100151005150f200090b0f480f80c0d81c48071302c07841c001d4100322996038205091090104d040c40012509800d103a90004004d00c01c00d04252444000c1c0034800d0304800e41c3c0c0300d04003002400c1c02d600e401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 100522212 1250 100520962 100520993
    0x212040c031e03080112060f050a020306010906020712030f0203091203090f010903050705010e210d09051008010e060d05030f0403020108060612010e071b12080903040506030c0c010207 81
    0x840c03005030381c154100741c040422030744a41004203442c0640c0c000030942101c1594111080b400c21060b15941514140d40a00300b0f030510681c2003800c0c00700b03001c203001954021314400c0000783d860306110b40da02c003001c99841c00a403242e03050040009a00d030300441d1003846c040c0400320316401124030300700c15440440c0e2008140900103170140c0012411601a2428407405002103000f460280411070440d01c0b241d840345007a04c02c07581800303046072090301552516203010200400300c44980303c10045400b0b1850b02d581007542c0c140300050b0040e10100d0f4520b0312202c1807000030110341e691203441e800d02c824840c1c412009402d46502000120034000010810001451507580c82e06009480350328510004d05050409004140b29080900ca54101103550082441c1140c4420100c1d0300107468010302a02c88100c080a04101030172000405814459801d4902c24124080d5540c03d035070755207141c62940c4070300990090b141d0118040004c500224040c20241c039610340320200040c605603144d65042d0a07941d0209 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 100523462 1250 100522212 100522223
    0x101418120d1809020405060f070302010b0a1706250c02190308040f15080a0b0a090204090c0e03281a0907080d14030c03040f0b09030d0e070503060118021204 69
    0x11115a8580d500b03544000e11420000b5400c0604280000704940500641905400740115502041c14800d4100d0540c14001500651700e4603142e00250041400c1946240800c0c030a99020404c8000140d0410400190040394148100180e1004440864181ca07003607030b011019400105e04140841c00540045110b4080c1d19522882e15007804840780c1c1035440072401c1c5043d4410759013101d13080400180e001240d45400207807440d81000040a41481d0f8018480f018400301c1c0110f0a0381080e4021300d110289603c0c3c01d011144008205550f6211155200c001721905004136180840405600140c1c02e02c9442d1640e900a001c2d5140c9100c403400b00c0e01c1c2651070780030708800c10001900344030f919006d800314609043c0358606141078420031301c0058290006d048002001900b404028014210541c1e400b107140205401e140d120940c0c0c980000030100c14003464034100404008001880d075080b83c0d005806400d26170b1800c404190754503d840000c20200b502040040c44841c1c4035101c1910891040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 100524712 1250 100523462 100523477
    0xc0b0705041410081909060204030b01031e12050903100e0703030807080c12071107030c09110c1203040309090501060f0f0810050f0a180506101418120d 67
    0x18504406502c440388000d4090750341424481c144540c0030303071802ea004c1c0429000310700710031800321494014210890058030048c4042404070402c505160350f58100d83c018a01c0520040301c99100c0c10460425090052400c4000c10400001d140030340c01400d100c91004065880100001812405070f400b0081d8440440c0c2041800303200309500024440e8009155181540f000d24010b81000400d10620440710a000030001c0013030041c034850045a100511060152401d140d80ca14103048442014000d107280142000340140c410040c3c0400d980102d1a818005e114015940814841d25170001e0030680c10001043d034003007210b10040c092240200107a0761071000040d042c42c0004c0040e464041d9440230000c0c51000d0002c000560001d0b0700540f1822212216003201d8000001d03d81040d50b80301c1280784404e0700244800501310f90040341b00310400da4040a072005444801c440c0545005043c0c51007001c00d0101000203400e60846035410030000d0038040d003d0281c608401c0c43c2c03070240d10f0356000040c40c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 100525962 1250 100524712 100524719
    0x11e0b0a091503060509010c09060503072a210909020a0c020603040c03020d08090312090f010e0102100e06011707060212030901090c140315060d02120c0a0f0906121a06010c0b070504 80
    0x4144450000c0012f488c00d40d0850a20510041c441c0c1c40c03034140617258002d54070750300c58203030b1328141c031003200c281d004080010600358003a070306140802907032010000c103078501c3c00000d0300c10740750013140c1922615680304106c00b02c0690170484d05401c007800603961900114008001a2038119444000310b014004150701e034580107042500d048a0f10201c500c07080c0090009070655101d05012110f020320909014025983c0f0800407440c00000c2601c55001c00d09000520a0108000c03401e181a902c0c00751121128540c80d2440300d507282e410780300d8030700182d10203004240a05c01e801c0c09940c00075021030000c44c000009464110066000e900030085d01c1014030b0032620710307140402c070a00d52000400e07094005498001c00288030100d000002034028180030200c00510f0300c091080b0001d2910040160000340e85803400c0342404140c40c02581c8405141803004a98060b01c0030351548880d920581400f180c1100000d0681c80a80107048203040c428480030702c10000701901c0c001ca1080304a43d550301d80f981d14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 100527212 1250 100525962 100525967
    0xa141b0312090c010e0d060b0d06020a0306050f120706050a0e091512010627020d090507030b09061510030e060f0a0c0305040b0a2c011e0b0a091503060509010c 70
    0x100300d0460760520003408071440d5251229081d0020054010347d00141d041070b0b03000440c00b00012603400500091000421481040c0c01d9031001d4252a0203984103400d8401c41ca061041c0f040c60781070740103040e620040080110781d05c00c5008004668852800103440c1d0030b0503000c124029000e0300d0341c1224a0200038110340c141032103032402440003110402440030a2a080d802640c104001142820300b41c61500c0200c4030302c0c0b19804442c545600000300b08044001410042d071100c1c0580421181080b03008003140c0c407402d000804038060040545000c2e80c000b030100400c024808000e80d810181a240e4100700002d100c1407040a102d081d0900d4100094a4416854002c840c1d40b200c1403002c0c1407516052102144040100769400040030000090020614464641c400880310800604180c1c56003501d00b1b807070064010f075071401003100300111002413410300c28041d01d404590b0a604451111f800b08160802c5070084270711080019400e5503255140c0c1c44500540b036040300c05c0b07240c030f030b444443e103110207507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 100528462 1250 100527212 100527223
    0x9020a0306140402131a09090406090311030c1504170c0d020705011d06130807061e08010b070f1e0503090a05040b010504120201030204091a03070b0a141b031209 71
    0xd50480f0114079240018412048940d031500a9201e0408450900e03412441608203c82452000034446403141c0740c11314048028009940b802c400083c940700e4100c01c05a0000155000600408080c0c204824071640d110500300340140141ca002d007983e00c515038061a02c100420344211503030040c089403004510041c0c5000d00070750020f4100200e0510000351078030170b03103060b8560860072a44250350303a40d11060718900c060386811010017130040c03010000311785410100d5130710582c1000c00c644807500f05410054074180424407925031014030820602002490f451000c000c0240300c2c2404407100c16a420920364034441c0204200c519030b00c0020104294680b0b10003240080000711800d1005400c0e20000070668001e91041c800f0100621400c81d04581c0242c0581c2c024211000c01000f0b8100241400d00d03050a03000d0007a0300038002c42d0004104208010100c8004003040d48552101d07603d401e00c2c2058a03840b4072080300e001c4080414491420a003440244850110340c0c0303a090490030719401c280c2c01c09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 100529712 1250 100528462 100528499
    0x1109090303010f091a040606090608060312181906020c041b0c17041203051902010b06180414010602010507110705150307030213030c080f0312010e070909020a0306 72
    0xa80c81072004129044103006854141c42d034255000c034a0042245152080e6002d589609130300070b081c130501040c020303405003509007201c016590301601070302d0300014551075413000510712070703008400c10030f6841c0001501000346006401411441000c2209031a40c5240881d5030071540042c0c0081001034a40c0c0781c1802022840303e51a24003681c00c054004026020314080d4000414603104216184900108007050782e00408451060840c3d55110b0b00e801403032584034840f0100346404c11238071108010f01c1441100c018290182c482c07450310395150301102804140c0b06199502540391811000c8144201d00e4403802400c00390000700d01418030100290006035034016510440d40001c00400c5142c7c2c40f60140701120038404401c50b03a94507031150850191064201660540c81011000400c014010b040c0c80d040b200c80005442d82081680307481503d0740b0901c01c1000c481410640140a90f81c05551703415004551800d00d600b1090740c2d4080c14017681c00c010b01060110703655000400c5501c9841c60507d500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 100530962 1250 100529712 100529731
    0x3030e01140c060f1009020c0109031103070f15020903030d02090a06080f0a02030705220603051308030414030403020d060c09050109030203030307030b21010203040c1202060301060e0d0f1109 84
    0x20030050200c03036aa034007002081c1d15503404600002c50110f0680c05007650146c0501300056545118040115001c0c1c081c060007100001c41c140e84c002c0e001c40c404400e840031160300c10b2880240f0700c6503440e110381c010400700b41034200030350030803031500265020401401daa010350030340940c0740c50600041002002c041d600c030b002806204c008001e00b90b034826103240d60040355040016101c1d1504030003210140200030b5112440c0b15a00000300c440010394043ca002c0310b800c4d030390a00c45a81d070180701c820410110400102144020700108000886004240c0602d400c000c0449040603601d40000b001182040c50680b400b40e41e0b80c0792041000d0b07005541402500382824000c010b640f540d80480d95a00c0018100c1c0c01301a6141c020080541c0c819160743c0c0864441548401e0050b84800924003c0d401550f003100d48800040700002c4480300c5000780740320203400a002030f065030301e0140d0540d442c4112403121070780503007400f4500c00003580070383c5240303400c03401141300355036252010003808140103000d41000703070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 100532212 1250 100530962 100530967
    0x30306030605090d050a0f02010b041e0c1409040e0c090f0115020c100302160221100608030a0513030b010b0304030f020a0b01150c060903081006090501020d0f0e090103030e0114 78
    0x113040d81100c210380740e0308038516142c2d0b1301340f0110004900400304072035280d034414200500748081e00c40204901031201540d401c200f2200044900a55039074841100c2032540d1502030001e162189050752110f000f0031103042c05c1d1a00c00741c0c0d6000151482a0444000000200d9100180150440c0e48c0050541c0c0446000400d10ba81d171210000c1d00314412007140310100350700043c0304220200c0703a280c041031241d8017030945038201d48600e291510020282c44040d00c42d1040714002140c3e170550740a400215040c64001e14a01a00648115202c1d8801020b00e24805115640000050040314080d0700030081817143d5030702c2e0f0030140f40c0280440f42d011100e00c215848005200082802202001e04681840443c810151448001652440d1016201401883c54450440203042d001280f052084801c04481c1c16415140c4034142c030a0420703401110b0059005521540185001d000c0b205146501070030281c01001c1c003140007480103c426001100010200c80c6682e00035600700b200301e01f040d12510011030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 100533462 1250 100532212 100532233
    0xf010605060403021c02091504180804050907090b070f1502130b340506060102060c0a0f0504051306050a090603080f0a051b010b0a0b03070f140904060303030603060509 74
    0x10705038015400081d1041801216000505c007514640c1402941e0280441c869458018684201800881ca0781070256040c81c030842403540b42842c0a81c08560712420040c201801e003414019400d00040c8400f0501c5103922003c40d0310710303101c2c004d00341d220721500300c2c400c2d10031903441d040b81c955170131400b100803250060080b0946142e140c805081510070740c8007110340342e003140d44002d0000c070a444140c100a084991104100210000d80e0009140c0518100c071016103a50004a903034010850b60b14120080601c20700741c050744920301c480140c844030b140990501e42c50300d0004d01e42070a889030800000f9a500c1c401c000c10304110344003030003d040e440381c100489403643e06e90090912880d40c40100421000501504282c042c13010358000000e064141081c03080b0b004000da000300320004a00c2c1c03003002c0c0302000007180e4014038110303842100070743d9902c60b50b0204400140c41090301c1c02d801198a0805018081807520703a031041c040114020b40c0c020480602e1401d04c80c040341c0000d4500829a04880b81d0b05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 100534712 1250 100533462 100533469
    0xf050f060103091e1110020d050708030406090206041d010e091203040204060308030108070602100b18090a05060903090112020a0f0f0306030602030109020703080601090e060d02062a0f010605 84
    0x10354440000c0c00c0100d03030100980741050642d0306400d8100412801d4450342030a00c02400d0015a844105641195040191020070f030380d00e130b00100c10600080d074104030505c0041d0101d005160050b110f40e40c08642d5400c9640001c030181c0054100521140d5070b26212066080040d00c01070051640c03044942d060301300009025143c034119034136108030880c000081811500c1e10b070b0210b0002e581104403e510f950711521080d46405c03803882441c006108082020010600500c00c1ca018004002c0030b40c00c08001031f808556400d80c00034080641401040031301400b1070018800c903407040b0b012001455880508000140c800040040700c035034041c0c8140300d0400041d400684039070b54410300b410074108100c6401001c8000d0034094000030400b42c004400000c42007443d8025181491090311040410f42d00c01c4011181030a084c419800303c290b081c03010079014205000b402c000140040c00d014a40451280301805854842194941210990303405280003c0c082c003012991070001c0c00240401e5103441c001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 100535962 1250 100534712 100534741
    0x105030d050703050c01060801021e04180903020c03100c030c0801080d0305060616030903061107051519060314070807080601050907111603140c030a080a020f06040b0a0f05 76
    0xc0d0820700c40c0024010007410300030000e580d07203001200024805e4545886170203020390021483c81c0070251660700c0d000344007030807101580c040d1105404c0035030740c25805441d0180a410318403019010b5008012082101d178809100d0303c0e098103122240071803040a140c00040c200e40701d03170700303280300704555600140618800800c56020035000c2e0311300401c2c55150790000a115100d54514a45044130410445042540181083c7c0c100c1e40503240800824010640c00641031160b02002009900b2415643c0340104450b81ea19421180d0840e10300400c05a00302284d046494580054403210081031541849242c100b0415000d40713043d902070101c040c9480c0c6066682e44060003545d20649000000841c4140305580b413031841d0394950100d41072040c5c0918004c3e030f0341c29940000d48660f0581c8140070030380e0304c0005401c0b01484000d0000c009840e042d41fa03104041d001008940b045014440002407145410452207014501800d80300030503040460102c01112007e04414803030508040030840c030000311468 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 100537212 1250 100535962 100535983
    0x209060d0303060b030f0a0c11030a32040f0503010908030a0b030c0402030c09040e01020a020a03050306061b060915070c0809040e01020423150a0c050c18070e09010503 74
    0x290181290201e2905801900d40342d0841c51400d6400b00c100304180b002039425078020b160001080004454a071421515412080070300c4040d544100503e1041d184a4100c0c0f4503240c080741c0c10075124034a90720040b80011a4004a47c4024002060500081100d42044402003104600805c07100744c80d86c1c0c618005001c01440070032142d07598610340c0b00b161400c1c080d403954031f04024002c40d034074a4002c48150759074100750301c4107015502e040c2040031000e90502c2125802c0949800400c0c14000e10f98044030103500040c40340c0d070001800d01905280401c02c0a16045100989020b0b101d10f282c801c41c041d00d00800035592452204010050101c1281c104080c000201c0d00184101c0e075400751030002c01c0180c0b02c11708180b1010361000900088030000403840d0f40900b0300310741d00c88140b0b00d131290400038240c0c24120500d4040c03104005031540c050140000c003030b1151040b02920668181180041c2d1222111840241000e503554100314a0903481000c0d43c3c1d452204440c4d403000c0c1d50519001c2641c6c1d03483c101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 100538462 1250 100537212 100537219
    0x4030804020d0f05010c090e130507090e0f0f1c0309020901121e030206060a05010302041d041406072d020d050c070305120403060606090b030a1d10050f0c07020906 72
    0x1225401440802d510111155804c280240b01c00d500fa00c0005054000303c1c03080c000106191000b04804044103642d03500b4068005005083c060709041d035820041c401414129824031070011300b0307540e0100911580c407a030302071140500b604070751040381000c1288008015404151501d2100001643c07480500342c107450a0320703080083c012452030009002c0c40c036249448140048001e01008055000420500c1080d00b0741380c1058555880c401541a400349004445000400707d800607c0c040481d50709076400790003504000740c43e000c1507000c10b0506100740c500034000760a10030780c0c0241c5c2e0b20b003441c0e1000c4806400b886070560030030b40b000251104a0503a103401005000501c0b44035460003004490082c6400070241c901801540050b9201c6a00610040390315074280800000c45c903009054620442c1d51071001107203165030b080c08481c002e0901c1c518111501011100004010300204032007890100e03403070b1000402e0f0506805810007200700424080300400c08210110042e01c81c04c43d56a00150181c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 100539568 1106 100538462 100538479
    0xe041b0e0d02130c0219030509040506060a080f0a0204080f0105010503011d0712020102032511091303050f04211b0311060d2901080603060403080402 66
    0x15001950000164520f0f0008119640000994000f10310581d25201408030310b282d082511840d094001420108220190781090310841c0c0c0c00080481c4d121381052600c0c00005c00400d0014194400e183c01c050118140700c05030380558010b8050b040540f080060118000d50080c102440f40038441c1d8209000d001030903031070f1401440c980700450042d00003641041e03800c505e03425410030101d045110412546a141d14500000b00303000f44900300c5500f403d0001c0c20100001c4103d400081c0c4501d50040500c29001601032601c0b4991f80c0c1810b040d0744a51018111a105000e50b600c000100901010445002c03641990010402845038122261715111031110245d54079190200504420140c0c440c0c815a15000002d07188031000e070f8002050340080b40c0f28200035480707001d04d04a800a5402031790b203060f6810502e0b4560000c2e00340c00a116601d0705440051660b50082c0008c1d019030700341c = true := by decide +kernel

theorem cover : BRFrame.Cov 100359712 100539568 := by
  have h0 := BRFrame.cov_init 100359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 100359712 ≤ n) (h2 : n < 100539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
