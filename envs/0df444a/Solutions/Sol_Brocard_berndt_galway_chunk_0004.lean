-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:18:33.092288+00:00
-- url     : https://prove2.me/submissions/9274c54f-363b-47ff-b271-28eaf5ce098c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539576 ≤ n < 719432 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 540826 1250 539576 539621
    0xc0304060e07030b010302091305030301050118050301060605090108010b030114040c0215010303020309010212030906010909080708030103030504050901090b090a18170d0b0108090703020114070b09070305010c0507050601030204 100
    0x71480d0003640c2c2c0c42510880e18810040c02180303849154207070000680c400d001c207580f406844580d1a8401840390310b060014407503c100090309615049002050001c0080000d550740340380251041c1e1014000078002036041d40046144a00d80054034180e48a00301e10500ca0400c001c144801005450708508c2540f081b40100030a00094020700d40c065031080c0c1c0950f4440d04140006850b01841220910700303c0d209100b08002840001411811580079500115100036141130944031441103ea0203440c140e4000004014590003200070f004603401540c03040844d81e42c90b4140780c112042d1102040d80f01c0c20403404140400302c90741181040b0ba42500c1c00f461800030036903c0d0bc416003410308071040307034003030100e5030f40f15190f111301c100c0c0c0c4202e00a0900104070700d490b00c0c82e951030b58a2030000074103001c501c0500360b8002e140d43e0252011151300104c411100d00f010385402d40e841c1e80c14801140e056003040b00c07c01140d48a00c054841c80f0750310500030009130742140e00b084081c104407071002200903800346c034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542076 1250 540826 540851
    0x905010504050d02010b0301020a080c0d060f0b030709090203040210030506030c04020d090c0501030b01020303010306020c070b040b0d0506030106050f04090602090603070804060e06040210050d060b0a03060e1b030c030406 97
    0x4950080748182e000708018540700c10068251448425518400d9106201c1800e0880d082604a5071150700300c49059699030915200d200100760581004803400052400818099400700013540078243e0ba4903030000c499921702c2001c06a2004443c025003001c50003034080c0055019400017604064014281c0d07010031542008141242c0000c1c68403082e554480c2007a2080c05a14441007010f40b10a00e418403c444040001070754030710041c48002d020f10703400a06100290b0003030000d60082c4c01c203204166a51a5108070100843d000302140154840ca03240c04100149414844d06007101d0020b00b10510903803180c000c000017411005000c1e10407540070082000d0302c6d07031ba181c002c52041c0c5250711540e040c0d0406041c0001104c1220310294020b0340905c09110141c3d036528011951800c0300c0c03500b10b5403145030b200450058203540d0700c140303d000030101e81c151442d81c06230004c030306854001030540c00c42e6540d02c0101250903e2003840240c840c1c07040001c11190030b0190001c41e0301a000e80b001013407284000c00e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 543326 1250 542076 542081
    0x20a0302040e0102040501030b03060403020307080c0102040302040908121005010906030f0204030501050a091203050c03040605070c02030a030228020604060503060102070b040308030703140f180c0306090105070906050403080702040504020103090501 109
    0x4611442c940d500003803c0c0a29a0144208801041d040e402400c1c60b1425a50181d960320540101400d80038001c200088883c4094048070003450307000c0c00500c04400300e494801ca0540001c07810030382408803c400901c100342240030000403140142d5810070014a400030540041002c0002c803200d0680800003c8003107a0709000b29400f82c5002180081c10262a04000c00c00b00d4030140364408141c10722080c061002d4000c2c1c140e0f908103402400000d0300362141e0f6429104c1080c4a58003d4241c0204ac0d4900d003415004204c0003603000201107840380d46043c9aa445039070511a680c000d40c04001031000b40140d521903800341d030384154180100d40240391a8154001e0036042544101c8001d0000000c019010754540541c0041002620a503c424202207039134460a00740209450600424170050405030b480400203c005480701a003a2041400d0443d0b00ca4003900c02212000d010403184800014882d00c6002160200d070f0700180e0081c20944603508000143c0b0000d002070f410591600444030105000b803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544576 1250 543326 543341
    0x80a0207061a030d02060705030a0b0d020d032c010207120c08030310030203070501210504020103020d0213090506010203030601020607080702010207021c030207050405010b0a030203041401060f030311120a0c020a030204 96
    0x14410b140003180a41c201031a0220049040045400c07610501251076000b00c01d50f60841d04006002c1550503505010810040103110040e5002d00d20252450905421101d2000002c0b51365101180e0500e00c005c0380202c0100d24280d660040e48886010400c60b0050507094940a02c00c035503044500f595a03a000b451600146e030b1100f50820564806c10840c0781c20081c1000404081c280b20080c007042000040c0c4424406014041c6151900000b03411a8483c0d4103c5111003a025011034a9600d5245458070001280c0103001150345800003082042d80000280e03071146005074010500f66580d900119903c000142c007810541d902400140016600c440c440e114401014030100700c403100c0350070000d02d040901d0384400c0c040c0d440c00e00140318030346402040360721407007840c14050b9480e1074500d0065a0305100101c400c00319440d05030080760080104040360101d0340255156020200390000440d164905a060a42e00b0401000604100b501903040115924002070a150f4a566290045415035401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 545826 1250 544576 544601
    0x30a050a08120108070501080406180602030a0204050a0e01030503030c0703020c030304150815130c0509040905070e090105070c02010c030c02031608010c0504080304030201080c0c0307060506010f0201020910080a020706 96
    0x2040040b1101c80b0300d2003690040507a10020541d8600e030400203404c0c40d402402c0584070369192400a6110214441c100540d41d901210440d40c914200d1015002500701c1c4c000c2c1031180c0c039103c200049804021400f02c0c16644c100780078601d0354444000030f031801c0c0e1180c10124103601900b07460b9007007a036043c07002d003005044810701000100004070004204140042c03c48081540c820201d01c2141c84044084c8800100900c0c0001c48400240064800307015040c02254400d051015810030041d000c02d04104030783d6000c1400305035480b000d80541c26140125040300019940c2501d041c055032042c01c142218038042c1c14840d05005140d00031034140700c07079000c54030700c4180022420042c0380c0091258440644103880d1107803c050a2406080e142c0c451071002038104203d010115549001000c200c826a8280c8001c6903610041403510700003030f040c00c4540341e001c6041c00040e101454018000c490310800010000301041418000660304890041e00500f1225801d000050000d10700d8401d862034041c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 547076 1250 545826 545843
    0x90302030d0c08070f0503070203090d06060302091e1504060509040303050906060102070602070b0c070f06032309030304020409030e030a050601030b0709030b01060e0301020d020703080601081506040302060306030a050a 96
    0xc000d488079090310b0508810300700b080400810401c030701e03910041e00d00402c9160705e8070a5480c1c94046080303145003d05c0d852258891080314140007004255803003102124429945005259074035194180000c1304603040c80d8035580d00c0800112402c450480614101c50b00610000d802602c4902041507204110b800300c2c00301c3daa420a001020b18204861a4006424070080c41c00c1400d0480082d1100300034414071404140200c0e40040c2881e091211704060110312201100d450798a500043c05440c00d004900030040d00301d8082d6450105c00701000d8850b031203c1c0300840c035503180d55003400000e010344007044e010041c84000200c03107a501444220680e40c002d90041c1031550440c02c2218405401402c1e031000d22101e000104001000c0340300c1e0a04603406070400034460102000030a000e48680c00700d0072119031000846004042d080301400713000350800c0e61030030b81ca682e44207e01d94941480b00b1800d544020b05110410044c54028011640f20f90064181c5d04240c025598130391070103241d0103007158901c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548326 1250 547076 547087
    0x30b0406020c07090e0a02060304060612050a0309050307050a12021503150406090902090402010f090305030307090e0901090206040504090305040b040806010303020609060f0601050702030102120a0509010b040204031a10030609030203 102
    0x11003c000000207000007101c00c01480061080c100d94810041030001d00039100800080d0900c08103901c510010720f40d1b0440c01c8409001d0f881d04544551507081c045000c682c1c1000046510705000500748181d410141001d06002c0c1801c1e00380500c0c40700c40b00b01700e03800b0410341030f1400540c0c00c800141d4040d05182504840e0404218200300c141c5400c0d07001500316904c0c0c40550005030340c62a49040d0056028207050820401140c01100c0741135050b040542144800030901002580c00880c2e0b900b1110380e80c0b1180d200340c40e814074060a803041c4443c00380d03000f2401d20041c0703c14545a400301c0c01240c0300b030418601e05503892041202e03a4001e030b407068005802903001081070640610000c0e0703005113014042c04952816002c03008039600007070400c50401c00b010882c40c085442c254125840c0312002c035003500315850301044510180600700d440c0a03680d404c1540c0403035141803c0c005d40b4166940b1108001040c03e820b0b10b4020300e140c0c006c00d187d401100540b00040890740a114061030b0a0003a4051079460 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 549576 1250 548326 548347
    0x90809010908010207080301030b1003060509060618040203100b0105090409050c0102010605090c0301091107020301051303020d090303020c040504030201021204060504020f0607030503070e0310060605070506010801060e01030609030504030b040602 108
    0x8001c9503101852503401000b80c3c2c000240c403c8110307815207030300c504d400300d442d1105031032a8402c5100c1d4000030055440e10046c400c018000144091080e40d0813284400a01e0880880c000343c0182a20020340540c40b07051042001046034001c88072004041c54458288800790700010300381d50b2000b00c107803402c2e00010a10026564280101c002070030007039032011131a017003024210103940300500c1000c8040d90b81c6d41032800c010708400d00710748281d50010000d100f00d080003042310130b05840010080b03002d480754901c0b10380f8880c025020341b012641c041e0040c00301c40071503109010240100070300071011554200030b907002850b1144100303405640500e0000442c0c0c43c0034410302411b0154510f1040c8150000c0c0030b102c0000798030608407540924603282a99090b000500840d1610311854289949079040c0b040110300168010094142d0500032801c42d802c0d640c0e81c000032400c807449401031f9403e9410060041c0045590342d00600d564074400d00e071252074030756262110080307410160380403140d607900010383e08082e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550826 1250 549576 549587
    0x80105090105060d030c06020706060801020307030506010f0c060506030c09010605030106180509070e0a0302060d0e010b040204030c05010503130501060b09010e010e03030d0e03070c03081908010501020703030305040809030109080901 102
    0x8010900020482410400f0001d400c0303240c000c500904000004210004101d01034040d03540e800d81c0f090b014400c8a49a10b503050103500102c1c0da41d40068030304000910702e0341c42215248203c0100c0d49409400e80c80540b00c180151900801d02e07034040c864007000540c0c61700c0c0c880e801c50090016030b031031a8995040c81c500030b000c4107090386c25500010300f0316024442ea540d0b20f124a034102003a801c003400303180160404500300e008603a001a5006a000c070b035409602c0c440b900710315810520381c0002c1004182c0207080008034095400042d02c0c00e20301aa060040d03500400c001d5800c80865030a4061181131550b400d82075a10346d07080349040481c0420301500a580003588001460400d003802e9540486040101e175690140c1d684a024503030301e55180503030000d0300348100c4030580d406c42c405404449e00e0b03082543e4564004440c000844200300030155105105d0700004c0d0503684140c0c083d002080c9192000c5010b01005002541c090100304400302d0740740d078244540b420891083c102c4544904028002414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 552076 1250 550826 550831
    0x7030206010f0303080109050a09020409030503011806030f02040e03070506010303020a02090603011b050306060403020a0807030b090a080a0309080409050708061201060605091207080304030c03020a06050703020a02040506010e031501080105 105
    0x12140c10b88020700000707400035603083c151109404005469a01c8180d0640500344600380603401038a8200032000b495484002141a19148140711801001500c801000c84020f480094110b806030446a4010326054000c004900c032440112401d0000b152101800e04e40d0a030310403409640581d0a500c1103013030015500307901c120210020840c805103014522510110b080c1000e00300000000003603100c0d9915030a03180619005480900d1990b240c401440daa0901400b00741e0f12000300c0d00006090400009030503c1c0c140d80240c01c80e051000e18007090740a41840341007295869001d010105500342203101d4240701d94600c0c0c4d10300805003003403070500c20b070003400295415559042c00030900030b854100044400c050000d542c010040203079055068280300c0320350481c3d141400300007030000c1030143e84c10f8950141d034000c0315120706440ea43d44041d582807044100050158210461b1a0050320705a4003581d4800c006041610000700071310000390904403c1c004030034000180c40700601000c8800d119155 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553326 1250 552076 552089
    0x3150306150f010c020a0902070605090601080a0201020a03050304030c0b04061b020706020c06030406060801020f0301090b01020d0905130b03010e0d02060901050402210102090d060c080906040209010b0c0715050703020601 97
    0x810025000780816251080358082606029540c0c200c8030440d15442c000b60000c05640b0811516183c003490300c02c01621058072801c0e000e104000c00440c80c0100030482c95a4160b0513002020844816601694903802c010016001d000000580300045030000c400e441c421449040001483c4611181c02250504085000390855008610a201031740e000100502c80005c1195820340b25a241d1074864040c0203aa0440040c55002003400040d6020002c091030684120360418451448000b004a0340c98405902200001d2a09201048682400c10080f00142c5a0200124003540c000e070220b42940c034010040000e6078020301c000941154140f2a02c0e400c40b2806000307112a05003900090030648a06d0340c00307600b94044c0a00c41d40104025030464072100806000c2c41125103180c240b441c0182040000356010845040004030071210100e000c9220315401030038883c2ca0390a00d10342ca1041e03000f410030315203039105907400071600206074041040c00d0600c03540c81030340d116a10300d0020706107601a4040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 554576 1250 553326 553351
    0x30308070c0213020c12070308060111030f0f0702030c030d020c01090504020f0403030e01050d110304060509010e060109020c0309060d0b0a05010507030c020603070903080a0305010305060603070602030d0504030504030803150306 100
    0x4000583e1150107a80f0080c3c030442000d42c46843d0001281e04052144004241883c030020740d0404040c0c101c0c2c6a144516026264401180d407075680f090384074422440718000c40c0d84100032450b003a42886d4040e0803081d0001d800ca42000c4580740200707151211400b4000c000d039201ca003d00c00e040da44040c070140500826103065040100c1c80c82c6074402402540401024031001203144100c5074461825100b1031a64030205100301050340300c0300000c50f48103590507031300326040170005000e500c0140500014945e50307000500407a07113004a444001d4100c1400002176000400155100b0782d00c0d08090b00d103900404400088807440402006011440e80d404241844001c2c070000010940000d2400001c3e43c0503624250349a440314001c66101c04035800042c20301c40042002d1320743d1a4507500982c1130381d101d00b08451140d2640002c0503074600981c8a9400103a20801c0103803070b0180c4940000750003c0c03007130400b01c0c1056240e03030310f084a640044502e010303100030f03800d80d2549920301082415080000030b481c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555826 1250 554576 554597
    0x1e07020c01021c030902100503040303050c16021011010f020d0b09010e040b06060f030403050a02010f06150c0c0506030403020a0501061a0405040c020c030102130302010206090303010506040303080a02040b04030b0103030807 98
    0x1c0c0d1661869030500280050308083c0180c054001d0300070407091603006010041110366105e005c3c00b40e41084d0f50940000b03243c070340000e08403400b000841d11119241c0088840c8042e0590810180a0245020701c0400621075102c0400c2182400b8441001d810400c0240e101c3e00c580018200b101c080c4c0c600c09101c0c2e50a040100908800c000a941e0019045060b04040c0d564140212b40103115002c104000f0702d83c000100800d040e4064060010f1140c0c560007400444030002d104000c0e10703600c2c01503516944d82e818056030014019004044814450070f01e400040e955100000d100780c008a405501580017050a401041001c1c41442d0207020a01d851321400c4a03914858019030141d0b019a0b4022540c4e000400c0c0954020003503400790060080c0203668a84038402141542c0d80d00340310172405441804040f480000300032003900d044e1280503107143d00b030034659107013211500400307090080c1150b0300300030204000018400500c0617500030070a043e40f951441c40d0041021000a02d43c8040240580340c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557076 1250 555826 555829
    0x213031e03090501080403030209060307050702041404080301050409020103060302040603050607020706020102040e060607020103090203070b09030d0203090913020d0b04060203040c050301020304050705040f0209120a050c01080403050307140706051e07020c 112
    0x42e0405848082ca42448107a0356803600b40c3c000c0c840c103286036038820790110800114139407040003018198400d071400d104c4440c0c8041030107481c040030368000b408444e0920052000342030580c0045c100c1d81c0149000b0a030305a032070b000701c0e0403210a81c100799150342082d82000320320340e0108031039801071250740700851510346481c1ca948101c2d24050032540c07103144000780d2401560301c26000135041b03540043c00d655801d682e031003041410350300000105000740181c291800030382d8000320075500600000b80088038141d85040c5004510448100100d03803001059514102040c07448240724844d6100b42d40041c1d6070700300390800048090326076002da88039a004204004c0003401c042908800c480c0c040d00c0120f20440c1005202c03001c1d005185010f900640005c0f20501103040010741074840700c2c0188250b60350003c00800440d02410300b21b4016010a60810120b10340500c00c2c2a0f502d650001600824140f50696481e281514400c1d01c41c010500d5229401c0704000140719402c03034020000c0c0c0018a2564042350 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 558326 1250 557076 557087
    0x20304061d0c0609011101050907030309060905090402090408070c06050a031b0c02040e01020d0e01060509010602010501060c0b040c030b0a090308070206010f030b06030a1703010f050406030b0402041e0213031e03 93
    0x40ba40d0340101008038204005901030081a801856800024820380ca00954000e40d5005648002e90004a07400c80c0090000d00420802d005d4031406000301e0010341da00c1e001d000203964060021288210b0801040c030200d1010203c00b030140480e17039034070f80d81d4400c0084001c003950380030614400b10301d95000c00f480101e9003004c0c00701059541940c0208501d41c01d24002d6009018500d41d1420050a08000c1c032a6070b0703010b42c0f0030026100c01707c81384089a41c0307a520403800c841090242c0780100d601604110b0104a1004404c1d61280c4150101403404d0303142d0b603483c018480284ea011110b030703440f28004000c043d001000642d00841502c01030443d03624003048140e10311440e1001400108000e00032801c5030b20b00340444042c00b500007082201004040321900b0155200740725415282c60b1081001ca810b1134940521012a43c204070036007556282c039000c020041c082102062041c000c540c44448c6d811200b40054290440c100216808041c03071424013101e00c3c904840c1e0302000d000c401d00180002a04003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559576 1250 558326 558343
    0x304030305060103060305010e0705040f0c0e0105070c03080a090806060102010509030a0c050c0306070801180209030d0503090a06060311011101020306060d05090a0b0907090606020a0b010302040b0103060302060d020304061d 98
    0x18500825141c460b6801030300109440c1e04081c11550074803502c4007209200041000480e03c1c00e0303504111004072420365004030707030440c4100e8000403004d040602480d84200080c2c02403d00401c1d0000140d6641d83d1111065404001014085056140c0c2000181400d01c50f43d07a210380280002c1c012407030040e002c0b903243c0c03003256152403e1200e2421a94244141000b04241c008000707070864403281800840070302004c03030902c20385820407040c4408200361034580c000c0c4c6100c0100a4001c017107841c01c482e800c5c3c034590002407081c2e032a88140721100c030102d0300500440005502501010080180000004051090031211402c01c0d82c010400d2010719101c2004a40400300980c000254503182c0303084907404c0c403190010240c4480e811805000005001040880480d50380c004208420750340e610381607071200842c44c005008c1c01c0c1c90000400c0036003401c1c0c1214440c4681450300040068030ad030f0028030650811506008003e5010080004100c40340c840c05500c036882404030043c0340c2e10148003d5880317450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560826 1250 559576 559583
    0x30d050c03070602030408090906030708060109020a120504060e0105010501030606050d0914060c030601020610030201020303040308060301060506070302030702030111040503030d09030e0d030309030905040509030409020f040f030804030309050301110304 111
    0x34a10480100c14070588801d142d0252042d0360340d041504100d2126003003400a82c1c41034100a011a50398540001e0990444038144040e00e03890b03280c121058000c0d0424007500301030280b58004e0304020705603441424420f51003003800155010b8845102401c603513051300402c1c14986090700c1840784d290050b0035203d03800940080418050301600d0f0980f403a1207a00c000c00c88030f1007520188804030940d40040c520644081c0e08031906599807aa4920700610103201c0640907030810030115020903c1042c260340e026402070004202d455403040850420390004005030016000072480c0403c6140a0044150b0150741c14a124101401d040000b5102c0c461084107050003035132410000c00709805403aa041c44000c0041c004892a107460802502404489030200d00150580c80d01182a2400748201c90103025082c00541c00c05042c1002c2100940c840d80310050210340c01d0000260b40144c0076850800345120700195504e8a00d98070b4003808624850b000303648240d041842e2604012500310a0f40c0d800b540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562076 1250 560826 560837
    0x90d06180b01060507050607020604030522050a06050a030e0a05121e041403010b041e0b0a050a0602030406020f030f0d0b0f040504061a030102030402090103030e15040e0105100201020702030d 84
    0x3036420020622605040080c50795078a100001a03e54104016006140c0030703005851040d40c1d845401c9071240c104440050204409000c007140501d030b4041040b4050b5101c1c00300708240390712800044d207085c1c00d50b0720480c005040042e00030302c003640c10702446400907144c07030090040f04a03130760310703107444401e048032003844144046903940c1d000d2a42d2030f0540d031240c4281c0321070342e40b191100c9404144480040704070b4020360070001603420500301441240317064104100c03058840356184842e40081c00f102045554070007030009000c41c1e996110743c89100100b6041d0015a96640b82c540701074108518050601c0c400d07003050001d040310109400444600c070004034030001e8403800802c00261440c040b001c8040c1c009251504100030820f1542c0000ca072031004c94941e030410b1868204241c01c0c0c0c4000c41c1c0080d004000794004200203401342102c1002c0d18001490310a6621600c0540c410726049a4494902e8549500041015080103101c030104950306100a43ca040c030f00340c000c0b03aa1808221414003c02c103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 563326 1250 562076 562091
    0x50c0901030c140c070f0b070f02090601020709020d0203010905010605040303020703060b04020d0f05090c040902030709050402030109020306090105040308010501140901080408090a0603020403021302030106020a03030203040501060e0f0406060b090d06 110
    0x144512a040c880643e401c40d143c3e141c4420401d020380e200624002c100c442902004007080010000090f40c7c1d01a51164408003180e920303070300f03000341c811002c0c0c8154194844d08401043d240514005004641d000d8400140c90350324108107901524010307882441404800c200900100e5030200f51001529080711010901610460102d40217110701429500c409103007218803880900a80c202a004105e400d0481700703001d85d8003003088111445000b000358140d119102c20011007109270001a07000d80001c0000801d0121900441e050050458070001140d54601c10802003540103200e0074054002840c0c848400c1040c1048070501d0300c1505070301c905015220300081c08100c5140210b03508468007a080b80c80c035580e10702000e4080c5d00300740801c030311910400d822072080030700c10702c02d0742d04a42e910b5001301581c5c0e001e078505134025400640306540e6552141030204100041c00480c3d80a18072181e0322408a25042c02d0102c200d03113451304150412081005060b08607980c0d0740b140c86130300d9000003002030700b0f4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564576 1250 563326 563351
    0x10b040207050d05071e050d030c02030406090501030509010204030f050303010e0106030902010f0309050708030c03040e0105040c020706080c070210050306090703050402100f020a1e03110c03030d05041401060b09010e010201050c090103 103
    0x310806c05103200d01c03600c403031161402c010000c9080d10398980592030070700c00c42d600410142c2c0c5030700403401400c0015803901010080c0f50310076000039400c080e008000500d05500c1c0d450f08007856540b43d50994031a07000000420005005940080c010301d0300d40340030003090801f580004c1c480c40200369107208068540030740390140b00090103040018140801200e079141c0e000242c0c10748030703005482481808148600001900d040030b0060495071045940a040c0ca01e0074914140c44060300942001400d803c02d021034001a03c8010101d80c1648403510340946a00e0b0101c10080e41041c000c10030310800d8200780078800140c5800b905209001d0040c00c101d01e01000b9000c0c2245000c0301d005005d86049201044040c240004011507054070340039130340e807034020307485001825658030300304a40e07540507481040320341c07210703100c50340455080352180744007482d40456004c045003903e802e60441c801880c4000b0b10103a1a6800400b20040f000c402c1c0001e0109207054040a0030600070603001c54149074485282444c136 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 565826 1250 564576 564593
    0x108010b09120a03080115021c0305070c0503040306020403020f0103020903070306050601110102030109090302070807030506010603020f0903030304120801140604050d0804030203070b070201090905160f020709180203010b040207050d0507 104
    0x40902c1190350748507150600501c0b1140a108010140340102c10b0340040500c08140c1195a0260040010b6800c1e12603208400800d00101a00104454100500005801400280000d5008040c0941c0342c40c1540104820031702c0104815062510411055409440109880302100d40000340012140c0d12000103070741c000803a026a5541c3c0d4400400424440202e920007015035010360700302d40b241c1d6200c440c12540d54101c1c1c0070141c0304d139100c00c00400416103e80c0041040c121101c500701c0c10810001c010034617603003080c0c034119120319400843d2580c4907400444940100459140314030071420341004116948201c1c0a45c07070040d620900c07210b09100074581107034011075015040b03c10440e5503881000e425000030604034000750816000083c84502c50040601840d01682c44520800103183c0a075071009002462000f54000c210300010720465a00c20070380c02e0740202c4079a035204001c510416003100c605c1c5217031070b220328418420a030110700b0004000000c260f86007031442d41d41815003480d466 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 567076 1250 565826 565849
    0xb0703020f04030b0901060605030408040e100b0309060f0c040b0702010503040602090307030819020303010302010822050102030106020a03140c061314010207060902030606090c0306060a050c06070903120801050108010b09 97
    0x44201c00140081008a00182507115255100c020485142c4807801160903100a0350060314261080c4828081591840c02c0207070000c0c80f2101c0140c10740c1c0c6e50580014250802c071240d05182e00200c04215504e020301c21030961013000810254503144c2001d101c40e66034003030083c01070704000021000508000ca1981210f81990000f0211201030340c0d41e180141d41540109041d9140c1101c1100d504d00c2d050000090340e0681e80c1c16107030344e4503d5030b8207107000400c0101c0c0c540b0840c2c0031520500c0400424070070f200560103842d495014140c05015420090030f450f244407010305007090100041c4400601c081412604400c20022407041150309007000c0c0c500048a84000b01c0c0c40d480041c0c070324200007150380f01c4c0301f64610a40640711643d480c0c108101c100c3e4001c41d1340c40c101354000c0001075950701e07000d4000c100328002828020300b00750f001441989040011604a004190714903030a0040c04142c8003411062440d510700b0301c42a6051100080c05600103225250040ca008501103d103030307891525004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568326 1250 567076 567097
    0x20a0207170705031002030c030402010503040501090c06030b0a0803040b0306090601020313080102030403080609090706030507090f080303010302090c03101202010e03030a0801051003060303051602150703180b0301120b070302 99
    0xc1c840c041d02401e2030b442e15210302ca00c80c840e10654201d009240c00781d00175240318543d00c10f0300d01d0840d940c6800550b1b55600082c02110655a07034100a40058440d20000014201c00c2ea00010780400c4235003485104100e03a08880003941c41400100a04080e03001166400f05d016698203102d03807103c0d00141d2660080050249510031751010104d0b07405030542c09107104600968803040c1c0d64440c0001d000d0001e0003074800c0005a0413140c0d060003114005e400060300301d0014035001030400c0c0d88629442000c0031980140c00d4540000004205500d0205c0501d504400140111443c5003401d41d000030b100c003814400c1000500501c00b546040d613000c0c002d0044d11200140a50342e03900c0254a004000724004d0007090b00c1880c5554185007454441e200350b10542e581a180c0c10702e000350038500103d003105003607804c0b070b030242d00e8003149900210305201601445100b80c41340070f0b11164a02410304081d1054105d4070488500303000401c00c0701e16128100d0348464008203281d0042e151032404602a01c01d400000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569576 1250 568326 568349
    0x604021203040302090103140d05090907080402011817011a0102060103030c020402040e0109020a030e0102030702030d050402040204081504030206070c0b04080a02100e07050406050607080405100e04090f06050906010315020a0207 100
    0x1c1802340000d1043d100d0100001695500f004502003954280102902107800070203410024500301c0c028081940c0060050524080d505c2400c048031403107801c9a04407048080b1072500b081c801079001d000c4d86a142c1c01e4804801503980c440c41c0000d50f26401440b01070f0802c004c400d061130954950b03034122009022200c94071210756855a0201000c1e40c0b00807040b0300040e14244040103c0003040c0300b41c0780540041d9020b185001500c0700f42c400a017101074000d07a030140d801c0000049101041140c805010711070001c1815520303190038041d00b8080010a40b81c1030143c2c101f0701e100000d0884d4040342d446540001c85d661660000c140813842c0c03c4004c0a00c04106160107423042c101c0030002050401c48030200c1d0b050003070039242d509000356800741e254028500241444107001174904101200c134150098501003202c20313000f40000b01a59070071007044c1c90f540c01719402e41c014810107004240d404450030b00105030340d516565480721036109451a159440d54045884004c40c1d1003801070100610600464 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 570826 1250 569576 569579
    0x3010501060314130302070b07030302040503030c06070908030405010801050103020a0201140103030206010503070f260a06020d0504060b0409020108040201030b010201060806090d09060c030203090405040204060302060c01060608010602010e06040212030403020901 115
    0x24004080300020180114004400111040b203040c13028205141c0c5940a041c140d80303880e42400b1a904455412000d00d40c0a2002251580b0b0030000303070864000b031500904041c14600000307030003200150001820354104000034041179800c540c0e0a41124030a11f80140e6a12038000100e00529603c0c3d4501c02c500030140c000003e25900240782e03030594008031f09403501c040e51a400c0545540c002c1c85030b51510700100f049036a0001c0490a00080b401707203181558002500f5903903034022a400160300c1c0080c039580300184001d00440c0c0c81040140c981c140c0c2e04105181694001800044c80200001d0401d40c076144213154a9100303400ac60018003d640884020b82000946652504910315440c4006039046500085091050500a030903a802d60065031401c0000c1d014000903100082040e41c00035103440d0000b0040e1580c2c0014425407007040c0000903001e0411400070405241a40300e0011a81020500070a24001003174031504198112803541e01181c0c83c0d10b8150550045600103075001001400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 572076 1250 570826 570839
    0xc0f0703090302030105070219020f030f0d020102030403030f05010503030904050a0204050a03080c0f0106030213051b03090a0c050108060f0405090c06030f0103060501120305070b06030c0a06030609050c03010506090907030b03010501 102
    0x2594182d81c030880091003996140102280d540e030281081114042d280c030307025000b60a1020910344035480140542e24401144c0a9030352a00c240c8035030550041c1e40c000104014154544a09800c03420010b1003800300d07500d0300000a68038086c825003540305da5640e4004c01c1428504ea4112001880d0150184800a41e01d06001c1c0903030300a044908000c0c0100c1903850003400040c410101600e50060071205000c5615044030000c280041c107410054144030000c011200d07a00000c2d52065001c0d01c0100703003480c514034014074000f002d03500444c18403040c9400d0107550750303e8a888030701300281510b0000c0c4030ba40c0c000c2c800341f40285121101d40c20102c00001d01c10603803c0c4050890680e4004e20041c091a40c1c2d444034203e90040300c200c051f001650030b105040000d07004800c56038005c0401030891b1903001d032101c005500d000342d9034800c80100755242c0f81040340904900540358003500342c120745401d6600d4200481d50a00c5807000052140042400140380b09001e036000c41070600000d8007c120641e11140b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573326 1250 572076 572087
    0xe01060609050607050319090801090c0501031b080c070c030b01030309030b01060c05030304030305070e13020406020c0102010603020a050105030403090e010b03060405060607020109060f0c02030105040b060906030d0c0201080c0f0703 102
    0x900d00000c48511010509041400403207036500da00800841c0b410341c6100101ca081600b0116240c1003061070707400094210024040e49040034007131403d44070380510b4440050704a9120381c4100004071403504410301d8064205100d6684403102c25412a0b03198114640401e1740130180d00002c0038018003900200c14194000e40b0003081e81d1003803540715600d07601c0700070555441680040040281c1c2c41000002e0000b84284c00141d04480d950421900c1e045403035000070b40d00d141c0c2c564621030165020034100101b940c100103140c008007013070000b04221421500868071030401d50003040e040c00300010210301012b120f4001800284280b05507519296101c0c8400e00c80d0384e00c203840141c422801c01001c683c83d441e101040300d584070340c161100703e812803820030107950801c07030300b02d030501842148000e072800b5072428001c00344524420b103001d410a2600788104a5101c20140810b8025403000d0a081131031030f0040c0c0500720841e02424540314075900c864668005101d001704040300004c000c03e00400701a0800c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 574576 1250 573326 573329
    0x7060203010b1902070b03040206130302030f0a03021b01050403020915090901060302010f0905090a0509010e0d02030706060e0106020604060209060409020c01020901090e06030d052101060f0206010602030301030803070e0d02040e0106 102
    0x300345020f044089080890703540305640a00540a081080481e005280c03080c01496420543c2484400c07203641d903000241002c1075010045c00f60780020030365404266050010081d20b0b1640c4840a11481c503540000300240203030b000081c000c168000200e11600c1840c109101d030200002c02c101040c0c5000742c219030103080b107440120301284412a00c1b6940c240188a040251140584075001c20707030700e00020102800010b014104030f95a54100e642c14000c1c240320704d90404500d074008540e2455145041411200e0903481030009600400050205c0ca0b4040303032031074100d0380000300903848074030000008106100d250f000d03424440c40052110300c1607070b040d00a17205103c0241c944042969843e844920121011185140d1513001060382005060140d0302030300c88141c001c0724120001c2d1319469443d8005400780c01c1040070901880030700d41c019a041000d1805020036101440c00d551566a480c04d0a02000c1d04001c180715510f03140d1f20468642c0d1a0000900c2e800401c248084156030300368a009202c075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575826 1250 574576 574597
    0xd02030406080f070c030c0303060302060409020c0609010501030803130507050310050106080f010515071502030103060603050d020a0803010302100507050a03091401020705030a0318150206010518040302060402060a0507060203010b 101
    0x310b80000b0b021040d6512064460ba4894440b091a4282582d003280d00c4182c03c00300700c0505980d030340080050b0715840c0103840030f015000c0005a0303030740380744881c6403401c04010008491a0304200c01400001c031100156a0081000107828901c5801d80c43e00c94200103a54111a80600c200341004070404e101e90419412260341ea00c404070140c4594030181840c01c024044d8a403c400140c40700c4d42c0361003000d0f00401066014043d5034001621082c00034080e81d2081e80b090329172548600003407040c01000e220f080444d01c210b0006043c0c644041d51102014041444060705c40c0d255000d180344036a0084003214840b40d07010080c0c1e09413aa1525001c1d00d4940e643c024034000c4030000c100b80e01154000030315001651001401040c04520940e0211440301882d07507403484000d020000002d42c0a00426000501d800c150050211903052000380024540c02104a9180d51100300600c00800c0d008500c050308203405960482e56201440410765140c031628000a01003480000000384c008000e10107090007908 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577076 1250 575826 575837
    0x20c0607080601020a050c010f050903160503012d020906040302040203090106030303060501050a0210020c010603020307080a02040b0402030f0601120b030703031e020102030405070603050a06090614040501050306070c020108090109050d02030406 107
    0xd42e08012680c549034648018655440301600702059030081c0507104040704a0300e0003a1802c0301407000b10b8240624083d0720340c15000c06460a0040385020302680f1410005850794580c54be01c2422420015980082a4008141d00142c841c2281c1c0310401154003560300a4829552030a242000728024051803000750b0000b458100082060361180049440d5000c0c1c903401400c0380d542400c007582c000c1d032124148181c0b03903598400000040c0c906115610080c0403520160001511a00501041e00d107131031050740c4100e1040040081004049007507940010080c03906510040ba001402c2c001800c45030903880d4113215440f4000700301907000f104590800d840700089141003541a03400d07401d03800280c1e1b008044d50084801405010711940c8655402103078040040382d2580c0d02c3d078070f2004560103500001c0e840f080c012100e0040b0701382030254500401c0c00b81c0043c01545003620b00101082c64800000b41003080041c0810300f030380001d401c002c4a00d600107040c1e98444101060107592035100d44107140c0801c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578326 1250 577076 577081
    0x4050d05030105010f0813020306040812070c08070803060414010b090103060504020903030909070504090c0306091b0e01050706060807060503010303020f060403020d0e01050c06010801020a0e0406050f0d08040801020c060708 98
    0x3441103064030304803101a194000b01c0303026031000740c1e040c0c0d200030102500103492100020151340c0802803180a40e02540c00b443d90b0b01c05081100050700b40007030412041c441892029000a12410112042c16800040c181e0322911808000b40107403804562141d007100c800070000c11040345d014020000c1500c02d80302045103940c0c840c10302043c0d005140b140c41d03050700306010040340c0d810060341160741b040503840d0451a058503680e0050480b0b01040040b40000d40d585814040c4842a1145040c0014a500c0000840c003500740c0041c42171294200d4030307040000c007107003c5040050b50307080200030303186250035140c149854a130000c005800910081d8014800c41c04020024980071403843d02803501a0702030005419000c81c25503100e182c554440f03040110812840600406c24802d89000c1c140140026039120750213a402000240c607a030b0600e00c41c1d0301d00b400400c0f00b91b49203890790300c042c0001e4a400c901e03074000d070030100700078050b561102c007203540001040400098003089541c42140b00c2d0729041c4064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 579576 1250 578326 578353
    0x408010c020601030b01030204020702010c0b090309010e0d0b0a0c02010207020406140109170703030c020d0f0303060e06011103120a02070206030108070501120605090402010e060d060303050304050d020c03030403030507060b0603010e0405 104
    0x9140a00c0050304d0140c80d0170040c005802d0a80041000500604000000080e0740ea101144d1500840c0c1c1d00724281c2010800000540c1d00416044040204956442000010741c4903600082e0002d4400c1d000140c1c1d4043c078090362070003901520b8940b40c004000b0400c0a90f1148a0744004a940e282b003400510f01130000304241c2500d060001886855800030032a00d401c5960603944540460030503a440a50b50300d8400001e03441408c410481c0c1e20954020490520b13103401034918100251a65041c045015840c0d28003c5001040c0c8891041c0f45070360a41a44a070000b4800034810044041e4101d180040082001000040c00b281100d42c20780e64444003945100350174080322030350301039258011016400300e8003540c0b0030003c180080b5402014646029148001301048854a900440104802004000c244501405580700c1075016001800e14a44041d0011b40c5901c0b4501004041c00008503030b0509000b02903003d40c5a03140c028201726640d5031109003140300002d044804450034810f400c800c030f048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580826 1250 579576 579583
    0x8060f060403060501090608030c0307030c02010507080309010207050c0301020a0f0804020a080d05031b040e010306020702040e0105100e060306070207030f14060117010f090503030601140705010204090b0a0f0305030a080403030e0a0501020408010c02 109
    0x1c5103000010f1070404cc0181d400316041da0460400742d04100051011102050070b2400450240314003000044c0c5d0307a0f07a6494550f04084403100c04601c243d1060241840c030079044502400214003900e0301041a13030b281c2c800120320641c03075080345201c0d1042180c0d02c0180e940140007140507020340044540e003a403000440320694496070050920700c4c162000104001403194000d000c001703100500100380900c45031005803c440c404c880d503404201c0710034070801001e008590b030150400c1065016222624254001a40d284804d2000402694083c2070310011b00c0092141d41c40d01c1e5041005075461542c0d02d070041140a181c4a1000c81c09500c1c05071800781205070342c402c0700200ea0b4020050b41c00d40d9552001990603005002e0340d4104001e04002c4400000c00a100400c00381400b102c0014010460206101c01c4040582029401c040c0d44402480414000800d0b11b0142034207240c0145281d450b0720b03044000d41030144040805101e1001308804201044d005401034900300710003042000070385401243d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582076 1250 580826 580837
    0x912080f030702010e010e03030a060909020303070b06060c03070506010e0106020a03090b09010c0803010b030f0907060207090207080408010504050604050f010b01050d02070302010b030312010509010b03061008060f06040306050109060803 104
    0x144000400000036024003000285501002500002135104a5401c0060a40d401c02c941e2402c40d4200004200200805228400103040060400c202c000300e01c2c0e010941d81c1c800c00074003801446186001545594540c82110102440b100659031510554917141b40d0358102030203020241000000003051140c4000303220b90140d501581c1e8a183c080c41d284614182c5e07445403d44c01e0404c8140103000005c51092002103000b0200191030742d41d02d10301114840403051000d80904881e80022104010080d0b0000d0f4290036191144001a5940c000c0d14051a40e4480c131350100d1915401d100421007031000c017041c500c1c403581c041d2065401141480f1443e41c00c0740c031640f900c980032503402e01561000d00c2c4594041c0500074424000051992100c8000038550f40207124000c14940400307006002a052039155079006001c5104c07500e08604040c00010320516040500d5801c021202c1e001841ca039450743c400080d503140182c03045a03100d480341411000b509090051203040e070306003500041d182800200321003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 583326 1250 582076 582083
    0xc080601120506030309060408030904050108030406140913050103030c05010506060310060e03010f060806040302010c030203010e01060e030a0b070c06050f01050f060309030405090a1a010918020a020106030b0403030209010912 99
    0x544501c0c0489100006101c05000c0d02d0300b40c417003800601e500e501c0d031800410281c0b1110008540380c017510010481039460503044000383d44c200b8003080001581010700f040e076501c0222074040e191950321000c1019240c03a54548513016080c600004185504204003286443c001e00090109507101c0c010700001c0d06c000c6e2413004500c21351b0441040352910980d42504240c400a0000c01c5149003c0d01510540301c007900580d0454015506100402d60248150030807248203041c25030841d0301d445000043c0001c14806d45091006411940702141e50901c0761003500d90f40080340781514241410010214581280b0803203411340340c100461200c548185045041304da000b0b0041292030f824034240415500b014080381c005100c10701c8042aa82d45403c0b000d4070414280500044e202d10542c1b05215811110300d0081c14051900c800307108400c060050b251035011010b00150344e41c461210100d00402255002415070204c40c000d00081607455001080403000c240d941564080c2c0300c9142c054821002940207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584576 1250 583326 583337
    0x203030d020d0b12010c09060306030305090105160b010906170a08070615090903020a030807030506100e030c03060103061406030304080a030f0c0206030a050103050d11030702040504060605060d02040303030c080601 94
    0xc00c081115400400d42d10540324000328000d104140072820364100c02c03000c8111651200c0d00c840480b680402020010842c0380360070b02642c0d04d0360710090110b20401d1310841c10008002880d1100c0c40e4184100440d01d80e00680c40d08880d81c0d100300e800c0086c0032034010408030900c0ca000e840c0c82d214001868040154000c0541440c2c440a0b0786c0310310013002c50110162035418400000550741c00948a0070705054000e0b005020743d90010300c0d008086c0390f0010524000d0500c1c0809000941e1180448404044903500b406035040c2116030020f8580404112156890b01c2048004020040c0e80e41280d55110342c0907005049603120342080503101c0c010360003000380c243e01c2124100c0109102d48803110b060203407802c00d00c00324081038000c80c4640d8000c6940036401500c0390010410020100010a904800384c50007414046540390748070f460b841600400b9200d20b4a41c4003240034043c442c0c1c82200241030041074181d540c06c0354804000a03411038031065001c24a40031041480d40e00401e90f041c41190141e648 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 585826 1250 584576 584587
    0x20303011404060b0403030203030f070309050c09040303020409020f07050d0309030c0b04080d020a020c0306010911091207090603030f020105060301020304020a03060504060e030307090302030714090106050f07020303040308070210030603020303 107
    0x103120481c1c612104641d440b50f220000050111110002000030b14001c1d809581d507454200d24000c1045406412002018500115a804070744c02103248464051b0454402540c1e444906045002c0c1c0101d80290800c0380c4009000c01d484501d480c02412820700c281d09032501e48101460136001c41d86550030260214400c0e03200c201c00216065030040d8028840c02c4a6820582c01d00c140004a81004144001603441b2006441e020300e002c000b41c600510764403000380300d944510810700807280541540c4c14000e01031419182d02084090044d80080c002d405810410302c2d5903420020b210000454004000d9442c0c100880d01a08060084034403e80d0040c2800400d01d05c1c5540da100107220082c420b41d50680c0d991070100309098280001c60080708a540c6800d051070460040604000b0241d00c4034101d0f41c5101e1004005840b40400e09045601d10f042c1652201c1201402d85000d11070558000d6240c00006004420031061030050101c15009452a03600c1c031102100c25411a402c5020180d0306a2040c0300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587076 1250 585826 585839
    0x30503070c0302010906021201030605060306010503030d0b0402090301050403090e0906090706110102090301060603020c011401030b0402010c020d080a0201060f0504050702120c0c120304050301050c07030503070e060412110102010605030102070302030301 111
    0x101e4145091082c400050151480d403a05001c030703040201258120030b5101c0c0104203120140c080d072908150300f00e002e070240c1e52510000940d240b01c0d141101c07061a840310f000680e031799910303030513a819041c02a00a000c0351420703190060404580e400fa9641c04415800498440440012002c0c421030311080101034a80c00d25105403404141440e03045c90664003003100c00344540713003801840014030203501c0150701c840c44541c103d030a4500f020044d0881111306001000859910b0341d8864000344c085c2003105030940d841c0040ba41c90b074850900982100d9000a20310304050f41580810200d80440c100e00d9601c40d00c0303004100541300c0a9956070010b03400581c05007402c443c00001001c03c1c00d00c140031940300030f08140200b1100c044240e0030b098031350000314041005084c03e0040380da0014807803451600d0840d0555010b019400083c1c43d50b0200820f02400114507144c00c0201c030302500c0300601c51550703030015140c07402c0c0a2103509403540c01542404030000399410140241c2e05100d50540186055a08044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 588326 1250 587076 587087
    0x30b01061209080a0801050f04090201080a05040807020306090309040605010801050607030f03020c070803070c080109020105030a09030504050d05010207020a0806010503030403080c030409020406020d03050f1303050306010216090605030c0303030403050307 112
    0x1510000220364076002c001c00245041c00400802e80141c0b0346015640c54203007088492211020402d014a00300480000140c6c0c0c8100381c503500105036400000c02d51240c0c01e10099a021b8030304025054401c6034180180e44c0c0e00040035204002c0122800d012181d2107100444a956080c440e10f900f0600c240450400640a81012014058a0319005042c600400c0145103040443d42c003501d03040d04002041018002c2c0034290030050300812009000c40380103907000910621000b0724402c3c00e195160811300030144164101e0300100710040080001103c00c4c01c1481c002d5100c1c600880c403030381d0324900000302e265003ca400303812030307a00130083c1d03003803d01d1621000f80c10340c008003511106000400010504e0085803001d0000b9100950090001c800c02403070103000c4410161000040510f80c800f08207414140380c0c01452040d5051900343d46a03141d01700181d00e00f66010040405601508a000c2a10009036000c402100c3d070460440e04860141006c0c142c03244000e86000c0c00086042001902960007075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589576 1250 588326 588347
    0x20f010305040218010b0706050901060f0b0f0409020f0301080f010506030309010309020a08060117070b03160c020103020d090602031006081003030c03020f0a05030901030506180114040204030506090d020f0304030b0106 96
    0x3a080c4d83c4000e062100c8203014040c240c12010b00080040b0b100024482036200ea6076018100314003c010300350400d600d084c0d1000041c45000c043d503400103188115070101c0300580300107261403d01076440750014541000242c100f405090743c0c920445959248941c0140101401080c000e8003961400c0044030046000d8400390200360303004000180d001034032200800426009041412280320b414410302011030400d20194045c504685007481448507450300d00f1410550760f01e250400d0741c00c0800510058001e80904d80c241c40080c2e00d045120021701401da00214800c00c951020401000e07104c81040d500110281e43c0008034518090302400000d01034a0400042c034000e0046400059518400c640ba0507050082207a064001194403101c03942c06002c2c00b41c002c00c0841e03c001584c960304200800c01b040522810101110402c032552103500c50341c4c122000366410005841041c5440c540c080d5583c0d4a40e2984001445003005540e9115008400c4d0b80507280c0c424082d001c41d9107080c0040700c01c078000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 590826 1250 589576 589579
    0x10b100e03070302060d09060b01021605010503070905030a030c03181a030c0405030307030f0201060f050102060412030f090602030103020a0b030f0403030c021e06090d0206010609090207050a02030111030f13020f0103050402 98
    0xb6110b001c00075a4505c006010000403a04000c01c0340c00b424900b00f001e495444111a05540c400e0034940c010f100d20f45c4c5003806960007840d0240d16980c0b112411254010703140d00c429014015502854181a80503288040b1139000e519010440d000803050780f911000c0a02c00c12024469038a00c50b0381c4000301c0801581c01c6050008024149503c0b40c00207030071741d1f0001c1c40440c00300b144140000005502030084000900c87d0b4011820101d140c03500103521417a005200411141000d40f2260213030380640d0103904224041102045003074040e241243c02035100307010580c03240344080d03c0040d2100c0f9090071a44100309420594410351070b075a400354060721a40c4410015070040500610b80b045242611854100707000005081d241003905180f41031103075240c542030440d00180b006002094002c007a240442d0403000c0c0060b42d425050070b049052503243c0da0001e40c55400c2c1001c0c40344124441c40514003030400215071504c6a1191903568017040a8103d00a40000068017840c81b598040d131304c01540b2500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 592076 1250 590826 590833
    0xb06070602040b0417070b120403030908030712060b030103020f09090703020d060501090b030f07050f0607060507020607120b0108060108060d140609010c0302070b01050603040f12020a020f03010b100e03 89
    0x15034400c01680c0141e0401c58a000c07000c5010402e040f032904008100c1c891304006008507a01300320ba080424030030305c503464889221007404101018443c0e44914040360708561381940b00d0501100c01801007089081d040b03840d80c1002404114150700b03c04490407654010882c0a1840f80310b814003903140d000400304681d03030140580020143e10741c84100c0f05014803608001400707604001915044465820000307000741c1c00460300400208000407008286c2d10102c03905100b2800c044000380c000c0c494036400800f090300b080d0a111506800003030050050449494200802c003101701c0d400101d80303051200300c0c006121407012032003d5000380b05003034003d00003400d0340520a401d901c3d100294040200c5524a60b40140304101c0c0050003881205846115460300f0351070580300351a0b17048030640600603148102c5002002c00d0800060482c0030341c9041c2d2100748909003a0295801075201c00d0800401d03030141e00a22194541403906219100100740020a500d140000c00d8004417004000c0c2d5040b01e40611 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593326 1250 592076 592087
    0xb030106030e0f010c02010906050901020702010c02040b03010b040e0105060405060d050307030e040608030a0206040203190f02060307020f06090106030209060402040608070807050903070305010b12010209010503040308060102070e0c0702010915090302040b06 113
    0x401c0c0100b8511407170540010135505002c0c900081224001849040183d105114460040c0e921508035003016030102ca012a03d0408040000d00606204903d1503209150194600c0850130642140d403181004a4081144c0c1c0d9403007051219506e000c14000741242c1082184200080c0142110000c41d24003610001d481520390500d140f0f5680810342040242e44000c00700f004503d01004100322480700301d103024002240c41d540c0c0c5140c0d82c540349402407251102000042c60301e403080003002900203d4004542040c1825441a07008000314001a801240c0300c0000032418101030080b501200e200355145809a030350b0407811034075120090444010008100900300c416034013080b4142c0654050000050f00c0d0074810200040131b15840e0481d4940d0340107102448641e070304401525482501803c1141060b518100100d007404090380001c80c1c0700f0010000e010341110700b5405010f11f140b003a201c5d852056180c030200340e0242c021110b101c00048541c001072006044c90b822481054802401103428907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 594576 1250 593326 593353
    0x6020a140301030609050105060f0105040b030901020906040f080106060201050f07080405070801020307090602061605070f03050409090f020f0306061c03051c02091302030402010c030507110406030303020306030c01090b030106030e 101
    0x9a01c207a100b6104e1a07161404031061040c2031291940042c8200c03617070000b01c924600042c0c161302640c40b4021084002000040e280d500a40460711401d00084c9000c3c2d580343c442e0034540000100d4091902250300c6d055000c140703130380140f003818025140c42c84644042d0307807000e10495100500410403510b50140d280c001401003002d0000d18001d900c04e4440c1c140050409030000d113071840090140c111003c2404041802d503030010100d8a80300e4001d00c0141c51248203041c180e5492041f9448007400c10325202c1540e080c000c020712041c403080c1c4212140b8480c50010003c043d51088141c81c100c3d400f0346400250818010301d0302895511510a080c41400d140d400c45000c409448502854642240c000503440d0f4149419101211106a12101182541000c2d0002130a800200f00c1c01400c1c040c0001d200700070300c050101207843c5500c00030020700c80031b5240d1800a000c0c0d04199a81e9010f48108582480c04d9802855000207469200308810b05583ca0140220040c2c03079015a8103045018105901310078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595826 1250 594576 594617
    0x619020f0d05031e0408030103081e071101030b010c0203100e01140f01030506060307030506070302030403090b0309010b0108010503030a0203030402060702011107060801030b0106030605100e0102010e0a0b010509060609060706020a 101
    0x401e6400d0716041d8480c83c00303140c0e2841c40814139070307040050780c149410000004c4040042d41e055a80150760705840300c8494240e062200400c20b1986100340d0085035200030048a203224058601003a03805110107003100e001900c1502031017400039415009420032a054025603880b241c100c0c1e444500102c2c0300404040191402e4105603480000c42203204011300c14803504201040c0c100c901034004004651540d2111030711aa00a0840d80c10190000045000e040c0711b1118040500300b1a0712840d600c0c28468642c034000c0070f0143c1c140d070114010300000202d074074004c026244000344a8018514580c0d4a60030081a07070f0000320200d0600c482c90f1145584c0d040c1c10071070000904543e44401d1038950540c18403540f28401680044205804c02c4d100f84600d4480c5071900f500c1c400241002c491120090006030302610380458001c02c10301c1001a018240100124890704840040d14101b50310740b035050602c0b505105500311150030004c01c100003800142d0950041074030b8080c0d89000040c031120141c2c103540 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 597076 1250 595826 595843
    0x1021b07030209160203070b04020105090a08010203060405090705060904020f070b0103050a0506060303040302100f02070e13020a0f030b0c0c010603060203040602090f0a06020c010c0501060503030a03060e07020102030103020619020f 102
    0x40940c8848000d0045060a00ca0190042290306020f0380c461aa108002e54922554500405004441c00070801b164011425260795200061070580083d86070441d1500030b400480b0303040c3c40b032820200400c40c2c10902040070740175102c024007a0f83c5003603000e1040c00003950004410344801070040140002040ca07085140e40694400e50250000c0d40c03070781c145203107011806002d0502c00d400c10041040140c1d41e8140c041c2c0c01c0c003000d040050101004140990600701c082d40400352811252040101c41e00102041c2d2045620854945c850303151140f441e140407030b02034000280203500300e0001c036801e01040c4000d4285020814004220395840c0d503142000e03a0020f460442d441030300401e940741e96181001200c4501c3c002901c1581c20a49050301c0203507202c0c46451041c0c18800d410861606019081d04204058031000e000c49503214181c0300b0040040150b4802c44203c0c3d025100411030861041c002c0702e04980c4c005010318101b04200a221900303020060b040400d6100341d40543c40218400e000007078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598326 1250 597076 597127
    0x405030f0d021510050d02010c02040507020c03070b030115050f13030b01050a05030a03020a0b060103021e04050102010608030c070302040209040608010c0c0b07020705010206040803040215030f0103050709061410020102 96
    0x20440601c840a49020640d0f10070b45040300c0c08000b008210581d4480f0202150300898032540715054074001031b100a046c0c50750294109080000f080001c6d90006102da11000b01901202e07205603892100e690580820b02440c00c1c001c1020b10703500e4a080c03144010384114220405060328080f206e821644412850390b0007141c03101400c400401c010300d030005041c4010081034000d00301000d0b081e0f90081d01d6034440703003000300a00940c0000c10302c03076403083d41a03070b64041402c000070300390102d02c0b1180710080d000717031169500641c200701d4040342d900008001d842c003000c501c1c0002c00350b031b50940c0c1c03c01c0041d4110301c41094005030384101c001402c2c83c0902460200401c1501c0300720702c04040703040c2400307440c40007001d900940d4840e890403c0a664006a13203548950032003451030300c903102c510004080014502c40018548004000d115030300d000560054109d902c1182242c20181c1d0344c0f0000d40599503544126044100e124000042c0e600700581d104c010000d0901c001450403c550b049650541004030501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 599576 1250 598326 598333
    0x60403030f050709030b060118050303040602060603060a06030b040b0406090b130201020d0f09170106030206030403020f010e0604030507060c09050303180103050a020306060301030f150f021206010c03050406030b060405030f 98
    0xd81d660041c612405800820a10705800250708580302c0000c84a030141c070350f90401c116807108103c0c5003200a80301d0003801005003526540d076a1000025520b507400c0c0c80f01c61081c007401005c1414428184103407400c40c2c0c0d01150400942e6600e49400700c00c101c0c004c0003a121a62521200c50002d0404201c181c4512540c4902103c02c1002c0d0000919001080c4000c2091040400e910081c03207030440400d10845206000039084000002c0500780034008560000b5004000482807108158022440c02c00f07000604008010644001c544550744001c165000303804680200800340102e441c8d90843d0b400746461b0704050510350366950101e45154840003041e0014003a44d903065046683c14004c043d0030440e6000d0943c00c5003400000940d8622061200a06190140c2c0049007001003805140079001005101000042c035121202d50181d807041145910101c2900000b8510350301a10a18403480e406503200350030a414281c058000b005c41d0358800b0303800001400001746980d0104040c1d0807049c0c0405c0034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600826 1250 599576 599591
    0xa0804030210140c0c01020408070905040b0c04060e060f0903060108060702010f0203010b09010302070203070b03010306020711011d040509010905100603050c090103030e040b0607060e0a020a090b030601030609030e0306040303 99
    0xb400c000c24140100c500710f0902e400d00c003a441490400c607410a0044030304076941c0e405a5015030080c401c5904c505840c0c0078018000440b07605960100384a1070084001e61500d03507402100190030701ca1070044201046031816451a58100003029111022441050619104030314002a103840426840690700d681700310108001c103a42809800c031107035441541941554103200303201d9180e0154415203810560302040250030340d9400c1088400401c4440c8103541d80b03586134204100a5844954161104520340c4286001035124610340c084040ca0b2003d101c100602c04e1b42000702508015100404642d01d0ba151400481e01c144401406003144060001d2030034590b182c42d9040200381d01945100d03061100040012a4210f540e80841107812240000c1c07481d01013000a030140141b0202402a80c5003100ca142d40c000002070b0400c0c0c4d5802203030100303103076aa200ea4040130380719010003c0c0d4154120400410020b140b82d081420f03003502c203041c9090034810201c04030380790810407902540083c1c4c0300c210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602076 1250 600826 600833
    0xd06030302010c05040302180604060314030403050c0904020303030f040204020f0a0509090a0c08011701110a0f0306080607090b09030703020603040804060305060603040201140a110706030902010305130203060105010813020301020a0804 103
    0x803e90810f5103418900d0a00789103800103070814030100b03100d244030403030000001d14655030f650000000d10b901c00410b03051254100d0760542d580d040303400100e5032407052030a034504c0c514186020520940c0d0040085145d03a0310b8103480c06241c2c001a104036009078007800000400f182850240010b40d400384c0d121500c40e01c0b25020440613140140881490500d0000010021a400540c41f415100840c02500009010207880e0780180785200030061031080104442c501a54481105003240c0d00c550f800340445a2661182510741c08107a8854011a101c0042000302d42101d40c00f801d501803000342500d000a6507500862010351049904480643d0005400e010180e00343c802c46030022400d49103a811454541e0001e403910410170084500031030045080c40e80b0501c2920003015668109080d10070072030345e512002d130251035040c1040703000c24101030009040041001c0320f00840d136001402490a64a460015103400c94041c1485081d6000101e50102680f0240007c0034a40c1c1540c1e074000f200c2c03800f0304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 603326 1250 602076 602081
    0x7060f0501140f040e0d0f05040306090c08010e0105070f0c0501060803030a02090a090207030e04050a0b03070305070602010b01050f04060309030215040b040606050108040b0a0509030d05040602030106090501050c03030a02090d0501020d0603030201 108
    0x160614402d03072070031100246800b800034001c0c6c08910207040020503c0400c550685440c0501d500043c440e5080c43c1120080000060b000011900c0081c020b00903041d401c04118280c0b4011920000020905c40c0300c0610301c0d128080111138a405040001079503902d8130381e0281958000c03591104080d80000b00000700e4100f08a44400070281e035a801c42c1050302d03079500101403100700e500c8948116210700206a00c0085036101007990b01d4001c04642080c4d5030b038907010791188030900c102d90255103004900d0b4582e500410845140034200b5200360300d4030741000e20507401002220b00c298114840c0d9080b20381140e403151003190080e40907030682c12a9142601c0d20b801624000e811003410810b81100340800180c030000301a41000940d6400310710780e0f890408031840d501440410300a024200002c2c0414030500b5801103040e43d0f407a6503a250103030f4680c80150303014800c80d40d03004665842000003986c82030803a800750640b0b12001b0301034140000c10361115426038005001d481e010b56650402002010b4092 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604576 1250 603326 603349
    0x3020307050a060906120212040308070905040603020a0302090709050303071109310203030d09030306140105030402010203030103060b0301020706020c01050604060504060f05060d090503130303020606030109080a0507060f050114 100
    0x1103509100050500400078144c40795881150244088200340601d0081c17203405880499862413050a1203282c54100108090340030307115400401d5082001240f5420140030744002c0e0f075005000701038124a0369080c0800c142c00100701ea01004140b003030100e0560350902c01081d11a01914600e0740c08004d9400b00078200c0d10240102c0c1c020745203005d264101011501d61140c035108001d501e10310010a03400070030b040d4072588640902c01c43c80d11000e1f008150b0164040c3d4103035280201c04010400c079000040d01c85100699000c0d015900a200401c0011540d400c0f41007850809000035040050035500c2e1000da070081944040c269450740c0c10070049007028480c443c003c010448043c003105161040c2070890300518055540507500006081410401d03a0b00701e000c6441e481b100b100c6d9650b0768101d0451a00426000880060080c2004070300303107240c14090003915680022680f03140081e640e109646640c00a04201c49190326440f0540409186224142c024a000f508041950303d01c0410442c154484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 605826 1250 604576 604579
    0x3030306060e0a051e060a1701050604030201020a0b0405010b03030a030e0f0105040c0b07020307180204050102060f0702030a0c030215010906080106060c080405040c0c0803010b040302040507030b030a02010806011205010f0302030705 102
    0x111103440b40c29a5445001c2046400503035044600c58944a1800b03500c201c003411042d000100003a0004c3e905510031009519103001c00070101043e600c80c801c000d01c0c1e22441c480030740180d0000300c40c040815021019181c00c64892000061101c4180b00840d06541099181c10040b903030b03400d40c0811940052008201461116008000600c2c0c6940d49174003d40007030081d070080c010003241c8901103480c100032000c080d080c41491141d0320b841c0340300004003035406802618014005d04020560500c0c03030b80040b90040f42035802075070070b0103030404d0101d070b4194a105007a82184180c1d1520b60550f80e001a4550113481000b40c0811140e040440b8a400d403a81580140204007118105002085591050381c040d5081120041885840310900b1101c1d8011150050002c40c4000000184009400000c0c0102d03807080e20180b143d0f655035030042d0308481e101600140c064000c249800c00562241c0c05580e0300050504051107964408a181001c48000f41c00039040702042800030320a5140401c0010003c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607076 1250 605826 605837
    0x1020901090602010507020703030f0201020d020301080c0307120305040302090a11070302010518070302031209010306050a06030903021603050a0f021309050105011802030915041505040b040201090504020301060c03050c030706060803040303030606 108
    0x40c010340003596503211744000303000c2040c0c1401d05c1cbe0019100b074049421182d15100300b5500c95071030756000c40d29081c040020030310030b210300600003c00740781c9000c0c3e4110322a09511801c0c02c0a185400b806aa44001030022241d295030300d13503500c030320100307103010f0280c0c6030007030740000f0300340c9406905a10904803029494181d548070300700070030060781c00107079904008200000307060b1078551100060b000360005422040d03105180d4000800c3d055416070152030014000d500310b650a0303481c42840780c501030087c0400307803468201c2d01e80c9a000c188680b80522190703202901c1d8200c180700885001c021034110a00071074159440e030004020090300191402c5210845030030443c554148000540e54840d038281c000c10924035414000740c00d0060414100003400f00304d0100b4051481d01d4680780c0d114400880e800ca011070280300340403485041c00d2082d42d05036404ca441c1c445188c4015182600d0942110b080c1002d941700811010000844500a282c02041d200d001992581d08516014040d10f60300c0c3c22030320400c80d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 608326 1250 607076 607081
    0x1050105041202010c021c0308070807080103030905011b020909010c030506030105060a030b0903070203160e0702010903080601140412050c09070c0b1801021b030405010306050102011404020f030709090302010209010906020105 99
    0x704182a1802c9665090a02a480d98204d1002c2440290764000055148104405d440300b031582000c40c581c46024159203c005c26510340e070081c0c0e0b40900c00c0c000900001c0d0303804014030035940200195078145115041d14816030503130b580002e0508600b241d40c156039175180c040c401403141d05809210b0f017156080300244503a260a40c045480d140452202800503d09603010540481e401d1045590301600541550300340c1140742e5900e0680e414a11810000b2030703254001855652040c0f142ca007081d40c0c07540c2d8000e859241d860045904c0303601c0520120011204100000707422103880c0984030b0041c482c10140000e0700540040019810f0010710741401c0c00200307240100040c010600907036105800d9081d000380e0f401d407045414020b0080c94020906843c4420348038036030500000180080721400d0380c05110054940004900341d81d1000b5080c4907103c0c107500420010325184101c0d43d607405001e0304489202d9914080340083d200c0040094015035400904070307009507030200986001e800c0d10300007413000d030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609576 1250 608326 608339
    0x3010302090f0403050403080d09030807020303060306010b0c0309030304080604030306050a030507030f03030b04020a02160501050c030313020105070503030406060f0b040503031204080405030a0b010801051b03010b0706060e01030605040203060105010504 111
    0x149004140d0380440b403090b00007404042c000c0301640c020715004518641c480c41c10319031540083c040d1050540c0410421b0b00041c00041c030000403039100c1c5030040d000c0e0510780d10f007180001e85908011500d8020340014000580d154070f003080a4002048100001c10b20381c103203420007078122034541d04068012a122102800403c00c00144c4a0440c1d607c0481c03410241090b0030100c0040c440300c606164428000501c1c5420154005543c80f48a4400d00d05080b0540d5200015207251185481c41c207040c0d041480018801032196046034000c1d8018180207140c55460fa5070702e8119401118100c6205a58000500c003410400c240c100c09882004031481c5000d080c000005c0ea203002d6400070140380308801002a041144003000d4900402d40903048070312800541c544261090b07024018451150301e0040000e0110200800303411071842c1d500c007102c2c43c1d40d00b081500f4040e948091003d0341e180752642d1000038540e00703075581c40d402580a01c07000103132420148101810079206078000ca040010500090003503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 610826 1250 609576 609589
    0x20304030308070201090b01030609020907030506030712020604030501090b10060504050604091a04020d0605040e0705010903030c03111509101103010519030501020a05091306030b010b030411040905100b01020303010302 96
    0x140c075058140340002d0fa5908000301d0141c0001d1100503c0d2104070000042008526045801036030b108942c101065540c10100f182120f02c21982183d06a2100c0710800c2a4401c01002e805402d001400092406441b0384425080d2030704007600f1164440a0001c1240310000009410060884c501c2c10340e151614090000f00140600d014000c9425170341c5181107072484262000000000303001d0800c2d0b44030041910f405004004511690b4011401e09107400c03652000482c8a40070380c0c00507198480c5060540d10200c81d00c1103001e000301d09101201e04100c450410412407400341c40c0b1586460300752031824076600c90500107940c8007d08640e0a043c4100542d201e1602541e0541d8005d54107150300050444001d00041c103540d1000e4001d520001d5002d016982c403400a0205204c1a2026072030b0250b511580c2e811220700d44000382c07008031742130014440c203002c00d07004580160180f0030f010140030702680010216040c0c88803c480384c0e8460300d824502d4110b1030240c40340384002400070f1421985548c005c07404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 612076 1250 610826 610829
    0x2010c0602030603010207060603080406020106060309080403110102030c0105130c0b070b07080a09080d0203010306110708040302040b0409021c050d020708031603091505030901050a0501060c0308090c060c0601030b0601050901020304 102
    0x2003940100010b10651400d42c1904c40e680c0d00094244145a601c0c10206200c1e03000d0f0140381c0040d400c4c10701c04207865029024421481d0f5000240910f03080c5145c0319683e0280a40151030304602080202d40d0b070441090190b94054810b42000c050f240c41320f440c0c0320001e1001d40e80400c1000c80c050060300d010a441240c000d9005440341020f0010f40c6c1e86100c158001c002d98103005001110100d2038003102886940598140c0307108182c10409001c0c0c2401c03150a41c080c000c0001d007410070400c0305000608107030b000794a075904081d001041c01e11866000481101140100307007038001a034680481030200802a50304040c480c4d00240c50030707900785071115442e4420510041a0b000c40d80c088070080510a1203440b00030b0088480c1c2000d0002c0c0302c003004000354415140880030b5070a02003c2402030181c1e00c500c904031586510390301644000c40d681a903a01100400d100440e00603040c020038a034071844000c12200c103104e40030b0b06056046180040c0503c0020340a40c2c10820309010000059800208460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613326 1250 612076 612083
    0x10603140702030a14040506070302060105030705040204030506150112061202010f03020a09031106040803030903030106030e060705040311040b03030c010b030f150708151003090302010b04050601050313020f03030c0604020a06020a02010c 104
    0x5541c407620b017454078001d202c1c81d400f040d086540010030b50245940418514141c0f2411001d80f111070b40d94000700801d03400f440c080a0840d40028010810361105000c2000c101031041c18622650f13503448150108541450744158809954446800110769000d01c2c0c0009034200b0342002c43c2805c400c4c00f00100024685d00004101e858441a2414190b4544042c1c40080c448441141d9607031601001898482d0428800e900c0030030300700090101e9004012442c0d900c101c0141e0b45003030070140f0f0b50302c425180d650000ca0944d00182d8400c00b0f8217443e1801c0c001080540000800403407071031032080c00c2c546001d00e0300e0454003241d0801303541c6251002d51709440341d801039020301c1e0002d81d60303c4580d20300d1690320030504c03841c3c0d12200741d41d6003540442d015000b402441d4040c0e0003c01c000cdc4428010712090fa042191042e000070340400002c0c0d12605d800004070341d4240007400660b050070107040883c2c55a40120002415035000400304030071071618030350442c0984072501c06484014610307400a0100c282054005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 614576 1250 613326 613337
    0x303011403010906020c0a03140a020d0516060c020106061812020105070302070806040b0406051503060601051b07030b0604060602031602060304110d03030507020c01050a0207050d0804030b0103060203010603140702030a 96
    0x12901a41e094103c641c016401c110110b42d6502c0300c81c0c9084c1e84a0795080100d0204286100d4102240f03d400242c8804082c9900075080b10f6580b0401295540c1c0200e18070318400c5642c041c0c0b0808a01544610651103100d50000640310781040005400c40b0415144141c0000d40c1c40c00511140f503201c0400e00d0816030a08025803107a140346426814841940c20611040c07080e00d0800c8184210680e120b40101c0c080c440800040c1c903040102c020704001c03070440c40d41682c010404282c25503c100001c00800e100f44c1d19102d41c100c8034281c658285a07a03a4003e80e02007841f0301c14480c9601c2c05100b450000d00c4540011440c1c030340841a0400040130540b80644110000700018041c40f256110405220300020001343d46030026140144c001c0c601540c100e001803052a074800d030030307501490072110740071a1034005010541c40c010400c480b5120fa00001c50b2048014400000000d0401800b5400b0b58440d0310096260340c1402e4005003102c00704202200e002d0706910a10420070f030013200302c402030301880c90032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615826 1250 614576 614609
    0x120201030b030a0303050103020405060f0108130305040b0a09090606020106030c0603020705010605060c01020c07050a05030a02150d05070f02011107030806120109120504080609060103081b0703020301060608040302060601090305030301 103
    0x5a004010419106030903025105003c070070198140d00040c10b880c82164204800d45072441484240200342010701c6c003180007000401d02c9861440040160327603100349400307407400e61203009901060700441400d5020500c4608180842070040c0113060262030300388001c010b81e86c5161120742c007102a074410003092580c00104c04050020a40060004d000050407ca5a0f0001240c505000b0b5004011448240c00380c0a00401e0030301d080348802c0100c07400200149040c05c02a002c10885c003180c0e03801d071b200804080054251704905400b94610421480c0c452200c3c0c410743d00740180c25111a025000c00c502001c0103288000390308659203a41014081e210203000e402c0c00140d080c01402686800b03086440d2071114180300b0740c0d10100034400d1b00c0d213203000d40304280c44030110b843c1c2da88401c1c08010b05e500424008001010a03103098031706c07404209400c0b2410142d481d000f103821110160003150004c0c002c40204414540c0400072660891802e1800d1044103103161580c603102d01041c003802143c88031000d803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 617076 1250 615826 615829
    0x3080105060a050903010606080601030f0504050c060a030b0301060f03020102070608060303070f020d021504051005040302030303060409020a030b010801020a03110304030906080907030204020d050106020601050603040c0302090c0c030d0b040b060a02071202 112
    0x240c8811080c045d00800425440b08800782c1414012078060303001900b807801d00d0781c00d003443e8041ca40c020f0f039001e8020410399480b102040300d16084024028105560b902103180303103680c00d0055400034880303000329084c6035056000080c20b00440780c01c58002e11640b20280304080e180042298889600b000c41d4422061171440041c1e0014061200079520007241000e0f9184007031040001d2080340c0c4200d0703090074244140f99042c1d8080c003c52002940c103410038800100c9508094100e010403620040c1554002ca449544040c2ea6405c01c0c0c10424a90794081464400213805104258004000001c0541540b400c0e40c0c009010102e10700178207041000e648080b07200d8002c1084020003031030740100709540b9012015400d1008000900c14000103100c0d002c000101d908184081301e0103130750040390f210300c070501f56000e02c907100744003810302d03c01c418080282c4001d00c50f0500161074004a000800b04a1952000030041910406041c2c41c0c421b1100700310301581b0a800040450441d040c41400d204803403240d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618326 1250 617076 617087
    0x1050403060507080106020c010e0d060f06120f020405011706040204110f040308070c050405070503010e0402010504030204020a03021e04150305060f0301020703090905070903020901030308090a02060406020114010e0403080105060a 101
    0x144018640e82c01c0c582800700ca2900310706101d0581d40c032a4210364050241c040112841010100c000d50040c012400c000040340154100000d0300c42a030f800803803003647d10340d409901d943d904482a1890028080c20000b1417526010340c900401701c04605080718254610000c0c1ca40c44041c000903c22a0760700051031101944000f501c03100700700e100c07029403266540e0801c072050f5400340c00f0480e10b441e195031000c40c0501d0580701c2d407800b81500d07a803801e0460382401d154221007000a841641400b409000c0000140d495000030201c6160a507000350700d03005800501c902002030301c0c81001c1801018402403140071144900c100110082c4c2c42d0125103a201c56010842614020010a0f01540000342c440c0515800450f49411241903a804100a81d82d084013114640c0f4640002940900000010008640b04402098200c002602922520341280e070005d060307a4442ea0180000d80d45543e641802000c40e458030b20300412500c1d64405561506681c014809030050150074400e400100300d00416038840c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 619576 1250 618326 618329
    0x20703050609030d110325030905100902030c01020604031409010306050a0b03100603020c03040501050306040f06080f070501050304050c2806020c040e03090d020103020306060d06170c010804030f0806010504 91
    0xa8aa41d41085140d06490b42d20a1140001c06810000500d03c1c068000e81100e04c160708040c001e141d00e15289003e044c0003a0403032049410152103650040100d2030902a1140160201c0c90004c1c9901062051605181680b5486419034022000700008a07401014440c100c0050301c0060382c2d900320100042e03000744a25000b641d005074800c007000c2005000702008500803101d120308000c00640e221021801c2c3c0c8600e003142c2045804c140401c201c154003c4015503000032000f0300c0801d00d40640c1d1075071421180254001203203503001c80c807505c180d04801c1c40881c025000c00c3ca080d51039031500b5144c0e16610740d0084101400303003070540030b850070940491446d191005565400d003051595110740c0299500040328010744118504040d401040030000200d5041c0c0e00060003440080c2d445800640081d04001d10191700301e481000708808c00384142c440c880180c035145900300c11050f20080c42901e041c001e101c469040c82410800d103c04660000030a00080e072052400d40c1056a03000c004a40c140603a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620826 1250 619576 619583
    0xb090a09020304120201060806070c020904030504080a0c05010306090606080c030a020408060405030702040b060304031205060102030d02070605011503061809020d02060301061706060f09040506030102070b040506010e0903030606120403020703 106
    0x700920003044500321042d4404c0d03141e44c1c02800107585902455807100009d03206100450100100000141800b03400c03250f01034043d04141d81840c2d5038180c4241030600307001c000c48440410700e0051004e980c00d440740a02600b500d800070810207050000c0684001c00c003a107007044c04039000c000100200031030740403540a401c1c40f009980c01380c2060b1a180341d50b504030001c12031042c1c0c100f111140580c102103007685d11a40c0c03d95940c0e0486c0c0784240c100320040a01800950460000b00100300101410707000038000c0b50b100e054005819854001550711000b0249200d0302014108642005452015818502d06200d80d1310002450000c83c80015541c6141a400039007025011000188060300700c2c58242c0f43c14036940d5080324541e12401004464890750710901c44800d02030128401a007069407085620440c0031340010300e03210700c07030b1117000c1103040840d0308844030741c4a0801440160080c41e59903400805000045007142407042c0052260701400c0300750001400200f00103070505100300030803001140c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622076 1250 620826 620831
    0x7030609030801030c050607150207050a05060112060b0a050604050909010209040f05010501030e150703180605040602040f0906030302030a08060f09010602032502030a08070c08060106020304090c05070209010b090a09 95
    0xc9030700d03000d00705160910040c0d41d180c0442000041c03509100003100c110030351002500303288030100400f6034002e400030007013034a142c070420701d1a02c00540c0070003d89001c0d01641c2103903000f880461408006507814000301320f000f196840c20410032512044c0544050f140220740c40b000c247e2714094031500900800360415446401c1411040c213548555000034144e40c0b003a602031001c2c05480b81c6441c0e03602009080703001c03008692400a80207901c6607105000340e008170350000f24000700340d80300c610985d030045d9002e581c000d9001404002003503400b25207000809910009010710391a54402944030300a1440b0038092112120004800780d440c05208041600014214030f15035031030b400003d681c0d4000d40704083c108292140003401c00411141ca4401144e4000c00a0000f40016540c40c8001d8001460440d80c1049221020403014402d00c0381c580a081d885e401584c0301ea285c80c0d8450107555643c9504c4081c03140c104001405a00e9448000f4195408a0b00c0c2640c1c0c0c0e00440080b80f80b0341e243d940140c045d41d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 623326 1250 622076 622091
    0x3020f01050703090204050105030114061320120601080903040303050a0507080d06050906120a06020d0b030714030c0108010303020d030506010905030a0501021b0c010f0807020109060c0e0102011a0105090103090203070306 97
    0xc0d0943c0c080e0300303a00c5c02a81c080100d03a032181c06050072100400000c240c508110400541c10340340c104141c140b241030000010035071244100c0131603141422240000c8c02002d0120300320700032009008040da0300c2802441c02a01c14205010055200d104500000c2c04000c40003031061407283c029030071504041c2e0b11000391075907080307591142c400420701c030b0007000c1c4103d08400c0410f445240c40003102c65a14001000b84c042619555130b050000d612080741d40c5802a140c07900e0048569041c040e0790000c00c0f4070b200042071007891508150600062450320b6040c00302c01001840401d0780042d9840040945040014140c4c44840050700d034984a6408643d26100340840c22040180640141c001c01c50030070180c5840c10a10030015450b801c009400e14000380c0c00710003848a56100c1ca080c95000900d60000245172040c9885a0040d6444140380c900460240d503103602b01542d09105030b01c1103140c0e007041100741d900b106000a12510030013605604044d1200d030000c043d907400303014203401541d10600c00c00902c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624576 1250 623326 623341
    0x312030103081201090204060504050108040c0905160801050301110306040504020a0302040e070503070b040b090105030c0903030703050702030f06010501080612100204080703020109080102030108060406020d0e0d03051614030403080403020f0105 107
    0x940c40b504000c4407606910000080c1d04a0500947d020384516444041c100740c1440011580154001d1085d03450744100c0400103601001445518042d0448580b680071815801802824441040c0c0c0814000d130326010090b2007100061040d01e42103007044501250b2500d4074000608412041c0e04060341c0140381c00161410324000003007079021154180e0542c0d4400d03503140601c400900803481a1020010200083c2c03401c1e620480007140d00c02d140e046e000e410b085401000c00d1558000c10000c41c0845c3c2e000039aa01546020040c61051400c008000c004540c10000000c050b10740c0940700c0c038090010035420b05110700c0280010f002d940004601191180d41e0340c01c0c019950711681c402a0b005c58213260001c01e0006043c0200e80c161358944008000d59100e03903481d04000e5001951a03603203a50750b031190911100d01070007000074518035682d0115517418160401c25243c00d0113441c038001d001103083d990700c00584400540703600075090b05090341c01d6513807400c060703040c840740c4160350a01303500c0c0000f0050745 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625826 1250 624576 624593
    0x6050c0306040b060720011101020703030203060901170706050903030d15060e0108040c060c02060708030907060305011202090103080c030c0d0507030206161d040204050a0303030209030d03020306010c08090312030103 95
    0x141c07000300c5081c00f41c1d40200042c130130244036481d8040c015807504103041410b02c02001e0002a41303a418500800810718001c2ca490890304441c0c400c07400240c000040c03020514090300783c04d01500c40403501402c1c1d94040740515542d405d0f244204424450085034034400e41d0b07424800e40b0501c40c851802030010410851005900320304500505010400c1603144076100e500c02c0108610039503004810881c2d41e03080c00c0055515607820f010480e80244100010000136220b0005540188010710040c4169800d04201070142c0d50143c001c807100b22800942c401c0583e894030134590440e50050140c0daa1450420f04d01401e40c40340e82e01e0b014491042011301c3d040d03142d100c001003501500039402d45046031900c285201c8460400700c04000040c401054000c0b04040100c5150000d050080005103842e94650200d01c08681d01d50003900071960104030708100b805c0502400d000d0702c416181c11071451400341c00280600000c070703070b000d09200f501080004d0325440030043c9842000301c42c41501d480c2e40c0d403444c00004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627076 1250 625826 625831
    0x40609050103050106090c0f0c0203030904020f0d0c020c060706050604090501050403020a110102010203010501081503070f06111902060708030405031c050610030501060207060f021906090b010609050d020607020d06050c03 97
    0x200c0c4c0d0b10702000015654030302d1099108090440c0d4405c0a030b6148002e044800c1140e1800503649400f04000440c0719689a00c010501c00101170041030b110581c40250f85c044a12010110003550420800756001c0da41d00011120003660050f000201c549a8070301240c01001031a1000700f0030f61900f0184400c0c1a00064000343c41c500c1201552003000d40c1e60f004a00380c0c0401c3c45442d0109241c07a0202d00d0200d080d00d60700c1500c1002400701d919841d9114001601c03504680d06c102c012441e8040f0000074001c0074006500309030b42003611107901c083c413a07001c9035852041243c041c154500c08400306080080520455100700300c0c4840d0502c606085a400c0e0000b840300340c030101c0c4074035000400110918001d00805040301c03c02d070041c00a140c0b07420425524142c02c008154114020151490b00565201c41c41414090045030300003001045441d10051910040e0020070071300c800344200b0421903440f44045000158140c0d500c585a803450700c046500c4107040980102250706201c104221024210050b51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 628326 1250 627076 627083
    0x60305031309060b030f060102030702030610060f020f03030106080414060403020c040515090f06010302070c080606120303010803090103091106030f0a05010f08150402010c020a0e040b0106030c050a030b030c040609050103 97
    0x206075075607070a507807411180700e4404c0440701407081c0f000605a002841c0d8070365215030180162132500c034080e80003c0c14030104842c0035041c0e0054182c10300089174002090080c02001e030008203005c100301301c0d40694a0005114030b4040001c8540040c00b000030661910f00807004100459001e81030502c6d000e0341780d041c440a1140207500e003400240b00410469000c41710781c4000f50482c002030b00c500001028a03c00205001e051540800c1a0000646100b0b441c40051000202905107401c24a0030000c441003025540c00045d4410700051180400100c116a030500003424002441c1e9420304d0458502c0da00d0581540e4030401c04020403400d14003003a5490b2040c0500f001c10881a0780342c0d91080100700c43d90203010780c0c660088030402a66414403d416801c14014148902c0d120003aa00081115850b40c11807080d0415403020310007005650702c403441c09004a400c0030b008940d01804014220700944190008140d140d586040c000c0d2001c1c4494044004040d0041c0003250305c0f825514042c040c28031044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629576 1250 628326 628357
    0x108010b010f0c02090408090a0603050901050a05010e0f090703140d030e030c100b0f0306010303020a110108040210080a0b0405010602010b0102100605060301030b1e040b07180303050f0a020c0406030503 89
    0x55503030758070032400d44600403031070388504250001680900c00060801001124025010001c4801c0e640d90b1040e401d0003000d03659804521483c15010306400d42e000503100c8849142060010300880001c5d66100758050b00715040080640e036054100762402d203403544054811640301c0525000380b03201103841004041a903c040c880d0b914181c2e24981da80c030441c4031064454110300d00c680c070701510369041600403d10042507103054811041c0001d0501030281d000700c0141e0b010b114810100400000705440c0032400342009003c1d8546030b0041641d168031000c0820803c044038001030b0010200768854880403e0213001001550b031a0032019000341000788100703000d4840c440024800a01d00e025120640300c01800503403d6918582d50080090030281a5428204c8000142006150180c401a20581c081d604203015814040c00c00380000045041d4101242030000090010a82140468111900d03141c201d0f41d841c140e5100072030828090f074255035445805d011001060101c004043d010941940003030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 630826 1250 629576 629591
    0xb07020a031e020703020406060917030702010203090f03010e06040308091513020f060409090809100206060102060c0a03110c0703030e0105070c05010309020103090602070c06020c03030a02030706050601020f0f0303010801 97
    0x140d9a0300c0100000a0004201d44055100800e0002400c410014140101c1e035042d07840b503000a05841ca103422443c00540c20100800080e555402003803800084071018500c0c00900740c0000707440c2d00c14009094052035048018520646003540403c46400c0b2410030303680c460070301d4540100140d0056a44980b14403170f046079100407000044400740200c03c410710710f0403031215640c2405a90104084216480401800001000501c038040d81e010310f4401c481d155690126141000350810444492204642c44001000100d90b00000d40c113170401500e03000e26803039100c2c0b001d045000d030001c03254000302440042100c081c80840019010150fa00c291035001d0103200700001100c1c10f015954000d0003003401c41030100701c2c650203540442d8480d40180b502260140b82d6407180d000b66030290710704071800b41c804075041224036410b200240400300101c0c003842c039009007000003c3d135a020342800501000d540380c02140c080da008114000b081c017a03c8099070604007645801c151a41c10912802a172075007841d26 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 632076 1250 630826 630841
    0x8060102010e060612010204150302070501060b03010303020c010e120106030503030f01060c0c0308070302070506030108030a0206010501020c0a0504020d02091008090106050109031203050702010603061e0b0d05030f0d0b04020301030b040b 104
    0xb42c80700b0000d824008141d1a5595801c2001c043c41140003580603540c200008205d0140d41101500651007686001d0303078614040c50824212209980104070030f07a420703c014000139601295005844500b4a002880c080410740040c038101d8030340031400e015600e4210300004000780407000e10b22801d80303400540261781c1d8038141914400e04442005103c40c00010040c400109500060000305009104946010391250b0106000d903100707070007200781c6038400b20354240c40329030400480380540801c0c4041e00424101c00040740f00007401d401218070485d0003140e0301c0117000c1c0d81d5054524100006000d00c50140e440100035292903005e44000c0099400c200c40800d2650090516008503035001e5200401c0c40141e40f0224020b0402924a50440d5210180000440c03003901942140703e80428034000212201049002150700f8030001034040c0d0040e04c45580428408020b03292003030102c445150351801850742d008000d00e20f03030110640c403501c0400080244800040124031441c444d003103c4c21540c48055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633326 1250 632076 632081
    0x3090201090b0a050a08040302100606050d050915060607080c06040305030f01080607080c0304020d12020d020d02070803040b09010207090f0212090102070507061b02040504050102090102010b010c0305030a0203060a12030309030806010201 104
    0x1100c03200813410402c40048032a1240360060f511078040d02c181c0c0d104120081d10f480903070340c10381c2c481c800103440400d001e02e1072120f5203c0c4070b8106034460000c24064007201108903001900901c1c081c491080410b114081c0000d00044844603007420003910100d14cc54a0048c01e5074006660082201400d8400450307600c00014800b801000592240199035403a1700c0301030020b1380001d0003260405100c904200c001000b00043d980d11546540182c61980a0040e0081c47c007517108840c0c80c11944a01820400b030780c408001c49042c0c2e0200742006541e0b9a00c580140d00d84803c03507004021213481c0803001c2c2d14024050717000d0f29000c41d103035a4940d41c030340340d5010031403d03030003520070203490741c1c0009108200c0d0900440454890310030145400b03200f0307000c0b5000282211805c03102650643d40005601c8125139081c461103841d21001d00306900c02a1154600800703c8c00010900782d0141c0e4004081440c587e5150700c81d9004040c00e01481590040e82c3ca40100644810b0000702d020807071410103c0d48035030060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634576 1250 633326 633337
    0x3030a02030d05040204060305060f0a0c0c030c06020703030b0303030703020706060603020405010813030306090f0905060c030405030304140316050a0201020105070503062407020a030507080601051f050702010201060b0a03090201090b 102
    0x103a0045040094841e0400010400500101d81c01a035030b403400400908140b2019114641030441040c0034136241d4110010390b81510082d03c00c2200f2050b450700040e4102c0030300000c50340c01c410010b0715a0a246001c0c0d000b0901d101d41c4582c14031020003040519641030300107000c1d0a22603602444415540c0300144d040c0d002d54001c044c04640c0030000914507000c2000002c103002e000c2d240c08101c1642c4c5041403421610194801c214250700c070880602803100400003036030070003000521189140342c00d031180c40d241e00000d40b00604100310981e00054a0343d0400c1aa4441c0c0c1081d481088202a80c0c075000f03513507403c03c010880c050f500380400145014003c000760b07442104050000201d80c0c10245c0aa0800520f14100013200c0d0f505000903005615007680e164061841030004141e2182008052442d0410503031020388100b1032000402c40014030b804100384403020908049455410503c0180e003d00801e4100c105045004110b40031029410317082445418001e89034042c5040c0c83e41c410701201e2080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 635826 1250 634576 634597
    0x304080106060906080402040c1403010902090f03070b070210020f0304060c060506040504050c010c0203010204030804080102040602060115020318010e100f030609090c050d0201050c01050a050103060c050711010503070504030803010e0103110303 107
    0x5c3c0002802504054014103004203c0c0d103004869269070002c0100141c200382c01403420160701190440c203d05011215405d0102d00300c0003030441c1482d180a000c0340d4428500002e0090300c0c42843c1c425035078000c02c6683d072a506020203607910385131280d03402400c0700484c0d01c00317480d45818540418090304191041e18000ca8208000c3c3c0a505d0300c060064448590018080ba010341d82008004080381009001d840030340040e800141c1d4685c0340c80070003840c080c0c041e08800c0043c1490041c14108580004c101c50303003404444c407041202119840166408281c5250341d60f0080e9103004c01e141001c2d403203484144414400e8404000c0356803280003000460f02d83c20002805400c956000f40300c5031401c030000d14089441450018a40268003005130300f07582041d141500642d0715480144204880c41c020001c84116501d811420030000e03440c0c52400c40300c4041101c0c1885400004950690720660803a4040c6400500342a56540d40b107030078108041c0e00f40700c180c95214030742c0141c40f020b10340401243c000094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 637076 1250 635826 635837
    0x3090510090303200102070807030806011407060b0402040e04050106050405010b0c0a0b060316030503030103110d021806010216030506060306070203070305030c03091606020c0111010501080a030e03010204050a080304080106060906 101
    0x2180d409450000c041000f04e106914200c1003690f00860034002070900c180315440168503040e02d0300d1f0240204502038140c0d41480301c0d06c0704014214601d40192100769810003800702c0d0101c001c0001ca002880344c1e07000355483c40080e40400041c4030054000500b2500e00396000c02460ba07070303213144460b503008100182e1038541021302c2000205a01c25021508014001d09803412010700302400030413400b49600803582d40d0400302c0100188001c5034007600701c4040c00c1d9858807a80842da40011028410b0f020141005450700010644a034400c00030500360200081c0d02214940d1130b07040c40b0f940c0d002c084600b54820f104c1c21b000218101d10100644440c0d581c148c941d6820340c0c0b22500c1e1001540c2000380010041d116498a42d081c2c05555880034004202580250560140c3c12000410303a1000031240d037610b0381814010850400c001460300a169054a440f0414241c1100020b01900c600d511a1b40e0048070031802046d180303004002041118034242c02000515900da0068808865500c9a0310105a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638326 1250 637076 637079
    0x3041a06060a050711030f100b01030501060c0312090204020c2a01020c0d05100501060f0201050a0b010203030105040b060f0a0201020c0f060105030705090402060c01060f050a05010503010506030403030e070e010e040309051009 99
    0x41c003d42c06400310901c103043c05c805140e25940400d00c4c25064000d410070980c0060303085034070190148510542c8000030301e424003a0f503040180142a8840f2035100a0800195081150130301505502103c0c01c1680180107550390303003a4203409a944d908880f5100400340b544003803070702d140425100d16000380c40b041e0090004203c0d0b450401c9001c12002005035624020282c520010311102d03c1030a01800040d01c0b800200c0700c40500090864500800400c07a20b0b1034a800c1c01e145a80000a036411500704a401107410a09000420702034090b405610323000450100f01c0c0c82001c2d4040d0040d1541451480c11501403a810b40d4070980c2c1c41000b8820603030540c203d00c1050103582400c41107994024000343c81c0c0b51616983c036a442d42115001ea20585800740c0124080c030032443c1010b043ca0051200346403240c1036506000008006100180006041c10b40d91008c800c20a0070610503580140001080500302e90380d58100e681840c0300072101100040c0b904913000c25149028410746412401a60701e885046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 639576 1250 638326 638347
    0x506030408070803090102120603150a050c040902040f03020102150f06010503040317040f0203100204030803060d050f1002090a0911180109050a030f0204110307140d060b04030803041a0606 83
    0x551000e031056a801c08100000804580d41030000c60040300d01d5000141e6461040340c035030741a504007400740c81c400c1d00544181071f18038440142803174004c181c220000500d070301c0f1040342181d51311880e400200b00c02d0012134001150a410700400040360f00030780039224014284c101c40c8510f0310040b24a0400141007401090095204801071a032040c03003424540b140140d02c05240309818003c0350121a500780c000701f41c0c000c5007070602103d11854891f890075802d283c20342c2d1300c402481c00700811080c06840070441d8901030140c204040c1080815030f03000e640ba0011030f407986e000170b98072011200b03009450321003001410108a00c01c260103000004503450a0250201e600402c1c034a144801a04000740b200002c152035695010100c000c5124586907900c035200f5106000035619280031101c1c0404041c02002901d5401001216000c107076402e015a46003903000900c00180312075000350a4040c004113003c4100042c0c8401580114000e940740c1c01c090090f01c00700082d02c202110020b42111060004030b104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640826 1250 639576 639589
    0x9070303051608030f04031202090102070905040c030218010f08030703120515030f0d020c0603010501080103020d0f050106060306050f040603020604050105070c0504020d0219020106032609040603050102040501030c05030f0105 99
    0x408201450040d5070b107000d0f15103140c2900180d070103813141582e41c800d100c04c040d0803180742c19111000c06000d5003440c1c2544000713500c0300c01911902450300e8450340000e041081c10307107000d030145034018440d0017000001c030740320060b4000c2401446e159550301c01012580101c008162140c5a605a072003c424401c15200d80300a040060000e04076400803585100706907806100c03288405001c98000e00c20302e20b829100a10b000317400355003103010f81010001880f541e603010791168152601511401069050340c0381038400c4401024000d4000d510700240859490f6250b0413810881790304032021030301d00900b8010001140c2e01403000940c17040c4208020032003540208003400200b4004d02c500308880742d40b80040340036039000e00c2110003200d6000882d10030003440d00788520181c81440c40200320090442d9102c1003034014255a0360b46200142e5256038070f5003140c1c000c032264013001810600000c0c0d41e924209020b50000e014080c04207042141401089205401b0b80c0d200d103825000b4602164641400d0005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642076 1250 640826 640837
    0x41101030b12010f06050f03070603050403020a05030301030506010e060111060a15030515010e010e01030b0604020706020903010c081605090604090b060705030f0c06010e040203030a031d0a030203040305070603050907030305 98
    0x14140c45002000d000d5461000c07400c5803524000004c942440302024440490308070b500514480c41c54217044003016240000c460f0b0555450b400c0006003a120360409910380504544010101c1c480000003104008011503a1030403942000ea81048549900d40107480c3c00403403825546590344002c0000714100c3d000e8201400d00b406070030650b020943c40c0d4a40d00e040000b501b4144519080d41d00041101c00c100d8800741e40100107800c0742e1441541540d40e8018a1040030345410b100d80c2d0081501c0007400070f564101d40109070f0090080220b914040d001070f09488046030050915a9150058002e060040d800c40c1c0c0c0c2100b0090290346000d042500d41d00041007420b070003903002a0f00340005000075404000030311981000041e23064480e81550b00d90b600d4010140c100f04078550304601880300584001058480c031210798100410014200e042c001019041181c83c0300c640e00c03c50089005168000c8000d000b607a00420036503445c2c544030035068054400942d0740302920307402824108003003841000a00f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643326 1250 642076 642079
    0x4090f0221010e0f0607020706021b040b06030406050402040506060a020a0305030c0409020301080a0c05010306050f01120905190510090305070201050f0f0f0406020f0601270e03030405030306011103030108060411 93
    0x100e140d08803901c0c03400c6a80359034078030700580c0c44104d184103130b040700708220b0307a1040b19480102030807410408001c0d107072240c40220081c440441c200e0482541c0d62500000d06170803026000640306e2615041c0744014010a540507801149040042141802c01d401100d00b0030000350020003c05c0000e41c1c044459500040104240c0c05003407001080903109400214000d2111200528150819050051a40440d54006070500d03240041c00c104030740b56900c1c0180c0600c42400e20685540c1a00b6109010307002d40b560040050141c1c0b5231943d41d0340d14204661001030b0081003100c0707400001101a070110380c00311102078081441032041f0b1340107610038402020402060364000341410008081014950044504c1001c0504080740c244a0154104403400300500504011702043d49482c1c00c0036156112620200348201504000014501705604038801c00011101101da980c641400c0050703d039001925030b603000544001203161550030000c1628140c0711444003624190300d41ea580e40c3c07040080c8910301c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 644576 1250 643326 643369
    0x80309060901020c0303040906030308011502060a0509010207020306070f030f0209060d020309070305010501030305030610020102090a090b0402040b040f030203070501210f0b030a030201050a05010503070f030807030c08070c030302070504090f02 107
    0x1219505c00384050070040c19007400101c0d0542c00c42ca0040d04800058004c0307000c0740300c5256240348903540020741c103812000c1540002510b440d4202180d01912907000e001c5d406218030014842c0c101d500c0450b5011601c8035650420481c0c4182061909070f210302000d10754000d5061101c0b0b294040141d00545e00207104a0844042c25603070382e1040d094420982c070542c007240c0040204141400c180d0144803810740035100851421260000040d84ad502034080c021102d80c0d10144504139807a15030440f0060b282801c4810341b42d0f60350740d07008490031001303000c12070007130107001400156940203401054118940c1c0c41300d0384407058044100801012101046080143c0741c410403080c0da241400200c510b14002da002044034a0030000c100181c1e101a1301c828041c1d40215820400d5100520f2072000303030f80d481440e141d5628010b040443d085140c0f000f0292580c5000078440302003003140d031b000300e044920036003c0c4d80c5090780c0c40d81040112079005034058643c40300022403c00502c2d058028004c03115200005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645826 1250 644576 644593
    0x2060a0306030f080c06060105070506040b060103060906080102031501030902010206070c05010605060708070309081c0c17040f0603110304030509040207020301060b0d090506010509060102030703120204030807030801060807080108030906090102 107
    0x9000d019403e98900361150100040c5034080d04c08103000722980710101b800c04616100301565a1a503c4000400103404480d403200400d440360b100740c0048005240000e002c0c004242c543c01fa042c000d50081c2d40700c00f81d0080b4052a0240c0b940240504004160140c01520156440800c1916403100c181c40450fa155606c0c80c01150907904c840103044203d005022040d1104442d10b409010140e140d000103089500180310410703021440401da542d45607291928250005440c50146460401040c11002c114000710f000300b95101030b20501421900603071350038030181c0c201c2120110103120a4a0250003d6010440c00c0401c0c01c041d00242002c87c80a800054066910b60f840c1e09160410190170b449151114440d4040c48000c01049000d4402200c07003141d5803c0900010b0341d00e204000004040c00104203c0c101103c02940c103840055801010003030b0380d036145103002028030f0424000c20004c5030313002c404140300c644100c0c1c069050f03d001710300035860030054800f08035040d04444600e50451140514 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647076 1250 645826 645833
    0x70201060906060504030b090105010b0a050702060403020307080303041505071211090d030306051002010b03030702210a050105040309140f01030509010204030813030203010605010516020d030e0607050c0310020f030402060a030603 101
    0x240c0c2d00201001d80e1069203413401d62414a09072900600400c200b0b0b81020018030050603288101c80b110314190520917560a040c2c0301048150295030700196040c05041800511280b01000030752007503105070590480300ca080140b50b0300301e900503294580040c0c0302e045c0600041d070b06035001c4010030802003086c904244512001440300b030703400b54003100000d4807440c2c10401802c000b403030b550300190240001d100d0351030a07101107640d0b1700070380e84085d2281080b56a03090700c0316200005400511112415180442500c0c20007502074882514100c00091107600000703141e0f165120012009040281070201d00c008480044000d002e0280c000d81155600300b0001001407a804000c1c0700208080d94480d10080ca5070040500f129880e501c0241840000c014030b645030307510501c0144007030341d044400c203548080b04e04080303804c030384140d60164021030b00044860a014000818908d14101101210794088152000109038051201842e0014805202081c01858100c001d48400d180a240008609503241c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 648326 1250 647076 647081
    0x1030e0105070c0203070501090506030604050414070603020903060106030605060a0c0501110408010f05060108060a03060903020109020d030c0204050705040803040b030a02090307060c06060608010e0402010804030309050f01150504060e07080702010609 110
    0x85074007003c28a401c4110046040900c42030700185824244a041c0b0b61070400401c48501c4002c1000344504c0e911030003d8100840c010803481c4520036075045483c110b0b11054054004d610030100d4610a00c5510000111a4400e018000c1698800303000b840c200300b00d03c074042c0da50b04031441046446540b5800d01c00e0b1036031810000f401c0246100b200100b03180b9002030503a021038002409041c1004501c404108440d115012400201c075402640042c940c07400e410102d00400c96041d0095101c0d800665010030f00d9845407594803000d008690400c050b464050054a591046104200a03a0800d000403c80c8400702d601842e4001c240c200c016141c0b400810000f0300741101608444042041c80107810140300d0140308071350240001c0d04040c9255410701601c6c0355017000060000b810040040c00180816200c1d400403501641d1150464080a1402e510300d80a09600b10118040c2150700d1300003c0e5a2405004840c04c0314680080f00c013180c0c649038021298804010180c206641d2075043c005007100451 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649576 1250 648326 648331
    0x106031202030409060902030106020601060f0201090b0109140708040201020616110d030203090f0303010302030c1003020d0504080307030b0108040209130c081006050a060309020901050105161b0e10060215040201030e0105 97
    0x10703409555038508001c10b90080301c1c02500a080c80314814401030080a030005203050544000e8100300c2c1c0704144186040b40900100000100030300c0401c0c00008652015400c56040010200451040c0b07980c0c0b840125225001260083c0c0140d020102140c1c4214404c140c907686029a480d1103001900a400280d00e044403840078000065400402c00014000c148580031009005601852540d4034540029581d03122100714503106448200d44000168000e0f411a0350240f41c0790002e000524180c100b1900e01d400c1241e81c4401300b0b0820080e0503d030b41c03060303a080b8801c55008080f02641d0311401003034588000700704c10844403007030151008107420000700301011145580d04070115500d41050140000101568400c00c2854289540c080044e40e40b200901d05546082c64219110b0f00a070403004003020b000c2c1005802e9442d0f01c000c43c0400c400000184040c0c4081c11021901038540e401d0388645040f0a100e08001604104c08030180c005039241603d4100303005140100d0303d001c000756828210b0308113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 650826 1250 649576 649613
    0x5090303041109011d101502070504050702070303091202010e1206070e060901050d05060411070c0302240409050615030a0506100807050901030209030708060103030203030109060b0406120203040203010603 90
    0xc01080100003190380c0008803444107850a0440d945008203d0001150200d04211444030f20800a085c1c01200004c074070003018818640241c10f07220070390181d1141905e000e4140924145000078003d80d000140c4002240da242c1d48104107549045640c882c0c1c1c101d14582203040000b0b00201c078200b680d0f20703d100c08555a01201408035420031040240c00e4a01041c1c4d0140945000e002d48407844c2c0e086000d035110b03031015281c081415035984001030010011a030030100503440c0400c003e401d1124400722541503d209072030b0342a402a00b010044001c02c81c240132441e01503c2000144085061908107a800c004042c14001440049001d071004a0b08122400101250b4890822104e0302e0541880400304500381820f810906044c04002d2051003020040340c141a00080c0b085a186c900300b001800401d43d6000780e0f61039585915009440e64028403400007010b0511102040080c0b240007207030110760194071b410040404480002c806500018801e03641550385413000004070755a1110084a443e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652076 1250 650826 650833
    0x5091210020f0301080c03070b0d0e0f060a0204030302060109050103050c011101020f0403080901030c0f230403080304060b011202120708040f0204050703020408010e010501050d02060903030d020c0705010f08090a030503130203010509 102
    0x501741c3c0a803816458510707013442a44284400c00804d120001100e1101d41c8004003c9107e004200505181c07603204a8445214810041000300300d022950140c01076030320940c00d94240c0d980e640074400503101d00380000791640d000342810038100d60041c0b46141499044030000750400c0b00a141112203a00158002d8420020000d0014915a4144a0410009164101000b0081241100402c0b034603c1680146600701110241d4010440600c152402160b01401c0035940307103024038100d0b014101c02c918150114a862201003035182d40e80c0207403494112640821901607962800c200c0d01902c2c0540700b51014442511000050f0b103c60240c07600c285529100903945502d070045050864101d42c0950074164501310040c011039442c440d0066441350111020358a0303110007030002b421440b0f100034200040744000340c4003609903000301c0e0704e400720b40303007620340e000111030031101620040000c40e075000711608403844217000640500007458000328500031f121b506503141d9001c07034216030040d1081007540c0e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 653326 1250 652076 652079
    0x22030909050f04030c1101020316050d02010e0d0c1101030b06070302010504020310090206030a0c0e030303010303020c1005030c0306010305070203040503011104031401020906030f0402040207020405010e040209090102040605091210020f0301 105
    0x512401a66084803071444419000c0c0f805440c014034501121400901204911030a480d00368401c1007960980c10905c0d51101d1002ea00e482d00c03da4032170040000700c016508086915000140c0404e030140d006503151602484c01e1905c0c0d031201005500e005500d4141955600390106a0725042c021b0081e45220303400014007410140101403418000300b25200c02c81d828130702c8010050f1150800c1da5040101a400410308421960003614881c283c05a01905403001000000c10706600250300892410181c44440e2807080c90001101c55101c12109240e1501040011032800d51007030703104c540e2240c01031040d030f03040c1916100003a094803005080c6469840380407030f007801801010100c811320410f99000862400251201203111808018015003208892030000b906540b40d6404454551364010410851582c4601d40c007154400705a03420303070141145000103403100da014402c403000e80e60704d0b44507103060a105008120900558206002860064114982c4055000d001600760340324108085900c1e036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654576 1250 653326 653339
    0x5010504030809060105010905041a060304080d0b030a080304120c02030106090209010201060b0a090b0703090302040504080403060506010c020306011806090204060806030f010207030e0402030901020c0708010b01090602010509060f220309 104
    0x61409006040650040001006188e80016441b01201c1094030080b8400020110100c514528540c0340d50300500004100010070010600818501c3c40e0254200228800002459500d2900321001024907400f0004240810103038000310744104101c1c5010f08130340d0f46540c042401c1d910a5400441d100f9004106990550f07020b000d46005032a03810041400c241003110006c0060000b1311602248410010380c18080c1403040041a0203150040c10510030f900700b914040c0c10039402840255405440c2c040480e820350710940c10340f00580e40090080c44c03180d0034041517070050300002032500359841d600d21000401544900240004140d80c1d21081850314081040c10b0421840c09042c0185900c100040400280c100c401e49207616800e5400503101d40d41d0349400c90080c85009116411440386590006404405401000340036170282c1e100c1030b03c070b03594032030903401c0e1803050741c0c50201600700e030001404e0038003a81850380c0c0c481d02516020707514804403501c86c54840407200e01500040d01040080c44007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 655826 1250 654576 654587
    0x90c050114190f02030c030f030103031202070209010603050703020909090714060403080307030f06030503030901060302040f0c12050408090d030206040501050c0c0604030e060c070603020702090106090302060d02090415030501050403 102
    0x3070072070101c03810785064214018000d40900c0501080c050020f80b858402c4007610800603211040c292008596581105100840042e0000d100c103c0c00900c0700d02c4200340c144110b00940750f01d150b003d820400c4503402d04205402400c001002001096070921820340165a102d0002d405200e204018003000c40c14132024224200000f44100e0048500304030800000740140d003120740c404124580042d940d8000c1f8100c2024200d968405072030340c407000c018402844419803013001100d100b02c40c10454900e0741a0090140c408000e401c1d40030444000b200301180c00941c1159030f2051054900c94580044180041c40b5901200c0068005a01200801c820003000744259a04000003640003400c0885000c2c1031307a5500750041c0b00604003e04661003103410784a06c000c0c2c44041c070b0900d00795070549444801c010003e4100403002d900ca0940381c000014810f000f8840003040c0c80c0c01a064902d41200c80503800b000c0c1d44a40c2c00150095956007081c04e05d210441c3e034200c0554450030010806c0d061030b0900429 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 657076 1250 655826 655847
    0x3040b01050405060109060c020609040608030d1a030705090406090204020f0307020105070315030201050d1104120204060f03080906030c07020301050403030903020d081909030306050312070c08120d0908070204090c0501 96
    0x180b4501414044c07940e03044075280040320794501d4402250320b15032000c281340713001d22a4525009420a900464441000300103441a880310001c01c02400030b417241c3c2c411a802d8201410ba8040c2c104030070a02881c24100103c0da40b20303002d0344002c100c0340450380c085000c80c0c0c000303142c40c54440ba02106000d01071368203000e0540c008003030b4602844125400440c01d2203003840c611000381030080001d140700580d1410740281c0c1111090a4845499a40d1804042c01511801034120700c02c1c0e14100000c06c061180042d031405480d000442036003001c0580043c00801e510140018080c40b0b400e01000f40140d1b000d00481d441944241e6000c82c02c1c280c0b915010f45400c110010324003c1c40104000c01080c0800216203e1205210010200b4512200e050030780083c01c03203400c02d0313406000d00350030500c111148400504580b403007440030b09030881d501c0410315241c0d1115140080358900400c0b40520b0607842c1d4001c8400e00d8011640b152401049900203400c4840070b110407901b48111350010800c070342c1c02204015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658326 1250 657076 657079
    0x10b030105030c010804030e040606090503070602030310050603041509050706080109090f0b07090807120c06021501030210050903010c0905030c010201090209060409050a0b070c050106050406060c1202031c0203040b0105 96
    0x9046504000000b6183d009004615040004900000b002c2c51711940203c64050806081004480d894a0000f4240a101c0c0200c500a01c80c5010004c0c4052000048a10641407e910202c0d00d40c00d10007001050351018105032288034110092311030350b0000f8031038a031001c0e21a078001d11180c0d2401070081c0c0b008a0503804841e40924240e41800401c140300c0031407080c1c80c3c0c400c1495031942d0780c15506848682180c0c08c10041c0f4800c3d004042554921300580343c4020380982900d50055a80d12022a40c0310704079000c3c408000031000041006007081901c0481a81003410098241130742c80d0007013800c5915001d042c03400290004800c010710309050000d02d42000c02071000b801000007030b4001c1403001002030b1145005680e80c418405c14480180041c43e003680d44001c031900181030121b401800c1c101d450b5402e84295103004800502c3d40741920400040380c0e11611000f012580c0d81c2c07136410001c1c0480c51580f00f94001041036840c0e81c6025400400c00c50b207200c0c0300680724102810071050035101604402d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 659576 1250 658326 658349
    0x4050106030b030c04050406020c030708070218090a0305090a0e07030510060201060b120c040302060c06070306050301090c0303050705010f020307050c0f01180b09070302030a0303050105030c01140a050c030708070606060801 98
    0x2d90780c40200c1e58829040c000e032000305881d11946880f400034414504100321900021a40508020402d0024501c06000b00c4940320440b51040c904581120280c41402e5543d000110140000340a00068a41e5110044c0140020360b6101d18121840000300e6050700002c0d40c685c10402508141c5010388090318030341c40200000c46c10099060414032507040a06802c100d44000207d54003072800844015581c050181c0d600d6611556443e9a01c4100b46d0b4001d01281c1880310205803410144180200950403140c10141d092031510180c409a003d004165115500c1d00310f0096100b56a00055009813850342d60345e6903032078080034000e0030046681001705960b4100400003800510f01c21003003c6150700420014445d44403114428031740760255100a406005881c440313424140c159000904032a130640c19039520101e040c004603072000d40001000500842072009041c111301c1003010700076031084030007164541003403500c98090541040d00d00301d07009901c81c0014480c1c150b100c90388900504044d00300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660826 1250 659576 659591
    0xc0409030801030311010908030105040209060c010204120b01080c0105030103020d020105090406030516140306060105090105040f0902030a05070509010807050a030608030c010203040309080601080a0602030c0909040507030606120b010909050a020901060207050405010603 118
    0x8c0045034401840b4a80c032454002c9000c070039980d51001268004800c0714000c45da683e540c3e1915084030440c4820680b40c4042d2540001900031010500a0704510141d682601d5a130039903003084090780b0156010b070304001050040314000c0d2102d200f52005140680c0003009020b880641502000c5840d4005982d01d003003212001800340c0340040d9094124809092003030b241d14240e00126514000c0f680208000a4103007000240d200740da6009501402185900740010354801805a681d031050320b80580c0000d05180009445922800203480f4203a500e00d8080f4096554038081480d5401c41400ea40c1140d5001060104140d0400c030308200400929025000039803400700c42c0b5403108116040940401d80003c00545542403050460fa2015002029144035003828248140d59000328042140c0240c80c4c610701080016103821640c841550040d00c3c01190703800c1c0311115001d80041007003107415105a448000c0141c0c1c0e03607003d46018110035401400b449261000300000e81c1c00607400b00c0c2c10306250491 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 662076 1250 660826 660833
    0x20c0a020609040905030d050105040b0604030201020c0d17040e0a0c090305150403021903030c020f0102090a09020c0a060908031b0403080307080601021609020403020102010f060b04050d050c04090308010303110109 94
    0x214450800e40458205459500900114001d030a0f009001040303400f00240c040c14081c05076102606850056400300003c0d03170f02400740000c42c441c43c000a80035034407100d43d0550f6440c010402e214128451101c040d00c0035440746031030f1040d810603044500741490032340412000a03105d00c42c80684030310700d2130a003050925645645403510108801504400803001c001010716000300049002011a0320890a03101003d084c010018944903c2d41d00c014090b0140c0320340e0701441402a80e940e980300600410b00c440c0b42a841400035032101c80140c1c4103001d200158000324005d0321940030b0042c000c1d03414503641c1c6846071560500310400c1b410000300c10b80070b1200307001180d244002d90340e1002d51801d2102083d215900181d03d0b00f06001594880f0925401c1c000c00c0103540341e00035108680c800e800034404048180716580945d5000c3c0070300c04103a030301400308100030b1034210b480c0001140900c0690300a4002000401c0c1966807440c1c0540c08100c2e070f10010800c25601c0001c1c5c107040e0b540c0d98004c0090760b802ea80c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663326 1250 662076 662083
    0x1120605090609090106030b010f03060c0201060b0f0d090206030c03011502010203010b09010f0c0203070b0408010e0c030a0204050705040b0d0c0806010302070b04030e03120310060201060602070b030703050a020c0d0e03010f020c 100
    0x100b0040c000c0fa0307000c000a01400302548414095900026070300c40a41c1c0d100420301840fa0103000445099007040d004000d13940c01400b845051300d03d042061401e0161261400b01c0b680c2100e400d181c002a1540d2a01c409600c40c18004e42c000c191302e0b5883d60b0749604014907808501c0c0311103041021684104010000c0300b032440700343d402111007440d041070b5801401d4005c5031325001880010754140210200001c0082d100d900600455041d803000f131000e40301c1c1e0b404050721a0750206100785c040c1c00183c1f105006103480e600c45a070040d814189103041c40d0325540102d80702c0e004a04406400d6648544900724141c0012055600c500c003480c003546061607950790a4192000580000c00b88001e05660402c2a5400e2105121201800040b2904d0340b810140c43d9440007001c3c4280e40165280c0348010a102d48040b610b0301c00c1d14a2210845e02d16120300f41e00b20000d00f0010660785d6280d9003031003200d00e40300c428841e640d510a159620100c40da00120101030840b601c0c01505901d091041190146820010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 664576 1250 663326 663331
    0x30503040302040506060409021206090703090b0105060d060f08010905100603080d05040501020405040c03090c050603040201020303010b0f07060606020d02010c050c0d0c020d0b01030b0f01050102010501030305030105061b0d0e0112060509 104
    0x15a004a103544885e008107049004a800203011140040f5a0354211000c01600e1071155004441c0c122454403048425001c55451030400740411003843c00610843c01d104c80200511400102c0c00503049a0390785000f4420805a00b0007115a5102c20302c44061000400641c0e0381c4541000f000c101c154516276a200751403007403080c0c01041c151240e0000c2c050007000c0d81520010310b00684280581c1c000418020000c11450714110390640c040d12010800307041c2542900c3c421581a0011461030342403101f8082d10f134011018001ca003080400c450340004541d40510802420700350020207112708007141c06401c0d141c5466010040090601c0f00600e00b03000040c0000540b44a0f00300700c4e45040190000c5104103400c00d41c013401059110000104000c070307400010344540b89200304081c0316601c034130049098440a1102400140342800148140d2820034014008007130720480b011040e000c0702444500b040c0242d6001008910900c0f184181540c100b000f044011a04006c100002400c00d03000400c01c1001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665826 1250 664576 664579
    0x30c010c14070f050106030506070c020312090d0206070609020303040b0a02010b1009051003060504140402030706080603060403030b010c0605040302010b0a08010204050603070c03090815060f0102160302060307090e09010204050102010e0601030503040302 111
    0x10034107043c248036080d8401c001450700f0800365090b51070310740c00140c6130142d4000c040303000c0d1180f5081000002580c8055540015005010460f102c0a0b9001c100301608015800c3c0c6500ea9a41e0500b80140d03001c2004100400c0244501d6464801e86903002e82102d12010686029521000c4c8420010f60311a00d00815940110703100d0205001501d0205d00424450304126082480c0c5240c8011021000048038401d030310803000c03a8102034540c2d90459511005544844d0541d100f0008100040c1c002e8110035030511041c50f140c00009041c0d1210000d0f1070040c0c905074054cd40d2154001201e0906085a101800f0b0120003585000e20f84004540c441c44000c1c44c00c010880c0a030006405c041c400c00b9014020a8044101c4545403115103002c2107495040e18910322441c1c951140004c1c55001003069440c61483c0300d21a0042031454092100c250306c0200140c080001d0844085510f543c0030740d8170b0740681c0c5440e00043e1a5030824001a08543d90031002044542c012001000012000022101626070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667076 1250 665826 665843
    0x1020a06051e01030c03020a0b040e0609070e030105130209010602030a05070602090102030f04140108060108090d030b010201020c190c0e0c0412020d060207030c020a0509010503030d050402030a05010e030c010c1407 94
    0x84500602c021031000b48844007000304100000003d000080c0c0440d02501e000316400b11080782d65004010061103076125401e0b1404040000508501e051030209603c1840c50908894055800c070000f82120001c0f00d44500c1c1c0800b40c4d05003019424040511409425140029440c1c0381d20b80c88040c100c0d0142070704c020001038000070501f690f64420302c02d888007440d084210548558a805d1880000a1080800c50014500a0020701c05601c80c03185180505164806440d82c5140f250086014121502c01c2074195034082114003801c2c0020032070000e4140344044043c841c20701600e8900a01c03604d81e03200102c80e5004101344080f408501040b5004c0f2100c81e030132045504901c0c404501d0030318078100050401440401c03001305064101c1000c0005901c200d46d40000710b5200d42c1007043c041002e010f9581c15034010b00c8030000a952a9001c0d0350401e00007000c582c040d1405681d05800c0d41c00c040b90302c074142d03040410030003221f41090061a000c0401810004180390b04071003541d1844c000ea10002c5e01101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 668326 1250 667076 667081
    0x702131b051e160f0f0b0603010b0a03060f09020a090207020a0504020c070e090a0803010b040501080a060806070e01030207080403061b0801030201080606030705070b0702010213060201050906060d050f0106090f050f0601020a0605 100
    0x364101c00c40e8081c3da07070104541404003814103110800c1d44101c4000d803042d0101200113242e40c0340600c59444040d50040c036000400e401c545500c0010450100e0100046a480d00c1c400b0242e618054000700502141c100541d981e0b00520610001c0d07000c83d07120078001e13070042c8809031440f0f0002c80c000e000d441c113040040f0101d6880540070762404202000161007250f000001051500080c0010001d4403800e8807914030707079110762002c20104d409510514829030080000b06032018401d6020280c0107074149005800d0142c42d4072244d80552282d4003c9510f00c1e95000703402525189400204403440d07160510070195071540d0000f9010702c80040c50b6500c1303080c0000004203054006d00079201e600e50080c1502c0321501d45890003030700070b45c013201d0100e0b60b080c0e20341800201c1a03c140102446500303254082d00068403450240184240555170071146800344000b07200340c0d03420074480e000c0101a510400310310005d299071040200e4101611203003481036102d08000c405d0742c0010792194090b42c400360008156 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669576 1250 668326 668347
    0x203030105060d020f0d0c17010806070207030605060103060f0905060102060c031e040311030304030801060e0a030c050d020604050d0c030201080f0405060f07030209030706050318030301050901060c020301020702131b051e 97
    0x20311406c1305409503a81b03082c0040c80d00356409201540c0003810014580010390302c030f000065a440c81118010f005030b100f440c0c280001142c6402c503603005076040c140490700603240d5038140c10034800c9030002007106907030750104a040d60b410404160890301d82ea80702465410086000d900059262204a4512164030702050401d8400c010400c120350f08013040c0c2e9140e09017840c000b4076140080c8210000500305003d031034054036008070070808413940020706105039440c0c00b050000402c0d80b040c0c280c0c0d008030306100011740740d20345032800f000c803501c10a80c030142c1e0303030440c4005010108050141081065004200310002d40c00041440d0041684d038100c5000f079030740c3c40088010b407151032481c50301400f0352000022400c0d00000074500400c252500003131000138854074140d41e80000d01c201070b4002c0c65a401040082d0013030481200311f600240000d4a840b80c1070300850034a114901c190100c090303491840c200c980006101c000c9100d00c082c50700901e090044245601342d0341c001101c0141c0c403030300011a00f909 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670826 1250 669576 669607
    0x7020d060f02070c050108090a020f0604030807030908010c030207020108070513050a0807030506090309090606030403030603080f04050f0117010501030f06090c020303040506070903020102030418020c0f0d030605010203030105060d02 102
    0x6403940144288040540405900060b410642044802ca400f2003004200d640c02890701d680310b0308000c2d00800341d242e007580070411040300300a2042e402a004000100c049560100105541c81c02501e034500303160b113021485408c40d00d51a054004152040c004400181e91049815030000032500c0c0c10394035212112000003108000d94001d40d44002030900029a0a0000c100b2100716401102601c51940e1401040c540360720600b40c60542c8030107044001540c514125015641081c000d181c002003007600c03541d510a2a500ca0f10800d010741e0030200e410040c42c079060103041c440510a00e0808003500006001520403d41130068505050b00c407880101c459889a000000a14458109204c2c80034143c60180d2a075000341d505442c0760107444006031029019000000c2283d42c181e004501c0c0624010400300f0140c0b4010041000d90740070000e004230948104403642e6509103000240c0511400603102800716003896202505542041c0010000e40d03503590305480c80808486005681c0303400b5029201403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672076 1250 670826 670849
    0x90307080106050a0905010b0301030602030405031207031406010c050706080a0f02070c0306050c0a0207090c03020c0607080907060207080a020609040204080709060e010905040f030309020a05060706020c060a0608030a050702 98
    0x105849090000542004150014400c45105403144000e031074480a01500f035500034011810300041c10401040041c40c0d0342d0045d90703c41c0c014410350342000020840302600b04803e46850340003a071030301100045c800c01a0f10042c0c00000134244080d1008403039992988330070315480745d001848000300015801d401d481e0828000208041411562070401d49001d0340e101d19280403d85420389014001340551071a1002c640c051101ca40060250504d0321034030502070036030a00c80204068091107044a0240d040000500981c1d9a807184801d51030042101450880d0590001c0119805000d00300000040031400e0807840d5010740700b05503181d4001c40414080e12981c0d21562161080c924001980a401e52141342580c0201c0b03080b00003642c4e11402c1c40e0940f030041d580a45030150003c0944006806a80138009591010b0105040039a60b040006c040707806c820400e450058001504103004ca1060242c558000a0703200304004050500884d182c0d2030082e0314450060103c006110b03025517441c0120350a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 673326 1250 672076 672079
    0x30510050607080309010c030908030103120e0402030108010902030c0a120305070203030c06090601031202030304020603010605071412070501061203050a120b030a0f021e010e04090303090203060a0b0102070806060108040303020a020309 103
    0x155903025603d4034141c260320403a2500220b510f444484164107101e4050494500d802600c85821039007591154005002650078000510500c4550024039456500155000b4501c0000008071005940181400c00c242c04c0c1901e0712505450034240072505107802c0c01200c1640602d8129140d203224408240742d8814000803a0140c410300703007002010040003072028103a84c42030380c440000d5032902d081680d507804152030007544080e041c801401400c1c802e00c00b0380031080c0142c0410681c201d05482d034604190411521004a83c40000c1e10320612000340220784c000d2000d0b140f0002c1e1a84182c500801d28000d00d18042c0410041d900031150000b00358100002c807040080650b08800220701c0c01d803080c0f03170300a00100d00a40307080e620100d0102d90340b1440049002e06031220154006a80c0c1044000c2408080803030034180c0d07900032080944c900300310032441181518000a0105c4000001a00d042d40c580c0c02151550b12080c00c0080703699000610540003541800d0150319031001e40010b80c1140076180089 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674576 1250 673326 673339
    0xb161406070210090b0609060d0b0403050d0b0d02030705040213030506010e04030908060601140d060905040b0f06150a0305040303060b2701090302010903020f030307020a08070609050103020306010804020103051005 94
    0x504405020403101c0c0900555000c4a1144210710150b03015100007060190240e0500d000242ea030b070a2040ca1680d00a90040c10150003110b44d84d51800320120030386084e0006400802d60649145e014850034468080031181d003410040c60f83d0001e550384038603010345405180c0200740c840d10f032a0044480b402940d4800c055039640d6031030300510103c1030f80c100c03026400618090320000c1c07600d0f400b0840c81c3c0514410ba4070000e1100d0110403030001030703114400000b111640c5450000e0600c00501c141e0340240d12070f108192881c00c2040311040c02e503501500c1c4034451898131541c41400003603c4200d075510303a4941400308050790345003000c1e4000d01c0e40d41d0211701240400240110002040328104401c01550798a0a003144241f100445000e400f074000240801c01c0c01c241440985805841c458552070000d00b1a03103030900c00c4d030124280124a50040c5026400140306021464006c414000504400c2c0f80460451a044000074561000604003074141543d5101146000081c9442c0001400019290 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 675826 1250 674576 674603
    0x9010602030a080f04020d23070603020304060605030105010e0f0903040f03030816030b03070e0405010204090c0504030501050901090206070204021315050a0206060d0c06050307020102070c090203010504050601030501030503040b16 101
    0x281d201c1e40141c98000010b24844000b45584000c403641d80d00a41d005802c1c600d50410650b500415404010803069545800305100c840024080001401500981c0e41c05a201d082a14040c01511003d810491090741880010301c040e480a140c42c56001d0302c41d008000c116100c414030203046110302c0e0000c0400e942048004414543c0001300c1c40e002340c2402e0482c0214a4100d2000c030b04507400315044591541201104101072184043c41e1a00280a14001071415644a09110071501d512481801003040800c04106002003845056800b03080c83c8002c5c4a2540998001111407003440c000034443c0b9800300304206044552503120020b000114000b030340c41000c2420190031a008038514800510901c0c0004041d818580a0241c110303038418840f200e00da08000090f05d00d0f030001400141159403d20040b0042950301e142d400050001100c0127a40b94103142c140829204000c00480c181802c0400400000e4400400c64084480744608546c540103c0480e000c2e5000c500d00c400752000061012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 677076 1250 675826 675839
    0x20d020a080604050903030106030903030204050306040b010f0b1204060207030302070c090618020408190f0c0312030501090207050705011404050a03060b0103140c090904020f0402030403030b010e0102070e010311040207020901 99
    0x2019651580c0d01d8545103a41c8100070801921800c44048030786030414001005070500036041458414464240036051a4a85000c24a4004121010745a00003031000400107041065184c0c2d01516400203041d1419210450080c00520042c000410351540091000185840b9a051361040342e4403180000c0301c150b4420355135004e003509010303a82a03610a00010725210481e4030848045880300310103850070f0f00c510605240b0b03901d44103609482000805248170b000807400a5980055407055400404100d60840001d0807600141c200308902e0303204000c03110101c1c0d0700040d01c904903074092070b00c0c0143c00c00034100801070f4022903000c650480c25049012042180c1074002d904d4002e4281c0c1d0401140403454810a500e0205440682143c0030401502e502c60400c3d091803076205001074903070502440300c4408038040340e108490513400250340d03812050156a00c10b07080700d43c200c0248001c04082c1d00740050b843c90b402041c0700090206544030306159580e1900d40551351038940007400000769603990384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678326 1250 677076 677081
    0x40201030906020c01060f05120c0402030402040605060c0f010c08070507140c03030a12110f070b0402060f0a0f02010c050406140c01090203011d0105010603091208070c05010501230301020712050a0e0301020d 91
    0x951f0104003000240486c030f0381061981084405d241c100100604860001400025030002e03205a80003612680041556120140100609001280101101c4048044036801c681e06d5549042c10007200006010042c0c1d40b0406841c84103410040e6484c0c9181c2036043c00e03107403050303602d141600340c04081051030819401100b1010b45989100303091084c0c04119204102911a0086e010000e040c203101c1c410208480c10499648944043c0815113003044081402c41d02e030708180419000904507620800c5501e6081c0100115441e907414564101810f2900107000c15100c690a21030100303000c40c880141040035040209a641c02800030800704962014428804151407400d0780d056080c10000942d45101e40b0400e8905a0030141c0314080c4000f00a00f02c0306110040d205004014800d200000030843c00c1c81400d0080100c5a0342e100e010001c0c46500300d01d00f28075480188a03074814400840410920f01038810204810315141d542da0219103400d0b1202d80380103003061303015032002c1604900610030347d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679576 1250 678326 678329
    0x203120c03060108070c0609050304030b040203010e07050609010e0a0302060c060106020d02060c0a0806010216090605030111030906060d0203070f030302010204050405011e0302010302030a0204030602070506041103060108060708040201030906020c0106 110
    0x610281455612050210501e11080e07401900007030380c038000189800c0c891261040d01a02c80c00001c503035285603032102c600c1c540168100f91214020b0100703000031442e00348170705003d0003840703400740c01143c2c80c180c0040d1150003085003841c140050b10246680950b221401e09000d164024021a1144096464070766510400d018100161240810901c852400001c48038400c3c071484440380c0c0361601c1c0d00d5003150448000b8000c28190711401060754000c1000380c1d003c1001d480302d1900041c02c0c0386404101400d498254046220141040040c0500307040c011608d07070340c0600140c1e4009511105840860310748030781540815a200c2c058200441010781c1174008100301c0ea01120705101d0350340c844c02c611203500841001f080071200540000c00040d4042e4010b10b9102025910040c20300f07030343c0c0d00c50209980c0200340454407030b0882e0b410003041060704450205564002e030001d200d10340c14501100c0c0c1d00da6000d00136100340002c0d8000282107a2280d00300c961000d900c60015516a090b0341c18141c0030744100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 680826 1250 679576 679597
    0x612010306020d0b030a080405150d0c03090506070509010e040b010207120501050703050106050c030307030b0102010e07060c0203070608010f03080c0102090a060c0203060604020309070501050304020604080304030807060e010203040c050405060f030d0203 111
    0x84c190743c49036514000900d0b20030b1541009003e1300d0240340004010640030400e00c84c1381204410b00425011840340e21405c56101d111f80c50115440f400c80c50321604044008008009206080c840d100459034010703c00110084103603400550101c0c0840140e14020140c2d100031003030404001c042d010000c0640001d401100507440a110f0742e40c0301c0c03c003503c141c000c42611002c240d00c28000980114401d822600340c4a6043c000010b010014201903402c00509400c50305c003044544469600b1418100711403002410189000c2d1543d5040c0010100180668400035010480c08a25844041000e504031051041e00400303050000307958850207024100c0464007a1300c070780501320000d26a070078a4000c6a108009080140c42501d04000040d540c9810283c03050380c05c450244408030718000c04000804c05507006103101c6071100038a2030184140d0f07202111900703e90f40180103000000c1e960b00c0b80d00c01900d00445002c2200d0f80d41c02c2c04900c0b101c8036264041c3c1d1500c60201009401034021005003c42481c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 682076 1250 680826 680831
    0x405060c0f0102031f050307060e0402070201030b030609070815010305070b0304051002040f06020d08040503090d030908010c0203030f010b040501021002030a020d090b060102010b041506080705070b010b030601030b040504020108060f0612010306020d 109
    0x26540304140c1c41c0c0d001ea12131540440d62b400c58202007031510768001d0074614414180044c0000101001c00e10307003482160620310b01d910050f0180b01214040041c1b4513100311102820002351304556580e91076090910814186e40404404030341041800d10103240e5440550004644865851880140c0c9861502c201e802500803520303408845c6203d11a110f00ca40c1d00980210f14204a03541403002084c0c416000340c08020b80c42e0f10108a5440070f0065190385d40c200d0f4011a200e0070f150028481181c0b047e4010000030204002c1005180d8010071203403484800100b006840395900a0490044e2089050f6400c203203103010b0040302000701101c40240264000e17402042010781d04814417080320b0b450450064071604548003007181c1489040c002c0c6d440507081c03410900380609170ba907403586207a0a811040510350044104540d950781031180f848a4503044406020600307041e000a000d400014020ba40510f1031043c4108007038a13a0022140d03c0419045804240d40e5681400c0e802504201c005100860 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683326 1250 682076 682079
    0xa0305090307020d08030a0f15050307051002060c030a09120804051029040b060706060302030c010903080a0f05190806040b03060408040603020313060c02030307020601060906050405060c0f0102031f 87
    0x4001007941c0714141c0c0038001d400811800d4170f03000d40d0754100030b02e6142541e440b001d410746501c58601a01035904d010340500704526047c20b08050500d80c10342c0040d805400703240c40c4400d04650000b8420380006089030340c03c0d82c0744c490403607500180410000180c90088801141005140d024180700d10490086040e030321011003082001c820344412600d50f4a0300c524002c60007c00102c1d802c0d91795800070b0010000128440748c080800e0b80d0b604418802d07582983e80301410400d41c1010700c4610382c00d010904c0c1070101c8500716598840d0368001c0041800030440302070301821801d030040b4102d542c03400c1072080041e81310100c82002480c076030044480f20b01550404c820800c40381000100140140d0340141281d0504c0d08221085000f9040200f0450858151003c000c001c01c4003445617070b50400d0642d01440d601e20301100040d18290341a8000c0e0308228610508110080d80171054405581c01150101d80d05e400c40c0c2d9140c0d14018101070072503441d510001c144640d04070f4250481064a08240100c0d43d0107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 684576 1250 683326 683341
    0x90603060501050a110a020904050304060e030c01050409090201090f09020d0e030f030103020913080a050c0d090305060105060705010207050105010609030309060503060306010303030e011803030c1b050703020103050403050f030a020a0305 104
    0x6940c14480d16021600622003050300f00d0140c50301da00c0700c0c80e81c0000c80700c000300c0a40001c3c40c403510a54003030b204d0f0f80000074203020440e0b02103c540e9401000750010044840c403180001c0c00e40c80349200d0380045c00d60b40c01c40318086a02c54480392005041d500d503e468001e8075500884020750206a1841a2a02e0400d45000300b01000c02a07503940c127001340d500c50850b840c42e000e0040d20040140b0071180500c940801c140003401810151500d0803441e5246604c8044550f41c032481c2c144219040c0c0244017129030b0030800604001000c03810754a0a4610540b07503005c501d0210b0190188070340007842d6500304400800d2440e400a49942146d0282c0c1d10444501d030b87c3c0000341d40a01c0b083e1001e6030550824001880420f029402c24086616154000601c0b009141d800b079071942012070301100000c0d00ca4004524465101103022003e15851000c101504010750740c2c01d40e942801d02c0000c2c18107498100280506000d8403d03503c501c03401d00c0d0603036528548400344600a502c4101900c0201c0e25000200301103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685826 1250 684576 684581
    0xc1018050f0d060b0303040305030a09050a060305040209160302090301090b06030c01050c060601030b010909020d0b0108100b040e090703020306040503030604060906060206060d110a0608060a05030109020105030a02070f1202030a090603 103
    0x40702001c0d00c07050240d5101d0f201d01d40074140340504142c243c4000c100020000340100028030101000d45c2d201e004a900306004c014a5002030790006042505010600015a072055080391300030076400320000745410079030400e40182c05201c001c281d040d481c0c00d0643c2c0502c03100108083c0b245200310280c1d007034509614019246030088880c00b804590103a40090300e554003a5000400c20281410a0b00c07030103070b40301800700c142d901061682d031155031105811f8202d0750b08506110f400041080d010305005040c2000080c1724040c503c5a9005c60f080f140c0032500c2001d041c0a80c2002c2c50700607003511114034060400d6652a48180d5100c1d0140d07240100008454906204100039070314030381c1c09420251a914100304054000002c00d54002c00e145103401103e65424a040f0300400040e15004110b14110701000391005241e03105034026418154504010707a88182240e07800000300d10016210305407420490b5170000915401441001c3d0000001d0b0501e40000c05040148404d507600c104164444608409 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687076 1250 685826 685849
    0x30905060a050402010203070206030103081207020106080a0312020408060c0301031208010f0e090f061003050c030a020607031b0203070306020c0c011d04020a020c030105070905010f030501050108010306020702030c101805 97
    0x24640180c008030381c006540c0e402a0f0b4100d40144110303800e00440b900010102d41c0280d00c00c4402c500b0000d0a40030381102c03040c07040e520103c640000c00c03c2c10314009065441310b4030600000c00b005401c110b40380380d0000c598141d8025041d000c0c121045403a210601d050950720a010641e104007002018444140c03140304814142e400101d20020f80506c2c0c10180c200b00b400c090808400d81c0600122519440d030304200c002d10440e1031280c40d940051075410076030b09102068105a010790001461040580c44a800b150503042d4180380a0304000601d0301541d90030b500804000b075050045480c0001440400d4020300034805d003920503220300d5000040192880700400d01d00c8400400000e8000001c0d103895070191000700a6401035071800c40043c0002401c4a00803504000400d5020300c0900c02568004041d00f000c0340360b818100225410040007818084052100030016500080e0380030840d10248180d04d00084040c003034200035041d020002c1d005040030f801107410140c0010000070646800e988501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688326 1250 687076 687083
    0x2070b09030c060a0c020d0308070e0604030b0705070302100207050d0806090403080417040503070b04030309060807080402100302070f060b040509010209090406020703020109050304030c08010507030204050616051608010506040506010309 104
    0x212500b5001c05105080c0c008686075410710940141100c09a154a120300721814032076603581d65a4940071307001500d07944d06242101d0180e00123100900000340301481c0030380c01000b641051a103400c5e030b41c54224602010810031882075130010818404120000500f4840c0800540300c808055803514144800360000700c0340500090080004180800c0f198002080e0b0b0041c08582076103040d4903440460318100b05980460100076000404009140c1e120341e49101410f41031411001d5402c007054014090440a80041d1044000c2c3c03800c0e803115400f03a030444400e264030038010145004a4140f0a00034a07294155500450402001900f81c91042c400c50f0348101004005d1803031a00d070782d15480000d40091500b2000e640da81c603031030408248208081c5c0300651007040c0060201741440ca035039003582e00c00381200c81810b005100500c01a40c400003681c0c001c00381e00d01c21042584181c10182d242c6992034469840010000c000031500c500c0640211f4401c02c0b0a50b401e000c5900c9010044007101e01482000c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 689576 1250 688326 688333
    0x20105030a051515030109050a0902030706080a020409060603020a020709110d0509030702040203040b04060b0a05060306100909020318070803070305030402060a090504020a0302030f090609060a110c0102070506040302070b0903 99
    0x40c0c040340303040d44040e40160703080850a0120300709070b0104003c03500b4a40b400385014004001040980b51a00a0541c2700b000c0c14030a01125182d540485e0755440c0501449040c007849a000406441c690b5042c3c80052602d0402405520359850000d4001d500804c1c018005020300540441c01c1072450041c868001000d01c4a980340140100c0d01d44000d05015146200c180010031207800580d0321400a503003d0344c0650094059030030280303801d0080311130f081000c5000c0e0f03c81c900100440d40c1c1c1c1000380c0358007500c2614103003040106244211f07000d0580b504528403140c4044107200620498008080c5951050001c648400f61505d110340c0c3d99000c0c40358002c001820800c0010014140300e405000c1c0607615050032030700c0e0790b01c40c03002030140e0304a2000e80c00000ea000c01001118040380c001c1641001190014101c03034200402c0c1d00c1e846480003028042515111503404800001c0e050071950004000c40c0219183c03041403030115104c5074196001e1f8018402c0a0340424008400e0040714030b8050000c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690826 1250 689576 689581
    0x8010e010b0c030f12010f080610090209030f06040b0108010c090503030406050a050d090f060501050d170c0a020604080708070b1903090201030b040207050106030201080a020a020304050405130507031a06040902010503 95
    0x703001d6198040c0303044a8540c00b007403202c200b801e003c0c07502030044008000031184182d07040c0410f02c0340c0408581d00222003076000f0401d001c48010380c00b19000558540c000090f81c0e0301c260030042454900c03000c4440d0b210348034210401007804520030095040e00c640704000d1048549000303085840c81500d01489616070401c00c801c1000b107024000038040700400d03042031401c04007290b508001311142d01400365905610851010f04100d002d204040c050710089038414100481c0f40c40e0810200f090540d00c8050410018111840c00000c201030308290303a004201c03954458a4445060b00c54103a841440c0080c1300e15071001c07654420314003c1d6480c920461103d610b0321203200c0d0f0110045c000b0090280d040c981d9400212055031150b00003410b200d4041c00c004180907181d44001056070340c00605418030244140081c1c0482c039804000c076000c443d000c5601045649a0070130210050f040414010020710a8800010420442041406000d44042e200f80300e20755802c001d03c8227542000c54000d0024004000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692076 1250 690826 690839
    0x601030c0905090402041104060306030c0905010602030307030e0102040807060c020a0501020106060203030a050703140103050a0b10050d06090c050909070303020c06040b0d0510030203010e0102090405010f0806071202160c050f0108010e01 104
    0x40070343e80304d40000c6c008150104045c2c0d103804103a00681000001a4aa040620500030714003070302d00040031224401c008030b40c074145000b5240d0101610040416407503c025400165094050343e0180c440c9a007910001035860710017800071141000224014141320a00084130342c010303c140c10840c0d0068000e1032560340c3c0c42d20071100501c0e00034080424140e481740c06892240885503614003035840f5200030726a03890a810b0405d0320490043c5030034001442c03024140070644680c1103a4080541c40040481c2c558401d00c0c0c20140030340d09801c01600f011100d01082040b03800001c1101c01c50b400790b007e0714415500700d014810b051040f030042d8265118100200f594503030301c0ea80401c0c3c1c890021803a032000161250b00003420364140e6001201c10340c1d00401c03404038a240a11030940181b01c000d0251003410b142030350b00380e191000182100e00b0700107070340c8511a850040b90103d030201000d0502ca1150000f0340e1904032003400c224000c09000e0818030004000c0e9500031702c1090305889100942ea28142c0c68560b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 693326 1250 692076 692089
    0xc0703080703110d11160501050406050c030405090a0209120703030c0201050c0f060f10050405040507060302090d0602030a0f05070c020108041704030605040503030105010809030703090501050304020a05090f0f0601030c0905 98
    0x902101040055800d6003e103940030300c44200640155650200541c458540542c84d004074000014103202018808000036a00070023180c013200c101e820441d8450060740e050b00c2c11802035034091a00b00325084100304801700b1590042064500845070403080d80b0102c0e1100713554005500005020030040001c8002660041018146013025441114644075050108604004080c2c59906004a040d020300011405a80c0d288000c2e003025141000580740c603860b46603440c555071284109043d03002500200d00d44610030040002030b0046010340d56402d2855400b40184001407110751141e1078035003c2a1103d20070340d40402c2c0190160b44541781c546a136110450907800d58012100110010070000000690034002c3c60b224074003890145459600d000005000414020302180c080d8000700160000a900801c00e64180d950030301e410b075141d54451000c280d01c10324540260f030307020405a00308601c03090b00d0031020340b240445c0f80307212800742c48903001502a101c002180b01c0c00300d003428034244418145403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694576 1250 693326 693337
    0x70506030a020405040905010c020105070f090902030403030204050303040312020105011208030402211002030105040b03070f0b03091f020306040b01090503070b07020301020d020301030308010f0506030f01120201020a0503190305060301020c070308 108
    0x20708010300d401d0351000000c04440080301c00f211240d440b19106114141c080c80380d180d1042c80c9017060b00710a405500018a1030082d402202d02c070725404004542450710a6042d2030141c6409000c4a64964427030134907a07011039100340305034010f609110011505515048258881c9680201c68600f035071aaa403c220681940f1101c0c00074401004034002d035640300420081c00211031502c40141c3e42d50401d002d110656411910a602030b07840401d04121271069101113804464820014a03200d4a80e50300c3e09040ca41c60440c0404072060341000d00c3c0d86050039a00450060b601110200000351070b081c0151507501a510606a254124072002c104880300d04009101c0c1d0b910003400185080c1e40760314240e080317030020782081d03000070000c00050044e0014040307024003400d0115106406e600e00001070313580342441405110141c055440840d021a4020000440c20f15404000d80ba1104c0313804d0b540d00500010200128002400c2102140d62824107101f1200720040e0207018011090454070ba00c14680e104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 695826 1250 694576 694591
    0x3030c020f040507030b030c090601050702090703090203060403031a030607050a030f02090603010b09010207060206060303070210120f050703060501030605060d0207020105040b0310090b030102120114030109080d0221010807050603 101
    0x1078100e03818160385a1044520480168400003941120304080c14a0070a55902c035501402c2003c2c103118680c3c0c3c000f816549003d50403940c0c00342c559191001203001d41002c1c2c100940510526007404201034141d0446058500411171000210340e440c4c041640c1c4020503500540861820041060700320b1194200e103404a2401d04090f1070000b27200c0105d2035940c0240d104120810b000700e003040e41581e041c45050014030f414801007456050500c0020f03100d102d4404000d10641d81c5001e003603d10b502941c1d140c1d007420b005850402500b00d44514000191008413000d50000c1e151400c00f1030198000c0c8107d40558a000d0700e021304002c01d41141074000d5214071010303410b000003444000340b04903105008600c10f10707240d40141c070613a1903c52541c00b91041130f600d4031b1080c0d0050104060381510070003150f04445180714a0702255400700b001c01e00510402c040039200c2c1b100000e0f15510002246c0003051070410940f80c2d810040040c00c0a0310002c0400c0c01540c4680c0c101c020100030070302e00b1801540c5c00032030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697076 1250 695826 695839
    0x8040303050903040503070807030209010e0c040b07020111010903020601080f03070308010e060a030c03030302130b070503070303050c0c0307050c03060105030a03021005040302071d100f05010c0201050304110a1e060509090103030c02 102
    0x5c550700000d10704809035220020b039520200081c811402d0981d00140101300e8450340c40158140110584c1c041d00450003003150707500000c030300202968410001e812781c041c0001d0080010b4150760400039240c0c2003d0140c10094803580800500b615000401c0790625034140d0f844440381e074200161240c10740300c051b000c0f0307511131003040e0048045035840003500015072194030010790300c2e85580c03807140134080207920034403280402344490b001040c404400c84031200d0381071600048036039445240a00030700034070303000442c80d00c0049181e208101c4005005103464004504a48183c6e90701c0c0c04042c1d603400a4000240140c004951003180030b29170742c01c8150054400c1c01a201000c0c0c9407a1800c00e4540b48008024882d00080c00b40f180d407004500080024041d011100700d011405d090000c0c001e136110700030003810400c00200090500071141d528141890340104141d22169480c0501014182e42690007001d000d88000300007150340c0103030704036210804080d0004103143e1035900c0a0301c400c2103060003a42c0004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698326 1250 697076 697079
    0x308060a05090702030705010501051c061e0e030c01060902090307030308070c020603071706100e010c02010c05010203040f0311010504020d0f020301020d0c02030309070501050301030b0c0c100203011503050a0c0804030305090304 100
    0x5503600303002d03407007002203600440d102c100c070b4102117007560b01c180c0c85035004483c50082c0f80540e003400c0ca00d12440c10b40042c004942a682d411103010010f0740740030801207407440c2101504a610001c4001d01102403008001c0c44081e07101c4800da8200d01c140800554035510401c02000000d000b1a0210f9000c4243d0800086041c07480d008140d039980b0403200c80f400180da01d50140d8603a51110003454001320244c40c40a040100020040c203030550740d9181c0c5040c40080b030742400c21a031003803540f2a0300980c13090007551641024a00542d802690170030480214100030440c1e0040368051080c54442c5800400840c0c0038201d80c1c41c3d5100304a000f07402030380c00d95000c00120508454034000d1000c1e00d900c580c01569280782000b1440d081007500e0300a103040050802c01000411900020b040c1c0281810000582c1c42c124000d26915050400018141c180e0005c0000240d04646070304c0c9180c0451a40c4040c005560f50f50383e4a01110307401c584010102e1801c0010501091199022590101526003124500f5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699576 1250 698326 698329
    0x7120507080105010305090c03070303050d090203030c0a020a05010809060a02030703020906030907030c06020703080f03090313080a0204150b03150316030506100806190c050702040203070804060c050901020a0308060a05 96
    0x898049800c40085030301040104240c1d41d041c071039190302892070030141080e07040e240002501c944103844041c0030480c0c007082c021041c0c0140c0d80204c8001e40c1c003d0440ea9076090030301f01c481e01c4080b80c50060384201c1d42528000790711350060078294820100310015280d0760342d609840308025040901600d041603402c0c00b034101a6100d0b0710007140210890380050440d24a5460101050844c40d0010700854120705010000102080705480380134041246564803583c85180d09842c41c094902840b0300e110004170700207074151001c184004a00e00913102440380c0c558441080050a80c44d2184184154003080060343d288400d209d903000b400c40080035101002c11102d80344807140b1950f0030680719904040c0600002030300000d1910700500c0300c10702030509441c0403040100600c1044111201d0f01c2c1c1ca428120f404140728104079010079a0041085403681484030004041420440e800c42d425072a080204840e103000d80203440b0f01c440141d00070b20310500e061b82c00302c034408000740400c0d40002d00180c0c040b82c85d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 700826 1250 699576 699581
    0x703030b06030a0506040b0411070b040f0203030f03070201050c070c0e060d02030f01020a02010b040606020c01120204030605010e150109030206030106050f0d1103040302062214030c010c03020c0705061804050712 93
    0x3d4070510800b24060030100100411102c0740c002c0c0c24403c9161040c00d1081c0140310003902d81a541002900c0c42d1a07a590810001804030104025818040054071040420003c00558060079940c0d00810141d5207030f1074440d01603c6010310152026070032040410062a051104551240000e41940301804107580400c0c030b84554400c1e01c2625940210780042c3d10380d424411903107111001c07602809210b140000180d12901c4580301c0a0411004210400942c000303074044800542c1d02520401032503942d40c034103011050b815565616041800d8040d001c2e5507104e202c00c01e056070b030010507041c075503441d14206542e16803101000654040302800244400b500c2c9100700c01d0403095011520340d8910b8149002800c1840040c16030840b2240c031a8459005445c545200f400c1c03d07805151038103401d13050300c9540e00c2d60140002c2c5848641c28010300403d016499000b40c20400ca200049030b8060361031710208242d034090721401140050100201c1c8800740f909030403040d044010750420311080003845015005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 702076 1250 700826 700831
    0x1030207060c0519030213030303180b090d090e040b0a05060406090501080c010305010806010f09020901050405030a03020c010206010803090108060f04060b0f0301050f0109060f0e1507050601080f0706020706050703030b0603 98
    0xb0031000702d013100034500540d6841d5440d8840d4a011864001210500c444645141c0409010960354031031212803a04800c20242d600c51700025070982901d49040c0c500d94030700d01a808000012003c000c0010b103007000800b0b01340070f258410501d00f803954501075a1401000700030f03c000c0e449921038000140130403481c8101e501030900700307000e440240e84420002d020380e034040e4003c107542da01c40307801001100034800021080c3c507000500540d4811041e00104da07540115041143e0500410100d501010b40000d4007207001ca5085e000e903a001c0c0e0b41c6000c0d05440303000e54075010340401c0c0741c040004c400d8074200c034510384c1c00391004000280b51525400c03404a2034000c50110814075000000600c001c1c6020803581d04510024030b405a101420b00c0c100074400c407035a00048091228078100d08405070380e05000e446000b9803a10505440348074504145940303010038170405d01c1c1406135600790642a10041440c400f56440b82e00200095850800103c9090340b040d8402c1d800c1541d105440202c80c0d41d220011030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703326 1250 702076 702101
    0x409020306040c0509030601030303090c0e01060201021215030a0b04170c0a0303060801020a05040308070f05010507030902041805030405010f03060503030304030e09060301090308060d02010302040305010e010606090e0402030703110103020706 106
    0x140c580c41c21006010446003500c000d101445402e0000c01d50700d940018403103054a034103240200f105800307441d008506a000381c0010221751075a60000c01c01560550140c02803800241d0308070b00d0b81d2502c1c00340c0d0301d0380c14101c441c80c7c0d010381000b4030303210101d5901070403140c01c10700c07803000603002c0280180300490365084020034900036000101d089040c5603050250310007a0a040c40218944566044081c2c4075100394070004185460100d01802070022940210018517040781c0244030a01e010400140200b00c80d0340c04900c1286005208021a0801e40180025940c8403004500c1d190a040041d03070b4001c1c0b001d800c04209620b0342404900750f201803000d14000c070311030b80380d8103084a00b4008100e0000030003031002e0f010b030b0b250280341c1c1d001c60f900000312030300700e00e00740d0b07903000680642d0004070040d00c03032600301130002d60801c00040101c2005500600469145a035101100ea0319800315a50044041d640170358164807a1a0900110314500e4440300f10035014180185080910b0b5078000544100c3c01100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 704576 1250 703326 703331
    0x7050601050108010b03070f08040201030b0a0312120603020603010509040507030c0303080406050703050709050f010203040306050c04031202030705060606090f0d050a060501050406030503070623010b03100509040206030f09070b0409 102
    0x4000035600f090a0702d01500000c00701904501d8056001069600c44c6c0016a00300480c030170124040da4040d910103010014041c0a030300309a5200c0c2131000c10011400600740028a020041c0d030301102003403203040142c230341c010b07d110714507442c2208004441e01c0c050021389090051450000c0010300d40c0004400a500c252903480c268a40303804c0200440d84014514028142044200300001780d1201456003507503011699200ca107410040101e10b54000d035080100490b24043c14070130b4001c0903201410480c0c0c440c09200c002402a043c003281c6030701900c031004229034820004210580382900140c4412071005d011150070044900000300340030545d41040c0d8454119100c804280314060051360301400083e1020320841c0e165507107007640d81c440c0c2500940607695804040300031161844602400040004050a15584480070032040b83e00c10b0b0f03040443c0d08440c440000310350400840a510440d0010910341c00c642e58500c80c2413030840028035010f81e43c0184003000c036060b4505030180000e0324228100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705826 1250 704576 704579
    0xb04020103110301050306070c0c1706091b0d060b03010f0c05030603072405070804050613060305060102010c0504030809030a050607020106030203120702100f020102040503070603020702010305070806030d030903050f07050601 99
    0x25086507144944a0042c900c100b0051290351000149150042420700d0301d42c0302d03d5028200007000103666040007655001c0240100004a000260320340a0520402a180150321742d40c540e80d00070700001215904081580c030a840450480c2d40310020700c08002d0008a40388801040c22012903440c88201404203602000b40007d50504100560143c100c420f050b14034205540f503450b50012615603003008010000681004000030700c0d099800408000e448151030740030341c403941d030360940b03690003884002868040040c2140d88140074510b0000d050b511401d1a060841c0c03038400c083c1e0701c84058140c2520800600c000021001c01416100341764641c00015450f04510405050195404512400b90024010b1001681d43c44080e056410080e0400882d800703031410040e40a030140c5d40c000c0b40e2502a5400015016030582c0042800c24400d80e03040250780d48821050300e1104040d01c1458242e806102040d40240c025484050101d00070304001d800c0c82c00818610007158403480302182c40c3d4204000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707076 1250 705826 705829
    0x5060703060e090c010806060706090b0103030507120302040e04030c0302010207020a030c05040e010504050312070c08040603091205070f02060a0c020402030408070c08030304050c010305040804051008010503070503010608030906090a0806040b0402 108
    0x9041e6000144040980134007114000005c2c40c40e0809000341d841440006801010000d0303543c00140c69a40c80011026150f0390ba041c0035160390003400042c0c640310007485812064500c0707442202e0a40d210310103240d03ca078039151012500442c12610071010b40d0344c06c000400150341c402201900640c401e190a15080d03042c00d050005413240317590008000c0e81010140000100c010003039402c6400a07000303008255480d00001c94540c802048007908a007030000740030894660607001451140c2c0a121022100f5940d01c4044403148a20352000e00300c0030380e909182005151900c01848400742501c0c2070b1800100c04d80004007207910a036801c54070b8040019442080001c4401d1207001000f8210245080d850540c44150f182c40840505904141d902c40018040103c0c0c20180c6001e010058103c68602c180000701902000d800e000301b80c800d12a00c14006801e1070140a154203a60010300614102030950b418844150883c030021075002048a030042a03c01d820000c0f0b900c602c0c0200300d4035840d03042500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708326 1250 707076 707099
    0x30302070909030207090b03010b0a08010b01030605090f0402010305040303020c010606020106030203060c070206040902070602040b07030c03030b03030301080307031b050109080d11040b03010b0c0c090a0b030709060f0b030709030506070306 105
    0x10700405009041039401000309802003001000c0743d088400104017039411030b0006c0d005040300d181ca43c1d031085404001180e068070550240001490a890400c0701c0e503295010860120030455011168403c200d00150065100b50029500070b442410094208910440800d003520b0140e042080140e54036401001545410070104d07070016004800301b4503085886e00440c05034402c44c000d1041d0660005803680402070b240d412540141440c0c4415600c07916a444c004101c3ca811820603130001e4103020000c40c0a00d004030840381200c403c040190301d8648165000d454a9002000c0b52402065420001e800718600780558404244228142640e0751542080c0000b25205072819641000e401d00052106400010031a8103580941e00e410303460304200090039140134800c0c071407039410043c0e440a0040c4844030390021a00c00c0300c11010741c1c000c0c98a40e000031080303503030901c51848504807450042003440405001183c10005d1403420707140c000d84a80360180362103030035148503001941d1140f041007500c0803131 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 709576 1250 708326 708329
    0x1140102070e070503060613080102070602040e0f010608070c0203011103070305160201050108030a1407170301050a08030705030403110109080a1a090f070b0a031401030507030210050a02060103080a1110050103030207 95
    0x5200810050a11800013840d43c04020300082c000c1030300241911039105404000c000505c0140001e5503102030508e0000c008c2d400c5841a00ea4482440000c6a6025011028107040e0b07421580c54405540d00d000085540c51000070781660595652015000460400350003584598102d0f100030840741084c1e10004030030000b10305250304692401d030051003500c0000c81110500c500d11324200c2c6c000e90145244054501c505078008158100d01001148428502c1014504851f030031240700e031109540707156040d01d074402e1000050050700700300014800215003203c2e02d801c41806241030041e0540f20918035140442171901075420607074000b039044082404401c03da5100d504040604511421031203516582c0841e170090480b00100881d1040380503110760300000380400c10306c40103165542d490821700d40f100e400b40410780c0501c404180f2554820701030400c40352402d0140d0300504003a840d680b0b030f02581e500007a002c04200000d55142c115032103400c000740860720540c201c0004180d451498080d2030b05206 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710826 1250 709576 709589
    0x105010c0b0601200a050a0b0702010603020d0204020d020403050604050705030115050303030a050702010b030a060212010609230f040e010c020709050702030f030402040b0405040302060403090506040e01050d0501060305060114010207 102
    0x600036490000340340e407181541025081c01c01d000c2c0c40c0d28402c0680304c414004410400e982c459030014406003d80003915814050007403814501c1c98803000713401c07400d03624a0300000c3d400000e0743c1c040c500181000e5004003940040b428006051507200d40c2c2d0241050700a85d400e540c00d40c4501010f010514003842074489280f503c8030386d82e50041c50000400c1d100c1c000180f00c1d09035141da6000044405000307401ca100b2480740102600e241440311324000c002500809121036100f058000041002405000380f1001d0328140040300340d54144502001003007028900c88039400c600e0746100e402c85621a409821034000d5850004622044c4024000b864030b01d0341d42c00304018500b000280000e06402104030340803950346800041d5a507842d4000324002d8402d803428540c016140c00f08100038140e000c2180d5000c3c40c401c0c2d50740c601d02682e54040100c1402140980c0542040c80801041549050b888118a1a11400012950136901d03100d090500d6401d0780000e5102c850a00000004d603814000c8002400c1c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712076 1250 710826 710837
    0x60c0606080d080f070c05030406050403050705060906040506030912030109020702010305060d020a060e0303070c080304050109080d0509060d090c060504060e12070b0304050a0501050c041404090201080601050306040902060301030807030206010501 108
    0x14241c503c0a000c40106095030408980c80b14401d5a209000540090031281d40305c0d5220070060031a4030070b1000740c0c2c80380205280440c1300d01e000307411078518240080807542403030f04110800060f80e0001c2c000700028401e6000c0801c40400d40d00c0071318000c240c000c0c0d0058842c07505000240076604000c05507441030025610803070050780d481f086030b03064552500d050030b266449840807034a144207507000a8010b902e515000210000000300034000d13030b0003c2c0c1c0c43c414003eaa9840c140c1c0e40d5a00d9102d180b002c6841882070488a003003110103400c101c8840b24000c1003034100b94a0b0011070351142d801603000144000f1703007070107c079412904800450340203071001c40700720941202180d101c01e0720740900490240c0020200c0d0501c10300304054683d00380c10400801450511017040401580540b041d100b10804012100c61185040e100382c91080da010385800702c480d5143e00044a090340001c2c00968025540e00780e20740540c0f01d4101547c0a14490b825581d0303907c9090030041d103400b905a001604005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 713326 1250 712076 712093
    0x1020909010b0307030902030312010303030605010906050f090a091404030305060607020901031202010209060d150b030702030306090a0e010e01050f0a0204030203030f07020105041a090405010801060515090a080601060c060608 99
    0x21500304140341150320420304a40c40e511a901c044001c1d101140002e54903220104520311410180c20065048030320030384013004050743d1000195418109440b031071010550038407440d10342082440080111400003420221882e45440000084a840e001083c00c8014608204010140c05116041d00000700300d802508056055000994003801408014a4024480c08094200e8003d405a900c041001094162144040b40183d0000d00b2a20070714a60b000c0144c60008100700340c07000700c0e80100303451760280d882c683d103003c18400d5851000d005030840c1a03070303030200300c204990a01c0350301c4401c2d1a0b00000309090078095000c085080018000251441c4108401c01c0180d4001089540d90002d0a0690382c5644960005a51501540e8000ea0b160140b1245540b25420408010449a80111000c00240c2d0300c0c1c0300020f00701d981a00805810080b00d18214290200ca8030107018500d40003880c962020b921010024180030702030b400f51003c82c0040c40c8180402407203025040180100600409442 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714576 1250 713326 713329
    0x21b090c040303030b04020403080301080a210806041d0d050a020c0f030604020d0311060c0415030c0801060507060905010e01020a12090302031c09050d0806010e030f0c04020307051903020405040c02010209 90
    0x620a030b00c001800e0566446a451540d103413601960011500014042e490f580c0d01c03402592034181d510021202c0d0001c40d00e40a00811020b0fa202e0b0501e1007960782d0b80303240e580744010301c0014488440c0d01275090450b034030013003c0d00c881005403180b0480340d9501e050719024130716806894508200310082c410840c803903007020680c40000c3e20711780c426011030710358080100c10305045e541c00300a440c41f1001406001c003000300e80000072004000b00d485a19029075980f02d4000200e08a8500c86000000075400f1001041114400d0300a07117141c07401000002214842e5a440c81e00b19590b95840c007007035035008289000c103d500000d4600701091650400d102107080740d0360003034417882014400380c40440a6451440c40e04580d40c03280d080c0b141d02c2022104c158001c09000b40c030f22201100d204c0c0c0040c440c04050620b600f404035803240c0900301ca5009000c07200341d01c2e0421020b90001048a0100704040c040440d50360303c9a0b0348120f51100340d0f100141e0302c50401e01400192070031690340d4415a030040140e6441e6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 715826 1250 714576 714601
    0x2030405030a03030506060c07060e09010b0304020904110103020906070c051002060108030a0c0602090d0501060f05030304030f0209060102010e070b0702030709060e0a0b01020c040207030306080105010609060503040b060a0e07021b09 102
    0xb03e61501d000100e980c0c5500003c1c0b4a8000c4112550480c42500030100324280c0108501c01800c0c03003129002d101d42e9172141e501080d4401180c000b50044440780114000810700d00451001002c14107015080c80342d0000803484940bc020010b03035800134490410481d5050902002070000c1062018110944c1480301e0a6941d100384524070781082100e40010007803110319410303900e000c40010006006c2042a04205001c1c0901d4010b1010301e185802d0002202d00d0000201c2c0c3c110b0340c1c0114907040802c480d07002c016120364000c0c0030030305654880340d5500d050f41c810b210200c09003800d0140c054991000d801030502d49082d40e0451040b080c92b0003424003118680164441c0d00014120b03001c81c0781548000103c0c00e10070b035160039541280c00410000b00705901504500c05039440c00008211341d0380c4c1da10088502842910038000800d0080000c203001c10509043c0a90000700644401d480b40ea41e143e4654496404803220001070702b150682e1071016007040c8126050702d0044828000d981450251000c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717076 1250 715826 715843
    0x3070203060115120507030b03010b0609010e04020f04050a0312020105090307030804020d02040f05090703060f05040201090302011101060503100f0b04060b04260105090307030f0c0f0f02040902030109080405030705010203040503 100
    0x710800c0c0c5002e4035031501c1455041e01061052105009901b0a2000a40604114403000c2e2095080101141990403c481501c5800340165141c801e044003410030304c002035010040c407418100040001107015199445400001c500c00c07170b0502405007500d04024210b131005031180009420400c42a40480d601000721500150101c641410001007840020010941031032030742000743c2072608102e001140410b42800303c0b03000724800d00c070028115402c90220341084a009000c03540e12441031016503c90281400082c480304000560b0300d0b15200000d09d0701caa601c010740b44664440c0424030311008103009440050001303032828044a8100030a0f035280340640e019254084a4515035001c520b083c2544810041503240001c11103420310700409512540246c0c000d40100d0045000321551034400c4d824040000c1c1c02814512800203240c0d03a40501180381d4605981c416100c109850141c1e0b02032050724085807040c4203e036a903600e010145806d002c0c8642c4910306540050100f0040c2e510301060400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 718326 1250 717076 717089
    0xb0403030305091006091b020601030c090e03120103120905061602010f0210050c03040317100b07020604030b1302040b0406030201080a0e0703080403081c0504030c0209060f130f05010503030702030601 88
    0x48070ba0f40c0f0160946006200108500e0440c248000010b690380607a004100d408803c0908001c11640da00081c0c2c0d8a010a10000300040c054003c03c00800071150b00960404001e84252454800040030a200b094020380040d03030100d1400000041e465000107d01c0000e1005a9034541490340c03911a00005c8610300b000a07041c400039100480701a4030910800303d0301d060765501000641846011454160800c80302140455040c3c071072841b02c484051001131043c01030301c00014443d030508800440a40049001b00e801400911000c40014022074031680718089416074011482030b00d004101c161900d5881a0303003d18505201400983da0003909a58000c100c0c1e540418a000072441c203600e881c00310750010b864100042008004c1000c4030008204900c40940b950b0031000c2c001424000700c0da03068a006000c070740048801c8005040040b2403c0d4041d034010044014a201400821040035030041c082040545c0ca41407641c007548980b05030b0f809000250000c50030000f07182e010039550340c410b00404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719432 1106 718326 718331
    0x50c0f0a12030b030a080c01091208070e01050c0304030201050702030c090f040308070801050d0f03030609020d0c030e0303150603090307060f020c06090c0a06030e01090f03020a0302060a0203010b04030303 90
    0x82e24a00402805041c0d0005d96a941c0c0b031a40d80010542c80041d5229218040824401000c0d00e1001c001510786004900e802c28008141020302d40d181410b00c0b40c148000c091031007002055a007940d41c2030800696624050001030300d0645080c000e6a84003a9820800494400d0001c079140a00c0c0729441d800b0075500c96040c281d90440b0301b40600c03908581c641c0314407004502c0c5240c192519038040d09000900c07030f45602c0c201c0140e2348500390741140d01d41c88080c1445074941c5840340c2030002ca0543c010394250b040c603600a40d0542c1030320000a124410200200f82c002170b00340200d076034081d80f00704100700406450300d4400c080d4210100c1015180070f4800002c0001602095503008080003c2984407943d041c400140c00610a118080b001c56581e9407a14001804031850603000c680030317400a00c110501441c0c000d280100003000110030f40c0c01400100064070100301941e09407070307142c00c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 539576 719432 := by
  have h0 := BRFrame.cov_init 539576
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539576 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539576 ≤ n) (h2 : n < 719432) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
