-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0690
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:09:45.874077+00:00
-- url     : https://prove2.me/submissions/6ae194d1-d269-49f1-815a-576eacda826f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 123920863 ≤ n < 124100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 123922113 1250 123920863 123920879
    0x20609060c010f09050c0f04090807021507050706030605090a021c020a201015080c1017070c14030403030e0f060f030112060f060509070309150207030c050114071409010504 76
    0x21303102250141005141c03030307001001004045140c0c012058000e1b400c04484200080c1c003c1d090703401180c3c0c1143d8220710f80440308078842250060005c003600a12a40c0400900c55416500c0101030790400e446d40c032080d41c1c036040d05405030710800c248508281b40c1c851200508144aa02a04100384030789400d081e829440b4884940b801301c03d8100c0a426001030004148458885c410030401034410a400c0d8402890b29462541703e08114a83c1c6d4003071042807402440091040c150b180000c0040e030040140b40c100454003d1403404410011144046448005042500008180c030200c03179266848503401300c400d00a200d605c951070350040340c104505000c1c001c81124054003440c040e2240e000000d40b5222181003081c2900c074425404040203240140900140d2580101164000000d00300803034000c20728a08285001d02814483c80c1062001c112601050fa2211540d45102d0040001f03012024202d180300414150030b0351148041002c0c458403a10001070b8602411005005050003800d0035650604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 123923363 1250 123922113 123922121
    0xe0f03070303122d0b0102120c01090c0b0c070b0c010b030106030807030914010c11130c02070f1703190c020d060608060702010605090718030206040e07020613020609060c010f 77
    0x41180802c3c0d0350b41e2601c010207100d2080d04a070000d0105841000e0700551850581c940c50128001c1d6900e40b5100015942d034000c001d80d010a020200741560788006c80c580b283d00801401c1002c0300c0510080600042d40440041680e61640070403001c0d2090a00c3d01c1d08103442c960104810721030300d540b18100880940e80c00e2180900840c002d100301036a030a4140b030300803d42e504541040c08e6080f05c40d240d008850340c0c0f1410b05212640d000e41c0740000c03a401c6070300265680040c1c400c0482340c50704095007102d2507940030500b51304907040001e000a68a4a038501c4003140c1100c4030b1343d05170710350060001301c0e824000c8012540c11424a402e06400b4400300b0380100304141c244000a07281700d0380760241085210000c22480354001c0d413900c0204070160a0100180844001400d84401c0011043e40c05a0024000f005c010085034000d243e15035580c0c0e140c010084a4074222134010143c01781000184000b41940c02240c6010742c0206218503007904081003041e5600182521480d5641c0d8906d0103481c1180381c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 123924613 1250 123923363 123923369
    0x91e05100816032009010c200f1206040809010918060f080a030f1206210b0108150c07061118030d020312040f03020307020d0f060b0d120e0f0307 64
    0x500c140c51858001541d440030142d40030302c64209490898086542404601500d11a46040710040d0782c4900c141c004841c83c1d10030074800707028041d028110a403410501206201111410307110184055a0360080050fa04903440c942422604042c00040000d00342000a00107540c0504241c0340090710342489081e10200441c10a400c80d0751070006119842010088000038030132a0005c00c400c01d09550010071401c0c01c160090140a8007182d003c1e0072148640184026150f0104a07101004a0300c0e1000e1241c04084000e0720141075100000c541d0060101c0d002d0390841200302d000850340c481c0c0850100642c4050000d07258a0b0380c600808600319122002800e40c594040844811b61036000c0401d414a0180c2200000b554001c0001c1e103c07084c00205400c2c0d116412103034100c524074880c1402c0c5c0c1036105940c0001d500108002e1000104480340009185843c051030017080580307000740c01d011100440003006042d001c0110324880049100703c1c580088028060011f4140c41c0c41d18000c80d2400b40703950 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 123925863 1250 123924613 123924617
    0xc0c0909030f03070c020a24030522030201050103020915030604080310050405041b060504050a05040209030c0301090b09010606030b0108040206031005030d0302070308100f0308030a11030c0c010b0103050601091e0510 95
    0x7184101b540b0344116902e01501031482c0382004508060340300c68103c40801954810b268944001401c445182c0316000c000035160104402101c1c0140343c001d00916003400101e2103800d0200205031103608601541c500400003800a085688807a2200d0f1416000140f8500300e280002d00045410b8a96008103405548030340d249507a00443c910200c01e4045082d04a07004205003400100481c0d503803050b0768000c942c03003a0341c0143e4410440300800d06100c81da0100640541c00c0484d0141080054440030703200303482480082160070b442d200308034141e400702e0806500140d82c48000c1005460000e00440d00000369022501045903504e01090800d903d102c511000301380d004c1102420b1542003850143c0c4a22175a0940140314144144074001c9201c40c00043d003111f2011000403500703000343c4c4c0028246141e2201d82c1c0c1d100c0c40c0403c18440154404120440f05500b06200c80050354060f01505000c0c0b10141c4810065500700a00060320727403841c001c214200c104282001503161940c0d518001412400e07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 123927113 1250 123925863 123925877
    0x10209090123060d091202060f07050f0c1c110102040303020a200301060602010209010306050f09040308041707050709060503211c020f0301050a060c030c031b021008070e060c0c0909030f0307 84
    0xc6c100796506150012010702903400c44003c001418101c86412540140d032400c00c0c0b1b450360700d018404002801082c2c00d000c900e01c1000d0706410203880e0407101d5621000b080e80c3e01c540d00200c0091880c245e014921005026038861404103002803c120700b07200c0081c0500762144020120840000e0a41e05540c1c007040c0540d50003d103800071944d00d4040d5402611080e079018046c842144003003480c4403c010005420460180c3c0400c0c10000f40110030b00859204681c019141c40d16402c210381c68030524400d80070324070314201000880c1d0401060209545c040300500c0751210103808002246035021401c1002000c82c01302410040c2481c5101400c0710a800c030815649039814841486074820700c0d50441000e024a030719111001a034040000d510f030701d5162800341c00011500803400c0c07541000c4440290b03c40f9620041c0e00c2c0c0d0940c4a945203103d400c042d50380c4041001c20200340b042512540444070f800750802400f03001d0743c2c10b0030411980c000140600300c80c584a2034105850103504103484d618006011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 123928363 1250 123927113 123927131
    0xd0903090807050109120507050907020303190e03030a241404060806250309080409050702070b03060d020418061e051e0a0c0908010e100608010209090123060d 70
    0xc000006005008180c0080c42e0b0b250503c000070b8030800c0300d4402e4102811501601400708041800103600400025101251601342000080d49a80045a107444000005ca40031240a180384c040d1658960313540d4095443c5407a6454580d010305562006200307264590381c1e52120f00c1c50780058010080503504058006840d10030104809d0703a249520007010fa1780144107002840c0345400c09600b05a544e004541c00401403400e0036005007000200c094884800401c00103030861050b0091403044080d0750989400300d4450380c254010340800e5400c00d030000811480d070001030034294005401c0c86c03078810204050f42c00f05c1d42c0c1d5a05450131401c0c00c442b58441e0042602c6543d0710b502446810460300a160707028a1441603c0001c285130080ca04042180c651604c2071609014041c13080c003502440b0002e016182d03c00328901e90301e000042103407065602e07000e80051000b1062003901c0c1a0880248001c245901c0c0c00c07010001402d02c0c04920440040308005440c0b150b880d40e004040700c42c83d640002c9602c1e03076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 123929613 1250 123928363 123928367
    0x1608010b011707091e05060319051e0106180803030901230106050720040903020f1905060406021b03040315050705090f10030b0a08060f010501020d08010b0307140d0903 74
    0x209015006540c410b4070090025890700019150241c800340c4002d580c42c2078111040c241069059800b040d000705000051003140d0100c40542698900344120030300c6240c4940000f00004004a6001d820405107000148903880c4110b610000d2502c0c030500380810300e600e0b401010f00716402540d51a0550b07540700c011100380c201041c80f40c2c07400c0410180804042d0314000d4094414801d1030801030000c8408043d0107402000c1d0a9a0624428060001c01507030700c1a2401a59079006001c013200d01d03210b1113800c9008000380b103d40e41c801681c002c01a0016841e0707507503100e029402c00441c15140401e045000100f071041080a440110700072200c031000e0002040d1800c040300c2000d4400010804100006c0c0000d0705d541c01c00c120070328070558000c0c08031007000d80110b00411711003403190b80c003000c41d06001407069000500140581c030360440300030b41c59a0710001645e86940c8411000040740305074004100d0780e5183e2015540c44022418228050640c07c1081c400f26403050081c0189165201c03291070a141d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 123930863 1250 123929613 123929627
    0x405190e0a0515240d08120f130302030d0c02120f030103060b01110307020906040605060f04030b070c050a14031b0d0e040c05090616021008010312020109231608010b01 74
    0x101c410030128a60b424040304000313469081ca903000c1000090080d040c9034030380760740c84894280d940100c01942c4a160440c1032071031514058a810035038403904070201e5032040c1d42c245035400035903041d0025490031071215a510301800e11035010308107500808544612031034000c0000d042c0c48040040301543d03076043d46440d80c1154401c02038203040100d0200c0864403078000000b21150741d501142c04008690314400042c015045075088241c111101003010000c0d412350f0f50141064a11851003000c0c40d40c0c1d0350700102c52082c3d07202406001c940c400148a03000c11b584458044520540e141607074541030b80215800121889403070300c3c4455922984604280c0743d407007440c0f02c07280d0008a8040c08400c80c1041e0041090080c5401c2030f1051000003400072011000d50412405564040c0003400400351030750001c2d2a02c1003d10003910150084801c40d1070541c0f0620500c030009070f014120608214044500b00f2058210661601d5284901d40d140300c21078688194510091035610000f1400e0442c10000510390 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 123932113 1250 123930863 123930883
    0x905070804050f0a020906060706060b040803091309021f030e010c0f020f06010e07030e01020904060e1906080709020903010902121b010512011707150804031b0b060405190e0a05 78
    0xc4c0d00032240020060743d400b0912a040203044a410341c035035166080040c0148555400003c82c54400240084e0802012028010020b0101c2d50100000d010b0075148080d84c3d10100000e5020b01e110210803d01c181c140358421510304c961900140e600c050102c2d80c0d08680001a26001240d04075140c584181d82c10040402480151805451079514081d00c2d20488140540444180b42e1a1800d0049515095054900001005109201c1c03d0303a06c1c9601e030101d031002c2d104091003600120001000700c440303004010450304110000d00109151100c03140094010b0000c0b43c2d030554a801c07850300580e48080804106841d0381c4003601c48190650001c07207840c65642c5480741448000c0c030004a034405152107a5045500c5102803080d01c802c480c2142c0d0900c01503800c0301c0341100c036450121703102c19130210700240309921a44400c42a14003059400740209074403407001300125800400507031242016040241c03c040001c007903000050803011030101340e0720a00c90501495101052030414410308110700010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 123933363 1250 123932113 123932143
    0x9050a12080f01150c120c02090423071208090a120b060102060a140609071b0c0609090b031c030605060409141006090608060d0b0f07180b22090507080405 68
    0x25144100c00b901c5d95445402c0903100308228011018064014491001d809034000c0c04c03405e0502e0640b03440c001c03410448018a0714400c00c001031a810350800103154050b20403010b000c413000f0341c080c1c0d1250701d1070303200e00455a04900c52800c0040d0b00440c00d1000c0d5441c0b4400c0100786090b20304400024a8000700404202e07090f410703c001184040540096140c02c40820354500380300d6070b54020151800f050b0341a9950565284032078140502c85509010010345400b9030b1403005d0965245c1400056480f180b62407503140c0c003c2e080d0055050b01000c10350304021034074200802c02582e50000503025400690204150302c1e1540400401411220a200e81c020710b074131810440e1a0805000500240242c0180c2040c04040310110307081d80da038008840321701a4085151403251802640c1c002c1e42d00015180800401c1c0da0200820014a0030301c00c48054581d031102d158108007007401008030b11040482c0c0e5a003064110000445c0700d03460390080901c41d402c1c540f40c05460f42414038005240c214904d0003090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 123934613 1250 123933363 123933389
    0x316080a110403140c150408070617010608090c03070602010c020721030507080d0f060602190302031602040b130504020a0e13030806011101060303020609160b0d09050a12080f01 78
    0x503503007540d0702a20192038024800740c00c403a80d5100b82c14900401d85031066800412000b290890f030000c2402002a100b8003820b5641c0183d50310360903035140c240c002e08420104908401071000c1c520403054242c0c091044022a0840c01c8031402281c10f04045420200045c0d44550f220120b80d5010003043c00100905107610f4403e014524a030b041071410840700408100700060710380d0a002d0b4070380544001c0486440d080000180c003031400f00040c00c041c07090304054000c440e40c04800054400381800b80caa0950041c61030072a03894540d5816240750403040340e2081c2e0722320046140d500d440c22a0b21140b0022000020075040600410030001050b5228488504140c001c0200400d00c208680e24078a034941031030001502ca640058804104004d044030140d840c03c803000051550015041d03008440400a8603901d43c00660800102091401a42c440c070404100042210150781d100c41c03240e501880a440c3c1601c0c0c1c541c2c8250748038080c0000000010410414000c01d02c2a10b20003038018a00390803555 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 123935863 1250 123934613 123934631
    0x6030c08060d03052212020103230a051308040e010504110703020705040923100c2d030908040801020310150c0204110f1b0607020a020310200316080a 66
    0x911140ba84070002410440082851400c2c82c0c05403148007081d1a8800c00b0441d015290000b0b002c11140544082e40028108131617890246504984041105030303c81e9100da00385c1c1c9455400d00604000ba01c1d00b41078840010030280420b540501500180c8001c803800104c65140c482001700740c40c200d042003c00744208010980002e0b0b00025407071708881e019900402d000c0c07080d040c4800c4104801200558540c19075207102211030020490b0f19440011540801c2031f4440710f001158404444004800c44a5250724061501c10801c40d07440e500300740b20300d0042a6204155640c207540e0700310758040c000c26074000c0180007207180b014105102070b00f1500c101700d030140c000d0390008040071000400a401580e4803030103203200780c0c214400c4030003d48180d104151348140401103101103810700b0459050700d00038400443d4460303101044c210100c1350010020000c000c1c0c0c0550200040c844900042c0c24040b0748521031075604004002703944111141c1606000742e1711120000340c81c0a500900207490790785801c0a070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 123937113 1250 123935863 123935869
    0x10b0303130905190c020a0606060302041802030408071e03080f04150b0415060203090f03190201050f120c03040b15030d050903030c120306150703140c1e0102030106030c0806 77
    0x40003190b000c1c0401054a4941343c10310103c9039503200b80800c03e90f00b001c0710f6648083d00002c424140601c00c001c1000074681d83d110071001c038000e50003403101d4120782c110101e041c020740b90041d42e04039010381c00e02450008603a46840c44a03041c88a060b124251202090083c10f4101247c154800e07850000c0e20581e10305552881c2c0300044104550803441c0c0e442020004a440700c0c1d102d840300c030f0f01980da601c01c1c2e00e4440c24003030354076000400f6951081500e045580510308001c0781900481c24080c28507025094250300542c2d8a8016200000c00c0b101e0500c0462642c10754004101d0140e01d02849071a40c1e800d00e81002c110440c2c00400304548e580e01000114280e032000600015291458130701151559210380000e41544100c01d0f11000e1841034240000c508581440103501441c012036513501c485819001c160340a01602401801051441e40003410405540e0010300c80300c1c88920660f04100c1c2c1c40d81e08107100507030303110110406039030100040c07169135014455140b80340700c14107080d13030300d46440400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 123938363 1250 123937113 123937147
    0x70f030309050307050d0206010f050a0b0a05091f05070b06090f1f030c08100b150708090f0303161203060302060906070302030c07061d180412140f070203010b0303 72
    0x402010103684003040710902030203000f551031550707205040e140d0b41d0080140013035880000b8060803000c440400c1e00042c0a03e00068004212a01da000f80c40c00c04e900c0c1e240954903030300900c88054100c54000071105807030041d001904201c0c159901c90356240e0106041c6100c03019001440c4a0003290b00e203060000c06407042c42015404414043c10101a4004910281241c1130302c0e800205400071550010803150f401040d00c10703140d295520100101441c1000b00040c1a45800300030040312400c1000d400800c040074000e11510303001400d82404180504007091440c1d002100d03100881c600260494204102c00141000465041c64184445421034001910f6071082204e014428280000c9400c201070080c41540c12484610701034805c002d45c0d800000e03003d04080d4008032000841d180c92101d42c5c1c6081d201c0204012072080c0840c0716517a072540e4120104c2c50800032802072041d9420804813248500e0300400d16442100b014076200d00f050700c149030079201280d80d003034400c3c1c105115000090040d809 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 123939613 1250 123938363 123938393
    0x9050a1112090c1206010510020d090b0a030b09071d030304141306030f0309060207090c0e1306050901060504140d050312040f02090a0617070b0405102105010303021207 74
    0xc0da1050354444401e090301c0e04030f40082c0c07660065001c0c140d40e94a0000420000d04890b4203603001e00c0301825405003241c070b40044115120204086140074440c1d2190600600002ca171241070010711084a04002500d84c6000c9600200150303a10301c52459003443e901218111000a400a41c209800d1070460f440c241d00b80000300d400758541d183c445480c1512034200d54011908161141410300d483d04008048040750302070240540b045850020f00d021682c450881200d0f1190744a441c0803003e442009281000d41c403000407260b85856001c40c9950381d85250750300030710482d141d00d941d032450540c00000703600b001d071005445030300343d0070540c1c0220344080112507213004002407100035561180344c0764080100ea0500607401448410801400300d810358000e000f42da8805444420744d1607011344c000d40e6140b05000b0300b84030200900c004c200e1800d150310000b050ba02c0905200c2c803c1c80c90410301240344c180140001c110360b41c54100410600d034050061140840000c1c000740d1070305140340c0324801606a450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 123940863 1250 123939613 123939637
    0x308011503090609050f0f03030f16051c020903120c0703060b030f010606030209010e090403020709020c07090e1501050303040324240806150102120d090203030d02030109050a11 78
    0xc00e4140554800d500410358141d005508000072415401d0096032407184516915684c42030041038103c224002050324812680c00c8000401540d51861a00700c42140541020500c2014400c29400718100360400901c81e038800030050b21040440105803078000c625a0312040329070b0410501c06403000204000094942080c400b154540000000c00d03e0410b18440c0c0b03480303552070200c0214030654540c00911041209a071441860a418020080c3c030140a50b0020301680c040f2800b0400c86045070080c000074801c543c15902120750f500070050503100e141c00c400c3c0a1350400ca240750a104c11071449207024003403d8001310f0605003541d0341c0c600700c40f000b000041d132880d1040b14070700d401e81581e4000c10588508603150141c1000124644a13100c511400b8285031400742e140000d500380032103e181020000168000e060015416900c50310950117900004807154481b91004c016840400c01410100c008100c01666036152a5001c01114405400a840141409080f52003810060f041d680449100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 123942113 1250 123940863 123940889
    0x20f04090302100c300f020f09130b030109050303010801050a0e1e01060f03140607030b0102120c150103050d02070e100504050603070f09020711031c0f020c0904080d0b0a03030801 79
    0x209001d80e00c0341d840a0031760a60304558590f8196404981d08404030051450000307004500c0341c007142c04143c0c0502020b8042031101480300303050a00c2c040410321860788144c40c0026410031510082400e444041070305441540c00000100305802c0c00340700c0c3c140c1c45401c4600400c9110395000d421502c80780c00c80d28410b10000001104100c0358030a52000000f0207250341c07038881c030340e07603921308500d0074141ca95100a680c0144000660518001d00070000d91200c1603016010380340220f0220090303070700400040e032224420700006203040001c8030b550305e01030740c058402408076841032140203245c4070103500301c01c40c0f0701050700500c0b0041d0301c001003c0054500032a0085200e640d44800b1034905859548403040c94403074010000b42c42c10035a401020003600800282c010144e110700ad2682d40c1480c2403030303101e4980d9003654102ca0188075050b22186d80f00306206580d06e50754090f00081042500b9507090b00ca840d400600b0030750302582031003070010341e440036030b800c518840c91078801504050051040d80c04032280 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 123943363 1250 123942113 123942131
    0x907050f0c0615040f050403050d09060609050c13060e150c1f0f0b030604021e1c060501050a0e040201080115020307050708060403090e150f0f040513020f0409030210 73
    0x140801e070340d00300c8101c000301c402c18078010b070320752001c10f800c0e60115010342d1405450600e01900ea0103858801ca1309030300d03054a460b409100c0312008000101080d11590355035440400e846607180201e500950011004a445180682800805614036840b000038020600c4400352951540c106a00c0e46c00340310000c036501d40d407084503100d080444040c50915020943c552440b14429143e001d2409000410f074108030701d4462106041d5201425940070b98414800e01500c01000d54091407412942c8000c0c0a00d4180040103418452510351803004607016034480c8010b000a04000030120001c02c2e13504202400e5080c0b43c3c0003e030020206001c1d003a47c5000100310100c10500030012280e8695008048a18969482942540320102510300f1800120510800241e5804101029005400540c2e103140d81c00c92032003c000354032005e1032059811480c0d109106280c0d9540c0d206061040688090242c040c43c514810482d054811400c800d205034905105400420f6001030340c03121000c9591000120020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 123944613 1250 123943363 123943387
    0x19050405040c27060f0f050d02040e03030403030911090106050703080403140d020c06010503010504080412150501080c090601020d0e0904151d06010603021602090a090501020f040e090c090705 84
    0xd8140c000d1080c00180f000802c940207003203403141480036180c500070000c07262507100f010320862151050a40030343e800c403020301203844c01c1d000c400708640c4010030008001e0308500041d030464000320b900742c02007039030742e0311241c00d201042500c004040f4080f18054065810000c014080380541d0b10042e0421111900240405004c2c4c1e0390703142007034028502162100154441300d8041c0d03204400903c52400340200001b49030405008950240d5440800c0da804c00381040c040022403040800186ca0080c029040801940c0381031040c3d502030084140941681032070306042c007200355005005941151b00200e401d1200c25070240041d1a041c0b801c541484954407a4200002c072200d203110070300300307803441c000c0380ba2032031141c10762010400b01106043d51581d0303984120950407401071a59000d8000700000071100140b50040213590700560301e50700040c80701510b807030380d5007241c004126070320b440e440c00901070100d5101000d0840e8820103210080c14826090380210315000405402501804030210724541150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 123945863 1250 123944613 123944633
    0xb040308060a0b161e050c12070513060303030506090105010504050f0607050105090102041707050a06081f0801020c100203010f030605070c0b04050d080609040309060e010203040b190e1905040504 86
    0x802101d0300f5100d0f00c44c1310301003441428004c000c403504070300304070140021034801c41042d82840e08407020f030440d2808501071110307102056000000501400c01c020585075284025003000403903662002a0060071460040c04403600904124810060381c80100001d80c0d00004032000d481c41a6140e840107241d801c08244a0300400c80c008225509240800650400542c003520840b10110101c00001c1c2e00841c3e11901c1f4640b034081c423074000400401c1406041d002d1040b09810044104140102c48880a45400e080a1a4001405c1c60350006045100030300b04102c9050752000607030007186994541141108180580d100c020109501c6200046c2d00c0341c081c0c07200d281102e0b0410001801c0d880d0501e4030a031a0341c1509100b03000300e403080021130894100a030056100b1176058950709600d90414100750f030396a851401250440c4000c01c00402c06100e05400b43c513901c8070007420340324003c00700a00030b811342c80c040c03a24030b000c0d20354420b41c1c62015200340800300460b402641c0c0010103032228103205800f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 123947113 1250 123945863 123945869
    0x6050910050c10020720090c09041a0d0c030b06010e1305040615180606030b01020d11070f140a09140103060f0204030206040b09101d011b0605070504030c05030a0b040308060a 77
    0x1540c40480e03820140154491b06044141040000fa44400030900400010b00c2c0b041d101c80100d51014071044a4608090b888202405603034414109034410402c0000c00c1e48581100459907a07112000801c10045c0c80103400350022000d00b0700d8a018402071010450010380042915030b940c0d11140842c3c113000c500d038403554a03000d584412011030341d19561008422401140308001c43c528200c1e0000b41d05119110303080803e441640a0885401c18080032981403840b00c01841c014000c00f88005240100c0350740360001072818070010600c182c5180c0401228800c1c60303200d0450281410b04580c203030481c0c880c10300d0540e6031044000582d2081104503034028040c903040290046c10001d0041191040013000d171081c034000321002d548d1550f6010701160034001c1200560181e0303011900d43e103a203600034510f16810096a848a111000040c0c603164182c40b02601d90f9408660002418030600c0540808440681004e0f4000c0c400c2980e95507441a100c10000c0010b41040b2501022500741e98a0b81058001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 123948363 1250 123947113 123947143
    0x3201308030a170a020301180203070e1314090607080c0c0c030304090509190209070c060f06030b040203060a0606050a030504080d0906061404090b220606150906050910050c 76
    0x940ba1078500c05000d808100503055031158282c400594581c4d0a802120305035001954070000c181544c0c40d45401940000d0110014040d0904842c8503e8841210310b0304154a40c2001107420143c0c040f0520000d00c0240180c5c840350010020032501070f07000a941c903003016155444a60f20702460162604200804504a074540070001d00011144a01c3d00098050900131041da508016200481141d00c00c552a000350058604400559070302d01503001e011481d40180004148a0b04010707500085560310b8004948603d0790109200550030200081c640c07112407400200b2200e4103048001e0213901414900074101a190070002d410880c07050300362034040f0301445091040b1100c0c0c0c07030070074007a0426018100160542800c114a645000d0044147d903d4212519004c039484850103031207103000046c5a041003480d1151807030002044d074400c041c0101500c010104650140c07013030003801c42404e03521400400c4001c1c0044001d0317a48801e40442c0a50b05814040e40e6200c0543d070a5040244081680c54 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 123949613 1250 123948363 123948367
    0x7080a0b071101021e030c12040c03030f0f02060103060c090905190c0203090f041d0303040b0403080f01140f0a170703050106060908031b030405120d0806010320130803 74
    0x8000210900350301404041c2c4a071010389100ca58458202c2c00307121408081004401008401015014000c42e042144120081d00d00340801d100c1c3e981054051b0f84c00c030b4007a10203450030010b040d4008511205e200562420300415108514025a924018040034000d259540c2d0550207180c040d0958000a00360600248500c0c0b0307102d040404a411b101451000050600304021149807000c0101c2c2d00030800140110000310002007800700a00300b400f888907641c1c0501000391018441000514400c4d84078a100441c2d5207045d14000700b241d94040c002d10808228240180810198212821040a410780d04030744195075001c0018180052136000815101155001540b00344010400b8015a805400240030302c598030a030844150031a4072600c1740c1900144a240424449521450720601014084038102900c031000265030704c1075281400d8642e4031080054854a4100d401039a01c0701013400c00700160601031500352504040b90100d9000b07150300040750104a5100300081002d0483c0e08100d035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 123950863 1250 123949613 123949633
    0x50d0b0a171501051215090f0f1f050c0a030c0e12010e12030c030c030c0409060b040612060b0a050c0106030b0705070203060a0c090510030b030a030509040e0a0203030a08090708 78
    0x70b41c41e54200701c1c440d410491078400104250034502c1800801d629290002c000a030f03018112079458060160040707400d8040c034000041a480d081001110000600d07003e8801040035000c06030f000030b210303a8840403503070404082004550700c40c001c0d03403d440018240440c074038583d114101c0b207122080355059400b10540c10120000340341540185408940d0b08221030030240c1d403440000b040c0c0005c6810802004082000424804011000e90f81111170302c051942040c5d10f914880d000e42e00560404400460045001c1209690003003d041c0400d01108003004614101502c040c11441020140d0061180001d0641071010303095001100440d0003001c0190f441c10941e00c01041580100f005170710030310411000c1240e41c4003d00c601500c86c0792603181c481c4e005181c03c0c24403840c454040101c000781603907204149010f032414000d44070b03d14402d0ba98699902041410007046030086069100ca5074000705a0500503180001101c80200580c1441c170155038508420070714280040c0c00c40009030099202c12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 123952113 1250 123950863 123950909
    0x130b0411090108010f0e0f061602030d050a050604180f03030c090f090b01021c08131a09070512030405090604110c0a06092105030708151e03060f0403050d0b0a 70
    0x950f01403c190030611110a03203001d0147c2c2c3c2d45080c4188071303041d00810b02207400c50030483c2c1e032000d18403d0741c0142d90920703040801c2030044030000c5412240c00358482080102901d05441003074203480902030b50b007400795403c3d100d006444000c48070041c1403550b903c81c1600c280340520350040040060b0100c90442d541c0711070700130001d454010060740c094403981183c0c1c0700708e9090200b2001c03500f03c2903071000d1595070394040d041d0b91403441100503942109012029100d0142e80c1c11514814101c81d4001d00d400d0740b518041c82080101c8500580303007500180030074405581c03020903068000c01c088401181120801050001d94807500d0b0b140c8070f141c412650807104000345a00030581d0782e805807070000010100064440c844c040820b402c0d000050b002c00c001012140907496541c2c100400ca010f5540101079030010810f007070081109460326407070540003641c2c145410001d944e401424001d00d0308440c2441da6000c0e025000d00425015040e03100c810312502510781000304d030020204900d8441c040c420310044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 123953363 1250 123952113 123952121
    0x110a0507330204031109010317070618030206041703160c020f19180b0a0605070501240315060b030105120c030d0e100201060810020702010201060506042c130b041109010801 76
    0x880b00c0c1214220210304031b2a1018045040340e1700821801c805030f0505110b01d07129840702c00200c4003d540c455100b80d840d2000c9e0701001e1910310031b40041c02d090519061504028143d002d4401064804000700b0030390f06044e01005640b0002030070900d0079841c0910010b140091060354043d04182644040c1d44400604070901301140d241540d14041e1405076030068040d51840496240c0010020004015641c4214010002c07075004200004802c046021013800e20700d88081d2520440e01c261a050060100451103640610082030040040a11707000c103100442c0014410140700b075407151040124000c05010058403818002e060343d600f400c0191000c2c15600032003411034010b040003002c501c3d05500510404041c0d8030060000c100050007800500040c1d8010201241155250080010075469010150010f0501d0715400400c8011101c2900003d4150340014104213640760144400380a014090003052900405d25060307580d681e040c00040c81d000c00d4000c0f50805c0d1040c0001803280c0e0306600c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 123954613 1250 123953363 123953369
    0x3160803060909120403080f1902011d03120601080705041e1502010c020a061104030f1415040b0c0f0c031315090317090d050a030c0303110a0507330204 67
    0x140682c680d01c40351a4199114075400b2a140d014000300001d00115510501500d201248061094a400e82c400c8010742c2070040c81501c580581e440d040d000b40c440c0c006c0000403151160800046003080342003244030f685603002401d04c034103005100b03003c01c003500e110b00201c1e4060300e110111a1844200c50302c001d04001441d1041c006d0007040e800010500c1031040c000e455514000c0e0f4003c1c02d00e6002610350b00300408030b101703121b000b07004204000400140e42840060b5400e01030210030851000007004141802814810802000001010400020304801c0107680003002e40e07948540382c055000f180d00d810b1185503505ca10510012844400c050801e405520540701c03c00d0000c04031045410003501c049505000041c903089806031021081004500a0001041c00424200781d0701c1d465107800342400850303003041d030024281c00ea0301780034103416010b4040341c100c034404064507010803810010310a0003103801c024803100d4002c1a000d01882104640d00a9807203001d40d0890410b08004604000d60141c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 123955863 1250 123954613 123954619
    0xc0c031207051917030103050d0e04111206120706031e0b15070201090905042a06090b0903160e040b01140904030318020a06030e0c090408160f0c090c0e0405090d030e0316080306 78
    0x30302c00c00c2a41802d01031a188cc1c05101001d0f803c0041c5041c055107030102c0140113542220030340d41015100d03182005803000030a01c0b910300003107100308040c2c20038015038010f00c50090b0900304900c0b060342c0d450340128030540e02c01601d441c64a92085100403034001845520800c0d480e82050248000d101d1909403601c1c0701c0f0380d003001c0f4181100304103c482c0c082800354800c400120b041010200014444000140f164050090644081446803061040e400d0b0068001c503004c0c21403134040104001400b15490b015100303185030598004024400128103d0004000400705900ca080d240c886810019060405550080c225404244c5aa00003030090a5001d00d81d1300f51b00c5034500c00300040c00c0c2550b440703001d0b0350020000c5180a01da101c0590405604450859143c1c200c0c040040209aa1412040182076240000314091b078203540c008010380b4052116510031850306060118490000030080500e09031814040381d80e8880101207400c1d401a030341103078040c011132000482005103c00007035104d06411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 123957113 1250 123955863 123955877
    0x1a04061b06050703020c0c09060a1203140d0204050307090218011b0b0c0a03140c09040207080c0109050c1002030909011e05090c030147040302060c0c031207051917030103050d 77
    0x100d040259044089d03504581007280f0680500011a6801c0650000c500038203000e51528441480c188559204422170019680c0c08101400300d441e0034825000240f405410660410201781e5004c00b4544d004107815050004504501d0821041c8403160340103e50840b0040c940c03890908a04400380d40031000700380000e407809044107980358142c035050b4040d541002409003011b05003000e1000a43c0605010f4808a82c1804142c4102900b40030300a4424850030107002d482041400380035014070300e200c1100640d0801c2c0301850301c945445482504441881c0000241000918819a41c0540399080346030012405003c00600d02c1018005604031150212641c00100071203a4211403800c2c0030884114480514101da8240900080300c1500030104020461525550b580040d20540c810f00742e0f591725030412611002a89818007a02d680150b0b0b490710b540c6400d5a40d42c925484110943c4608810041c40e001203060000c140d8080d03540342c00e8540b00c00d035256140d0a141c0c2da143c2030005294001084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 123958363 1250 123957113 123957133
    0x8070e0607050721080301031101020a02090108071508070210090c0b04030609140a05060711120a08040507091b080a0f0213030b06010c0b060904020d0510151a04061b06050703020c 79
    0x50301c91020701c04da402c040d01604590841e1f65502441c00f1488016045125405500300560340310501d0318024440300d4000e0000501d40302128241071000c82411050050440c1003004254001c5660190120601c4000a92107190700c0e000c41d9032010b0f900200311000c004a00803040040ba40c1c030449100d03024070480710210311700e011100e50b07444158400a05d00d400050120300c140d80a12401c00c00f00c40c051013922031840001560748030640201d034000c40003c4600b0144428087c041c403420014085180302446100c00181e0f03ea449c10340d540368542d0410100a0000322a080281d000440c0b030350400b441551380b0211080e003405015901d020030f6070300024200c00f051103503016078121329801e64030107004c81450341d5410030001c40742c070000c02c01c1e80c0007070515240c580000c0080c0049155441203540005030544003040f254200d8281e600400b0105c42da080302c01e003002c071412090358102c40c6145414070f0200e2035100d05072440c074000708004015a041c038007404515034064000c0d12507408010203d510b1148 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 123959613 1250 123958363 123958409
    0x19090b18070b0403021008090a2009060109080d050c0309030703030309031101231306090308010f0503190b0603070812270d030305060f09090d14031608070e06070507 73
    0x802d92000075440409a43c010034a24060007e1350340c8031a03c0c4082c0c441840940d141c4d4041c224500c80340d03082400102440a01d01e1070031550403034000c0c00030b18000007034606000656546940d03401c0b552050010100361161114005c1003204e01c02d01001d001d40b842c80e6500d1030094090100c001017240420300c410030890003a4814031a0030900c0e00c0e13140000010400759850003a441c2c0d800303401c83e84420f4498803080701041103070250340b2000c0e1280d503d2403001d40c07501900058461140e008140702c1d03001800007000340503000f90760031304c0c1e036800102c00c8003181c8403040040c0c68450329030700c2800c0d14024142c5404c0710012040282084105860426420f00c0c01d41080c1440880740c1c02400754040081c00007400424425440750390310903409440354640001c2c40000500b008422110016613a11400c000b50049a010408094030b081a9419600b9410920010744041801c2e076036840c10482c1c0d8100207030f0400c0c81152200f01c9210b024108590314401420001c0d180c06a40c042da403042c99614002c0b9582036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 123960863 1250 123959613 123959617
    0x2030f06061f09060f03111809160507062a0201020d0c080601020d0c030203210103060e060c1602010509040614040b0a05011b020604150c03030c0e0919090b18070b 72
    0x410301c1c0c0d44031940681090015117800244203903c0301007640e540384e45e8440b404c0f0341e00108100e4040b8090345104264a20800402c03541c0200030683e03400090018100310f42d0400140c41c0c1e080e60200000c281c0900d401462502c400001500201003865450740244080e010f40c001d0080d0134a2ba081030040507010142030b2880c110659565006a200032400c0310161301c14070705180014030910641c1c1c913140c000380613420028442201d248500045a004104000161140760003a41c101d8028040a240550300003000d40a0418480510f0791482c011800716840b0f1412180d500038010801c010880e152000c045c10051103100d6203000e107240c003000b40b0440c030740792110b0011207105075100c0da000589800c60100c20070a84100700c0c2c00000501010070b15004c0f031281d00b800d601c41030f074803460088032070308005040c1d80d03094104c01d007801411006240c640d02c41c1d503c50341d40a916103640e450b552010800d00c000a2080c3e81018014000345030510502080041ca200514000e080459055030303100c2c0da91081034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 123962113 1250 123960863 123960919
    0x80105060105030619150f0909090305070f080c0a03120507020703150b06040302040906090302190209010b09030f0d032c33010b03062809021602030f0606 68
    0x480c82c14070010301d8038541441d844031021351814100c100f2940e03810991100c81005280507000c550b11400086d01e8039800b01461004203802401031001e9000c0340c8000d88107104e0101d0280c80e0503c6c3d00003010502401a04540000740c07040211000200302d410014007002100c81c10881050510700840d0259200061a8064a412118820310b040c00e510360320340103003684001d00d034100b18240000409643d66120b00385842e0b00504001c0f502d08114540203080c0041d004203440c4421102d018040580c54070f000080c1907070001c507000ba80c4c0f0049040000d00d05204040124118413a95003c60000f5174035811070200c0d07a080b800d95901a80001c3d401c0d41191030310303003d1000e003640000c50940216062884404003e00d0003468525240d280c000c4010b0105003d030040ca6030391000105029690030f101740181e0b0003126031030740004149074070607030503041c0740d980c0c86690103640e008149001940000c150a52019600038120360380f4411451030180c5404080f00c00714480d00c40445d0802c1c140740ea1a4800481d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 123963363 1250 123962113 123962117
    0x7122010080a0b0d050a0303180f170f2b0b1c0206070f0309050109050105070201020a0213020904090b0a0f05100b030403031d0f010e030405030c090c090303041e0801050601 76
    0x31210300e188121040c82004064902c600d4892a8040c9141c94900d800d030030450141000c0c5c04031545a080150544464030a03802000440c00414404a400c60a4402c40b003640961044048c40e0b1f0b5010118481c05021100300f02c0c40c400141d00a03e861081070b20910b01d40c0c4000c1d00302c0c1c1114089102c40215045180000c1c5c00841144a960403003545d261503035280c0d03100502c4079081040c1607c43c003034800303107418080f0080740c09850140065078021f80440001c01091034990305d810550740c0000c2d1a00d50f44203000780181c50800515818402c40d406035803146070b014004002403041400c00c49495a420b44400c40c0491400c001d001c12410300b400303064800c50007030004003400c902d008040d00442d03100420a41c20140c0d1200f0100380c880c5860340410001403440000e01c1002a034002f05800c40c3d80c0c1d041310800942c800c02041201c1d03100464644802c0a080303600c20244c2d983e2039185020b81c4100500344e0707418000081e01098243d021a00c8038603010556454078000da032600d143d1130882c1d400307842c4140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 123964613 1250 123963363 123963379
    0x50a050a0509180a050f07080a020a06050c0c10180b0408060c1e030a061805040312021305030102031e0a0e1203040609050109150e210705030c071220 66
    0x100d04290002075000404000d8550310f101d9401c04031410b142140e081182c603a00b10315140503200d1810000800544070400140111901950004809002c00e210b10b800740000400c2c0e8807806139003488042691a0050066030140e02d900400400d0001d880810702104000c0450100780981d0702000e4805680c0d03d01c00038062030f11090150440e0390011202c1c800700c0000c8428602250040d0000340d4050301d003c4e0707404a8040d0522180e20251076036143c0c0e082d1402d01e000108000309901c000140203000c0340b1100180d442d050b461440e030384141550072468142d03000000380710165901e08102d0b080140b602d44802904d0b294070b09110241d80118910340e082c0e602c14513000c2c204610f48001140c0144c803070b2100040c3c45100360381c3c00d8259081004190360701d11400f07080b0610607649005100c8040d414201409000003440c0c0d81c46070180503000704040c0448041102c0742005801c02c1100c003000301c02002c070740b4141d03070f9002d0040340c0c2e509400c0100c1c0c03c0d0055060145040580d02202c618942c0028048a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 123965863 1250 123964613 123964619
    0xe0108120309030f07060f0b0603100519081506010813110f0f030616021c170a060b03090604111005030a0b220e06150d031404090c05090307050a050a 66
    0x1004a400140001c0300c82e00013001400301030000c010003412454890305c000b080c2c2c403641c80040c000701d42035042e041d4003440b41001045500740c6080701c40000e541d4100e428113924100426201400c0e50076420505191040c400c0d403404003a09907170b80d188110401d0341c59000d079a40703100840303540c0031481400400e80c1e04459294103031850021031000e8001805020007501c03028900000b842c0020a50b421140340c40c005074000103036075050041c1146c180302c01c10107200c200c08034400207099400c4c060035900c4100003040480c0d00107105800010007410a132002644a09050601075240c0b201035404072015206114680c43d03d040202c1c5032440d90541344c42d038905594a85c9645005418451701055000c0c800c90206000b405d82139006021501039001c0020302e1000101c1e10515000015182d10320300450b40c50b0000395641c07405082d01c41503074103160080107140104ca0340c100d10300541d04480d10b082c1c24020070064450b4864060081d1000403411241202d80d01d800348501c2203028001c1c0740c1c0202c2c10310b40034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 123967113 1250 123965863 123965893
    0xc02070f03030e0d061407080f010f0501030b04090f35090913051212010b0306060f160506040f02030d03050f070e030708010501061701080c01020c010e012f070e0108 73
    0x841e0b03d020007921005102e0001d40d0351104036001c0416190140020405012042c1e41c0f005c002e980c0b0a01c0320030074900c55414450107a080d03417450f1060a0415440f80700d15001ca86881d00710641c003a900046404030b8503150f2400ca090340010344100100070001140303210303d808031050b07003200346102200c0711880c2000c0703882071040010000780408404802e84c0855400900d00300a1941ca58039031340e2a5036241c3c0c020605035240c2101c1039001c1c030a610410300c1445500d60b91102141c000c4407001e40180d03600d5464511286186a04120240c598002ea40810082c044801440b5801c0ca1007181982d0300002d00c000b0a5003240d1301641c1e40700e034044000000840460007888281000c02006088449482d91140c0050035540241c01c14000103412801009890056111003400f41480001a012011103100000c5d41d60860f0f8801e80e0400400d1080a9480d034025a02002c0081080c11190903800c10102d035000f144c40c0e6140d40b41d41130b21401900046012041d03048034166031007500605207002c016240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 123968363 1250 123967113 123967127
    0x102092b0b0405030c0610150c120827060f0c0c060103030509030708030315040b01050304050307020402130503011a01090f050108060d030203040e0114090a06050906040c210f0c02070f0303 83
    0x2c11a8603100c200501000000c0c1044454400c0c2c030400c810020290500000741229906080c0c0e641c141305441d13811400003030043c070880c0c040030b4051800c2c108a6540c4410310741d001e400c0f20500d803800031f4003c04d1800000c202180c1181f080310200034075000ca44600381c002416118100328050603030880401400002d11400081c804840000c04580d04503449002060a43e40180e070b45025908840001c080d0b43e003820f02881182038800d082c03031170842c0307800d0310744688a2042c1e15009200e503500150071403100340700c18141c2d0064032002e80200a011450307524401c0450b080064140444c0c0c5071003000858040c000b0440302070300c2c07042c0e4800705207840c0d1009009080c6032282e412015400700744400310b69102c04060b030038002c0041c5c246507143d000f824014803c9101c0094203204115042c25403c0c4080c1d2240c07030559130070000c1035030001003d600c0c09100b1944002c00610100e12101c01c1011520038802941105000300d40400301008802840310080e0794880c2da070f201c2e100c01010300d54000c00109006081e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 123969613 1250 123968363 123968371
    0x20a0506040320060d321b0304060906020c06070306050306011203080a0209030a030801060f0201060f12020d06050c04051905090f090a0b010e0a0f0902150d060f080102092b0b 77
    0x4c04241004c030008401002e90311448003034441c618901c0c10407540009000d0f40451280b0449454442604180d45048000850590002c0d800400003001c641040320985c840a03109403c03000840d1140c03941e41080d81c031043c00784c904100003400c28102143c0e515010070b42c01c0c12904003d5101c001ca07050f503036003031f41c1c841801400d00b01e01c10703030038004810241c60074018542c401d44250f548091540c1040400307071440602d5034040045a14103103090210102440380c11041d103403442100700003840300788009001e00d150a03500402ca58144414080e20010140181040c3d40d421528402240d40c01000500110810310489500c8942000861113030700c4003034417283c0c00020000650321560100c2e00c034224520303000e900c0b02c05c0c0d60003040200a0402120703c1182c464a0400b1024070410708640c0020701d0740c1901014140d400d510000e00041e0500c4503a00920044c02a140c40301811a40c030030606000790802421913010701000d07148511218205030500d222806801e1048a540003030303403984079034028020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 123970863 1250 123969613 123969619
    0x1109040902060c1b090c040e1305010e121804110301030204051b0307020c180603070b1332090106080a02030c07021f090501140711040b0604060c020a0506040320 71
    0x800f00d6010b08092203000324030303901c030708190700d548800c013040c41840c080c001c00401150f031040c8018008001d00ca103440d60000d206840c0b660810032141865401441014900d0405104180035040304050034400b41250501c601c6400440c2c40d0603405000039588405108801d200c41000184010714040d8403c0c0e4000050080782c8448a03118400303117442b0b0340140c1e150000341c6c1c05468519414503005040c95911002c1c52225580d508002c00801c1c3d55540501031803103150b8001c104040c42044d501240301c0144100c42d0004480289017a21000c40c6084020060840902101d00321140c1410703141c42e03048074203661b100d0256640300b041801c000e41001d0b0007007500603420060031002da9036040b0f80c4402941c0078410364514810886000e030810f07865a220b1410700c10b0410941c0c201210740d4099414454000c100a0a22410f0b0fa00040042c661090883d503c804003107000b003000da500c40782002e016482a607003251401e4941c070810080e130195202c01400e01254030110369454090b00001140c000000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 123972113 1250 123970863 123970867
    0x3040620070308030405060613110304060e0c0406030b011503050c1e0405040504030e0415120f050a051c03050a0605061903090204050903130909230c0402040b030603060901110904090206 82
    0x41d03903810f60160b1050f00e007510140e2004080c410285407541c00300700c0240c4142c10421a0000c01d000c21070700c034080244041c11181d40e621020071301c00b03001c0c020603041c21401001000040e0f00c0303103005144004203008480b0001200c01222003030501078400c4900610380a40100e08181d0b40d10b544043d000b05218074201d440070b040c4000201c0351198050140100c0c0300c0d8581c80a07403e0084240303c2141d200d900d00d40e8107202d07403902c1041054684440301a2132508458850040001420704900d0030408410007070071781c0700d2410840628482003401611000943da07044c441c0d030f151340c003908054400500030360b6803002c410803003401d20384001458043e844003c0e05010481202c242c00040454604030741c201e03103075040021500040001201c8040250001c80010003000c20306445102019050700f43c54000d810174a01402c031207080c10400c004422600030402d41d5559140d1941d824142c10a4600c01e000341700321004100280018014030300180030905405040209070301c108006010004c8041c0d03005001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 123973363 1250 123972113 123972119
    0x7030203070c0b0301140109030c0902090f030303010b07030908070509010e090c092805040b0604020304020a08010c0c0c0605070b0c0f09040608010507080618010306020d110a03050f090304062007 86
    0x10701410b01c000c0041d00c242c95125890308013941501003038068024104002d503141030000071030260500b825511060390041e06d41641c000403454803102019840d0385480302000005481d0070000041507070f01c2c0700f552016112942d0320040d03a40c44106005040d400aa0b180050041081a6401940c060300d22411140c001d201d640128a00e0441520200c95400281500302012a41940490400624010100b0242c50030303444600a1042c041d2541c2e108980001c0800c007995201c00b541d001400000f0020804414503641c05042e8006018040344d401c00d5010000441c0b40c01202600c1d00a174204c00c4000140c1d95901c50118268483c402148414105006510782c50b01d03148034240190032100000181400c18110141000380c009180b10700c2aa0031901c0403140e1416006000c0c1180d50103100940c4811881180390083c0801200070100703110301080001495516410243c0901c1018507042e010b501c0d119149900c9105501600c4d001c1030302c100e01521203454401c4007040d45d044103020f0350741d100e031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 123974613 1250 123973363 123973373
    0x4060c060b0d0506070305070219140109150527190501060b04081e011b080417030c0d0b1e010c1a0c1206030d09090c0c0c12140102030f0c0703020307 66
    0xc41010a43c0e060b44803004005030250984112900040e445c00288118501e49000c8005041d03841c03c02030000c00c107199503c0c800e240942081030b403160f010411541c031910302070381040107103030441d01d500014032444003440d161082189940b007614024405803040c00d22260300720301c04050901c000c641c191360340d080002c0c25030700030340240003d00a07860150a080d10512503c03420f11541708091601a490700b280542c40b940b0b007081e900c10064190800004907915414030510a19440c208104010000030401c03070640e20b150010494014241010441320030b000040c0302042c010850701d04020000c000204280b58020030142c2e800d01c0c8500380b010020702c0000c001f07680801054444040d83c50f07010800340640d1080417241603121500f074000f001450b00080c0001c24042e514403480042541c3c074415061100d22908d0202c2d1880d810000488203103039500c2408840180c05001501d140e5980c501e83c0742050f6042c021031740a0075165a501483c0d80354000482d50360f81c068907085095110422008000030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 123975863 1250 123974613 123974629
    0x10023604020c0c1f020c0922030512070804020a0b0904090203032113080406120f06060e030d030203060603041112010f090c0b0a141305030109050a030306150504060c060b 75
    0x5060800303018100541014040c95000c1c0960b050748490003181195213443c1d0010701d406100804840d0074030740b500e600c0304103201c1503d0307110030b125610140e440340f001b81500311008200d0b151362000700702c0286e43e40c03003c01c440c9500301751030096003c41c03105010020084014080c046c0c052004200154043c01a070000b031035680012070050a5910001943c01d00c02c04003034406a000c80c9001c1701c0d08107240c0b9076941e89c1c0c079407003180220400e20042d88090540b664035540551045072428404108903611504042e04100c00c00b41030510900c114100c20000620a000340c034040c8002404607400c549580e5112040442504a52a0814011803030a6a4410240603101c450f80000c203001401100d00d040c9501240f115400c0003051a0701040080d0769540e00c2040c001360400e5003100c1d40e031248100192500190501d034415035141d82843d001809200c408200908001e1298500b00b0145923107040c040d82a0f0040d9240c3d00c0454018401000141c0c020300c0e1030000c503032080a0014050300d2801c0010000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 123977113 1250 123975863 123975877
    0x20f07090501030606082415130509010507030204050303040e0921090a14011e230417190303090309030602070b09010e0f0a030507020a0e0c0c1002360402 68
    0x103107440e0310040082c009984034107400350071540094100038200380705c0402e104050070400320080e08810f000812520720384544000c200c00c0100f02500d813244501c0c0b094081d100560f1100565442c000200700d0f400c0c0284201c2c1e086690141c040c501f0280307001202d0f100b00e00010101e5005009140d00318441e51215403282c2c4c07032081c14510040d280d80d848020302601c2d0100d60025441e004282004200c1aa0400003060b400e04003c80301800c1c0c0c800341d1001320b404081300d0400c2000038850403005803004004401820030381d00c0c08042014458981d021990780c4204a0300d00301c0920031015004070101e84250000c1701da5034000e04022120300d42d2a0f4402c0101da0010780283c5610210206108500100b030044802c824007139801008042008480c02d500e58844020040511500140c81011501e48009000c0141101001d41110740b420007980810b55000c1100c6c200d260240c62001806402c183c400d6401e40800407000c403c11140282c010244084503040700025412035484009483e5214001040301c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 123978363 1250 123977113 123977129
    0x70504020f0408161505120f0403030902030d090e060901050904081e0d090b060a030b010b160b0702061006020d050d0b040b12011a090402030a0f140d0c0c080303061e01020f07 77
    0xa152518000990394170307400409600700901044040b042e6410000300c503400820103003007001140c44070301d401c1d4010b08420b20000d405001c3c1e0440780306240e8020704404200d0702d4080968000750303508020040d480c1c00901035130343c0c80039000380401e000c9081000900030101c3c952008840780000e5208844040d003000c2c1c0c0200c0342c01d440356050030410045a0aa542011064581910b2030b410360741c0d03001d240101401581615500406ca40d04c080c2041c4005001c20f6403c503001c04401e081020b4002c1d00da2030300b102c1740024510342850000b01c1c1880014901c001c3c4d045a41d50b9420000220074030070103807500c2d2010303ea02c04c0d00d5a420143c9562035040070004c03a4040d20000612920030748000c0c03e075a03078201540d44103110a408000250302d004c0741103603c05620910042c45103c1c5c0e031a05140041a0a421803007d100b880300e0070420a80080240c81500c1c001c0190f500e15550365400b181d48d078030080303c04070b8200c00b0018500400d66a0f0101d1860f01c200140151880003c04180c42da00e000050351019030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 123979613 1250 123978363 123978403
    0x20901110a26090a030b0a150306050603010b100210150306050a05090607020703020105030c0906041508040b0f060102150910021815030c18031c050901110c0102070504020f0408 78
    0x141039100c04860042c0600300b882e150342800d0a40c000507078943d0701d52002618081d912000030b81110926030100094084c6003054400700ba48170b050500c0100800c440c010300942c80c0110030303003c52503c6107007840004410f80c020503064ac5402d43d1300e005008400000c030101024410302000281c030728080c152281e10b40240c0082e6900d01101105d2410030082d12034002e54118880a00150740e01030101d039485041c1802c0b60b42d4a440c0316021500612565120600091143d0800080c1a07070200716a8043c6001d80310f0a145511000d10099070b2040c192541030150303000480310801d5040021a640e0701038070007819245800003906219060342e001c0421604e80e4070140c82d8079806890005480710440c224034009504525000d4031001c4544690002001040e00880e20100d042c3d8081082c03600241c169000c042c140c4030b03040c0024010f42c200da90703040d02040c491081010410000034030510310100503401092014a04000e110003580300210703034440c1b0101004080307240c42c010814262450140c0035011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 123980863 1250 123979613 123979643
    0x40207050c0301060f0803041e0b0415090506030f04020d03140a090501021504110607080f040e0708090a020a12020105070212030403020108010905060906060a02030c0a030801090b0d08030406020901110a 89
    0x250840e42590030540300e41810f00002c6c0000030b800000d441c242d820382c0d00c00c0641e0182003410080511060f6011624480c000107010403040c03566202000701c506541c03500401a43c42d4010401c40340402c4407015800410840082e0143c500f8400c42c0140398024108081090341c0548071403510390003840c200000c5032002c0c0f001c00603942e0402c0b940000683c50101180c05040580c0d03403400c02146100f0b1240b280c50b0100700002840079120468803200042d1088030360380c17580e0303a00301d040084080340c50b070001c01e4440002030080c040100b020203c0302c2c0e0090420504600b0202030109500c0c07828010390410105204180040e1100c0307100c0205118103100460700c3c0c1d46075100050a403c0140c010008590400c0c06021082e02d03258041078001008950035602c6e4000050304a207940501c00b80e0801610856194209058203c01854162084843c042c00019039120a00100701a01c1c10000c01145003080000d0208846038080c100c1641c051401511750f00c00c1c00c0c2c60910f844000c000544801c0c165150079 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 123982113 1250 123980863 123980869
    0xa0f1b090b010f030509371209060201023405010504050a1e030c0b07270303120204080613050a050706030e0712080307080a02040512010e0c010e0a0b0a02010b040207050c 75
    0x761030380340c003a45005c0c030691405441c46511107010080c003040c521070101e107018550b40010b200e1640120014003841c45144141404000d54241d00b06c4203010a01d0507130701080e21813041c02207030b400a8031020b41100d4034681c07044050380e0b2910080300c00303400ca10451452000690130b0180c60701903170140c1c0c000c14003600c1d182032462003031002494825144900c84030742c00000707802c99107110300c4540014202405035070789142551002482c00c050608a045101d02c01c00b2012484481c4041d64001d503181a80d025240921808a1140780200005030313010800041d8a20b10a1340410b4560b40b28005a8428100c1a51140c1c0751008680080300407984400946030110b100700f09000052211804170007440e50706d900c031403080c0d20001e401e41d01000280c10028407425543d8040700c00515001e040300b4422420048254000d050500c0300c2007041c00b07943c05500785d0758405c1c4861000c00c5002804120454909406925240d1242d0103c9007555210300205403261349620181c06100e0080001d00180c644c40820 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 123983363 1250 123982113 123982127
    0xb06040f080c04090c0e06010e0d05010903080903040605040902030a0b0405040305040e06041a010528020c130e0303070c1505070306031208010b0f07030c08041706180a0f1b090b01 79
    0x105600444c58072140d0300104520326002c0d41119040080f075038082d100c3c030004031a03204d03040c0d40300b6400088144158041210542c400c008181c041e035505007042d00c072103000320303200c2c40b42e8821036000550520060154011540c0115008140d20340c00140152a20f000314040e29011601580820800320b0108079000602665540c00f4804950800429000060140030450032405450410034085500300340040d820320310b4030700308060b0742404121071550311000350758a8005204a0103903044a40c40e01e4140d00398050000160354060286007035685211040352081602402a140081e2056a290307500c0064030585000d80115600403a8450550810003025041c40e41c0d4141013008400c010060360165000b92001421400643c0703656842e217003811941c161021201a0288100040014406070003009400d0080e800780184c0351079640c0c402640104100107842080140c000100706000141c02030240c000c0c1600c5000031180c0003a2000720004444401e070407203044241d6400042c001c0d5a04441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 123984613 1250 123983363 123983383
    0x30f020708030c030322060608011a0418080702011403150f010507053301120b0f09120a03021b0705012c0d0323040e0f040b0403120b06040f08 63
    0x861400c840b5141c030950301d00c0001c081c0f54034a546a06c1294150a454042504144c0c000c501440b402d174503040e00600800d011649040984c402c01803914807030900e0300800000c03a25a5500844e204102d8a03121010350004000f02d040001c0d0300c202080049081d0301660080340c4800c1c4184000034500d041c42041c014804080341440024440c14001410001e0504e003208011f21140d541104081107500403040c20440410359407a1080020805c3c3c1d40500d60011000d014180390000c40e02e0710009407160043c03d03600752101d5000750800c00c440a100e2001851101391903e001490401c1c2100101222015566940301e00c1d00415000c00c915a880381d50035803c10340c2403284100649000010104680250048a00850f00702c1400c100741801880710038120180b80c3c3e80d03800b4010940700f15100640c440e005000180c021600800e201e40d004082e41c41c0700c1e1768042194451174840e40c0f420741d001c203200360341155000e446155074640c9840300b001420003232034100011140c61b4207003141c0601b4074600c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 123985863 1250 123984613 123984629
    0x1908070608090c0d0606090e01091502090a03060b0604090513120503161214010e010807080d0c08070c0512031c0b01050403031826010f0c0e0f01050d0504030f0207 72
    0x5420b105078010085404621002d0488407400360840500c0c1c240302515041d030000311001d142841240001c2c9040d0421003941d403160050024941a131050301049000352008142c0110f5036603c01d00020701c4a500c5403590110007003880d428140e440c0e8208060b00c0701202c1c44540108800742840402c502c07030516407095005410120300310310b441021004000c032030350f05501c208141030003403106240c0c05501038961030340c04603020666980c40340c4400745400000e00c40d07054180314082c0001486e00010134520031065040c0c0c0d030b208644400d51078901e100d801103d03040e903420148280c0000c1d11b40e0b030102804060b800e03c0d4051916592068a440b0182d00c1c60301009010905101a030350701c982e4002d003104d06807a810300300048400004030902c901880c485c2c0050100300020b8907061848002031b0b01900485e510300000f8019006195002415500c05015801c08100c003140030f18242c5c6020000b00040d01010714215042c86070581030b8109481c0d0540b01940800c40c84440790781c000750b0500c442d40182440c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 123987113 1250 123985863 123985877
    0xf05010302150a030905160501090609030f0807020609131b020a02030705121006060306030209060d030e0405090316060e0c0307080304140d061406040513050a060b0f19080706 77
    0x141d000300c0c107000c60401480e038031010001014051140254020540d2981200c03c46102c20083c1c80f00d56995001d07400b50358003240c0c8040000404500c10011002587da00840700203072a0000c2e595401d9541040b901281c0c444c00030f110b451055120181e0802480344041c0d00442d0b42c101c602c5040c401010006c2c03070300045401001307001d000b43e20000ba000e000c45809980101c0044040f090003404c06042c41c841101240c01c04a0004185500d07401003015603000f2a00c0e84c1094594004009070301c20443c0000b800310382500c1c00001c03a0f03d45544902d44c00034603902a640360414080c0e64000d03203014400115002c1d641d0306021617184408120b00400f450050300180702c03590401030030541d0303030149110303c0d407524544054284290702d440110810650340120103002d28404a0008408404101c40c06070040d45803d00003010030307480c1c0030200c50b4a074000c00a8819a90151500702c06011088003003900702003503100b20490381d12140d02005c1070a1040056000c11400c00131101d00385407060340f14000708818 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 123988363 1250 123987113 123987119
    0x3031c0b0a030b010e06042301050108070809100b011b0f110a05150a030b121e0d090b030606041a03010905090c010912020a090f020406020705030a03080601080a022a010f0501 77
    0x2440445810b488030440140f151b682c0d400d0000d400b810038044513910004112058444a140082c01503041c1c0e0400d0f02e0b039510f16510303110202d03070b000c800b01c40301c0b40e0310f0f4801d840e0002590481d520028542c1c2c0107140c0003070f110b10712607054140403904a8044486241c02c0e4100018082d0050070150480e50444003002c80502d01800200891900d8400a0782c81800081823040309004c0d81c0240241e650140c02040e0a0b80080700f4aa00e44d080290510050048800e241c06031140100712400000d04d26110f42c656507017880c0142c105a00001c0080b500480e0030003000c034a081c0304081d4091b074120412200c43c2d0300c0d0f0429031002d0035294082d00d0f1050b141d00959000d17003075a030011046825604a07101c2000c1201003800014019116680030030000c1340b403c40c1403003050721640c00a0041d210700342c0848607081e030341d401495036072034540c00c0141c001411000403030714641c400c402c0103070003140f8100c01500b0000b000b49180721034081d500608004c1c90f518440000c054000303008241521200402c2080310791b01d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 123989613 1250 123988363 123988373
    0x50706180f12021507020d030f0f0c030504062001050901020c0f03070803011203030f090305040503122107110115060806010314042d05150c0403030e060702040b03031c0b0a03 77
    0x100d0180013881000d50455040c3d0440d440015034a4182d00146034000c18a605c0c00c010300080400b0b80c8040005a001c000328101c227010704004044551f16548140c0390628219040b2202d0386000d143c02180c03180044907aa1b800300034003d050041404200050799002d40303998441c5004103200310000700ba041400b240b8040384429042c0e80c1190084013213070950700d44603e411402001100a10000203240040748002c0c50741c8840504252603059084507201001e1107003401642c014400b10040c0d43e8134a00f2440c0800e50404506500055541048018241e4540c00282550b95201804c1d21440110300c04002c0c255001d0300ca250803c800f07003410014603040c090101d808840003840502501c0905221f81005140d40f246506800c14034440e544601205241c00d5441e40040c50303541c03881c0111040440c0c9101d100074102c90403658143c48107440c011118080c001160481c0ba42030340d00c02d540d01403d0203291020b000170002401c040b4008148a0f4081c441c0c24100c03810449010b0044039241c00901c0019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 123990863 1250 123989613 123989639
    0x1109090f06060d0602090409060603020f03030f09280603020a1e121104051809060609090a0f0c0f060503070807140a080a0906060308180103050708060d02030a050706180f 75
    0x824140c442643e00001c50400c01c0c06440f40542e2982c10515104501e0240300d502c0d80040140da2088501207849070b070220405589004084040d1042041046480c44c1440c2182840c2440d84504107041d4031030030b40c4107030b900d034595180e880600481d4001030451351003944a0303c0d0040700916500d42500650704101c1c010490a8100003100c0c1043d0fa4101058200580c80142e400500e40140700300358003914a4040f0150410660383c0d640b05110742c0740072400d00d1034000d03003081c4130781c80a170000e219050194441500e1861401c4096650040c407203004a00c065032000050083e2842d9114590740c1e0901d814000c041400060000003084500c2c0e10004031000204100d516526840c506806503845000e8204000d2401300d100400c110328007140001002000e101504d10b040b00e154a9480c4104101c0054007070f0b420440d904800150004000382c0ba41c40d185170490a414009030854414207201e13034505292080d690482408110742002c25030740500b03030360070980207000410116404107141c059064514 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 123992113 1250 123990863 123990871
    0x9050408041518060302070501060f051c0c1503020304020306070e061812100b01020d09180504050c090f012112050a0512010b070b01090213060503060a121109090f06 73
    0x1515902d4040c034a900d10075038461150b5500700741c20100096031524090025403100ca800c5400c0d50821800217804154580454100c41001e021b500c0d0300d0040f042c0040c141480424106c1e50482181c0c000300714481417440180455074181c40c0142c2d64109070040600d0060000d065008110034464400f2090b12540285c1b401a21401c0054910165034000207015100009269090340308100c00c0035001151034026a140e04403e0b025075401c00f22200040700d031107000d4010881000e030081810740940c8001e62103d0388c000c1c0107500b42c81035107900b080001d42015080d10a05800c4131208014003d03114038a0a00e0460440043c00440c501e54540d21071a0042c0d50070054014450042041035625002c1c5044170880c40c441044030000b0341c0c5405820401d03410119055905540c80d20001c9400140ba10880c2c1c3c4090685030a084128a0110115015400103000d507400010115002410400340501585007510904850040100070001d12040220040001032242d11100a4203a1410302185490700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 123993363 1250 123992113 123992129
    0x20a030302130302030609010501030c05150708090409200a08010b09160c0b040501050709090212060405040303060906030b0121031e03150605030603100204050f090615120a060905040804 82
    0xa981c12204002c2e03040841d540065014010300c010061091010361002c0d051b40d200315941c105258a0348244041c40141c0c8030701281d810020000000400c0c0c84401411071104001c001245d49400d84d40c130001269400c8113048001241143d00080a1070b001c1882400b805050b0000c00ca010240360000d03140d041c000d0500030200b1008803000749018410a50180503c0c0c20692000540c1040e10304140280011549400054032482d80891608814001c03a4854040780c40c024030303161160030811001b440050302c100d050556510001030714070072601840c8010341c0242c020103803640c034001c40130180101000201d0f20001c2c0180804c2c2c00aa00309040784100104041c111400101c420420740090500703040084100580c1c040001c2d0a41c0e018004520691054064544840301042c150090f0b00480c09944e038020316032032050f945414071601d410707030101c4c0040503101d001d452030320305040c16031100056403480900c1000300116500309028070030040900082c100300c00c1c0b4054a4011403801035004a01c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 123994613 1250 123993363 123993367
    0x6060403060b060903030c0a0b09030a08010e091e010f0f02090a060516150b01170114060c10060801050612060c041208070c0e0603010f0e030a050a09030b04060506120d020a030302 79
    0x100940743c2e0b81c1a980c880402900b200d54803100284043d5a074134152004481a000000026071842c0c008002c0e9000254541c0300d000040c1d08062144003031070002072180740d444c400c1160100c0010741d545848610074080e200002101200d001003901501c010340d070180368860041107464095101e410601003282c80303d00c0d01c140c41d01000c90006c43e44008001010b080c1901d58070012075100c845500104091009880342401107104007a1001412800d208054400080d15441900b5003414001000350048042c10f60390602c140300f800c0c604030780043c2c00c40850703030303550368200010b60074105030f1810241c2c1c0c07400013895203240100c0400f14a11071401015802c408240d010000c100176103003514052580f01c8280c8080c55216040c60721064011525503110b5030030300c040480d03000302501c034001c100c6400300003031840c00c0461798040e1210b0f80b21214480420549842c00030101d524619958041e034445c00011031742d42001020413801d004032602c141025080444650419500003490980040c0e05040240e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 123995863 1250 123994613 123994631
    0x70f02010c0816080d18020102070302010e0105070b0c0309060c04030b01030204090804050301050405150703060f1208040807090c03060501050a050d0e0f0709050907090b090106030203190906020903010e060606040306 95
    0x844240070303000c02040307080c10b0220fa40080021000140000f40c03c0d01000704541100825111700054046001a02607045087c042c000355106410762218410181040c900e000c000b6a1040c004501c100c0e18440050b0020050118015081c41807540045101001c2c07170509045484c3d140300d208c410300c0000c0c41a07076141910380c20031003040203940c001c1000030003c00c294076150810948541d03c0c81503944130088400c0014a40c58044e1060100340c03a480040c0259550500340f40c1c5c040391089040030ba500450900000651180812003400501030b0400003044503034400e8005410f44100e900660b0605c1801e1003050309850f405005e0719101b0300d8941c40030036040b00c0c5945a80c1051082640f5482d0390080590210311104143c1005006840b10070880301c0641d80d0305000300803240050046540603084d00010000d03248282c0103180c000c09440400403803014144c03000401c071000460200c94807034012840c0900c4c2c2c902845291580c01020000c0d0041f1318280c070001d003191150f4000186125542c0c5051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 123997113 1250 123995863 123995873
    0x10504080303150a0b07030201090201020d03051005010c050f1e0606060a0e06130803030c1309050f04020d1e0b0718141504030f30050d05090a05060408040f050303070f02010c 77
    0x4240103240840c0c1c05903641020f420028007824003042b060b4094410400c003408581d10074451140318520003001020140d05140045900207061042a1150b00c65032411014110082c40609036a17910034000301c0c036101c450405107050600003414148242001c0c000380203529008024402d00030f8003102c42d1a6030701070030303c0600d0f41321109401403130751440003100700b2144844140007088004105094090030321794078200c82c005c0c0c8800b1601d04a200b9403a601083c0103042100c002d004a920030700d00360540079000d03561340c01e110f402c0b9030050700d0070b440220a0160f000c0c4c1124001c0c03008150109070f0350380c0ca0b060520080b2030841d0214010700844188240a10000481b0305171809554000c0005040c1045810b0080081008501c09081d6265004800d0056407402080300400d400c6c86e224039007031410000303c0c0001000001c03c15461402552004e000049080c0003861085205240542d02c82d802c01003010203581454100c18042d5100f08140e101146020001c414101c0d0309107070202c8006003034602 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 123998363 1250 123997113 123997129
    0x5070203070f080a090801020403020f090c0d1a09090a03081503010f020c011508030301230402070501020a030e0c1509090907050d05010903030b0933060f0301030c0501050408030315 80
    0x24240400d0711100400b0006860010003188a145d07035075a180c0c54542860500b00c5c403e81c0700080d03103d078011086000a08180c0e00e10350340320b04016065410000c00b400084140d503007484c000c1c582000c0c1039400500500c1c00314a0307103400041c01c03001000101410b83c0c0203400f03d880a40030405081401e01507140c9560250048049540501c00943d05d0381200e08030a406013002c2100c61598040307009012942100000c1500c0c100c401c9099000c8051400f41105201400440009030f00290200500b002140007400204000d03080d50764001000c40d51500c40c2c03418102c0b01442e0030b01c03400c2040c546101603001a0309440003140708443c00c02d0b85031500d00702e0728980781182d44600c4d00854160f0381801408010b6002c541d0150003a00c043c08800d155800b004018141103038a40b0740308161450b0300f401ea5100504800300b50000900c051310880816002840f0303900302d8543d412000000000600800c000d03c1c2d1a50300038402070800c642841c1c141100f0301c1c1c0380c0c0030080101869800510340307462281d58100f9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 123999613 1250 123998363 123998377
    0xf020702241909050909010c02060f070207270608010b030d030f020c01141803030c04120f022d03010203010b031f0e01150305070e060d0b0409080c0109120c120305070203 75
    0xa508000085000b009480360b043e5104042c0b09500b841c000542505041c091440c1200c4150b004e400d10740d403810003180d0860006403000c0b007144034036000440c08000000081102c450403c100403c1d1000804214003504c042e90040304959051400c2d810781a140060950f480c2001810045036606132200084002c1c041d564400c401ca43c01c00700400d040c214103030001401408640804054418002c2c0c00350b60780d12090b02c904030243c108000401c03e400480201a095600c07680413490b000000d90000342c81410ba00318112013045240303403200c03011044000c1000211000340c2c003c3d401e5615008564145000080031034440e1002c88003078245888007070805070054100465407049079610307140c160b5042007481242d07201003840c1c000802d81ca1070180b000c40702c680780001d001c3c518200c04442d10302d001d40711b0b0b40442c0760000c0e180c03149440003400d41c1002e42022002a000060141040e081c04802050711086010901c5100f00030702c004100701e0061003811817018103001c00e4544403031004a1643c85026 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 124000863 1250 123999613 123999637
    0x219060902041a1f020a02060a021c090810050103050714030f070902030a0c0c0b010501110c1e190e0c03070e090a0902030115050a2303070305010606030f02070224 72
    0x10450780103109102070607143d000b005641d0b110304240c043e442e01110940b440003070000b6921140046005142003002819041c000e44151614500b04483d0481c092264044c620080341c4001c00a0090324020000c0b0528030004020920440d4559101d03907480352050302605003400010140340c0d9807a02d0400c01410301807508011647e903159100d200708001c0d0410380e600000241840314048c1c800e445440074450103500000c0144c0306910385401510307000100f0f1032608090140f160521420381c0c5401007c2000100910311810000c11401004083c82031510341502d072100150040c40345062400300a54001c003030b41120b540d2515032250079140341c041c1c0a0510f5020031400104810180700da000701c6860fa20a4009000c00100840c030000f203a0002d00840d60400303864101003142c5000303002021803003051800d141940d80442c2c40840d040c102507810548141c1c2d101c1c41d00300105c5505100c1c0b28000307840c0b46c1d01103003010317110350007e008130f4141c591828915010f40728000004001c0b030110380c0d80305201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 124002113 1250 124000863 124000871
    0xb0114040801061805071b060b0a03080403061b1d01020c040c03090b06010219021309080c06070206090304060c02010e040605120a0506010b07050303040b07110d03050a0b10021906090204 82
    0xd20005406080c40b8044e21058580d0b1041c0c1c207020005a0007150b0060b0340c42c1e2200340f4100400b207281c00c52000c201c107051706d0360794659845c0c2080c2c0d110415014041e5008141fa0b560310b43c03c40c100842503801408120103400840002c1219807648035282d56540740611103080d40690003000105d103040d040001e9680d0117441c1c8546194610b4040c0d02c500d0803507105402408441c0c3d600c2c0010390300d55400c0722225001c0d064061411005160100c480100025541400100340303050761610304c0c480c5c0104001d031900c1d900600034096103980401c1000c0c1e10130900f100541c60941801c10050101c10352000003410301c140e01d0581c0000d0341c0d8603000702015001c081e01401d00301e401c0304952580c0d407603140c0080d1450b0044100228450b5600c0080305c0b0300310380000065295481f241c0e100300350300200420550400c040c0c0c8800c08038000e414840c0c241c0000039950046107034185006200100d41014541d58071403403091b51038040050700400c190b00d0301100550340d00e420f2140350805c64003034095100000d40c03144c54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 124003363 1250 124002113 124002119
    0x180b0408160b2502070303020d030f02120f0906370b0405040804060e060906090607050a0b09030d0b09040302100b1302070503040e01050d080d0207030e060d0603260d0b011404 77
    0x10200743d500359000442c0407044500f105400c00c0c0c0e15810315000240060308900c50003460715000340c11960841201c01c40061802c455001500a071002c1a15000320401522051066034982006840e030444560541144a035003101c040f401502c09035070700c00e140e0809101c01d58001700c50680c440c4000250280c0144400d2405d4500075a07207034410300070340021410203904000641881c6041d40c8480030003034000c0d4984000c810030060560046c000490351880b810454400180b0040c8042e4000d141c07210081da10b40400c0718401065440003e48103001d03604070b00420021907800101d8201440308400300250707640307402e80410041501d04880440c07403400010280100f1800000400890742c0300c00a050f1581d884004000441c440648043d20880090010b100c003800d4030f03402050910302c40c0c10078589240308500481c5207900801c50008545507901000c2040c8884080d070200e071038140b000101a00000004000400c3c050801112001030782d5030242e440c203900880c0320204403c818070f412921603a07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 124004613 1250 124003363 124003381
    0xd09030806010206090c01020304230604060816030c270b120f0105030f070306052205010203040605010e09030d0908130312110a030c021311040909030201180b0408160b 74
    0x10907911140144070308000118480c1d4041510100c0c0c0c1d90580c0694503041c909942c0d40d0400000b095480b81c1004003800b100050395485004000800094903041c4241c500740240d8907091081001003030626007005e0401c0d1541c3d6210f542032805108a542c030414808207000004c0403100326030058000c115002030f4046581040ca8442c1d4030030909031880010305ea032908103060300e8001102d8a0021070b4445403007400020501d40180d0780c00100d00c6106809141e14501070702c02d0312051a030136140c596001040c0f1040c08010300449001d0010344d0b200c80c2d264103080100c26681c1c400e00840000e85962045640c00b00a000d404840110201500a0b9070300394480c00c11200d118855149580499041e40c07102039000008108001071130f0f01902c940c80003461507003e000c40055640601440b25540b44c80c4581c02c00e407030201410203030075074a400003510310651801908460800130b0501101040c10241000602c0b01840d00d03030b1159012002c1c90b21103000002540c94011804d01c020120307801c3c1e90800642d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 124005863 1250 124004613 124004627
    0x606020313091b0f0302090915030f06150f01020c030a0606150e010203040b030c0c010c030f0b06030f01030305070f080307021b0402035208060a06050a0804080d0903 73
    0x1e40c480d42601e1129640c048280450300100f203616000303a80000c0c0b61841c180100200c2c202d50f5100e0801501d08500440080c031401c10448020f0f801c1d0300d280e041941c5500b000c2040d0345103148440300902d0313181800c034840000c91002c034600920a40c03c84503804001e910901c0010341410003c0c0481d0304c125403620345500949194028100b40f10941c0c40100c1c210f034407480800061107010b0300514586030422603002c60341d50008000c9624050100f29503403029609200c0d15003416081d0b640004c8036610005100195021003c000d403240c0360600038007070003100010000d41100c0c0c0c075051580d0f850345585030800740e20b001d40784040c005001c0401001201600030400c0d080700711a5000c1880201000010041203010513580300c1014a4608640080f0724142030483d150081c0800c1c1034405015a150f11900380e498009a00c00103040030782c441e401075034204101d960400302c01c541903480181401c2c0003c0480c000c1e421513004011404001c9000e10010760212107c01007815810705c20000c1605026000e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 124007113 1250 124005863 124005877
    0xe01060203270a05030a08031f0e040f02010c0503030702010c020c010f020c040f06050a120204050c12060409030e030f150703020c0a0807060b0603010b0712021902010e040e010e0604110103051b07060f06060203 92
    0x403810708803032020100c11b16881d0200b2b40e400e0407415211a1516100e83c2c0c0c1051300d082040b03050003002500900401d41c200060341c4254075550000c42d0030124540001d003005030140700a4107101036010350707a50b41ca8000c181e00441d50419074000509404c0c208001c006003000d5407206810640058020514031390840076041058000d4905000740d89400121012510625407000708554449010aa1500d0503030003910590380607151000e001c9480c1c000090524040201c54485540444c5001c00700444401c0c0f001d03802901c90a0450030b200000c3c0260352140380c4c040c4020300200707001070f0740010041305038064840408068401900d030342e11000d40403040d9000c810161840c0c004184405251440020404090342c0f00030782d031101001c070a0340103541550441264030742c4035890b10620007a0700f4007445000c075803040301c0d402000c0600f0300341408820790500f00c0c09107040600740340801c84907407030122001e4000d03507034910196039945144c24100001c01c1800c241c005417504055002486a0b8008060a05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 124008363 1250 124007113 124007131
    0x415110105010806010303080609090c150c16050d0314070c03060f05060a0b0a0e03031c0c0f02060f1303110106080c04060e010f0b0c24010e01060203270a05030a0803 73
    0x41c50362540709240c1c0d078800912000740003900100025504d8100340340e030b207074103c02400e044500208540d00000d52420344804c03901c40500c0040350100000c2810041303075800c84064280000d081d41004081440300c800c82c4009000d02c04a8140000b07440000b00840d8501c54010702401c000035200d1070110040c0c20584103c107145420040481c07000d00c1e000510700b049460700d03405603103000c140e14000d56203c46142d9660ba89400280400c070501c280800c0c2c00207124501d000f0004800303840380405852000d80244641c2190320503800c116146c2c0e00c0d5022590800f41ca034114180b0403003a8541141d00c4d500c185882c060315424213200044200c030021f00e035841038904a505011554440b10007000b1101d007403151441e510640441008049003810046c4100d20104003070310b207480c2c031602e4141d20325414010940c8200e5040d400420001607111541d5014020310301c06940303000042201e101a44c407145031b06940e00c030a0346902d1080c030350340e9407000c3d4014900542070390300882141c10079035041d030012201012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 124009613 1250 124008363 124008371
    0xf160f0503010509100b0303040e190518060103030804021f0906030b060c03030a050402060f0a0e0103110306030c12010e1005040c0e090607050313080313020a1509030b04060204151101 81
    0x40e00d403906004041c480c010010042809101d04054400580381205043e034150104010118582100c984051311403072409111064144c60042303a8070403114004c012201c0c60364083c2c89115203800c04101141107030303010304c2c1500300b645450000580e50910085d1000c0c0a0140541c1141165080380308142101d40d035031000c006240d80b0905009981c86845c40c410096042000024100b0240e0391006801500103008207040c1940380e0000805036100d59041000b00d004900780303908542e814042c03110681c9003015241d04506211010030f43c2c0d400540201d42c4104542003003948165802d520171100c1010700e80840e48a540b02081d000d00a020a840540310340c1020b1401145008142465038000c40000008012756951540300310741c01d40014102c244121138040b198408250001d000d0741c0035106d0f074441c014840141d40304025528005a212000c80c0e90390400519429400503000c01c2284e4201140195a6031503207400c1d00284210b403c6842098910f02c450700769950305c49140c0703100c401d852000304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 124010863 1250 124009613 124009619
    0xa020c150a050a180506071401050109140406090311011a0a0803070309150207030c0609060806040506030c1009081606080a0b060702120307022e03050c07030804050f160f 75
    0x8095104440002000c5802081150481442441c0d0203500501c54113440c0062511040024207aa00c06241a10f21181e0401585495102031141d0342c010123003994104030040800994202c01c10004001404082c0ea40703030702c40c0038580030304032801300e41c0004030082290707442c2c0c2103c2d40303095580c80c00040c1c00f49120020100d00110000201d408140d019166032803114501511240703585810031500d0114040c610001001801003d8058098101625101240c90404c6001003401c107000b0081407140b410f01061211684000c940000c0d0540281d525803040d0613045019907101680f07512155141c810401c200b64007050b070f01c89010030b0320942d80e40c0d60307a240c40340d42c1810300381d600e01958580d06c554100048001440e00340e0100c1010911407080e40d00700612500054186176010111034000101d070040a1600500040120001c1d102d03802d081000d820044181c54840c000c2c01001014050b6120125042c000c04000c0320312565603100c104c03074002c1c9803000c141c0d203814014450555081c0c03220381c000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 124012113 1250 124010863 124010899
    0x10b0a090e060d0b10030f060b010806030a0f0303150e0a0e1c0207060507170c01090203070b0403150b03010e0f0a0506060d1e03092105190215030415020a020c 70
    0x103a010b24001842200008010744803440c010001501d800c083c096128400400106580b00036403c55000340f400050021009001411210004000c01e2103500f01340e445500040380c0c001c401081c1a094600029810044081c2400c3c03c0c80c680c005500820f00c42040020816080e000642201d0120f0306075070407800140344042c101c1c2e001400d044c001d078110010070302a40b4800c601512070b1500841e04480342c1c03c1c803000301c61031f11786c17086000b4012a51100c0d00442503060810220740140400356000e03140038a9902c1d560710211011224694182d1180346d541003503602500080201800c2e10305036510407003075100c00d039910030044a04a030240100400684685400c00845001036040344107202680e071031080d45600302e01c0e121801c6040c000d00300707400308510294108111110443c0d0305c2452511340c1c5802c2a0381741c02da0321500d169a01c0c800500c1c81005031100000205040b01e80bd50903922611180380403000b10058a03e1080100d201044d030408095000440c0d90040744191344141c88443c03c0c0c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 124013363 1250 124012113 124012139
    0xe010b0a08190302030d0906141b0a110a0b0903040303030608070f260609070306050a0e03070f0302121c0506102f0304060201060e0f040f2009010b0a09 67
    0x1410166030419002c6025090041c88441100c81c460b04c141e0345071124a900c3c11044400d8641c1c00c0d18941e03a146050b040300c132460f11380103400c4252125580d4442500c0c052801c000d200e001481e8041000741c0b0082030300e1700020040304c401c0944c8005421703264070b48a072401c0e603642c01c284000e8000038205000021321070400b05d10f80c0305555080c141c000d0002c1c10104a0240856a811038000004000e81e402150701402d000d0180a650740c040500700003455820404180ca0000e041c9640c058a00441e0f000014000000c40e802e07680e111500b079424440d5800c0c16410403001140986d12480300280001c000081c0e214040d0071815904410801629024144041e0148020440001c10484c1410481d50780311640341100d0041c08005c0345004803240000c81e8110740040d03101c43c003d80e46030082401402603001c070051740300c0300f1201c0c01e030407524154403515030803140b041010300444161305110310700090003039003600020409840480e8551352480480a10b902c540c007101c1c00584c0380780c40802caa011402c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 124014613 1250 124013363 124013369
    0x50a0302090403111606110601050a0608072309010f030504110402180402040816270507050d0504031107050a1a090402091201230601021b01020f030408010e010b0a 72
    0x4509503400d1180000e400340082d030500c0000c544c84000340c00c3c100072568945c00301c0e0b141c2641c25450800301414080101005a600c0c3d04091f0050006031140e0700c03210103c480c1b61a014680c0e403958041030710300302130344260345408003407680c4001c02c0410114010b0103400f600782d84414082c2001c8d41d080b002c80d941928000e21891966003100d41514140c0c01038044007a0300c0d81001210400400081c00701d92103644044219000328580c20142481e11220100801c05205a8880003400e645240008c510150174161031564840c04100c80d41d2089042c2c07884000300b0007007001035040c00e09004d403a52040c0c411451941c85140000700c0c2d107041010883e000c03241c945140442c80c00f86c5d40ca480316181c000710b40c11030f0070650910412100f0740d10031208442e64000800002880c2c1e03940001c1007542c8554803d17a100c4040350f14213209280e640040c000b800411403800c02c80540c007400004034200840501c100229110100340400c82c1c52043d0300c410003c0c0c41c0391001f0400c558400b403c1c04100386442c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 124015863 1250 124014613 124014619
    0x1603020c09150f150403030c0606090902010c0b130c1206060b0a0c0609080d05010b0408010e0a170903070e090102120112211403010b090907020f19050f12121005 71
    0x28404101504145810703460941c0000c1c002141c5031440c0c071304480b040d0002c0e40107a000515416540c002c0c0705003485050050f0550300018811640e05c0d030001703400c42c124000024401ca0a641c00202d070391407901035481c3c0c003e074041d11840503590355000d1101c0c80482c410068444914140300000c500e0307203040c1102d5402c03001d40c45051242c083d80d11088018101ca41096410503000c0024090f0101c05100c1c0c02c1c064070f50700312881e440d00c0c01c08a059085919140802182d84d00c034040403400302d024004180c10b09494640031544d244501404607003410510760216000905030303000e01c125001c0640180c00c0541c0b2150444c3c1d8141e07601c464400c81c681071281c01825520703401041c3c0810640b00d1004520031002800d2070f00c40c80074131800c42c400c16402640030319012103010484040505d8103409440d0030a00900c02004282c07008100329448101ca0b04500b514404141540c0003041018002c40742e02041c81001d48011b01019060b42c0720341c0e4030205580d0305114804001070303550680c40512506031403001e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 124017113 1250 124015863 124015891
    0x31608071106180703060c0c1a010509040209091e0606130b0a030204050403090b0301080c01140901120c0e030a060606020c010c03080f0a0204090c230c121b031603020c09 75
    0x111008000c1c0b20f040f010050050141150110200b5880d0140c8020780d030b2207030741751a805d1009081c805040068a010144040c0d01c41c40100038a503601601190000d4040342d26110b10780ba42d245c868540700d1100c62a0002c4605d013140010504000b050a612820702a1400d551122030f0241e40b4045804201c680b039800400d1500c2880941040d51150760f00034030034145148080c0d100c03880240203420980c4000003d9200071180d17511035078003103070701c1d0146088026a54213100d18800040c014415500c2202c3c0d60a41d5900c59000c803d01c600c0100703d4409002d0709a83e485030386810158082c140b11301612025203d2552103107095486034041d241c0454040d640d0030415200d0000c1070022a1002d81451748a0360240400300c2c2440307017403044031108140794469043e06000c0c42c10082d850390001c0014903407450244400146000045180705c0102c003101c003800d50b20309010311070004000c10a040100c55110104410b0b203079509410049005074060303002c070b906007114041004076056086a03090a91004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 124018363 1250 124017113 124017121
    0x60e01050c062715040f060e12030610080105030c1003060f0e09010e0a02030a03050901090302270108070b040506130b0c0a060b0d030e01081305030c07091503030c0b0417031608071106 81
    0x544c50300306d4400313071007040040703058034090450740d1624014542c810404a000002d224003403030701c200020074041c0141040c00141d0302d40800a41c50b40d040a9034240100003000c1c240241c140300760300080150201c40b00865031941c6954000d058200e080700c940b90305600c3e01c140d0480f04100002c441c240f060780113005010517005a6812100c80d0860300072107041c031481550100042e9a1818070b04480703500342401c4080e0b815040d40c1035026210613488062260822a4148180c60950b4111000d50f10107403040c40d80d0300c1c0c502c00505030900c415805000309030408200030060400c086400d10b0b4540c041c0400b8040400318000704514491480f200030049550750821241b154003411520758426095110007299040136102c00303041d5071240d0517580541d042845c0520803100c0504c030741d00c043c1ca144008403c84c9400d5540c040c01c54028503102400c0c6110900025040001d44500f8500c841d5010440700d840782400c4a0102d890030042c103140d40410121000200110b114140040340074500b80005c0296450b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 124019613 1250 124018363 124018373
    0x20f0a02030723090103060b0102010c08151e0d080403020102060a020406080f0a0b1003050702010c140d02030907150207032306040314091e010206070504030507060e01050c06271504 80
    0x102015031020720050f005004210b56514004e00707008500070351012441c41c2c0d5040009084030450548942070000d16404d0115a0f98041e40c5000c032144140c444440c0308564192486501030400e5403c3c0c3e1110148031001c040100072030107030045a10030303021515140c4441408000707a0150740a580005198036000a122152030303004250402c07400f14002030300e164800003243c0710150608400000c00d880d50203000100354240315500c16090702d8508400c4107051020740145074800c0380346040b0354a8020001c2002d080042c860440108600d9006c1408082c3c21500a03442d40c01c04d20007a02e280a00303460110b80100d54280d41e1003408246006071403541c2e81c1e40e07010790b580c0004100c2116901c80500030f281136616130b14468148400290041c50b48404040c00080c0380410003010142006010b005c1040064000510401600c010f0f00b40550302c0d04030480122510300401e07000343c07581d1042005103e07480005010031940e819a1908014100219140e05969994840c07601c409200f0140c4c00100861 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 124020863 1250 124019613 124019639
    0x1060b0a0e19030501090c180209030303040602070303110307180506030702030d0f0b04021804050601172e06111002040f060c020607050f0615100e0105211303020f0a020307 76
    0xb00925100081c4584a450740c0d421107010910848030f017604180c00b840100f84e8000e0054020300071040030761412072140f010944a002c068401492560041000c0341018002d0304540500301d44181d400f80c032490000070051181030741403140404110014004030f100e0420004513446604142c00031403920055080103802400d80244d2040c885544100c41284c80d601d40c00100400d204191a0403420121001080219580074204034140a00408090000e04100401a9100c051012040303e008030383c0b1b55151400c41603424180d0310854050300403c00380c3c0c12035004040658002d0807600c0d00d41040d003144089100350f0290f07010050740328004002d014400c02d01a814944040c01c0340341031508030359a0601e451418180c2d607695800000802c84e072004c174415118240300040b036003001e40c4d107420756001e000c223011104520b0420000142041d000c5501d0134001a004511000c071312050301e0035004190001c1c0300c00c80100c00500035010100300301400015000391154000740502446460800440009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 124022113 1250 124020863 124020889
    0x51c02060a120c03020702181b070602070812010e0709030b01170f070906150306050a030803130b011710060308180a090e010203100e09210705060c0c01060b0a0e 71
    0x102e80491800d210240d240500c6440e210300303840160322403807544104500c07110040480000c091381c201c00c001402128002c1500c0201a00f92071aa4034113140c113103000648144180a401d0f1000028260005030f15070044c14100d5940e580492410344880800315a003c4039480701901850781e1034014481003409199549040c6031b000308450401c0344001816042c40155841003201644d5048100211138131020101704a10707440c0340401c035060521002506010a50202404d43c850100010318081c03030b0403500605080c0c02c0350001c1c0c207560790fa0314015400c0e200b1880003e000e00400c03013403030111940c1c0e018040035070364000c001c08d041c00103c100f07009005402060095001c0c010000002e4100000d2007081c0c400c019070030000d44c0e09c1ca080f07604038511161070303489000d02a41010422a0b4960042003031094000d9164000044c0c0200b40401d103414000c0000207881e0703008810501808440b420000c2c0800b0784080020f10045558189814030b50050315198000301d041d10510291914200c40751501d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 124023363 1250 124022113 124022117
    0x180d0c020910031707030221043005010b0a05030d1d030309090f060306100e0703050a0f0c03140c16030e061c0c12020901140309030f03070810051c02060a 68
    0x155550f9032100034090120020b4040c10700030000d03610040c141c1c180015000507081210803414100010080b0301c4c98070031841000024101c44440d0141031600100700c0105450941b1120b414404500f0000d00070320118101034451102107e000580d420003140c0313029a03c60f04d0b243c01c400c0754250b8004c0340c0c00112080712258507000810000109035244030515000f2801150802000e2400707505051400201400d0805005555401007015500d0911455404941403401140320f807591402c82025242c2c0d02c682e05459800c0a007021043c6070b050b0710001043d008412840c00f00e8540c501c0c60941c920807500050558030340c0740700c54400729014a07020f000445006d0092854244800312480300d80b151260566101074840c1843e03403081d640101000606640c48604614211519001030914050001d0b0a444103c0200004003003502c2801551070341600c1d100c45990b20703c0c011000802141046038940c904005100002c6081c0c2800031007400681312600348812800d500740c0030403141d03802038210802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 124024613 1250 124023363 124023391
    0x201150f1a0c030c010c02030403030201050c030105060f091915080a060317070f0204020a0305180f071205070302030303040503031e04050d030b03011805030a030608010e0a06020918040b180d0c0209 87
    0x4e2240c01d110b042d41d80e089544c040c42d00c2d94103602c0c0081c25200c2c042c0c440c5803442000c0c0010f100c1540c0f031004a48010014030400c40c1c2d12000f00020501c9101c10f80900524031103503030b00c0080d1500d201810051a0f01c0217584030030a9513034054821084410a000c0070303054801c01502c0045442c0101c00030a5041d0058442003074402d0181c0c001001d0344e20141984000035181c40034443d07608041e428011400c40d1480243c08129001c80b41c0c595145031501c43d02c40d80412800d0008140041442b40c6009943c001c0c059079540d10b07140c00c0041e520b90007a101c100e038010524a41103000418041c0c200d008a90260160104005048040f00a0a540800254195a201c00c0c0f101003022184154016600c240061a2a040090001303411943d095001e4a42e59044c09403171560010301107016001d480e0b01c440011f88070480b1401203101f074041c0c00c03103020301000800c09000501c14224200c81c810841140c0600c0e00310151a2003a807902d1103035984402268405117403d00510b01600419880001030343c1c010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 124025863 1250 124024613 124024627
    0x615030209031905010c03050c070302060609190203010305030c0607020703030f030c030b0402070303061404091a100f06080901060b090919150e06040c02060c030f04030306150201150f1a0c03 84
    0x3c1c1018112001155169502c0806110483d0503000f1113500400640d10182044002c0e14065141c010050076248900009030008600c0302c91070a0003c8030100da518119220360312460000d90f6a80010811113952044400045102c0d20004404c1c091380d6140d942c034181d01c4080c031000d03009000f01d180407005241c1c8518280b261a03c40e44003500c100d501079a0089800d40c505010303400c03d903503c142e25500450410341d41101141070001521940c1155070030380300440e40c803003c10320100d8220303401c180000c402c9200b00103102544080c04600500c000c00080081503a1141c800300355214209466420401d0880010344848004280d1803644006407008140260030300d000d826018020340000308410461028083d00742084d10421070344d121f00780000c2a950803d020140701c90b000003410980d01c00d1030800001e042502c260800c500800d51540c81c0724500180c014040c0c06000550114080ca14070303041c002419800501d0007800321031154800e500d0b2074010a401c0788a55200c014180840c0c40104200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 124027113 1250 124025863 124025893
    0x9040b0d03120b011e0507060e010203040308010609050a1a2d04061e0e0907030b300d050306010507060902060409020c0f06040503030609042109080f01061503020903 73
    0x800d103500d1007a540c41108050401200c4215040121000d040100c0201d4036504100b410002c0318a1a40c14105142c079414a444d00c2d03800740c03088202c0301e8101c0d400031052008058011814030b0580b04075461310b14100e5100d8007403240400e2244a180b00810610600040480c0410014141c07411501d040395500a154843c2041d48940c8c0c80c80380303492100019042006c2c9070301c004c082c80a42040c1c1c40d03030f03621b0380030404005045140c071189951280c030012002c141c010b4007941c081c2c091003001811074080302070303003402700d080c029102c4904080300c0510f19055000c0b02000300300c0c609900d145840b094203540301c91004440c0c0760441c1404030fa00d0f65452610701e000d80d9601001d4402082805005650b46461070481420040c5a46001c0b440e64406c0080c000010000300540e0303071102c1c041e40c24a0480d5236a040c001700310b60300010303812098240e884080c1c5001c3c0d800032511050f0740e2400e00b240e2000c4486030017a42214003910030f10f00003d844a000000045c4203030010b0a2910005086901c00b0416403c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 124028363 1250 124027113 124027129
    0x2010c12090f0801020408070605030c0c06070509040e010504050d080c0c031305180f13081209100b01110a060f0209060c03130b070b06040e010227150a120209040b 72
    0x600400300d003100400b008060510311800c4007501c000c400950800d0b1070907544a90705e01c0700380a0142405008400906501814010707110341080381c00c1102c6090406150140995000d103018601030f90074102420544041400b4443c0a039a004005007480e01e07000c00100c80c5010041e0540642c00800c000c0c24580e9041000078003031824001803441d24452a03d07040040700011501510040911482007161026402e540360f5805840c2207098206590741d0721f050302062044a083c0d00e00440b00e102448004140022030301101440440c0c10054003481c18010760b00c0030381c0c1c00040e81e001c2e4808140c40c00020300c1c540020440c440324010140c10036180d035001540f00d401050312210300381e00100c0c0c950102c00400182100402080181500d41081a210f070300c070084d00204500d0049489030100c80c3e110b4800d5044900c49048400c9030729611004520703685080c680b81d200340d0b2042c250358a41c011111160f00403552065910b03290a1864194038075000082e410046865a0113552a80d0344042e94984c011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 124029613 1250 124028363 124028393
    0x601180905090c0306090304180204090f290a03062406050307020d080f04020f0d02040203072d08070c031106040303020307030f0509070b070f210f02010203040f0f02010c 75
    0x100401c0c079103001c9090324604400000039600c81d034420000d02001c11804821038082e02d52500005c007649200800030b00192103141d0121010703c2c0b038003c0500b01b02d1000d5000c0c041c0c40090841c044000040040c0c40500d0304074280110707901c841180c104000107600e42d0301c41c1000546030743c10300e05503190345401d5840c0c812596000e000410300020070410000c0d41071200084524507070a001d0020300b4091f104005810000340000c2c007a051843c10460565500600200810fa00820542d601e15120300007d01100340d10b070840f03400651184503043c04a01080307400300240c0c5984d8696080381d40e8440708551a001c030002c19030034001c45401400960343c1c140105445035000303840240e56810207441c01022030361559180e100c0940740c503041c07048803030b40495500304607500e00410503152106c03402d10500009052100030702200c0f14140c9003890710081645440c3c00380070350719042210012080180c0c24ad01c41203030010100e0004808500c00101541e280c41410381c010315140030300200c00d40c3c45483c80e90a900d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 124030863 1250 124029613 124029629
    0x10c0606120b0c0406090b0f1c0606021504050613020d05010c030b011101050403020c13020f03010909060e030339120a1503021509010525051005040b0609060118 71
    0x600140e041c4403152292540080010340d0f600e00d014039041000703025425500400d8411b80c000144854040107800503a1101c140a031001004014400b9644004200c140f2650025006502c41609000400903a140c4580d400401502070343e65003001c20040310b81101c00072270344140c3c0d03800c03501c010030424896001c1c01000c58400050b03440458001406044800c3d8030009945e041104200020b035010541c1c82c41d4030416640580134184444540d0301034021801c1c204560342012000141c0c900e000e4000094080c05200100071448034070711741c1501d0b0708c01104d07040000b084003080e00407440e05101c1200040c000701e210403441502c82650300c03450760780080313881d001c032070610b000744080d180303103842101c245064000d41910713154030b140e001c06c5003154010200c0500c0a800301d003006c5264002c80458009414031200281d0a0f40c0d40c2e0040c0711310741c542060545440c45881c1541b43ca101680c480d45010f1500100c50207081d51707aa03000c11402d140300500003410003d00000c0001e070142080e1202000d00600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 124032113 1250 124030863 124030889
    0x190b03060a09020301031e08040911032a0313030203090406030f0215160803060a120c0603050a0603021e03010f0204090e061303050a0c030905210606041415010c0606 73
    0x400200301800009030008110342e44104010000038003085240450700c810176840580380200c50906d580d290040745e104541c00707800c00f219841001001c100440c484c80072220442400c90001e0080209201c0160010748090ba0410103e00101c00c45401010054400d104407440d003500b00000c10141e5000e907101321074038a920b4582104600c1c000702c0724002900701a0840d41001d03012454142d281d068420003801501c0b000011411540f100981040136160785025954060200d1070400301940a902c01c0300002480d02c0c01140d02c20a0600600c81203940081aa0310120707448030840f15034102c04620b040e45991703142182d148000c1c550002c1c000518a800c00020711113200c0395030307070f060800081003c401da814200090000a411009541c91852240b07071100200e00035180a0f0784405442e0002c3e07602880c0700c1da18207140c60354804501c41880d240800d07070303082d07031198000c0c03100f80c40e0442c0c00003250109040c00600e14035080100d0a031003000501d00701c81c5006c4c0c039490320405c40d00d50340c0100d400e240d10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 124033363 1250 124032113 124032121
    0x21204020f030d0e01030905071221090302030703030809100c05300a020a12050a150611060106050c07030f0b100f0806040f06020702030d080601020d0203070c14190b03 74
    0x30041e0035000408040d0050141c9000704a0000c081d8400d101007203050507941c1c1001d40600204000300000f0740900383e429400c11480382400607250740400e118021545200740215402e030310408211085950107001068a24219501900ca4181c001c020b0403591048400b82480c8488602607210071012179110507030364a10380989500354003500d04603080c40c040c13010704040f0014000c44582d540425040380044c1c48222805080703514018400b2000003076400d010a2218900c119402070807202d9600701040c40041c0c1d191820f5980041e0680c0307440c5180c006100401425004030010464864040207850349036490303540300b070f5400080c81c40c1590200c1410082100c040011044c0c08041c00c10300700c0c5046200d00e40140e90b40c0d1620010802008a40d541401c07904200290701524a020b40c01002e5421011080350010803150048859a0060ac00d585060350287c1c00070046a5103036400642c10400f450920b0120140c0e100301146160b08072000c941810a1003008007060005000300e0720a032580c80c20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 124034613 1250 124033363 124033369
    0xc030b010602011a0f060717120106090b0d05040309080f06041101020a0c15050f03130203010506150d11040506030103120311250212010204081014150603100902120402 74
    0x20058018000790782c5044029100c080320407940d13040000c411035443e481c051100d00810198000c500005100c2500e00d14091084480c1002500301c000041c15011031980e42c4520403510402c091007400807c4004000c44c2612170b00c90b41010f90b03c40d02038100f5591590b030780d990340d40c5065894207034410540c11403070500c41004040d80d10b8400130a42440141658506600c43c1c01030707184144103201008070b909021140c4035001d80160b03043c20804031b2010780c40b441d212420103441007821400b01e109500e0038001980a1814125070f80307540880101450034110120000c0001700809a0b00782c0900d44213000c00075565444000031070207940704442d2000032018503d800340c244d641c10b03801da0102980034084d4030300030318400c00c40c00d92080d0b5281e18442c3c80300e200d0020400071900c4c201d901c40c60354000900412807450000e800018400340f40c00410051a0309c98452151400c103441031300711099400b00a2217a0b103040300103141c100305100070041e03a003503441c3c50840032a8401401d1030142c52005040000354030b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 124035863 1250 124034613 124034633
    0x312130801050f0612010605030703030c050105130b060d060204030803090304051c120f0c061a0109170d27140f04091112010f020408060f0c16020d080c06040c03 71
    0x4000c0024805401e1000600480b610b006151500841d00740c1c402c0800c8190940081008041c06816149440d0304c07428001d110800c1d00400303580940c00d15002c5100f004410060700c0b0705981015208846880e80c004100c500c0d00d034441d040c0c0741a50217000100200b88100c0c011805070070340c900119a03840c600428403400b10030000f04100c0f40c5030b03c0303040d10700400e00011240d6007900baa440e2004180c5040710040d00c40702c1d00000c02038422480d10503200402c41600e503207021180400d80b1401c21055803980000d4444184000179500d6421481840741010f00809107002d088218099059030010b922800d6614001c440d40881d600f02682003000c0c42a0410030940921010295024000d01d03203552a81c54403c1c00021009000e541c170010030064040c02035002074030885800000f50344e00d51b07441800c1030392503030f00f6a03100c00d0b100b88032000f007408200b0710800c8078082100e00c83c1c5d01141d081103408211241e80c03464010b44140703808000704086c2c50400c0c040c441c4120b104802000d8400e045080410900c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 124037113 1250 124035863 124035869
    0xc032101030506100303121503120305090c150d0507020a0b040521090102060f040219060503010807050d0302100c090314030a0206400516150504030c23031213 70
    0x44d21042d2060001c6640700803e0840080c17581408030702071001140065810081e0761029000d440a90300e5408500d0307150300417900074801c8a04607100500ea1074104045001d00c1400381003040c3d41003140d04081000d507000700b40c0c8011a40151020030902e5203610503004802c0300c040b2401d40010b009540d10b084080142c900c0014107884280c108060b000005c3d6540101074420700700c02600200007011950350b0740143c02d080b030196001c0146540e0ba182c0141440c0c20a02070780500d800355050204c3c1ca8180104420f41c1a901680105602003001039020014204005890f0401c4444800403010494410300200300c600308038000c0d40d40703450100700242400805005401c4641c203c1c0c0e040034400048410f034807200b6030720100100b801180c003180d15503858550400203009000f14000c0c2d101000c1c05640020450b918254811196516404105c8103441180030043c080e40c1843c806002d0300c4070a01c400003480c00402c0c00c0b01c00c154020f400181c50034240d00303041207000d0390011340b001010200450f15001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 124038363 1250 124037113 124037131
    0x70f0605070b010e100302031603031403060d170d18060c03050c0307052503020c01080c1e0a30060e061e03150106020703060e150604020c032101030506 67
    0x104015580c2e8056801c5041c070805011105100105c0c140d26500e040d0000210790045c2250748030103c050460005508511090340405c40c3d1000e105a4602c4010840e441018000c0120000c681c1070b40d200401780c0d9120341c100e50860b500380300020000e00e140c0f00361100f0a240c44c00e6000c0c0317021070385040c80581e401c1012407002c042c10712007441001c062101c1526003080e05403c00b1500d480203054685560088442ca04403125401c41c2003400f03241d00420720103140202a81c500080b940d40d1811034805226030340390300341d180e5080035900c501705003550003404034100107142070041c4500c0c00130f507603051140f10f1380d00c1d500c0b48421100c200740300103040c41840000e01302c14a1b01e11061801d08000b4459140014014400d03082c1c0d00e039040003e540a1195000d1000391094010072541c55410007076461001c0d02003110001c1c40c1071794500c121040000c0842c4149191a48001641c0e562800d01c07029400c01c0c08640e09d684401e001c40080c40c1c0000c03000000c01c950f0a01024043e40c51802d04910b407103070141c01070744 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 124039613 1250 124038363 124038367
    0x100528020703150903120506010c020612010608071704020118031a0a05010602070303080c030601090f0e07031125080d0204080a050d0c0312110702060c031209010c050a0309140609070f0605 83
    0x4002030300400d46e524035001102000450713545150051b52003184a810007540103000003100b0100c0c58061074401c0c1030707480a60301c0c000c0740e550f001d0050301d84104920910a10025110010300190711400c408401d0410740491042d2403981c940c0c42804200ba126900d0001d00c02d480108880a807480c13080b01c0c01883c082c030041030300034515100075004440c040c0039078034a8000000007580c16401500c00300c009080f21031429903d550b449410700300d0000c1c10394503140064104580f120340e015225050750544002e803480704011412460418041040088044400c404103200000010708288050001003000700040c4c640300d1410300e005030408002407040000d005090304440042540f100342e44407803020404e000a507100300c0c0c414688240c010f058000358408000a40700a40180100103410f200c4c10f483c03252036454445070b0710319007070385c0000500354001354090016401b2588071360894146039000360181c90800c02416403281c1003800c2125108003560200704208100000d5402020060041c0e00e4094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 124040863 1250 124039613 124039631
    0x30403020307051b0d140c10120b0a050618040906061205070902030705031611010606170a0b01020c1c06050408040312030b01092d141305040210052802070315 70
    0x2e0000c030b01d945400b6190208203050030500343c900b0887c500c00000010315804003d11005001030040c002102c00d90402814185000c005041601c03072881690001026a810038807905209054032802e81c01d0141d12584864007000407a81c1c0e41f040714090310101c0b0444c85c84030441d040c86858035000340e029003440d40c4100300300600d5944c40702c02c2c1d940060700f81d0305003021800c42540c110b40030301c440800c180d295441d052002807000c0c2c1100305c4500310035000e070811203142d5500060404031000300c5085400350308a150310414619040200110140c120a01201c0e0a14103131544000c82e4002c03a8211340000340050705105010f040341c5030701012169490240f1004000200007001c007011842182642c00680141003403125201d40b074558008000100480f269945041c4441c90b82c0c03414403554010795981541c2140e0724858086c60f4401c42e000740508209140180d001c40c1c00340c0c003844880810040003a5000206d0314a100010210010340c1d00500701d490460500c8500054810b503007019092800c4145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 124042113 1250 124040863 124040869
    0x160c090b06030405031b12130f06170403140f03040605090105060603010f0308031003240b040e250b04030302011e0506011205090304080d0c0c050105131a0906030403020307051b 78
    0x341d100d06c024004810407000d007051810702e0701c82c0002a008407804c000c0360228100d43c1040103042110004a054013045980e502e080d2052116000030710071401100c0000b601080c040c1d844040040b07a0303c5a014076040e000101d200e8144c1081c1c80490300c072521582071000480f002d01a003600100c04495040c07565240102c41855040540300041c071242c404800544080c9407004054001d503005008910301181410a5070390060001200b030b2a900c0ca001c0f034100d02400c040c40f40d0304065008000822895247c415031840c0e640004144240070080c3e030202145000c010406040214032a400205480824002e901c2401040a2401100601d00020824145e0307111203509084444c1e80070000389038a99410207400d500c1542c212403ca84100c14456040c654031802036582603006040d80e241d80340c0c43e036004441c01d02c524480704241d0351070141e09018480032207501c00a11007401c0743d000c0c9401e2402c7c1c01320712aa00101c03000e9015820104901c07040c001d040c031070301d00e07080410782203400d0410b440000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 124043363 1250 124042113 124042117
    0xc010204081615110a0204020714070f0807050f03010608070e0a0608010902010c02010c111f091d04150e1603060c0903030f0c06180c060908010e0d0c08160c090b0603040503 76
    0x1241c810000d01c00b01c600c4182c4805d1041840640d0050019907444510b4149000e96045041e11030607a40f05003580010703a055081d0545056864483c080e0400918140400100170340707607540f141e41035589100c0002c44440401c01da0004260494803c115481c200580f50202c4e05140e01895459040101500050383c0c0422000c680710760908002c40c071801a41824100c616017401c074290000c0038480c1c1c40312940c4d21191440d90341c1c0000d580d1000080d4803088000d08114807a00c901402c504014003060002c1c05d0000c4401c24005403070800a02004091070003407900509412800e02d200010f5820300038008507003d90f10120b88a401c044000350300d07654000300100424000300080142003da1402001079540100f020301c1002e504003840007042d414000c81c9603449201c1d03c400b003880d02400042411040c050384850001070400340036240085001603a5424850600700c2e00080100800a1052a444444682c1d1405100e80400c1c060900c00200b04031412200f000b0720800e018002c00c0001400041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 124044613 1250 124043363 124043399
    0x816020a02060a03021b0c0f0d020f150c01290405100306050901090602040b0909090f03040902071110170a090b011226030405010501061103031612020c0102040816 72
    0x5030340b030f645281501d0110024000c1050b5a202c0300140e03444640300040000c0c41c84004101292242c150030070130010441c2400320a00029007141d129020002e00b0720b81a00703908055031071400030318a0100000011800c4440c00308020b001d84c0710111402b0303005465035040142c0402c060320b0401841c100115000b968424030b1000500f441d807030341d0003da16140290030441440341e0184096403030b55141d605002040e0041143c040c0210f0304500042d119a90024805c1c2c01441c40e24095860241050402c0e00a54861241034612030340342c103082c200300d4482c814041150001a96021003140041030381100c0e00c1d0300507240e002c1d036074180305003a030101d690745a80e03a04443c200031680410003290f242140a2034015980c40050300301d403040c0768656076640c0700154032a51090f00200442d80c3c8a82d010368002112081d030401c164800e0002992220580b85a40c0098010781484108603403d04c9048040c2e0384070303045e5004ea0765001f143c10402140204000d04001d070310f48000f140032600708001410480440301c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 124045863 1250 124044613 124044619
    0x190609050909030d110f0c010617030406050a2706020303100b033303060403170a02120a02070201030b0307180501051f050310030b10061709030d0b0f030a0606060816020a02 76
    0x220301c130381503402000440311071086d54090680c0751070b424500107001b0810380c03107007406845d03152071101d00c0c4501c00310446065a0041d201c031401c0003940002140d6003003210b0303048041c0040b0001141d813942d5090072580002c1041c0e0380110360300d24001c103418045c41d1803a4803040d4001d00130301c1407155000c85041c4203542c0c803055002c210414240181e00300400d40c1d03c034180b03c0c1c0600030307401407100f0b0644c0600900f4400908515204c065144c40c410300049200300c05050810039104008115004602e80081205500501d0041044041000064285504c95112200e500b100d1000e8041e110000c1c000d0900402e8111101006410055400503840d60ba03150ba0600700940000015001b1480c0e034801c1d400317190842603101081c5004800700c0111049402186c0116846060b40c0200b0ba00212071288039102040182d801e00d03442107041c1015007803031292241d101030f10801c070042a490406c44001036a00901002c5002c46c40e1250242074102c0250000440800410300720044580004441e00b03600c1c2e0507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 124047113 1250 124045863 124045871
    0x1009030906140d06060507050d020a03080106030509100f0b0307060c0c050d050f0607020706030608010209011e0210020d050a05160903170403050312060f01030b13020307030b190609050909030d 85
    0x19442d400003d102c0c064035800340f20b280c400d0124925900401401c01984114111a4a0700c6000401d03a5a43d42e844401400234041800600910b8171a0b0070007038100c0d210700c0c125004000544405c405072a503d002c2e039401c3c559100c0442d00315103010441f0800414031810584064510790700e40000e50035860181034010a90220300c8402c0000410001c1e0300086841c0036a440350502143c0203403101904d1240b100002d04004c00841c4600c41071084841a11050312014000080b0118024410b526000343d28294015400c951036042d1903800200340f2060861400122450030843c00c8049603000703041b8044044a81da41051450f40150682c41529004500d0315202c0c442c1540820041c41190002031680c0004101a00c10700400c1c0110390140608541014040c00424011401c503044d01d521550306c00c2c1182a4159a103c80e54020350700411140360204032590a00085420490a0450240548a580c00402070700b036014842c2c2c00070700800c40b4411158201580c409980c0c4c0240d070802c00490b80d43d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 124048363 1250 124047113 124047137
    0x140a020307120f02011b210b1c0203070b0a0c0305092707080108030a09030206070213060e04150212041e0b0c0405043c020904021b1009030906 63
    0x20030075108050381c04128070b0071591503040001d214598840c51500036600740324040003c100010101c81d1402079540d20360000b091841c440005d5203042e54900194140d40d0b00c4070401c02d844034488541460101ca04828a502c00c9205161030100c0d90750002d94541804d0102074441903101d014402c10306c0d007502d0b2070741c0c0b01d0443d200065411014107a4040c1d10b24034190082c108a80c4180d40d0310301c178003038507101d02d0810780c3e03540c200945030f1040350064000620a003609000615014000e000c1081c0043c00c003502d074200c50b4000e00700b100d00d5500003880151003c0c0801c41000003000c07000e82c0c00341c4060710170341c102024503a03040d011440c0030348018681846800e1503500030313070724812186a440c0c101c840341e0040d0402c1124900564410f00840d80154108160112000920101c00c9040005610300b10494120701c480320510080b12001d4101185e0200242c0314955114005048400d440c01c8444d102c8405d45844186424100060071755501d051100e4080825000000b1104941c2c403030804c5003030444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 124049613 1250 124048363 124048367
    0x905060d06050603040b041a15041e151502150103022707050a02010b0312030414120708041d090706030c02010b041503022e03090c0312020c0405010510140a 69
    0x201c0340c000756008100881000b00380301526042c1c138019800743e020609a900b55000c00c140302c400450b4a030b200394610030400412401e05501240007460610380d01d0034211050a005011303517081b112040c0381d2010301c4d5410302c0101901200d500b1003241c83d000074814001e5868018254100510029108150078079140c0d81c055545003000042c03060400341c1c061a454420000f41950f040700380000c0c010b62038039541301064100007076880805c2814006907803d6544996445421481442c6c80d0100307801100180e0151240920282c0030083c482c2560540303440c05d00c544040010303454821444c4465003442800552000410341c001600c14900c0e02164400c801642640901088425690882e01c1c058010100701241e08054060b00d108440030780c810000c0740c03c41741c070fa40d01c2c0c041c008401101c03191089603c14040e500c0100c2d4184607844060689030740f5181d40c80001c0014030200007580110382180b24924041c07140c2805480c0840303449080e080860f17801004c40c448131106074241d100000d946841d540c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 124050863 1250 124049613 124049621
    0x3031109090a0510090b0f0603090f0d09060210060303050a08040203030f071a0c07150c0e090408030702010c030e030a05070212120705010b01020105010e0610091502030403050c0604060905060d 85
    0x320001d00200080e05203440040000c220440c1c50742d00c40914010085000001030260038401000242025000c4402200300092540041c00300c1055101c1c144c6417446008040c4091500c0414545038908443d107082030290a1201c0028034104152500e00b003800000e40200a40390b032071100d441c1404590341c030b9101081c80c500c284c9451080d1804041000c2040240c000720030280e81c100c0f21843c40c031176100c01070350010b18002c0c0040208030030900c0c4180507040d0b800364040440b01450345018800e944c0d0f83d0001c1980c514040d01e0030f4411400000030407014503024060050f400301d00389010071601f030301c100446489019038605d0a04000b80001c0348801d40d66443ea03560003440f43c0c40e01f40c801071010300361181002d80c84460b04584650801a01000d258018400d45040f0360014860003240d85d11242013110705d0000640307103001d00040300c0380410104440001e1100d19461030700150b6503142503050141c1380c1300d85510198440c0d00200302c14854954810031400c1121816658551512568035a02010b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 124052113 1250 124050863 124050877
    0xf11010e03130311040504031713080f0c1905030406030c0207080304060302040e010b0304020a0603020904020d0f0e1203011508070908190b0c0c37080304031e0903030311 75
    0xd10020655042c0c40100004202c11284911078984141000c6400c0c4000e64004490140100d0324a04141c3c0b0141588528280d0044442e0950300d103554103a038407007046c0e03040700f40c0300051003c011030030003c050000c010288038a040301e414243c0d490702c195119030f600d1282c0d00410082613154594610441d008220380e5001d0701d000c100f5681c85a44461000300290494484e0106441090340001070044204c3d0480f80259005804145140c3c01c10307005034043d50021848541141d4200700d205407042041c42008061402c1e00c801045503141c08801c40c0c45e000c2d0b24110f0781c508d203204200400c1100d404404e40320880000b404c8c100342c41da403001c0b401e5420b49200e5110858501030100c9002d03000c001402ca40003160b100301030440c07242d01c81c40d503013038154061510300e61055440064007240c1c0f00c41051082d9107080044002143c01090440c0380221000151011034581d040801030000b0035801c840c1000c0400d103564a00e154044888200400e205c0840c4001f500349940c03054038409010080d8219510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 124053363 1250 124052113 124052141
    0x91428021305030f100c051305041109180a0e0f1e15100513060605070f06060b130905060103020307080411130e030c1005131e02030f031909060f1101 66
    0x303030b40080d0150b662900e04494040808a28046c3c41490880c00f0780d040d500c51900f140114400c0900780b200b800020049101d4400c04100144055000b540da1440c000940e80244400702c082c03800c2616414003901c081c04940a859080b501d600d800403440060911020310a4140100c00840b00016040c01c00800c012a0161b07440e10b402001110340c081428038085030001e481211061580b005400200c0d04603005120000c0c03c2042528003052600703210a090354080e090021f141c40c0c0c2e80b21941c101c0c0c0c0c001c01c8000341c030741e07124002007110744d145202d0300e5800a400e080c150b1451800c0f000003861880028002051269600c11804050300c40d100301e01810750700c00c103040000300d9808207496503d030807881100503284910074108070000f98500455018144000e1149210004c55495045040c00b032542c8582420340b181c0c0c0400503035010801440d101c0c12110240d03589000721180c07400d07605448842e44091107120282006443d9200d40724488003101807901003042d2494014030340c0540300d01000445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 124054613 1250 124053363 124053373
    0xd050705040303170403050301091a040f140a15030206030a090f0303050118110f07020112050709030c12020105160807020909030307110f0d111609142802130503 71
    0x14099420000600a99001e40c5801c00c45220303540080c00c0360740003210001d00240c001d000420415100c2d41014030300828444681021710344250215003101c2c11100c2e0303920001e885000300e0041400c14440d0342d40050f8022001d00c83e000c1c40c0b12415020310510b2200078003900c0b00000042c9541002d038040c4034426071059504a40410328200140a8942070040ca030400c10081c2c001e014500070340c8500002c4008014203136040480d003195420706078000002c141d042c0a01303100842c015105901ca00b511404490b00d40501e11400e50501a404e160301d07401080304c00603c100a14050303131f005426a0034803000040010441311852510a0f018000e850000350000c3e46030051040406021010310f20454840c0d90358180750804030145641c84900107040012074010701c041d0b4122074440c56407032104080c40c0080790240c40050741001300f0707010305622003d250341c2e0311040b0401c01c2c10003443d40d82c0c10010030017004001180703c614000c000e40f40c0c01031080c1095400203c5403a0500912000c100600c1d005007911 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 124055863 1250 124054613 124054621
    0x30f0408010b0f030f1b1203030405100501081605060a0302040b03070c0b0903181201020408120301051507030818010b0a08161d040807031206060c03020705090112080f0d05 76
    0x180c040d00c0b800d003105208804200030550607080000b20002851040d00040014009102d11450f07008000c02000390424008043c803030201c0010001980113900c5100105030b0790b14440e60140c110703001a0001a060f4000582180b2a042007207011404d80d0000c1391442d60704c5800c0c1d8020f6000b442294080d40c1151404010010510f4104035800302482c010110955982c1d01d15079626140d10a4200b64081900307183c4480070306060840703074000c8100c0c01600040c641603c0701e1100d440d020010081600301400007005003d2810100100602840d00e21545801c00c03485540141c0120030041010340c0c105851001032000480c25007140c014000054181d82c2070940b10001c0c55200c105000400340c0b1040003400000c1c0303c03410301d00241010040381d411210b0640f225500d0100640c0002c4080d07041103865101d2000f80c1e840d40c0b060b48014401c0f40c940541c40300c0c2c14513020b401c0092039840756119000e80001044403141610462003405d5108020698440c07101d042d450700c5000714003034608000d1901c8104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 124057113 1250 124055863 124055879
    0xe07021c030f0b010801050303040b0d15081e010507080705071a090c0901050f0f0d05070f0f06171b0d020705120310090606170402042d0b0405010f0b070203030f04 72
    0x40310302c80d14000240111031003540191010802845401d4040d80104800c000c01602040178264032150b00720f01180003103028140343c1d04c1500c41c0d00010300b50340000d20408990b0190aa0003843d07510190020b1115150569010340f00d4080240602d0a03c80001540390400c00c1c0d0410b0448440c00e241c941d02d940d4280801d10a41e03a80b0001c0c0b005020f284040000b182519080f030401d0080d00b4014121042d072000c6009000c9017a04d0b0780003c44203482501804120000034900000190010394103550540b807a262004000742d54440c07907034090f09416014044902c0c404541d003003400c18554102556400a080304400070321900c8030180c00c0740030300e0244101d460368000c015805810f1301d0b03010304003007602d88489104446d1079100d07213004500610201000002440e03212036000e4001403000030020883c60f00c1c44c428410303081541480955440e0040c0d096601440b92038050207043d5410809581401e80c14020b401c2e06010b55407003002c000c40c3c4141150380030412540e4409040903100e80322941c51003c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 124058363 1250 124057113 124057121
    0x31a10020705040b0a0e01030f1e03020303040b060108060a1a0d0501080601090b151c11070303050708070c030507080c010b0d031205010902070f0620070b0a05130c0e07021c03 77
    0x1c19100c3d07810030a0711010b519021010000f610b00801000907180d00c0c60b690848000c2c5d101070121901034500c12881190424071103518203090086e00607540c0c80c0f030980b42000006500400c0300c0d062000c2d820901c181503c1d00a1803000752001c0030300c0386003807c0395243ca0381614041c0c030500d0001d40e81060700204901c1800700b0031a04841d00e4075001d1146801e507a0420a410403426641600740c841031044504907102c400c998044465201c40008510040a001144503440107105a010946403001e000c04c00364071885041c0d0140d100e240c2422002500d0b039004110788280c46002e44502da0100e15185034002c2076100ea404c41ca4020000e0401242c94170340504940c0c0c84055005105190170300005a00586000300c624407540304a00301107152003a500e000080a00c0440c0e84041880c0c011007102140001340201160b5010f4041c0003c2d914181120200341c910041040c2d0300c2041d0b0210a6000401c106107802c180d0790140214403c076503912030120703d0018504602000700300e200c104840b038580c260380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 124059613 1250 124058363 124058369
    0x30207030c060819150509090d092c06030c1804060f020909011203090806180f010b06120405011404140606010905012021122401031a100207 62
    0x30001c00d450360b6500a94240c0011142c00c02a96070782804259800b40d1036000c2c01d0b405070b0401e20314070400e4031500450264034007101c0d0b0304002c2c0d02c410540c282d066004508803005103050120541c02121001502c0c410649407072040e540c5070035030408104241e80510241140080180c0300c14008000b2040214000030183c4060728080d25141e0342a0301440c1d04d000311142144050551165039107003907038408016070040c80550821804460104480a0a01040d4050700c9100c450078446514800c445043c00801030400050740e26003080c40b002a150030303003a1541d5050300000b5050f51b6955041c02d0303015003c1d006100601c0c075035101c100404c01c41039201030f5540c2d000200840d02c0a94038000191035000300383c0505404240e50404017040c00b9084202c94014085610079184c0d404820188c41c012116240001251042c000c260107407000311560314260b01c22840100c0c40a840101c8140e071004861000101c1e0405403154102c14500b028000c0c00c4926800180200540c10f42d200070013500d801c0640 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 124060863 1250 124059613 124059623
    0x3020c12010c020606010813140f010f02030906040803131a071b0218072007060216120f030c05030d050f010602030901081f0308040b040303230910021903020703 71
    0x440c045002032014400c04038922001e40041c20107840d8903005442103e4014042c00350f203034480d904800080c404032540c0070040b0b0001d005000403000c00102c01c0c00d581900700c01007030851040c020008038650028003aa04247c00c1560b09949171140d64400c15448040c01c0080c0c004440e0300d8401100d20710b07241d203951103009255905085081d00580c0140b0182000d030b00a036109442c040121140031240303290a400400314104030300d124180e40066448244c240c554100d0940218408200a640500206107240e010003c601d80031400c4c00444024003000300d00142140b1828401e640401d40102e01c40100150800c0071682c594590740f2044000d170508071040b81c6000f0390080009002d40c0004196802d003441611001c55503078803251302c0e000410580003942c07910007600000201141303581c4001d0000c0c4c0401c1d01e08958981c250700300901084a890481a50400c1103c10b44000d1759080040c1c1e40251800c580c40350280010a4049191261075944100c41450302e0900d4000c06400240002c00c891040d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 124062113 1250 124060863 124060879
    0x3010f090605060306010f02010b0415360c021006030b04050d0807020d1101090209070203070501050c07120806010315120b060f0d0201082e0918110607030903050a03020c 75
    0x5001080607160035109540c1c201c10240085640d030b40c0600d2411503000702d14400050300380c0d00d05c4000b800351040c800190380c1c055494141400005201003034240002540316490860034180400c00c80542030305c1e2040044681c0c0d0b02c1d00818254400e00400b178208400d120b05100c0140c69003403100540d030042e42c0c121480e10a4a444d840d955000b0f070281441100f16030003803e90302ca00048269500e501a00d54096503550710420303240141d032404039580c00303844168000c503140e1442d4030b4410b00315040a0710310300d1444000d21010b030004042122242c01c544c1c90f49007256031a180c2000607005060020310503024403010032804a0030b48070500e011428580500b402c061103132202400d0019442e501d08203a604241c04610510141d4041c0c044103402505c0710a2100d0b0080c826400780c1464400005d0490841424540801105003180500d070504201002440183ca1050b982d41d20120048200703103000d840003244100a240c010001c500c0159000760070f44c2c1d00c020962400030744416a000c9101d10880039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 124063363 1250 124062113 124062119
    0x50717010c030603080313020312070b10080a020609130f0603060b0f04060e04060b010507150c111603030311040506041719080703030f0b040e160b07051e0c0a06020303010f 76
    0xc00c0c091001160b17005036450b0701d5030f1650100c81220a440d004140d0f01803103015010806480c0850007004414016403c180684c00c11445080c1034030740710382c0540d20507800340103148050307524581260500c0d071013190b01c4c5009148840d5000060240c804081805d02c0c074100c1c0000501c561908040d007890b504407282c11280009900700011508a401103804100d00c00d4001400240c840d817021480c1c900504085050038102d83d600e62200031031101194146446a041d0780007590841440750f000801c3c2c0e8080c00300c075032140781c0c50414a801880060100358a42014030440c003111022200641005440a40d440b5211455001c41102050010310383d071041481961900c0303900d81c9221680c1c0e41c440c000740d240075106e440481c05020400181c400d40c50b59900303005400d6950f440b6004420b404e0001070a040b24070300c504503140c490550320610311920108614000100082500b91080c0d1341566492210201c0c0440189400040c607440c64005407810b5000c11680d03000030107141240c003100c1040030784c81d803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 124064613 1250 124063363 124063367
    0x160f050d080a0507090b040b07020a0b2209090803060f1507030503250c081821010e0606060409050c0d02030c0d11070305030a09031403190f050603060412030603050717010c 76
    0x5c0da034800c40703190003010710040c4408034407c03000344000c80c00100b04951142e05c481140500d070744a25a02c4810303007040c1d03980d0419038403102d8268000348100344080008103d00d44071f0b0407042c0f000074881031261a00c010810503070f9541c800000301e80050242100d440c0c04c541d14010f4081d600c195031031420508451003850310400c444e00c03180800101c99403494440c0d14142da80c0e50150308048085c2c403000f4060881d42c82a40c0700e81840d146841040020454600c000c0f035004c900b1100704456410b140d400030410443c0d02e80701c0740d04441c21a0b500400000340d51b504c40b07800740980d00540c000c40e542c03d40000188640080035102510140c00402400c00100c0202664800c5d14460b03448010080b400600004403a0760055000503801e40c080c1c240748680c00400700926499920450790600300800c0c600041000e4169071242c11000022400304000b40c0c03d01b1000282e45d4440200005c0000342102c20001b20107120707070803031130003140e1000884003e1602c03107640030312401d03d010784201c5075840d090145004034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 124065863 1250 124064613 124064627
    0x150513030801140d02060307140a090e10241b0825050d110a0203150718082808120f0603150a020309030c0312101703160f050d080a0507 60
    0x280300070000404200b0b02e5003440346d81e4000601d000184900d050103907041d04002401012120070a0780c0340b071129420183e10785540032024090065982e5524420300035a08200c4580054010201c901c844c003644400044440083c8c110302070501665a03c072040410196501501e0840c100c8445881a614160f010b485c61a490310000780c00b9500c00303030a2490403401280c0072106a556502a95640702117038022a1030701c81a003441600a00404003003115040d40110711407464010091201c8009207041c0784242d4900301c0001c1c00b00b202ca541c030002c10940da01c13a01c5900c11603a000c0402521401c40e00200c00624100300c07590f64514951000040f0545008079a4910700d006641007201540c540750501c600070342008040603920b200810010108100410103010580c01c202441c03101440c0030b541c04a0b290296600400054150700205003405e00b0120a2303600301102c1c400014074411550a00d2801e07521380000141c10350155084541c00e203a0320442e820711401d12000180060785406c1000c0314a9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 124067113 1250 124065863 124065899
    0x2070c0308120612101526070b0a0504051306051804020310090807030c050c03030d0f0b0a080d12090b04050d030e1b090a06030506070c03030b0102010203011a07150513030801 77
    0x1a800c001c02c440746004003030b81700c140341b01d88101c0750200b802e0f2038115201e1060064003880a000300f01000d14610900104114006010b03989170041c01c018401c4405407042c080c40c0101071188a24194000b1213000c0ca511280081000034040e424049554404018150082e034050b8000d0060b4006944009514000d43c1c40c41648985c400f1b01c0e080c1152801c071102161200d0850f02e038090303010411410341c0d0401c00740c12070b000ea4200005004810000b5401111101c581081c054000701404110305000401d07007541040300c0f4140f41c40c07440c00c0f00650b1402005e01c4d0380000c0801100b0010300092060000d8180d0074503480b030f14200522200e1000d101d540e100f4600c0c00d4241881440404461810310904554025046140100b20f2a407240e8035941800422039800e40096506074a510605505d406081d44e00e0400380000c519550400340000900b650b84007900c0191903001403810200900c0c0c3c00780d0404040011020080360608080c0340090303503200042500000d00200002c504a400d000300030f282 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 124068363 1250 124067113 124067149
    0x21e1c090f300302090f09070f05130f0b03070216050915031f051b03010f090b13050a061403030c03040501141b030706050c18040f02070c03081206 65
    0x1112199664601002c1c46400d0344100180100c103801e8005003540002154400c0e0340d240582c89440c4a01440074242c601d0142c54801c06124090150540e04458a180340d01c80510300709a43d4103140e00b03009000d11040d0700c0307503010402409000070f00c039950802841c003603a40c0d90b00707440120915a08a2203901e000d03005581d8000d4071080468078003a110030521a8000014040c2c0d00540d091010081a03580d80445070041c640c0c0ba80300300100c02d00c0c407401f05107070003010040c6c090555052182c600861007079402600002d50342c52940e5940c903518050070f540c0b4400600028403807480e000b00c0b450701511443c8122020070f542c1d0a40e01d00e5a04d0080705440101e001c01e4011400d203440e01004481c107401480c0700006120782041041e0040c45620103807074a040780400255660080c40c034083e0704035413008003910840c040c00d10100550410001140b807140d00214ad011074840c0c8200090802849081c000070100010b801c1c00004001c4404040d1000c1c0308180c030a61243d682c4c40d0248040d4150345590101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 124069613 1250 124068363 124068383
    0x60f1e02070501080a0b0405040b09010b010c03021506062a0615011d0a03020a090606180303020d111c080105120105090a150b0405070302030907060e0a090f021e1c09 73
    0xc15544a00004c3da4000302900c0045520041030340402d04544d81036401755120140a020007103013120074003071151a0034082c40c0c07100b1200c000b61802900c9004407910010018500b001054403176a17100251100d402c030800c0ca018003915410b10240c075001c103122034040709007d80700000d03034100c03210b4040b000722400c1078442d0900038000c20911036401f1504030f100355001c50400c0c4080b015071034240c1c0f00d6000d0060608005556410200d014001800c0d42241c11030b1135021107424030010b0350100e0218544a11414802403c654501c5640d0400c015804001c0c032040219221450007903002d940f4904032034081c0d46009504c00368455143c00d0341c0046490101540c0001102000282d01070b260002440c0408400240c05003510005400c2c1c81d016100200081c1e00401405a014000e100c007a00801050900c40740046031030300030490040d0b2a02c10220144d41c0c2e903048080e05400c980403a0101c090701803003010300300105204c14040380c1010481c021003040511a00029000d07074403400010b02d401113604c0c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 124070863 1250 124069613 124069619
    0x50301260115030b04030e0604260c03010e0a150606050a080403030207020915010809010504020a1707080601060908070608010b0d02160b18010b010c080304080919060f1e0207 77
    0x35401a8140e45608040d0b6807030035900a406804280c050166108500c94100c5050a04000382040000b000c213611900c000c0100b00151000c00d442e10750031102a00c0c0c108000c0f91004085403d000e012000d540e019403e000304181102804541012161712602c407201c1649524030341da1080384d011740180c03c0032810811884110710302510710107034858402d00c0c02501d4000e0550120740219400d450045503000d120607a9840c81d038114190070b07404907205000b000240b5040d00040d58800b000e2041c150010288a606103e0b02800d00000000c0c0040300c003120025696641c0003402d00d0228841c011090044140100d110352280b44c40c10704030f42c0c08030348250910141d04500c00080d8080c11480c01000840121440000c800c5480c280c4140081d50350640205005000c850940303450b9842e25040080c0c03d400d000000741b20b9000e42e90880c0d0024065603d40342d0240119103c849580c04c40300300ea0308442c1b000a03105030700c02914102c842c0c0380c0e0303070f103410310318528141e01c3c10709181c0300050015030441d41041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 124072113 1250 124070863 124070909
    0xa05070302311d161a0f040e01050f100c11040e1e1002070308130f0803010335120408040902040b09100f05030a0203040804150807030507050301 64
    0x414004545010403014901e40108115140300810070a102441d444418248281c0c1200d0754250240b0740f018098240350b5828443c40400c0c0c10f4030300a205208004404420004580d402900d01c032030800394a803907640e0303121521490243c1091140911440303051442105a04007007001c02000101070300c80302c0d04001c481e80c23070398948100f400046402541e2241407160fa050304000000d0141c0011030600c00c001c40f511584c9040c1a40c100c02990002d00401180000aa10804144d13105044606a00740306201e4903256003d170300306280c050305001010002005004002100d408c0d200481d4043c09404494262a4001010a0880c005001e01c0500104071038017504124a64001c0c4219000c1c0e2805881e4080703941280c02a400400c0c80040210304c1209500f441d40314407a503504079082c030fa0800c02c40c041c4010442e10008100000b09074021010070100002c1100781c60150501c1d4031401c0c04190042d1000700001004c40b5400c0c0000d0802d0041001c0c079004008403170689140b070800d034404035620026 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 124073363 1250 124072113 124072129
    0x609030304090b030a08041202010806010305150d210503010e060d020906010f0e090129032502070302060f1801080411060c07030f0506070f02010203010501020304090e100f0b01020f0a05070302 85
    0xc3d81e0140500c1e074820002480d5100108082d02501070341c00301401c03003400010003140d8001c0200d41898a04000e02804d182480c5090114010840382c01da100b0483c0d02d400703030f075211703084088a0f0030f006402694040941c2100145050310394101074512079540d00d00410503940182c15002e07410202c0c11000c15050351060b60052000c100794100080b9024440000c40c0241a00f40e016031035440d80c0102101102400280c00300223190800d0030f207410b50a0503207a0807441c602c0c1d50a610980010034403e0071605009000d808001d640050407a41c503803540501280760b035480026566402860b55540305055030140c403045014540007140c426095030010113001c001d44c424070301901540f0550300000b000620780002030003918425005083d4a081c040800b40440d000c1e00c944c8070541e4011320052007e640d00005440844030626004100d9039903100b1400c0c1850070307030302e0609a5a42800444568860b1642100034031000a81c00c8414000074440000d0b107034600054000c01e26004a0350400243c034000c12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 124074613 1250 124073363 124073381
    0x30a02070807170405010f030504021804051014010609061805120f0715032702040906060503030307090602070501021506060901090e0a060305010c110607080c0f18030c060903030409 80
    0x1c070040c03604949440c1c41262014040f030038010000c001a05103c107582c0420007200514250505000a0800c3d03030000c1c0140c82210416010102c0c1000090140b00d01044841c2c02b030b418880701007160000ea02341c3d0047c0c81c44240102c03404904a0340c00012100e01c5098003460302c003001da108620041c101010050001c05400c030840580c80740e80d8030003815801c00c0c000714005007665150303107030301684082007d0107a91415071044664920281018410803071500d00424a650442e400a900c00c040e1070f10300f0007815a0381140da018400402000b015030341090b14081a100d0607000c86440c503507110300481c0d0301c207400710030b070325085900402240040c24a800508044001410040311031601c4000240d02c001c2d0443c0c1d15008203440b01d8040050240078070030000c1400541c40d064020311007150090b50f6492000e40004100aa07050015080403005000d075843c8980e20700d4480d589180d040e0170284802c08600034240300e802081400740540c5418401c89044800180141d03041c5441c1c400e500001b090240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 124075863 1250 124074613 124074623
    0xc010c05031b1e01050402040509011415010203130e07021c0504030305090a09020a0513060503060907120e03030108010f0f0b150c0109170d0e0a03080114010e06030109021b0a0305030a0207 83
    0xb81034040b180503c807426003140390fa8500005403a03c0c1c00d00401c4103a54003d011140301c1d0f4501116011112840e6030b0b070503880400d00c00c030b5424181c0c0c41c01c0100d02d18859100002882048100c0c00b16280d03003e070706668001c2e0f2069080b6500307c0c02c8002140c01c0511035540c10b5012410030013003040040e00400140c407200000504041141380c0d60554102a6444442c035000000c9002501c0010315000c01d1010300501000d250040c154503110307001c01c00030318000c3d0200d001e002c0f5583c00c1c00d4050081e50000a140c0380181d0a8030b8036565104151806400d2070348104081301e0925070078a9004280f4459002100d100400904142c14011440f0540d03038081c8031180419525a00100d001c141440181ca91000040068035035488542060070112449800030265a4000100010102c0c1d440b2056506507202444d05600c01600c08005a40300030f00c107600b554116034080000a00509180d02402c1004040d01512101c5022000f0310b13500e402c4000030050110340144007040e0140d1140d030188c05100c2c401c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 124077113 1250 124075863 124075873
    0x11205060906071b0c0e07080403140a0207030201030b0d02040f02270a0302010818190c060c1a0601230304060506031f02130513060f05040608120a0c0b010e0402030c010c05031b 78
    0x107154a0341402001c47d1784002050350340007401304160340944114081d035284003c44e03003040c18481c4003d4844020b0300c406410183c550408200320380d01e44000d80942c2d940100200001910403804d140030f5000300203544480080e4180e450910f0030346104100415034010b008180d003d08507070054451401c05000501d003160008100c101c071880800a610115501e407911181c1204280340101021000d81c22090822a840044e0f8000038242e00c1aa007c8107400c070301b4840c0e00c0d0b4606004842420b1441c104080b8001900c111203500ca1308940111b00030381c0604c0782441555508424160303100000d054100407030a200818100e107016642c0580364144a071041c503424165588009030600302101240c00a09640b40401c002030702e0389424940040a00361070a001032403801c048291210041080e03d51003143c005903444c0c40a2003007100301c800551240580c849540c407074407951802c02c0301b22412402031040030b00d40c0c16298041e02c460400507030711000442c6000c003554101d1030840c041c903403610218822 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 124078363 1250 124077113 124077119
    0x21005070203060405060402040609020903060624040b0702090702150a020a03060b0c010c08101202010507050a06020c06071209120c0203150c0d0510050d120905030105011205060906071b0c 83
    0x3e00203580110300a10060445041c5801004112900c40d40105c2c4410310400c101500d54030045029503010a08880000782101d034580d0b240e010f80c000b01d2555400840014010030b14008040250511500a50399020582d4440006903901d0f400404401821803503040042d01603690768008207280780d6039240100e0f209581d1164002c242c0c002c40240843c0365102e40070b40702c0b035540c08403c2680c4040d010070740e103800628054111907601e07101907010b410002c0002c4c0c402c0900a04101244009500440855803808004c0c0090f4a907501a01d074800000c041800010300480b441c015202002e8102006400790321401d0001d0701c0041c1c110a01706c1c3c05014403100600c0c02242e183c80c0620400c00000356944d120903a50680cbc0840d81e006140040717001c0d400c00103110f682ca58024410f40d8540c01340b60345154584900d0f00381d46000303250b40400e0317056007080004540c80c1c000c0c60b4542c59143c410012034101b03454050705907032a000100c8a001c000f8544090958648505054080d035103030250040040c081c1d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 124079613 1250 124078363 124078369
    0x140304080304260706080702010b04090209073e0706090b030114010314090c0a06091503020f040f0303170606090904120507020307030b1b070b060603040c050607030e010306080a08070210050702 85
    0x7a056001714080b502c541c0402203200d80a018000c0484400c40d0100070503e003aa0029040c0c1c140a490038080020300920041c600302c2c2080c0141542c240301840c0c0000c00d023001e0220ba244060380e00c02041c01d0280f01400074802c3d025103070040070788076856052800c42e030a05450804842c10220f149042540358401c0460210031070131400e0041c00740b000900741e589010001c0c841140c2c443d40c0314a081000921013080348400003000c02d840d0000c1854050f0340c0e40e5100d802409140101d4020003040510401c0000c209904020f000700385400078808442d02d43e40c1c10042011900402d9545500300480e00700180000d0103072114100d4007102810302c9810030044e6000301e8a0b1280d0380e0001c962214650091040f02240b030850b14812068440019103008420382d11460341c2d240207822a8010031022011070100030445240b10702a020141400703464101c3e901300100724800101846001c645050404981c1d40c0d00494084461070f0480540c600c0d2200e25420b00480b445030340c020340d007000424000140140d0f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 124080863 1250 124079613 124079623
    0x1180f020a180b04120809010207030b09011b050705030702090405010f14090705121519020c0c040e0c0d020108061503070c0b060612010e04020102120d0914030408030426 75
    0x50440c0e441003640c1048201503080c10406400c4100c0c2c000041c4000c1050507408100c8903c5d040e44000d4083c1c40d0101300340187c0c40c020700c0e038200901000b04202000301202e8154020401d803112011001c0c410350302c01e030301503503a44100038000e0b05c160020400c60000d410581e107401c5c1c109104a0000958a40d041e0031441110720340031012192414000c241f05141c0030030814030020b050100c80c0b01c0414651306900c0d50b61054012011450980e41000080c4900c4100c40c40d01c00014421500f517554500065420791540700c5280340512843c540802d1000d01580002c00c610041c201a01000e080c1d401a0010f59160300010003e030307848015006820300c401c005002460207501152200400d4001038500766110b0000180442e014000a0000c40700b000d0000c40d0729130441340400e0031542c140d1540d0004034100024010f104104070000101c12035000c0702540103e014070b001d0035010600c1401088065101d22907486007005540c03003400184201c003001000c0f600052150702c0b06201265680070414104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 124082113 1250 124080863 124080877
    0x20705100e01030501140604050d111305071d10031a06040e01031211060402011209020301090b100801021305010f111c1412071416080d0c090b0301180f02 68
    0x40c038041540180c558140c02031901400044005046a107241004500140160b1044a2245034180c22b400e042c0103020001c1411301c0320240500f0002d030f103e48480c2c00600019a076070000181556060740c0850b0880d5403030680e00c40e0040c1810b00100c055a412405000700c09400902c0d100c1d035180315116507840030000d01c0101800c40d0410100d6255040030342c139588014940c001488180d0703e110160820104080e03600950900344040044080d085010041c01042d00080d0598a4114158248a16100d034140300c1c03510b44840008903a226940c0038240d01510b100514074840c10f02e406d0206600518a402c0c407000c0c5071410150450080d100c4600c0c2a40c1d003500fa6100101440c802038846620404000910103038200c0d1510744941c0c048064040c0100405c01c0c001c0102e0100303145140025001124145d40d103505803a40c0e09006810500e40b140d00180d51860414601200034103010300400d0184120b4203680941d5055a18142c1c0c1a104603a426145c04489a0b56441e1350000c0c188510140c851 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 124083363 1250 124082113 124082117
    0x2130209090a320709120317040309180905010b032404110a091a0f1e06041d011d040c1a070c08030904060902090f0d0f0501050702060a0614100c0302070510 69
    0x2c2414103104c0640560031039004440080704201050700842c0e0012103202c0310b01c9005030b01201c2a50b035420100d80c00300300d50700130441d4210b18048100d039080c003a030440c0c01c005018900810083c1100d0080580d0745c0c1d6028000f0007040d4003000e00305000c00c8100e00150340a4040c44002c0914035a41d00090211100398002030200c5130b583d450440c41d11160001c0c140176400988140300004070407030010380c0629100d40c00c11803e2001418528603521210203480c01040501d80f18180700c0881c0d000c55100c11001d0280c98204080745c158413541c50128446a40559004813242001906010130810f41000607504603208a0041080900280203142c806005002030009141c03140b4000003000261041c5a00000059006102c8950709681e45a554109603e04035050b00c0b50741d8407071820a940a0a8040142165103403004000815402090b0f241c8202c0d21240200049030312074941d0081034850750121343d0407019480c24110040d000e10110b82e5024040c1c01220001991080003802000001900e040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 124084613 1250 124083363 124083461
    0x9090b0307080613200915151801030f060e040b0a02092707030516030f090501060f030b0c130303030203061c1401060807050306060f060c1902130209090a 68
    0x113000c445082c0e02085501440031400180c003540000c4d02c1031b5405032090b243d4042c00c131400d24240d0380740032081c0602010311000c140c40b00c03240038610508041c40b50940f13010a0409014a02900c1c1512441082da0000d03c14000756403176a44422081d150000c0c2400841d50b1300300301c40d90541d5280a504400301d0218201100b2218013844518140000036007204149070034003041c020b29044210104c01011a81d1800140502c403001091003d0105140090300030b51034001d020800d08902d02510080d240138108110311515a041003c04900ca202c085902900c103442c02800000c0c40381c0c0086800400c0100128030f10080140751705800c400c818800c4480008580e603da142007000e004a100a1001c03c0207040664601400b00303454040003403c003445414108550907442e44c4510036991000404d00440309200345140e5210440d903007041040e842541244a01507600006008a440c0d2910240c407515003501c0d0901c600c000341544821010745034101d030a00d44c02c43e1004031038010040c005015060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 124085863 1250 124084613 124084651
    0x10903060e01051008190209060a0506030109020a0f05070305090f0625050d0f140c01020c340501020c04050a060513020d0b0d0302060c07030e060301080d030c050a09090b03070806 79
    0x4941c04d080d90109200307800c404644983d500c2862500c0d030080d034040e00d402220340c2d12075001a190440300e0f00156032140c000700001c50180c0c0740d94080c1c0144215521189882241c480c0e06855501820800074001001003029500b581030500c1d1070214914080c4c0410f050900e0641d0701c03c070344c422049000b60a1114240904107002040246041d034400d00e041100340e031030013400c0047c40c0100185102d210741c00c0c002014000b60100b5411590400001c00544a40050304000c62101000241101c4803614101da01c014144121490710801c5401c1600103042c50301c14503007030002500300101005600d0760384040000e06911030310340c001c032514415007005030303910041c04164040381c6002c040180a03680544507040002d4001803900e03001045900c00c070703403110054542112200d02d0034501c10780107100440001020000000da02e14801050340341842100649442150344e4080c442c0c2c07080020b08011801c101512040e4403100701640d029098400311511050400e181c01e0050311580503c0714910504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 124087113 1250 124085863 124085881
    0x601152714030714060d0b120a0506040c06050a090e091509070513050f0c13150c030807030c050d0e030d060b03010f0e04050309060a0c0b07050c010606050c1506010903060e0105 78
    0x20f41c01030b0a642d1904d510309001440400c2040c0903003006103034240e42c0c90114807800da072180070f2070082c503125100b02c81600c13040d498480d44401003500c0071070398013200540c00b0030a94021390595070203c00395503400d01054688072a00c0940040079010840c82d02603d241290401030114003603200300600c0c001800120724100034040c02c000c4400301c1d03a05403858401446051500c240e4400c0c0c02c80c00584c0c94a843d006521002500e4201c65441781011038102244030f1440d03034001c0703042c090b16406521584400d94580b0000c4d819036244003000e000103070b8100004500c030000d40c0c4c0b0042802c141d4504407030402c15883c501408444513034104c084c4055000c0010000d0403c0b102c1c400307010b08200c03048031416081a81e40c440c2e0b82e01992030f546100d001d0100d08080d440e0b200d001540c07800340d000b518070700c86401c0c80c90000e020703541f0078804403045500309030010841600030400c031100881050b004080f10112548100c070000c401402042c10840e00080000101d5011b024022029143c0070001819003000c50721 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 124088363 1250 124087113 124087123
    0x605010b030108070501020c090a0915020a020106060e03010b030a080a030608011104080d051905030c0c06160813050c0d24060e0f130b0709050d0b0405010608060115271403 76
    0xb017141154044048002c00703443d4000615005002e07500d011840148078902007042414407004144c0140c8040344406029505401c900c00701c0e160303601c5400140741801c06141c08d0b503001c14602505640905400c0d8009001000100f483c1451440d00049442d04d0350b25481c00d43c5e00c088140061882e01107828006504140400002c1c54a1801e11500d40808101c0690509585090300c1c4c1c00e020b401300008110065181c116540440540156101e515002d040c0c038a0400c4211883d000050203240025180a85001c003a400540c1110003420f00081c2e8104004101d40110003c8441d10b00301c104d158100301880e461064120107803040413450904214031a04031420040690303070003190040034803142c8030222010070030a40d00542190b65940d20000142daa43c05e407070344056001240d10030943c060280e035020340742c01903120f04024452199984074280c0c0e030300c10a000d0003101400c209500340e0400d000c0d807142411800c0f100d408001e020245000d448000c0d01e9540014800e100820316920545000c4c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 124089613 1250 124088363 124088369
    0x5010302031903080c07050c0d030503100803040b1b07090e06090f0c0108040204020703030b101215030206090907090b07080703030e0f0d03091a040606061403130f0f0605010b03010807 81
    0x405034400e6081034070014134503080903080c540d0a0000054081c2440418480091050005400841c2403225840d004220342c0c41100c00040080703e1306e0700883d0100d404022102102c005650083c100604403441103205001ea010001d264499081c001516514501800346072b81c048030058180c0340b801030f0b01e8504140c0070b110880034075008410105e0803a0f8000142d03582007a015a8010303190304851405400074540c040314264005482490201415440600c51800205164052005000c42c0c112440c81c50750345d0100030f40c4040148032612050409480590b0b00903840e10341038000c182c0e80c5c64880103d501002040c0c0303505400058290078035415006c2c0321102e104070760040c005041e40c0300116455050940300401095211841242400700f4840d0782c028030340d4250144c1109044c0340c5028401407082e442402c0118626040c0b510150201201766407160700004458003400803c0c0c0d031000780581100380f0841d01400340c00804000301d00c0c00d20800707018065661101e980c950514048614018560b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 124090863 1250 124089613 124089643
    0x9021b0309010c080307020f12040501020709090c0509090a060204060216050102150402120c130902040b010507080d0923060a05090c0303041401020a140d0f091401081b04090501030203 81
    0x3022600b6648110042051a00a00c0141e181c2c0c9409004a0405d07000400c0c01c90188114880c1c801c541d6014030017041200e00076000c4817a42c0380e54841140c2918511100a862000000020012400c00c00c416a81c400c0d88541510f00c0142c01d903440d0412a00035400100c0140d10030892051041030064110000e41002d000800030901a0700404281d035400500082c0074209a212503081d11200308100817071100014003480c510102c0400440040c01d8030002a442681404035001095004401701e5420700c0e00401c42d0b40c0381902042e0300801500600070b044074200080d00f0001069680c548044004821800c0030300301a0901030000d000750b0300090b0805d03c103600b16800003156681c2c0002150212140740c80015042c40700040140e0601048003009007804034001c070801c4a805c804034054400841c552903042c0071804181701111182030350700503503460a03001146030b825076003c0d203800d6911101e5401c80000c0d4401e041a40c66180d001036008000700e0b0b40364401401180341c00c1c1314800d1403075084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 124092113 1250 124090863 124090867
    0x303070c0e131509020609040c0c0b0c03090304092f030402031e0a02300f21160c1707030204050c070f0201180e040b06040b0a0602210408010609021b03 67
    0xf61100d440c50b403407082d0070301d04566407080800115158001604c2208030024005c0104d10f29402c4082d0a1555084003181c0001811001031908030f450b500356801144810300960070542828078000091030b40303501104002581d440884524184a12428000c000c0b10010030703100c4c00c2c00e10505103814040b0401169221004010f0070076047d0000c1d03a2203c441e0100c034461601c1109200360321107a100c0c40342e4640c4045045280e411403c60020742e00c01483e10000448a01070601d64081e00d80c015150003803041540e0400207413201c0001d42240c514000d0164601201c0c2654687c0307800034851001007501c1d2260082c40b42001035180600ca071315446504109807901e42034a030764030000301c0d5004c51002410b00483c184140c4008603200e026401030141408480401d082c01e041c000000c40d03040360014407950400300681181d0502e030030b5803000c07144540c0080958050040e085200c0c1c1c040d1500c40d03021028240000034541400b40540e60092801d50070041e82d50052415110500030b04140e5000c20b5071003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 124093363 1250 124092113 124092151
    0x30617060105150f04150816030501030309030201084b060d0b1803030901050402040c051c200f03010812070b07140d020a020c01020d0309030e0d0f020303070c0e 71
    0x2600c4038080b080e060f402e503c1c1c3d0344508501400d07000d4050f0b42c00c60030909003901881d4090980105000c0c0c001d5099015005005521080840603078000740801800510242c1e0b040006500580d10b079600001164050311180c0d8070302e40e44203007400d015010382041c1002c0f84850818504d001c640c20710306080d804400e046038944003002c0b4016001c3c140307004020b0b40840c0d000441340784c0030305000c0020540c07420541b03079030781400829103028080560f02030744078a24280b0b440b03401c1c0d17006004440c0e030132204040440c1942030f4202c101c4020310388020070301210349c0b10501503908100c4110040000101c240750103500e0f541040182c83c903005c050344500240034020040c0c680030420301c9403142d034407072840c0c070384200717402107191003003070140545080752221600114070782e10801e40100b425031801c41c00381d003203d10040d464a800c60a40345540e2000d40800c066584400c003e080600380d9680c1e107401811500d10050341341d400709266030300014043d15480908001441054654040e8542080110010040d810f103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 124094613 1250 124093363 124093369
    0x9030318050f0d0507050d0305090906010f0824030708011a090c160c03020d050604020f0402180f0607230d0906050909040c170109050c040e07150c0501020307030617060105 76
    0x82c103402d51803040c83c1c03501522040050400c50700002d8907000c0d060300d807811090325003e810b0780c0100407501c1c8145485400180654440d8500c92642030003551410400e44441008903c802c2c0d10031081140f0964240307100200d42c40c208401001001312900004004401ca0881e0360382000400e14240301d00e10240922903059000000d845641e58a442c8402c01000c852a2541030310040d648000d41200b08c040300f81e000d1180118195124074020b49550f01c0d41c0c0301c0481008200c0c46500d0a40007000800002081c00e824424406050304202070314551a0080946560990b001441d0301218004803221117080302040911100051008500b0034030f01c907500301033b030240140c095023071a05c0c000d82d00f0100150a00c102082da18006140c6903420b0070740351000410030360280c8251764042d1241c1c8070310302000700303941040d11400e4101e00904002d8251a401c0444049500c1c1e9183e01e55400c001a510200d000710301c0070302c0114043c00c4a500e00056861600b9080305820f6901d20010f075045e0000b10040046403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 124095863 1250 124094613 124094629
    0x4170f012c16030c2c01120507180c110303041a060112090303020901030c080105090708070203070501230c0a170603070e040b07080f04030905010813120903031805 72
    0x186030300003030000c03032802032240c0740c03521455140c0390703030216128a0b0003c00d1160354006081501c1c080360180300a5140070a038020032100c10b9801440d000c0c80d010040015402082c1012001c81c802c400f40c0d0510360755800050861001e99112500081e030b128a45c828541d049410b42c9200c90006002e5419490980c0307440480358900f0810342c09421b03401000848580c0b2940828001120b03520041008498506005009422980c00e060219103000e80c0110918028003109040b510002d02c104000d030303500c07031084135100e1014000d041948010f01651300014428061841412294501cbd0b1070f400c0d4603051103440e01d19010300410f0f00003408104d50350042d60701511010401000c020104000d8503440003207440c080855002c1c0d43c05088000032b0004000e0340b101c030240a0745465541075000d172a040c06480401d2000d40b0005c02140341d00008000c2540140c0409030b04c00200705180042150f161500600541021000b00005044038001c1c01010307084a1012004844a10241d0696041c1008101070f2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 124097113 1250 124095863 124095911
    0x6050a14060a150807031803030e0c0d050c060d0204050d0f020f010503060303090904020a08160801050714070b06010309060c020c03010c0302030919060908040821090a06081b04170f01 81
    0x8804c1400144441d070094001c041c0050f00c40514041c500007a09004004040c0d80c3c1004c201c034062003611031200e2409400a800c4581c000000e40600f40c1c4203410000140e00005030040804c1e000c4c4400545580d07000040040680101403103883da0b1114810046441c05440c04075061040a0061115941b000000e9a508980984400380507848600010780ca80946910007a203a128104898210101e0740b07441c80200e0f03600d98024440364503a0b10040c0c580c0e11518050500381c8000303114100124181110079900014103040009080f80348e51508019101c400c0c8004001d43c1c0000d0740010503007002d20074952800103a1a08500398101145204c2d19051512500d40201450f00c80c00d00074040d06901065020341d109104940d103a90740e1000780c0d2074190347e101d1605980b00503261009002843c5003119203010004200d01c600504200080d10250806405410a12031b00c44105030030001000c000c001419200c401d140980b00c14020803460042614041140c90b41406148528403100f0a018000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 124098363 1250 124097113 124097117
    0x303070f021e1504091a060a05031005060d062c0c071a0907050901080703030503130303021b010204090b0a030c030b0c070c030c05040e0309150d0906050a14060a15 72
    0x2251080b00001c11818100703402090f8403480e20825440e9800440300100308452022005020b4030461212040e004d010840c66141c100d88104601c809451041c002103a0100030704d80c1a00142d5180c40c08920799400812050080543c0d0302014030540054200c0648003040350883e548000c0030200960f61401005000340707003c0d00e4007003400310400c115070813200c10f64600d07024042900d1420b01030710765680340c0d40e1080c5070099120b08008190020089184030503a50942c69461850326a032401d0a4401c020344030503801c1643c284014140d43e8110161180003401110000da202d5060589060441e03800ca0481071107028a203100700009510220302008880d00f14414502e90358450710348601c1803184042c02460410401008002c010030382c11080182e80050350200028245c0c0100c01d030f80e82c45000801a4011107111401a50640d100001c00741040b400c80041108000780d9142e900303680b025107800103820b0310f030220aa0341221145c0d80c80e500c40c0c404c544001c1843c0c584480c203030b0b4503000000a003007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 124099613 1250 124098363 124098379
    0x5040c12030905102016080604031b0201050403051006050901080a020a15180e0103030e0604050117060a18020c190f0f0c05060301030609021206071b1704031a01050303070f02 77
    0x1101c1740102d00d0404400000ca5540158a05050f0415101c4002c040051000d2078800004640400009036152142c1e038980c47d1038040c07044500202d11110004a0100e0410008001c0840060028000440c051032100000b04030030341800100100388005800072225907001002060140e42c4081c41d92080b039000052058511188450881d81c1030b44035a140649403440031800540003140b215401e0403a4080d0751035509020b280c008004041c41740f441480d00140c103060700030f0300030b402c0100c0168002e140100300c80140395691800b551071030704003801d07904400d41c0498104d00d0729a0230f01034880e194408002c0e2001c3c00c501ca5a4a9502001140700540b0700042480400200315404603804060400200801e440f5a9645014030260109034002c81c0680400c18803164003410014600c0c1c0a10200d40b91030719080c012410110340c4a02518050714610b400041101904d412840104080d50180c0618803d65241e50440b120009040c0d001c107000e5441080400c010605890000344456811690780b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 124100719 1106 124099613 124099639
    0x140609180103060c1404090509011409010903081305070b0708041a040302130e03090f03101d06070e1f0c0b011403010f05040503070605041a090105040c12030905 71
    0x4411720505120a02226140c2e070855580706400c00c0002807520080f102a01103043e09544c07104680c0d640304114020b05500c1030760700340d010503082d03002142c002d090343d034984e585c00c5d05101d039026220001c50070b0030800070313940102e40c008c2c064112100c03a21038900c8a0485503602c58071040303208001012010103849114000d00c00000c034108082c50910f80404140701100303200c00d9070303280e050190104031030f6420068400c1811040c3e0104004001901a0100074075081c0d01411580a1201125807a8440c2e40c804080c1d80201c6101002a02840290081541e007100300500007010403422600210303142c09003284c00d8080380b508078003e000341c08880d550041268003d85028080c5e80040200401060700c581016810501c01d92125400c04000012815030250039034603000c0c40e944910a010902552112840140c0303c05a52014174202c3da0303802400c12403c500c0b0b0796000e291205140c2e = true := by decide +kernel

theorem cover : BRFrame.Cov 123920863 124100719 := by
  have h0 := BRFrame.cov_init 123920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 123920863 ≤ n) (h2 : n < 124100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
