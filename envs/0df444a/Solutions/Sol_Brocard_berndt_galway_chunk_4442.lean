-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4442
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:37:40.182143+00:00
-- url     : https://prove2.me/submissions/0dc4b05a-98f7-43d2-afd4-ff1768aea2b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 798741007 ≤ n < 798920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 798742257 1250 798741007 798741011
    0xf060109090f08070c09051609031106040315050709060206150405041406092a06040302271e1605090907050f0703020102030907081f0b06040504021c110f04030303 72
    0x780c00d0020b100303503403140d20b984042407a60790710891809410861030703405141d40ca81c0c80c200c0003403103014855020031000005510f030f460600b4a565030b0008c1500c0344c0e41030700d90004010700c4000000351103104a1103024200001c0803855281c0074400419900440c3e00c01411036010750107008c20304c00620f100304104002582d020946541e07600b0700300100440b12403142c2551050404106e24640041074100618014215400d4584212354035600038083c40d002ca40d5106600b04020001841c160740f4144140e41c80328040b400c905403a204034a81241c0882e0748202849260851030300b100c0c00d04600e568030500000411419441c0c8000c0101180900b00d185070050303082d0700118062038002c50070348035500c00350f42c40300b5030355030552034028003070340085c1e403042130510400d800800c000c4008a400300c0e0303241ca211308081841407056100405800c0004005402010402002c10280c03240d000a045401c141011003050310f0007044143c2c11031340d0983ca0f10315036101c00e10242c040a15600c045034100d03501882c2c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 798743507 1250 798742257 798742271
    0xd1b0807051c1401380901030e0c1002060f071409040218090a0b0909060108060c18180106020d0f0e010e010e0a0e061018030b07021501060806120f060109 68
    0x1a80003001040740550240c034221000181d025030740000007808170407180c41803075000c5603807910240d10189580c10140c004402d010815455100360b0040b49688035442c02c03120308034083e40c082060315140030601e80040c0c100f0020018071407005070129030080380b1403814501c0d9609415000e07080f4095055440d2150ba000107400026040942032207080702001071040b201400d20046810040c60882c403440c0c02240780c0c4000412250000c60003504840c0300394082c101c240d0302c04a10a40e1580100864082e4042c0c1d400a04596100c8090f09241c0264811000c94154104003001c0d10b4110a0310052040046400e145501d590b070000c1c4d40c640ea40001c0c00d000101a04050058544814000b41c2540004903440c000541441415046001d6601640c510b06a800b200301e007210314601d200603074048560405010000204071a070455408500e602c15140b070303100600c0c84040607000a80c080000550784500f480514070744950241543c0c00800010200e0700d009409854440005200d800d02c92960380031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 798744757 1250 798743507 798743557
    0xc1103011b02010506041410090504020a080d05090909060907151b0f0c0602031e130819060605010504050a090c0c020a03050604051b18060f03030d1b080705 69
    0xc081800c1c000e403829525298103500003402400201c869a10460030700c104415091a1034181502403031401c41c42491481c10140044e000d000c01410403032300b0807040703c40001c0010b014012546912002d9a0b195a1045440304010002c0070142c03000c5002c0e00f020050216a142c0041c682c41119089041111070004030502500c46040c06d40c120001303041034a40300b008002a0009941c1007170f2040344105181c90300c901080341daa0007860000c010351040e850010350760420f07941c003401030414004410600c0603111098141000f500c1c4010b003602c0d440401c02041000402d00a9001130002840d00307908042c608030018440d48224406d50b0340301c0e0b50360b42c40000018401c07045002445d40291424407c1696850025a1030000f2281921a03000d19108484001c80c0480d0141211000130100c90300c0c146101c2507a50000c2014001035405600784d441654541c90a01c00b515400705c0700e40d000165004408800242c3d5041c05000d034040000080410a10a4000040e92003029890800014508440c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 798746007 1250 798744757 798744761
    0x10c030806040b030708030301031b05010801091a0414250c1104092102070522020a0e130b0f030303100e09071a0301050f18010b0f070c060e1804030c110301 69
    0x140303c03a42601070b024011555130000002036040328800c410728000800d8008850380b0400140c014940018000d200402c6000c525411101300040c000316105411041900041c0c12181c0203000e02002c4003400e420400152002c3c4010141035040011100560b59021310081000031484401070074003c00e640195042e0301d441d88040c03003e0350300070076995a00c019249050f10f064501d43c0c0881c01071003060004106030518961040350340002c1d00c00c0100700307460746203c1c8000c0c0d04000805400c00c107400e40d61070400d682d14075080e19075034503007100040d41d1070300c810074130011014090381300d0300952080007803044440034540d1420480303030101d06624607915005903840c14440c80f64418803441c1c040c1d0180a49000f407820003181250f50407202c01c6426010306042c4400992005452448102560b004004080b40e000c014000e030000604032514201c840d41e80c2140b880c5e5690041000141c21326240b94403030806c11580000c41300c00c00d00b420510b00e0207030340040840b091540000c2001c0c400082e00503050300c0075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 798747257 1250 798746007 798746021
    0x9051809030d020c0f03072a0e06120114071e141e0d020304050d09060215010b0307020a060e01090209061c031407020303030403030e12120c030603070e040312051005010c03080604 79
    0x1d02c041c1c0f0b40d5200e841c146440d0f6034071441d40440c08d0304410804401d251980c00028412540b18402100e400d6483c4800c105518080020f19000341d501c40d000620b0b001d0116a6071449a40d203030f250040c0b400b10786410301440d1003150100c0002e102e000c0d401c0d01c50400740b603820360b25502c0c04500301d10b40c141504018040d15001d174001029aa81c008010310080003004110845c0c0c400c240c7e6500d22070715907141412a0707500b00918100c0c0049400e04014001c0c03100760801554090624011102c6985c2c655803603008a4041c1c1c10005a140d6442000204501c0c0c882d104540290045030034000c1201e400301f1200b06141c49460050070702680041d00705441454005a43c0c0f1079400505482d1280f40c142806000b80c0310050040f5883d00610030902001e040545c1580c040491018400c01c43c1d50b103110190000d94006400c096140c894494001801d6840c0c00003180710794440c0d51340401c006003e03400802581c201404004685c980201c083c032250340e0280c00b1500c0e064051a01001c0c54880c60702040041c41e030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 798748507 1250 798747257 798747283
    0x91d03070605040b160e040f0b0d061505060a0f0302090a05090a0c0807050a0f110c060705160902160b06040608010c09080c0906010801050d031e09051809030d020c 72
    0x20214401051050a520441c4241e002e0145100306944180c6010300381d110303035820440815050305149039582856800000c0c01481c250f8000380008445000450100c03038200204c9003161900e0b01d2003016400600418020202900c421342010f4902c2406032581e00240800b1041550200b1040016680c40018a00074180504400030354240390301020007400d0402d0b5003034040b4000c4030200780824407403000c44042400702d86c2d4000340c40c240c1031b43c100c0d440346414070500440e20609040d003a560b540c0c080180b0080303201d5402404170003aa119135200d1114140d200065591040c00000e442201c0316802c9000e19521000303a02c880da40d00710026005101c00d8000c1c032265841d100c01e0480d566084240e10702500c21150446012000d10020000c000000b221094001003083e0010003160601c0151840898800e082203c5050036108442290314245801c050001e411007008000c030b8246080190001540c40340000038030b181c522040e035039a1203405078200f01a03030300040104141e01c05201c1c440402c0c2c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 798749757 1250 798748507 798748513
    0x12030b04050c0a0f0c03050904020717030903030f010815040b130f110f04091211101506110604120509010504051503180d210609140405010f0e07091d 66
    0x4040100702d035290407148030500890303138040d190081640503400541c182603044da2928a44111501400003a40200504680101340c804a0782c08011112014501c40c1c50707240021a22441c215071501402c2006900c44070094003d11807510b03003001842e845550040c2c101d001c2090585800c0002001d03078001100251020f90711101010400004140a4101c040125030707100a1003140d0b030400048517205000201036689400368881136600441c01400402c0c0300034103603400c0403440d0b100302003511408180d074404100204000e100c00354000000e09903e032011001030500c0d02d8207540d4160120301202601b000c0c0300000c102c0c58090780c440c804a5001d040094282060f03604442c03940d03503040c0c0045d5142c00c40520400549840c980780001d4040c545c182c02e5548004180118003a000074045100340d8280d855200e202c04120303003680c2d001d10200099080c5503046540b4243c03d00302d003106c4100c07220050b1181064840e1031010b100081e0078058071401900010820343c006038012941c2200c80d141000340c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 798751007 1250 798749757 798749761
    0x80c0105070c0509070c0308090c010c0b0c0f04080d2606150f0a0908010605010507050a0321050702100c0801120320070807030501200f030411060c0109150506060712030b0405 77
    0x20b03800343c072064400781f198840c180e65454818811b0303281c0c0c4841b811103000035200c840c0200407400b51a4020b8100b940e24250600c1c05000f024014016030158101d011554080d030b980604080d403220307003001403030700c412402824588044109603c44030041d04592080d581c02d800c0d0600300c0d800200f02e07408040f000200c07a9503500348040281000801e44242d40c125481c1c030400258030750050341180eaa1a600c0005000d210907281c1c0d003920b2000005200400c44041c00b032040d40306024034400d90380503041c0f0b0f03001000c98031011181c00064900b0414014208007640d401008503100001700340310300641c10b042c5459124080c2c000c00d261100410b120b55000e10400b80001404400883c000040e0703030051009100e54500d4004d402000641c0e60320360001c1c2c19041040100407140386000e0b580062141070404415190600094800d42000d0350004041e55600440400c002d800c403002d605c040062a01480307a4613058002134031038055104058922414505490030f0345100c2d50010450500c0240100140c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 798752257 1250 798751007 798751021
    0x32d0304051e2214160512090f0123060a03020f04020c0a0602030709180c02030f0d0f0507210515010c140601030b06040c0815060d020408061f0609080c0105070c0509 73
    0x141c070004201005407130302c02d800f0404509410203202c001c914540c131070500e000d000d02d41803c0407401c002c10a007100d000300d80c4090707a02d120038011440c407420100a00b0307002c1101401c50a042200c00740885100e03030100601000182c50f040c010b07018542c42180c005880e4200030b02d101d1304203080d5a60050880c0d01c0001004125904038090b00184c032449000c00782d864400c4201503040310110034801000d43c0c001c0c046c0c00381c41110f580c01800342640c52100400d07002d0303a88041800b5034a090f035540b001320f440403000100b0403042083d0741e56003807241c2d003081c0046c0c145201c2c51076441c0b1041d103e480c1001030505c0c1445c00d0101c1007801ca604180b24604503641903949003042504250240c031418403550030402031a01e0144250756643c001c031440200340e001140540104216070b446070b2101404650248400100090248503841c480d201c0e08240c1810904459045002120309400500c18441c5045003400401000941941981e0707003070030003036603070340b4141045818030856034460b9078816050000c108107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 798753507 1250 798752257 798752261
    0x1051b06040b06060304081603050c1c111609020906040503030a0c060b090906070e12030c0106301106130909060b030111070305030411032d0304051e22 67
    0x71607030107004100080e888a10401003244419940a804000c2c24004402d036a050f001c0c80004443c46424420f2070880100c21907401c001086070035000b410040070b8080811a00071100b8a0101c80001c0a071404502d10420003114043e1401800303110baa010502080e541c0b180300480d00500001411641c0b40d14a8400050003180760f9002103c009040c07007207803900c134204980d0850081140b81c0103450340c0e581d5070b1421140700075446502e50b80301035454104c04515000784020706031400c01e680086061810701c0d0021091101010004100d60050008100a05051000040b0403a400701b283c1d4070070b4449a000980038098640786041c082b58040000468001d00d5110171107141c0300d40c809001d021000302c101822591200759800324980100030206c0001d00c1400250b0b0b11074811482d504000e00320f500460301c0c00302000d00648298500290181001c00c280480358220300307804000b18a81400c20010894544404001c0003d072007104090f0212941d8409109010088502d0b820802045803505000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 798754757 1250 798753507 798753511
    0xe0304090605040204030b1311090709051c080a050d02130e01140415090b010c1a010303090f08100e010e160f0506180906011709010f0b0609011202030601051b06 71
    0x562854100c1c009042e0030b040c000d44044039000600d012683d55141030300290f8804054040700c228440c480f44403d240c1e1344e104a24050302141d5030350409941058280203034824003148912600c1008070804000850100484500d98654540240c0342d031400e240590180c0124260500504441c880202d80c190300740507454100c0b0b1030b60094402408030b880030320085900700900d4410155130300e0002c1c0003180c40e5410180b030441040c900034600c80c842ea01e95107548101103000c1031a54540794010400d040d44010030340c020340070003001c00c8103c51070301c0200c603500c1c4941b405400b18a501d0740106208140300790720100302e041d0320a0a071a03180c024481401c0703003002e141c01082d0401c18a00c5e004985402e1580c00d444c00d118140e00e0f012001902c030300c02c101219274020221030400203600d44e0701e0381c031944400400e40500c021400125140e409003508600b80e81d0800f014500958040c0300d034a0311a030384140352940411490b000180d880c1c0318040102c8051140030001e4803403204880b0003402408001500c14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 798756007 1250 798754757 798754769
    0x70b01050d08160b3c100b04231e0910330e010c060f0905030406020309130b13090c0b070c0f091814011d0303040c14030a0b06060702040e0304 63
    0x104101407080c00d81960184c6000c000010170040000244070211000e160002000380d880302c0f541c1e56034840b03a03040da40150040b0174028031900c2c085004c0f1803031002c0c1c159041070890386501c0102880028445050500010503c1f4201c1140070410105d0703020000c00c00f800181404101c4513459240c0420a40f6005c491500240c0003001c0381c2c41c48910614006540820503543c0e00c0b55170302140c6030355028007111035445a55599510b10030700000ca003000100002d2045401454a0b91040c1040041d07065240007940f20060030b111500d03805603111952002c4035a02e003600010a010581412000c04241d03820100034041c2c00280c1d401031000d19040b8604803031507500750600c0c640e02c8005080076145050b0803109020141222100000e241b07508a2802d41803a000003c0c0315281007000d01014086689084995000042880f06000000d2695005051019804142050510003082e581d0703004030000341109113640041889551100d04460880342c0042c018000d4401556003140c59520522840f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 798757257 1250 798756007 798756031
    0xd0c02010b1807140c0727050a09020109030303051f140a0801151503020d0c0309050c010c0210030c0c08040f180c2c0d0503030105100302070b01050d08160b 69
    0xe07a003240b841c8542030b440f4000b113a0742c241c081c208070b070140c0b2000c0e0080d4060b000b0500403041c02284046003d0440d011104002800302ca041400355655800c03038802610a55100d42000102c0d40541d800410200449605207000902d0307554086540001c4100d0b03c840c8040d0140790070001401d180e1180003103040b83c40450b0b086610940d01c0c000142210355892404250340c02c4820304119068095058118000e00307410090b00d400114200309044650300c42d520408a82da0700d45500c14007000700326081240d00c00b070801e02040d032256000205c8000705441c9000826403510b01014130301c0c2c80b40c0c1101b4803c0e94014481506c0390740b00c0c80c0e444d030102118010301607800042ca00604802e18503000b60000c420454460b1031001400034036807500c000306030201c009215612155030b981c80d11800c2c40026594005d501558503035040c6020400a1090741c0c219004050041c080340c0041a40100824111502164102e5440ca0740307103404c1e034140c00748254000444a4250180701801303940041284076060000c44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 798758507 1250 798757257 798757279
    0x110d050c030c030613080a110f100c0f120239060912030403030218130609111321080a11010507050408100c140f0915031306050c0d0c02010b 62
    0x18559140d80840b091102481700d1200c0501140d0640020498016245858002d43c0c89034040740b854000e1030341c01130074170b0340c4a020103089a038250b01c9039041d20350041c582011040f02c01c0760000c015040d05200d524485e6400200313a40054113a070100e80111920b480350ba450a4010501c030030740882d4252a800e100e0040c00006808050042030408100e01d0700c011043c15500c4e55107044000703402c0b180b90102000304540001030213694206420700c905201c101e001ca4101d003030010000a89406a204507103120f0240100c2945242003070f024020b4a03000b440740460b0081c0c050051580e0951105c0160164030005503203607509602000c0704c075603200204003d00c42a210214115124480c1c0d00c1031445039009440040d40c420203680140341490340c90b1508035000b8004204405450340500000020400001007400c1c1609200d511a0f20340c102c491211030861a20b00e00e00800c500f4802c0d002049150391340c0016050707038000402d032680e1810040d000c118829091401078001c0582043d414454420343c00c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 798759757 1250 798758507 798758509
    0x10e1221040b0f060a030b04050a1515230402041e0b090112021308032a0705030a08070804030b0f15040902010203191b061418030313110d050c030c 65
    0xd040d074021684040d06074600e40d5035035409440080043c01c126030011446900001107880100720398011400381c00a0040c0c20a149451800361900e08803c2c005181000b0491014258982c2030340c049512025208500e040300040d105a2010411803040c0d0040c0b000c20003084015455260005003412100d246035215154400c400341800b6100b140307030026454080010ba100059005030440600142500c6511519441818116000300e4000401e60400041441c501c0d1441404032030b9560000010341411414400400c0e10754407690400307441901c0001d401410400c0490440303000310340003032080d146401d08070a450082c40003990401160711809150105620b0b091051805590b03050300103600d0700c00002e002c0e035103410b0145d04040c2400307500c2c42c2004580d95884200d01c030043c8503001c00078440e4081100145d10303d602800094040001542c1041e040a00104072074000854108502921400c0d19080e0484180e882e807183c0c0044403542e60008000700001d010041d00d40c01c4066a448800001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 798761007 1250 798759757 798759817
    0x6080d030e160e0a090809030f01022709010303051e04090c030b010206280216080405030607110307060b04110d0b2d04020a020f1b031203071709010e12 67
    0x80516034a100f11400402d002611503401402550b103e4140741d428400300100003410041020f04440050b5000a402417005544103a406020fa14105e0113008896186003c5200102d0500008080c400002038280c045d105000103121440a10062142d45a40303030034149000d0200c5104541c0406d0034800034500c2d0f0743c001700300c0314450a44610b040c0c440c50104074001c6242c8202c006000240740e42006012070001d49060749001070b60060070036941d0f403071802c020300d0700d030600040c8494100408040540b00c12076010088820264000c0c0c8081b131000d0600780010010405880d2250707145600040610340e8012540104003003120803120381c1c1c01c0742d40301c1c4112800c107221001400c58212018090b01124a13082d4090100340704a481280c05404411006614001504018071240806501c2c48541d5141c10003c01c1598101c140d8001d06604051401910103c0c429100749138005031030f800501410425400928031030840e1013203c01d01a00c2d11940d903c103500814591040d46001244540002030301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 798762257 1250 798761007 798761009
    0xf010501052a03070f110a0303021b0414011502010f0c17100b03040c0f050411030402040e0a1b05011b030c15090c0f090c031413020406080d030e16 65
    0x40e1034691802d0650070000001500c0c01c04049030340494002e110025480c02c1003d8020103208100600800c1c0c01e03801c043c42c0e0412038408503171140030605801c0c80001d0b804154100c400d80b1007140c0500c101d0110300040d0240c03502c50701b4180c1c0d8000d08400061400f03040d1400e20001801500208140b506c0c05000c4416a50130710301c094040351080a202d100320810034201c5600019901307280c1c0010351514030f0500c0907801a1030a03540e00c2c070b00103414442d016941d81c4003401080100c030100009a800300b860740080c040100003911865403100071841c0f145003404902015070780084c00e080401c07103181c65011044030f030740550360000710000309040c800650342900c88212a055111002d0550455490080070795000512158264030740e9035138000201100039001c080c1c80700c4444080000d0030621154100e440c0d02200d0002c1509040203101c5081c0500c9447d0323000746101010328036100b520300100700508491f40c8090664440c691500b80041e9241d8001410303000d071402a10821550380c0b01d220000701c02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 798763507 1250 798762257 798762259
    0x10021c111905090406030c030b10142e050a030c02070513020306060d020408030304061a102303100608010614040b1803010c030f0b22020307090e090d080f0105 70
    0x100104021030711008990328511210346041860500c0203808241540c400f50b00448940740c48800500c00c005c0e03900c078003503804680300040c0d941c00c9180c841c54188a00c41941c2550092000c01c132212219150040039840c01c1115050010828603c0755009002c0d43c411f020b862f0004e031808420311140c51000c1170303a0003141e100900300c40d642d00c03800c1c244e000251b101a00d40b40e4403036010000c50399140b5480c0080c000500c460800b4580f40d00d8941440c0e415a0510508000b14003001d08a2440c9583d0b11820154005100d20f05464031101741100c0361610711a440b0040c00c4040040304015850461a10400036950746d07540b002d0082c1d0761098207480340455481d400300030140501003445500a503070081c0030031624400000703507142803083c0441d007104c3c00700484100117610303000b2403a400410b901840080f4842510030161003d0f071070710381e04650390540c0c400750310003a0008085214030f4420b0b100d00e009490192102081400d0035103045550f03d000c01180c501040c0311000242000d070203543c1d0301c0d0480c0c078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 798764757 1250 798763507 798763541
    0x120605032b1e020307030206010504050c0d05040c18092d0f03020307140606030615030c0d0c030c180b030102090d1103070b03090705030705030c0109050d1410021c 72
    0x9440100100100300040100200a11000c1190340314100080110309180b0030340103555030700c40e0380c10001d0404038143c20140c005d50401090180f4002c021044881030850000000f07920b448601e021254400d071507000b01c0141c1445040030841204940c01140d00901c42c0400740c2c08000c40c480a20f20054a40441c0c031a08075400c8030f0040030403110140035256034031a1064a03e024034a95403048001e10b130310002c40c40c0e0340c49182080300c1c2d03041c20032500c2c0d0020303650703803040c0b12030020200000d81d211426608140100c0001001400f00100c0d11200400b03035510014080c1920740b00c5940790004400d052201c40c2c3e00f400c002c0e00801e141018800c039501c03668042c041c80304041a944420340d003072f05040103090300351103003403000111000c0084c040c0d8000c041c04409415460f14040805183c80c8961f00214801d4004541851541e80c00c401c641089030400c1e41c40620600e43c2d0b0034484000d0000ca41c131440603014500304895a00e4542c0d0041045c06080f1b0710036110200c04500e800c2c12100d002a01c000758403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 798766007 1250 798764757 798764803
    0xd02011b060209090408040504150b0a180305030708091809060f04080d0c09060e0402030c030112080717030106140c0c011209020d0b1e070516020a030602030712060503 74
    0x30100c4400e10003460084201510341854000400c0c00d10b00216820b988131500400c0c2030000e854036015824001000250000005042c515014400c1c82101a62070510141420f02c100300c1c041040590700454000050303d407500c0050500d08a1944011b021500c5485250002da81c0c204000f640b0500440141d4010500741d0740b0310352203c03031101010340203030b500182c2880315001d08070a030300075231441540302d0707035111111482c04c0c90107410480105907040c8107034010700420080810b000c09403411a100d01e90300b145e1a0805050403034040c424404054801d07440c0c00040540b01d075000005604aa00644d210741105654188840076406145d07008800c036004040f00394150341c1b01e5414100030a50440c00040d61101c40c0c0e000800c41240c08400302c40103d4100f00300003a0150300d100d003042003815100c1d600d0301480c05030390045c4244164100c1540c0101c521408009640b40e83c10848043c50307205804650307904280a001e00040c412102c00c005060501c0300105490401040d442e50305040b01913058203c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 798767257 1250 798766007 798766037
    0x13060203040f09330306051e0f040c03020a080606090709080a030c110a0e04021c0f0b1306020a0c1104020f040e0613020a0c1401051e270106140d0201 66
    0x900840c02c1d60700c40f558412240c80d5280d9031500402041e806000304c200c2c0f4042d18519128040d03440c0184682c00c1041341000401d02c00c2240c4040f503030b04c11a2824030001075604c80c17805044a25a81c2c0019402082c0c00c400400c0b103a00015450780280e8088075a8440e030b546011003103c0d4410076014008060f0041d0f40301100003070088c105401e004d445800c08200359030025002c0742c0011980c1c0e000d01c8060b451a010300c420f6003498650345a800d101030390503100d404102e031541041c100da841002401e0940080018800401003401c00306095445541513586111403035004241e40e15200301a00d224040c648121403501e0140f00b211448a2400c0803203050074940140840008001070016404c00b010307030180d03d40c1c502035100030f00c00c3d180c5c2c03520b500d01040654102180f4100c3c0143d408030b180e0b8500010700c04d0455456148c3c0e00c0d2980004417209155032904044442c01c2422440d407050100d2080c41d100340800f064100b24180e07044074140c00c200f45520810800b900c078801c0b0f0061b0200b00068507034812 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 798768507 1250 798767257 798767261
    0x2306100b0a11011509050a05010f0302010c03110115060f0c05061b04050a0b07290c090f030a120f05121f0807060e092401030e0c12010213060203040f09 67
    0x841c1581c00c1000080c600c005429003550341ca9098403a40e890343e400140710b500d050348034150300054409010042c0f503044c5584440c56800074040039050051302c603034020416125041d0b00106000e40c00003401f030929207034407600d9070000790f000e180041159403040444c1c6511401c1c00703091842d003010080446440d55449070020000c226a0b640342c8000c100b1010815464141c180e000504010180568407101424011181283c1c1c5041c00340441900c03403292143c4207081a801d4000000034040c1c1e54400c0d0040009200710745850040b41c050040c0760380b001c02c1c00720780e080a01010005403566499000051804c480b07500c81c9251020354801b5150103e1081511960050318080c2d101c4142441a51a00b0b00c0d245480703100d61040340003628145810019041000000340c02851410340c1100c80c0452041610700a03c117001081e04160fa520740c0c84513041c6082020081169004d0151360107078020161540c040e52001015010347c00c080b0300c001820610000c200c2d01200c0c1041c00f40080c59080288d2400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 798769757 1250 798768507 798768517
    0x1090905090a080f09030606060a02071a07230f0a0b010e0711030414100507030c060504080f18040c0c05030f0a09050616031706060912030f072306100b 67
    0x5218070401001c41c00284010b0018040c282c6400c41c481d46480412041507d4600c0040035180990014041d07001d80035000074001c0e040c1c480c00f0845001803501a10148514061244040c0600c100321541a4005107400704060007201c403002551001100100a16904c3c81e9100000705018031940040100300c10210706036030402601d00d45103a80c1107044420f603103540c001da000800360304c3c180c0300700210314074120b140a0701c1c2c00e000d41007260428040303840242c141c100500010b403074103803160000f908018a0800300e40200380590403d54070381410041030440081440161400b503860210401e140600035101100300a03409030047d8508442c01010041c2034211010202c14084c80c03d001040c0e580c1c4610190030000c44604051440f4529801d00502943d043e440880384481e90109101d015102c140845144460136260100c000c4020850680355214010f05440c680c40701181040030801d50041c8081c904144a0894800da00014006170715450240c9200c13902005a00b02004080780e0240904 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 798771007 1250 798769757 798769771
    0x503011409060f10020d09050a031a04030e0405010914010801110f0f0d1802280510020a0c06031b0509090604180c090e2104090b060d0608030405100e01090905 70
    0x20a0a2840021400c4d016036000d420025070056200042541d50141c2da0b10b00600c81100c1000310b040c65901d40c031600c511824004508602d00c40002010703d40036214425004c10702800130450366a44240c0100207040c4090f40069501002c4000107442205002d200e18030b030300500c1010b01c2d10801a4018103181c0c001820070b4250350051050801e050f4061007440b24441140c0e2809842c0303040c5104011020580401029040003180d240700c0444c00b00602c200c040d12002e40f240960504d1018099181c01401203005100c40742c0c0312004901542c5c1600306201c1c0c40c152001d0324407591150201076030140288a1941d80011440c40001c29070325050308800100c01108106502c510701c503450320362244142d6000115029140c04e070b01000c4880400031040c0460007280c40d070b000300100b4582c440f0f0070710a07446041c210a480d415440420344d500403c9a40d50080d980b810803c0950322454103490780c1040c482c0340e224460352554003040034041d02140740c107040165150166141480c0e5a0301c01840081d18130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 798772257 1250 798771007 798771019
    0xe07050a140c030403030e030114060f010926070503030423060702040509011a030a1a04140601180501060f05030a0c030b0d050604060c0e0d030f210c030c050301140906 74
    0x1c100800111030082500500c4500907654076411030070041c20020076050b8880c02030385406081e02c03801d20804555a00580f0490300078500e698890300480d200d6440b60881c01000200211100e0003003a00c8000024490700f02054841142d507420805899005a100c2c40c09504484540ca100c41c100c580301d2114020f000500080c10402c098000c5011540101c1d07407040181c0d560a005c01204064000c4040300900480c0100800c0c080b07a5559142c6120042094035907181303041c00b203030420641810140d810514201101d16940c1c2d9010424036850074003445102c418584000070a90501c40c02e414a90081c854864034610b0b02c0c1c1110f840b0003001600b00b51401c143d580d806003200e994441c2c2c2c5900d4294081c000400c0b0300d0509041c21030841d40c00842c0c400920124100c0390400351244101c601e110b58240c20400e000c40800c5105a0b00303008c004201c403001c01110301508100c50306030f0b8040452086e941d07400f00b0845403004402d58442c4070a0190b01804000000d0121075440d007103c0072548240090a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 798773507 1250 798772257 798772277
    0x6090c0f040603054606050120010b0301090305030f07030605010e01180f171b031504051c081f03080d021e0c46140d020717070e07050a 60
    0xb002d0140300e11403900816155030300c003410421405c0c0d244454070a000700104010301490300c80003030011884501c00c02070304a00d50f018680404020b6010030300444024009001c240c0640c940140164400c0b40c00724441011030020640e0a4400d220703180a48506860301d600102000e001500c0030503080340c0d01112402c03a0000418406a43d11201000302140071041d0000c0385d2504001e030426800c02c8010072a03402e00d685000707055800042c0c2a1f0707500e1207800b00403c140c80c0d03400e1160800c1451021091030308403070702c000d0001c140d002400d82d100710910403110140c1f41c403041d00c0404113145440007904030282840320341c1e03510075203034018258041201400d051208035803004030119000840101295004031110680c4802d03d06d03071010216100d483e9100a50303520b500c84910243d0b00c001e010280c02d100c0130005003000003001007114520b0808044506c03074a1b8407100290b44540358040c84600011280c036071002c0300400610340003a600c1001d03000300c01d5921400222115005105600108001ca5103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 798774757 1250 798773507 798773551
    0xd0206132415170d080402031e06040c361404151803050d0f0e01090b04050706090605030a0b061603050307020d05030f0601030f1e0506090c0f04060305 67
    0x40100c0803520314008142e5680c0010000505007080e400b5032014040d18801e4280300e94046645203400034603052850094940f80042840c02c034501d54481c40001d8500c00801511301d0000e03655200d03030303c0f601064a8283d00e031000b400c0001030700408107050b420001240072001c03e1242450041410405002031072000b8000c050034a07202c252001e951690980414074140c60381c2d400b5202e880c0380c0044241000f110160740040880c030601d060f1401050f074808400428010b141c1008180c100210001d005840c2c16040c40410494199000c46540c0301e044000144140154241c0d803c580300c98407854216a5100e240f51b000d001c40c6062a0751060040010b48680448080c403014458000c0d0b0f00c00e616407178801000b0b0301e08190140c1c140b0901c0400d01c10071891401c0c580002e944880c2c2031030013090039000c0b407144001070a00b001c0503400189100740a0058801d42d6403005202d0f1000b2100700d0f45580f1914441080d91080d5480d120801d2010002804064007940107140c00401e800005140410481 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 798776007 1250 798774757 798774803
    0x10050a02130303110f010501050d1203020405042315030a0602090a03050304060c03080a1a13140a0b04050f040c0302010813020607030f0206090c1f0311030106030e0d020d020613 78
    0x142044000c44c1d401c111942d80301c0c10404c00302d006058207a000300465414040081c000c810b200000504540380496046842c80c4681c043c3c80042c90b0241c000e0100c410140d20820207030f403050030244001010440010b0005440101860340302e0030241c050505000ca50316858041c0d4000508190002d24082c80000012010002000103044680c0c4030480300c805e600d030042440002800101c1c0c0c050512420102850002c42c5040c0b81c2c070004c46501000b0f0610305400009482808000e03254804030500b080313100c1c660794020b1410207800700d03070030042a5220a9109601c880940f00605141c400d05018001075014000c9540c000d01c0d81d04500c021465540e00040040d40304910460000d01d603184261405601000095044030700b40000c1c10308004094040345010700292040d010304a501c9015406847c000e0b4050880c0d08060b01c405680c942e1035800240103800e088030500660300c07905404030551840800d4000d031130710090340a0301071034848070100d01c006040d021060352042903141103120040040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 798777257 1250 798776007 798776009
    0x4050a080d121a09191104051311030a05071b0804231e0103020c0f030333061c0507020c030f070305060a2d0504170403030210050a0213 60
    0x4400506512200741c8008100c809140203800c0a241003655070b03070100c891015655020001a5004072095803101c0d568464512068121030034540361420400100340e884000f0819502e00381c600d1400e8500191020f41181c10040310410920400c2c4045403208100d0f80049810501618100c25000d460303a22400ca040b01c8458200c40680e000075003004650055000d40710380740081c6000100d80465207012405180040301c500550001c440071201440e07003e0380c15201e580c0c911808480c036940030f6008443d82c0c1c0d4400d450340104100c2007a0320740f00060a8045000c1e0480216580e8a01d01004106200d240c1d01b09541c000c1d5110010248051a03100a11a2501c031700540d5000303124080d000d07400e05050180355100d5400755000700405001143c2c0000d000c0360030000301718002030f43c101300c04d0941e6144c41e100d140044010080350f943d1901d030b04051300000e002e140a01c1c50420f40c150032400e80b00040c4140c2c4402005600400c4040c1031a4010383e120560145400502503d84256144410301030846 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 798778507 1250 798777257 798777269
    0xc01140a050a1b05090f011803030c0510060303020703082b0f14090703021e040219120b09040818040f06210330051005030114040c0b0c010204050a 65
    0x514000c11101107414002c640f4500203203e80c0e18603005505800802c1c0b4070030000018080c1401241350030301a4401c2d03190401d0124082e4041003400d0301ca10380240409045942658944545420b541605e4035510980044940c5600105951480c60303a880b94607411500c0045c0c420340c2200d10b4a50310740c0000034030b220708640e407074400201d42020018013001c81d0340c1d03036180009040300241000850000003d165045d81c1d0100d0740741c000d030f40104044411008110540d15006400440d0f1703180ca0707289008411550340301540381d040c5607100c5180d00004507094423404684c0611207801080126144000074407000c10340c0152005502c20b01d0b03010400381c03400c40c0405910203590780d030200031080980f1120305465100c2c00c03482500342140c2d140108900800441580500740400490409000030400030b4044c0000c4ca00500c8286400b948100c80100380f481014029400c0c840c2c502a04184000300d031313100f282c0c02902c1e4160315040c00c4490045412802d00b030402c96500708008a0640e07103025400c1c0c01450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 798779757 1250 798778507 798778511
    0x507050d05060a0f150509150a1814060c0c040e0304031703090d03050919050601090c030209060f0f2104030e041b030c030609050c0901031d03071509060c11071a040b0c01140a 77
    0x790740030002b485000d1615840000030459003081c1f150080c2c0150003403255501f05c0d08103455003031030650a4102140b00c00c14039400b40c900448411362805c044003400490303008074403203e401d102e484501c21840c07208903a84105908980c040e45c1c01c1b24000ea0046420029240c12641c03004810344030300c170618000c4035041d6025403041c001042506668007c9860b10b00051506500300001000030680314014400202c0d03e80f071000c14440162101e003001c0e074607906601e82c40c1081f90180800030300c071040d005035815400122903100d4142031b401c05001d1a03505a00030445000c0d1a001d0660890007014a03580340000c040d101c800006014032640100c2c0d00030b900c1008541d81e5004040000342c2129070401a8015481000f0b41ca4201c03880040103456003550888903803a40e8613401c043c2c1c40002c0050078001001d00e4070300f202d030130100e660200c441da040c1012001201c4140c0d80b1540c6000008596a081c508bc0120401040c40500181009000e554021a0010400c034008100c03901042d1703800c03103030180015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 798781007 1250 798779757 798779767
    0x2117070903050c0d030c080c120708030402031b030a020415090207140606040902030304060c020d020a0303020102030912270a030512130b07110904050705040507050d05060a0f15050915 81
    0x609000035414508103c42000b54800142d40c0a022030840d4813004d003030340c0c00100304c080580328148040c036500275103076500d250740b01440d00d0310b0b01d055001550180d01a110f0310b0170074a41840703500291087d0210080052079100d480340d00300030107440303140202c40481d810034900207034241640c0042c08a00740b06240c0303180c00b4117003280c006140c0320000f0051403141d0308014505015803804402c840649441e481c0408070182c1600108035a60f50b4451f0080d0404d2528100101749a4190301075401200c200f019602010842c2a40b50103a02480d07018000064030720913000d0900e50081d125403031070039015208040865076500d83d20b05004242d1490b0612441c0050a59001c01c851000c10340904007682c0c2c40d07400c024050b11200100c941001c0110f00411030880498180714007044600000c09008009012031303e444032008000b03802c504203282046041c0070200d10940340442003281900c202010f040c44051178030402c0061500d1641d080e0040c8002000007261a49550440540c4042c49034002d581e26 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 798782257 1250 798781007 798781013
    0x20907090305060a0e0111120414030c1006060e19090b1c060b01020d02030a1407050f010c0306260a0b0c0c072c06131505030a060e0106080a2117070903 67
    0x7da078058005200d195400c12030042c0b0581200445a007294020350b0f68a12484000c0d0060325521500d06050030307920a681e000b0001c401940c1201c8280d82c45962000da1161a11080c40181c00316800503d6240b240c090081c400d201e510b0b0312420300c03000000c04009070020181002e05110103402003d803047c1e42c54080d900441c0d6010000d000c940314152004528061200e0002001016000d09074581501c0000300481841020854102c4a0245000070001d013004600080d0043c41070744140c0e944010b40c00e82484400e018000143e2600e0000700c040e01c9014000c1e82d8801c0f0080f001441d00849110070b2011034030010013001488080c00000200301ca0b0000b0400130804541000c445880d40445000108420390f02c5142e100c4006410380e100c0820258500c0141c64010843c540043e5018031a900e090428001c40f0f030040310040a04a00800499807140f600e251079641101014004004544d44042c9031480d21004942140041c45e1001034944201c540d00041c040540c1c040000650000050044c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 798783507 1250 798782257 798782261
    0x30606020a0507090b010519080106030b0f0a05062d07150204050d0201230c03270105180303040902190f02160501080915041a060405060a03020907090305060a0e01 72
    0x901040c0c00201000741e03156030750540e103031224040d0030384e110b03100e01c43c91540d41d0048003500c081c2c680c414810701041c000e800004040310001d200702c40000c0e0400000855900f0540305101a82038040d080759585810305061140715840428018031010a05054148038420031003001a101d41c10b81c0385c143e840c42ca07401c0c80700c160361f40781c091004564410041000389507a816940c04030198203080100611000202d000402040340844084030940000c10b03a07003802c404401000181022a1184040c48580d60a20321700282591580e000c0790040111400020b200c130251158104003c0803645800e03201c0700d071203090360440e001000303810f2207034103256412350741004840302e21168610042a0750b0050001c0007040b800e05106242c1070244400c08141180c50621021440c00054445205181814a004070b850010004000c08641090340850a54581801483d000d02d030000e00c000034003030468080108203a00a41100700344030701c03001c0010000e082402401d00c2000040000103510980c0058242 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 798784757 1250 798783507 798783509
    0x4060b0319060b0415020f0f070812030c0301060c1e03051209010b010e0f0301021204050a0b09010608030409020f0d050a020c15041e030c140d1101090210111f0b010306 74
    0x400d5040c25028000e001e40c00058808540601c041102a60f0444205a040031f0f503500b040c001c140a100c00e810101d0300c002901800300d50300c540c00c80d00a0305002818505a00007610002d180002c100700400945110301c2c40101d00500404004040b00203031151803108810094084000c10000b0800e500c6003814182c829a11171358880007404440906030009010201030718000c1d105101d641c42c03c40403034800354160f425500780f02034a03ea0b5070519081c12341d03071384120141c00c071000300b0100700040c0c0c0001e0600030b0314100c0d81000f009505041c20080307504007a400004180f54051002d10101410001e40d004d1140142e040500040e510201c0c0d4032440e0038031403c40004400c41c60400280030005507040000b49518101030074030310321601149411100a0700d0210701802c000440500c03100168000704550041178010745940100744004020030703082e030b02b038680b001c2c0d4400c444a1841d200c05001e4484c0180031440f800595031b0f9401c894000d50b5003400c8001c42c4203038503682c402c581d13056540c02d446450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 798786007 1250 798784757 798784801
    0x30a0c030614030d030c110303040804080c061936080d0e09040f050f0723010e0105070605090c030f01020d052a070312021801020c0a0612110904060b03 67
    0xa0300b014152000c01d03619400c0c04a40c0c0109507450503034211a42c81001d0141c82e50381c261068940e20300b00344c20942d94981141c081d45000b40210744a41032545005d000301e03070301c503240c20866010140714614251034a04000300c041110200140301c41040101c584121858080d9400082c0c2e010f03410006942d142c007048480410600031420045a502e41e80c02c0c6501d50b2055202124014607100382c9003050820580718468600307481082c0c00410207060b0242003580000e150790180c5041a140001100c1080c96145980e000c21070420141c40400c0303d542110350701c042d0442c111511112900003091400789039207004a182c0c1d60101d04a040078415006590300680c1180040c80195907801d02100b200c1c0305002c200031a0000016031070209030041000314200382640c0000c40d100d00380607280340c0c11200c0104c2c0c031a005010341c195001c2d40b80307400b030f80c040243c903100d5a070b21141c0c2201c2038000300104140c1c000201404000d00007000d4a80e0f507402400302801d03c55500c252030741080c00000b41050701c041501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 798787257 1250 798786007 798786029
    0x2280902040b1c0e0601082125020d0c1707080105090c0d03090504020310090c1103160309120f14010b060d0b01050904060806093309070b030a0c0306 66
    0x1004142c2c0c0300026140e000b0200180e4244030880482e5580040880301c041540ea40940e030000200c01101180102e01c00c95030303460b486a42074080701004e4141c0302d101074940d45002c00c1d80c80d8201942e4108500c1502c0d51015080c0d90183c0c003103844003007443c00c907030b40003003607007100c000c20300c0d0744402c0a00100d0010400c0400a02640c1800a000b5842c1e401d205143c40c083c080741071820f01410704c5020b041c0c0c010400500115960300340f01401c0c00c0e081001e07020310b00e4060b05046062581a205003024120498420040d40c00c00e641280307610600803d6400036010011030410100b10b0000b10070702c4c2d0884600c260f07081c00c014007240c07400c001c2040c3c0020303c03404580d152203008203030703500c40c90b081303c0c003022007110001400c140c40e01c0140c4890147c20305441d0420b02e403410101c1c4e44440002ca80d401002200102c40102014140000c650b000b00b940265120000440ca80f9801c070007801071541014a140070781d11072686031a802103003a00125503102000d030300d500142840d2601445460007501c0f070a40c407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 798788507 1250 798787257 798787259
    0x1050a0506330a05071a011a0c070e0907261c120203040606091b0816050403060c02030403140a0b130203030a1103270a0b03010f1a070228090204 64
    0x20a00d501c0a01c1000420b80641c002010f0006900c90b204031030b8078551200d0001442c3e520300c0040c0d03d402000340142c1c1140c0200032480344004512030207031840040082c004000d49400c141c548911484c02600985243c0f04030000410820352000c0c403011181f803490a0380c030081c4d40c0b29052500d0503640320035040da6011141c41042e56a40d002e00c03030442d100c482000241e0342ea05c46250800080015600540040740b800c41c000c0315038a200034000102c108250b8584059841d00c0a908050004803180d6201040c001c03c4108000303078061300b1461403a0b07514010742e41404e42da5118003008403070014aa541c45e802254040042001d800c03500c0f50083c0e0300440601c150507007a0b003c280d0700d200343c08180062000d55002034a2441c000c000311035440024009006512400031484a6040c400301e00291117801d2080011401c0006807081d80e040f81e0304003080e007169a02d000500901c0c0602001c481c1d00c40201003080354003588a0040907040403500307030300c2c401c110302251910290701c5000b5044082c4e01401008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 798789757 1250 798788507 798788569
    0x10e060c10110a0f08040f060e0a2d02040902120a0f0611210619090c03060803090a06050c0102070c12050606030d0f030c02100504050303061e09040602180301050a0506 74
    0x1000740c8502a144c100305d030442e200c504100c034403445016002807940303041010f0043d029030089501c14a03244038004800085000300102180b100c2c03038040080002ca02100e0080c003624058109070030040c000b4142c0000c11550202c860b017002c0f48800142c420401c0140580f041113040e10418040f6110030018501b840741300c00e000a00c1c5090900604001d680b80d00101d4055078403146c5142c5540e100c83c1090702010351740c62001c03000c0c115051003000441e10f0018002070246000c4205c9030400700081c03a442c80d450a0080076181038202c00c954810130f41d8203022041c001a0454000400b800c01413483c00c1451501e85040392030181d0040416000307412440b02c1400c0310741c00c400307510b403c1c0340141004074650800050891424a2006c00808030310300780300c07e110a001c4080001c6000351402d880c0481280c010720f80003071200d03005a5030b958108000ca000103000c40c0d46a805418500840c0921a02125000001034256202079034405074140e40c0d102803007201c6c0b900c11400c849500d001d00b40c9030403000800b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 798791007 1250 798789757 798789767
    0x8120f07020d02041b0e030d020f060f190c031506050a08040b1e0a06091d03040e070903060903081f030809090402040b0a080114060d0b15010e060c10110a 68
    0x3410081c00342c0d6085209500319038581c0c0104420a044013949a034400607807030004c04030090b030480c140c02030049422100e1440c0c804106040c000740060001c01c015101c0e031408a6469174010081d1003114000141c075485070340140500458282d143d80c01240366440350140c0c661002441d4801d4003801400c10070100d0540d006000d540e40b040d003003030410400e580c0711400c00c015607844202d4003c0c4589031008100380e05206034420000d90303081040400921a840a4500ba88007914400641d10f60040c80f0800c1461144103841d42d01100500c1c2a03092907549030703101001d40314520004ca000c6098401002a0008810652200f007110070310b0311035030a880c0d910f40310707002d10401072414003881551001800395110f903008014003c4024040d00c28450740d889045008010120f8220ba0120b20040440c0140c580407100c0444980c00580e1000e2a40307440c1201d0303a88010281c0d12505201780c200f50f0030f1095a4210117055003403901d1000c0c2c91102c00340c4900030100d8204103103502c29400280b00c80103903540c3c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 798792257 1250 798791007 798791017
    0xe0a0e010617150d030e03100f0f1e0525020303090d0207140d08071a090f0d09170c090a0b0a0b040f18180c14010c020907050d110d02030108120f 64
    0x50301c80700138210660404031400c10740d4010194040c441d4034640f80300900554004540490076000411203115003030381001c1604e815503103141d60b41540c05044030341001140e0009400c01a40702840701c0710f5030032400460a0452501c006005a0000f100b001800c101c00d004101c0a02d110344080c026460406030310201c0a407405040c9400f90122021150401c00014100e42c1743d0742d00303c5044951a414009040010034085407240301502030800007011100307000645070008000c58581812071400d100905926660b140b100e100140314600b01481561101031034a8024a400c010200b080c03429001441414505644007100c1110100010003170b100d420144078013611201007040c00c03890b40604003d0083c0441c400031801b0400c080d00d10904101100006c8411128001c82c24a103c172043c900640d46104040c8001c1d400140100029940c03038443c600600d100e41d0501400aa04a0546080232441e0010b040d040c81c80c5900000500441e6010480c2200030a0850b14031442c01ca50154540180d000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 798793507 1250 798792257 798792259
    0xf150901150c080c01051305070b071a0601020316060b010311030603120c030c010c120b010806090103030f180806040525120606050907090f0b0705120a0e0a0e01061715 74
    0x1c0d41d4103400f0000204111002d40050344001e21107030a02c00c1c052505540b0900040300e8500c00c0240010310140b42d0b4007510078250700607194084020421010604402c0014205411800200462489041c44031103d600450041c8400100040c005c8000750803200b098590300c001000a00420010366400240c44584900074002a03880c0e14907103281e540741d0f014849940c0701c2d550034190714994040d8000425203a2640c6a4000c0c071180c51840010b64001509441d840d821016510051011074002d11031100d0101880c5451907841d1981d02c1282c0c10340d025600801c21542041e028042400f004111048200b01e4464908450340340a0211209494181c45105a00c80c1c8503c1d803281403144c0d95000000910010300400c00318031705030703034014144140350007504042508601c0c04581c0081447c107132801e1b103900c10000c01044843c202c860316283c01c510f80c039200700b0040f402c84070069104c18242d4001002007103007040b41035041c650050a0641201ea50440041d10041005a07640c2e11454003c41404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 798794757 1250 798793507 798793517
    0x9010f0e060d020a03021c060f09032709140115032a090b0c010b1905031b061b07082b0804260403030905030c030604021c0b0f15090115 60
    0x10510200305004c0165001a6125070200b02c02145018943c001ca00c2c00351056000f00041800e40d840642140c41401e40135000420800c41c0e10960f108070b1070003050300641c4620007501181c0c1c40b04150103a620040c0e000507a141484010044030010317050002c03c822060900748040e440440c45541000003c8000498042e0a0302c0b5030065a401074940401410200803850703900e19160045602a040d0121018001c03604160381e041203040100111080d41e40c0140541801c0c544a808804040401701202e0392001003003203850f8007004200e2100080d418040701a0801c9072a00c8003c6060003521101c2405400c8020401c0c0914040982c100580f00030608201c01940c40d14100000c00108107035a594201d5018082d441d00d40b19410007510449100341c0d940300038103844005040d03c500d0684a4183c065115a02040c01882d06403600c0b400b0741210610003000141544503200d001c001036440428186059041c040462081e100900343d403001a00c8108040d49048a03451914960390700003000c100c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 798796007 1250 798794757 798794779
    0x10501050609150d181218050a14130e0105042a05010c0816030207080c0103060e15011209030806090903030613023027060601050f071208040209010f0e06 68
    0x3d0b009500c05c070301009210440f0042400302c2d1038140303070041d8420600c4006c1a00b004e4400650b00303e240282013a208041c000d040f0036071414074111403194401240700c3d4428841079405c1109100da102c0e604291078040c0020546041c1400c1500c40d1340c680411420902081002440d101070f030203400c2c0340c00c40d0b00030b1034500701d81c0b000b9003802c9100f03018420f0003081c8042c0c0c0308202024594001203503401c0d101d00d2000d07a02190605070043d4115030441c07040c91001250207000545529080310041d03511201030500030752800200b0014002c0b0380300b00da0201c002c10903801c1484040d081030040300fa4002540c000840c81c0d17080403000a00654081110000c806400250006425181c0703003110040c40070026074004140805c18050780c4903c4106d43e021410460300e000c5074000b01c00803078003121030076000c0041e09017500c840c0011074044e48422414901c141c0100803100015004114000b10f52040faa10000d0505040c0304100c0241e006a0008002510a000604c01e0182000f083c41c0c10800840c0c4000800c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 798797257 1250 798796007 798796027
    0xd03020a0206030a24050a061805120f060117011d150612030a0206040501050c07120c032a0c05060906040909290a050f040f030f0908070b04030501050105060915 71
    0xe84171451100c8403014079000c9040311003d1145010050b56030440e1700210a80c0c484c80d040350140c40201d00f02e107804144010400c5a8203000d04145002101d14059405c0c0ca0940b4031071600d000800c0e4851001d1495040c3e00c1602c44101f0b01c1000069100f015600e56602d40b8810000d030381d03841c40b600002c050400140440c00c03655500c85410700790103200c01525152803603488061b4959030207d60070303211075083c04002216a000642280c007440e90108107506c00c00d10000c0b0843d50049100000ca00703100c840050400781d204103140c10303c242e03441c603070a900c001c4015190101200400da8000340c001c4c81c3c240184805507440c4020b175025900c1d1030000103242480c41c01c02c40c030420180f203c05803440a041d007140b0001014040002c1c401c00800c8003d0080d40c40e80003079030740710090850b000780c2010015150000000d1107480c0b207946031003951504520803600e42588a040c400380703510610741d404000404004016080c06440e0040004541c0c007814071810b4408109800e0301031840075450b5200040701128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 798798507 1250 798797257 798797261
    0xd230307092120030a12021213260304120602070212160b04050a140117010b09031b0303071101090803121015020c01050c0708031603030b0d03020a0206030a 69
    0x52a22000c80000c2195020150003060030749503042e100c50703200100d9035010791202c6602040f1030382c01038010700c034009981c1c41e001c0c04211103074002e2007107008409400045000304c90240103092820320303000010b18170b000104503149080001c0502c03100c5101898042480340802540c086807144100014920824500780c4020f12801c60029030105040040d603039a0f140000d405048101007500d0716241e103840e807882c1c06e03c5008901c03455900c119a42000d01013040c40c0125100c40ca00181045459075145c44d1400400c3c0e0705c26000036503441004076140241e4030b000c002c440d100c001050000844a0303107040121340c4901c00c40101900c040100c2102100304d912500461000b020001d00b9643c0350464120070341d0022200b69040107402e0351480e0041850207042502041403140d50b001024142c10f05070040d1500e400a0740c5031041401000000a110301051000781926181902080b4041a0a190160450340380b40c00d41d0740900c10805003100040d400217200c2d141607030100c40c00c070b449030758000c91200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 798799757 1250 798798507 798798509
    0xa0f0b13020a1d0606180d0816060b0306060a05010e102a0201031103060d02130e070617010e01031a0c04091d150714030405030f03090a03020d23030709 67
    0x1412510410b4005040b01c4000700740396a1070040654002151a90003c201c024002e030001190540000b400c40425450b245907001e214520600c034681c28108a0780740300340c0d0342d020768500384c0f001a100c00280210f40307800c2c8002c0742d121204803003190402d81400b00003048410030b48800da0041480700200223404d4003400f541c1d070b00191300c0328800394012841c000b41c00310901c1c2820224003003030518084a9001c00400c01766886010042e008060a203480c0c6c003000300070715030302c000300c40500d43c4c0b40d0940070101030500c0380c0d80107400030313446042c1c4644841d5906001158164000c05296000340010710010754202d200c8049601a4500e1088940b54022a40c000344110b5002d82d044914041d400300c88072006081d04840a5405815a0302c40c0d10b6000e0410f40c859812115103001501800310042a4400b030405580c110340268122800c1c5a88032004440369070003940e4408180e40b06a248170704240d0304101c003412102c0350f45880a440307501c1d070b03541d00406005600018103000021001a40e8940300d000c401c2c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 798801007 1250 798799757 798799759
    0x3020d0f08010f05040905030c1e070515250602130612090308010b0a09240f08071211070602030c0310170a02060d090c17010e01020903190804030f05010c08090a0f0b1302 75
    0x603954110151111504801c00030440d801ea0003514400103207440c002410102c1160dd140c00e4501d0304e04410f50001181480200e900e280580300100d4001003061440940062000e5503040f00c0b000e17007401c5020703005644103040c06003003508019584000a81c80700d0b80034112100141e03050b03212990414140c601602580162100e800410050f170b0351000d034180c070f80d101c96045032605815035100f80302c00c0380e4070384e021644c4034003090000c42404200c1b201c4c0d84c05021000b281000e0b0300d051195513a180000c1e070380142e900081d00c181c00b00034003401c0c449149411004105aa003d5075410b400300030407945071440c0000c0a0310802000c10503030314441260308205d0890307174000c0c07500944070384520789500821071720724003070107a0b43c03034003030142d02440051003161400f902c000c00403c0380d03060300709901c05c281340c24010880d00c1407802e100c0000000c00c00d0b0034945006201d00b00100e10005000e500411107040180007000303035840154682c020911560a850f4000e0f00100c070035419541c0c0344400c1c02c211500c1d0b0310003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 798802257 1250 798801007 798801013
    0x30a02010810180921020a0308180f25060c1506210525050d0302072c2214070b120405010b0315010e1b0703020d0f08010f05040905030c 60
    0x20b59400805a4091102e00e44501101c69101010b6480300f0200160100c00c0400369010540207c0800d0249403181e07031004250807659048051504110f0501300c110038590717080d92100856811420303007400450b0b2404a2900045c0c0841c1c50030301c2c0246070701800d000203400d0303210034080800040c43c1030300080c000e85244050155144c0c000010071030346e009800d10076181c6008241142c1107072540c0c1c001d8540f00d0130030400246045410f0808100e9094440d039011825440b51070800608141011547e1113044c0300b00300e11005031900b660f5804101840101519540f0305030a030100b52059841c400103120781d8102041c10310420f074025406107450090b4000160001d4080740c1c04005225030800b5510031441800207010100040341415540c6210200d5002001c0b040c10060106c10b8a00444036030000b40c481143c484140b440480110365400200240e0041e0403003003c0301400c076002900e802000c400da00d49804030350302d007050b107150014240c02820b12503501d560102d01408810010382d0000d0b1071782419 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 798803507 1250 798802257 798802289
    0x70210090c2c1b1803010b0913120e0616030306050a090209030c0d050a0305031b0d02040801051302060a030c020109151506050a0f0c1406070504091a030a02010810 72
    0x1a01040c041c2c0c0420700d61215451000040741c001000803845405032910041504103840c22200d04180c0c25203184041e01907586901c8891030f40d503000035840c01000f16500302c0803141c00c0b40c00c042e80c04450190b000d0040c085548100030003502c608003124402c6815044032851408149011405001d965100540c001078890340403840c040c943e401003607880780850454801405020900c46400c42203600a0490303000320303000c4c5e030109000348000c43c0d001c1d16510045504e6411000c0b48803150f0070050b1901f000d82c1d4045428412a03000344a0741e070300460306a17004506102d45900258061090440407010540c0b21807203140c19a000350807020140d0780c8220f441035440000d20a03000200301e1a05213054185179400c000548502031400c07500c8512056441081c600420301040e0b817610350b21101110b56a0710000c0711a8151000e200f62400783c3c0d000d80d038082d6a640340c4001802600e100420b09140140300c2c0c82d1000103540c00003140e208032235080c02c2c60440b6076201c01c0c1240445000d0741c001001580c0300e8403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 798804757 1250 798803507 798803549
    0x12270d0305150405090606040e030c120904230601050a050405090901020702010816050423040f050f092b110a060207030828050a15061d010206070210090c 68
    0x110074429910141d0110b4000b882104000c01e9900c20313101119980c2040c0c2c0400c009042503000042695002c0c0f003128a030290042450f03203080320340781c00201c4028012401007010719280c0500c41a1100032800d035110101c3d03a03181c0061030350000d0841c034144840014a208400e0080c0140d07802803000400d440914070300685030b94040e500a0100b2400250504005004400c043d4245040008180d40349410f050030300780c0384800f8010f007544011500d0000c030006140e96446c0d00608660044d400c0004c42d4a00b00b9010701c02180340050485074803078219440300707182d124060038070410781c0207440705c00300450b260350000707544542d5100c2c2041c0c543c0c0546441c80050003460f40050620718420780e61003330725594220b5070a00c0d1000290449a00c1850120f140142d20041d402241e0002d10311500054440700400e080c030481d02c883d80c4a58085007540d0f030005907c100c600c02d01d1400c00400c0c00500350310b18013050001e480d003941e280f90350350195469121100380108842040050203c1243d0050071206201b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 798806007 1250 798804757 798804761
    0x207080f060f0711061801060302090408090a05030f0a0308100b27010c08041202130218090a0908071e0203010f1409160b0702010c050106060503190212270d03 70
    0x54100c070400407100089000d061248404c100000200e2000d401c0988400070200303c00c1020151054a6649412010015a81e08040716000c1c0c1e224040c10780d81c821840c028480284245d91045100380c0080c0e8901c90705010204500d001c0581c0361a00403d251f442100c0c4208410854104d510b407504003180d420100c0702c00c0c00208204680025621000001101c011200e41c03480318070050102c6800d00003089840b40b0324003c60200c0d480205042d01c0c415002d004501280c02009980c1d502c192120402649800c100c013080790400348200d402c2c8204170280d11040400e01c921b0500800e100b1155040d4212100300b141c0d840b003244e034007d00a00184c090401d0300c00141118407400c220f143c42c180c0200e0b01380280050b00c0300001c0101040d000b40540b038445c02d880182c04c45c11069040c00100b911100016400388941c001801d000c5d103615848e41004806000900824504079849174410068405440c00d18403038168000382180c141c40100d00304400c040783c0c840c0e1000c0401d81a20400c0c3c01003540a402d9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 798807257 1250 798806007 798806011
    0xc060c051005161e021c2c01030b0d021804020111010203070314010503191b0f0b0d0b010c0c0e180a0303140a020f040b0a0306120f060b0a08030d0c0207080f06 70
    0x60766400a0703003003000c130f9007440d00501031a456015a0018610200150007100140c14004650426020728415036290300c4a80000700d1102603d0b011100c600403039503805108a0000d60783c00c2d90300c0b5a01800c40c3d804141a01c40c8901c81c10300781c0c1540780014085a11450400040705100e070000d54482c100702c400940907180340d400766600b4100440001c61076081c0000c04880d0610030b03c0d48a54059080d480e0a40307019240d001705040b60703590080118501030522a200e00030a240d0f0511a51480c1c03000a00701120168480c0d90304000000c05110b0214012040910a80300a0f0314402c0b100d86400c9500d0840768504e229500725400345d0510361041c90f41507440f001800f1200d900d500b055580e0b42604004a101310841c2e201900402d0005204d211185805403525801c107050000741243c880c03000c01d10541e030003030003100c09050000f10350342003000340d0003500f40000e81941d24611042c2091030030b41d00ca0084602c5600080c0c0e80d4003109208038400c00c0401c000f0703c01d203030507119a1aa049030040d260001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 798808507 1250 798807257 798807301
    0x290a050606090612060f0a06021e070503100f021e0a12230c04030209090d09060507030806060919150206090307020906091e07030f1401030c060c051005 67
    0x5810002001400d120301101d0005200511291500c94030709034051002c403028218030b0b004003d00008032095100c9402d020301409554000304030309907089518903020b40400e000c41046401c509020001510000740c00104118000008074421004001c00002400f540030510344154114010041c0354900e000100380615140d40c40740c1611340c1c40785805095400c000400b4894041300c80c0b409080f00d802e2408e080d0826980360b0300a2a296413500011144042076400260540003d1401d0010b107801c1085800104501e041850801c100c980780900000d100805060184500140d074100301e5881e80c25030700001d5440700d036040c0519260188040302040540031040507206010100b080c03000008143c0b0300c0f480d0b005080000941d80d50040c03008014001e01540000a14003038000c2825941d6452144140b019503400202d14800da45140c05691000c0c20a0281c200040c0060011030008610070041da8071500303190500401c07500d8000d00e882c8110341a100c10a2800c3c040c000e01d02d004c11907008100354 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 798809757 1250 798808507 798808511
    0x201030c030501060e19030203100c0f0f09030816120509030c12060a0b030f0f060609070c11150f0f07021801060c060b120f1608010605011b290a 64
    0x300c291001e60071100c1c213014220200e4407500d0410501d02d0541c0d43c0c200d403100f014801400e9030f550f0703501081c90003c0c100d07040007041392a4241c855445511115144500c4203074a41101c2d030441d841030240c507920041c0030103001650b0000312080c010010008141c0540d90083c4d1185054420700701c0106690064610a8417a01400c049174820349084154050340c0c034503241c0504440c0d15240c00d8180248036a42000340c16000d516070f200d00c1c01e813080c40040040710b00d04000d4819403800e00100300400000509190601032029150703030204401251005e500b00041e150b40502031080220100540a038070003c66481c1c0b000204443c4100c0c006000e01041ca10a544081880b031025180c1c0812120900078a000100080710141c045a5103401c0058900c00c003030709908000b40417044150410b201180303c20902d6000c40e458080d42003162600310300500c5110020482d103420310000809001070118107116580022381c0b05000c0c0000003200c00550b05403030301c8600f248a00d62002c080c1c560412101155694 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 798811007 1250 798809757 798809771
    0x70603050606090307180b190617070519020c120c04050901110f130302090a09050606040c1709030c070e0405160e0a0f0f0e03070b011a0a11030c0a0c03020103 70
    0x1c209001503903c48074008000c0c20540d07003040d01d8141c0201040281005958850032124003d031944050501c1080740008004038076030400201520ba03141259140560340311690810120650100035a82d171021040204000c901129408034600610701d10750700d9000002465a540c10f0f40002180c000c800000e803018401669102c64a034201c520000740f03501c030030800b00243d001c01480c000c010710500022049118141d81c170381e000710305c25607000c485280d1b0403603039903880e42c06100040100c0c81d030201e0200c6e002c0c013041c0f110641c0208140000584510403168110101300f0741c603824010b4840505c01c1c50200d60b00903944814405881e00c1c1940c040c1d81b039015007081c00c40b500d0403810610007a1444003201001d207444001c00c120090410290b1196407560340d4100140c01100c030300810550520782d2000716256000d13400c02000d01a01a44030302502c1c0714418820408220b46c07016a00c2654503400d1a8060160110346141581f18075048150680504443c14003086803054540083c1d90027070360100011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 798812257 1250 798811007 798811009
    0xd080c030a051024080f01050a06080901110d020307180b0d09020103090b040f1202061b21010803030711010603150209030f0105041212021c1109060424170a050709030b07020706030506 81
    0x41b040138060300d50007603960202400f080d405800615002840003000007000829441d0390022900404032414038103400005202900d64410505060407e9910108001600d000382044040c45403604001d14070307403a030110b00c0a40e806603020b840b08940040ca0303800c040c64945080340345001c4101c01250b501c42c261000d182c0c200d10000d8500c0c440e03940c000e1640320b80c50711448132895507005503d00da84050520a45c40d102640d500954600800764000150b84038101380101815600503800b501100303030700d0b20f4000c10100c0c5c1f400c925805011188800180d4482440001c641040c1c030f407a003500e40d60360800060108001110200701d06540107075444d200c2c0030a800d41e40c00164425601c00c580d40441c0e400840c0d01c078040076400720356010b2410300300c1e5113050144004209280c0003a400800109040e001c40c921505642c4071182c0010503070320f0134280400752904c08400b5180b004d00310402e6145e40c0c00004140c58014801c100c051070300941508400c0c9481d00009561728554020301d00081e05202c045899 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 798813507 1250 798812257 798812281
    0x1e0203012c0105190b190318050c040b0f15031f2319170c010311070308130b0f06180106021e031e07050d080c030a05102408 55
    0x16801d014011007005900e8181045414002d00500e5040296804000100304c18500300400c04000d05d04151009000784100c0030301141c65000500030780b809400842c0e0b0014801040078028103204031000a034814a0300086402c07099035910b4640c0041802e1645024407080d100a107100d00450003401f218401141d8084d212100203104105004002c451031304500910f804690864072000390041004201c03070800410316244a0b88901c680108442005171118000e00178181012001e0030140440307c5c00c080440030a224021001d4200524a404075004600704400050400d80100a01025042c11149049085400d40d280e91007080c0905005401c04198010141290f07243d0300034143d81d519243c1500c5403000c01e404580710901080062150861404044601502c0300036101034540c1000e2801d50303c0d1500d0a03054505109040f4100315031140002e080f00c1d4003249a500108140e160824101601c4815800645822601880018060790a14800d00010100303940e00c4c1441d884c0c544800300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 798814757 1250 798813507 798813569
    0x70905150d0209060d06051e0c041406030a060e04150b09091b04150626061507080706090311190203030901052b090c2411011e020301 59
    0x5000308202814401501e032420f0700644c0000080c1800041c5003559882c042101c404031600c40380c00d0701000c0d00301da08011502009902016001040d45006c0c10800401095121005400d1084030000000390022801c2c0e0440401040c442c2507928a0342014070b001500e1807208a00c9555030341c940b18076190f05141c050440c0c0e0155611401070441000390202105009440d8056950460340b41c004190581c40c24024880003407980b0741d81c3c001524079494a4050f9244400030044034100a80c0034460749590704200c801406922071812036580f03006107010001401459400340c005441d03d001a070a254000254203040010301c02030f40c041020105d0a1480c10321600c40181d0194414004619994050340080c105840701190001c21800d4085c1610501030007140d01503081d41d20303142200304100e4541c02c801c000e481841880a0030414003400c025044494002ca03008000e070662110300c01c0c980a5001c07881e2001c01240c0c40031460030440c6614042d500a10807010089454140c00746a000c03103050602c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 798816007 1250 798814757 798814759
    0x2603030108100f021216094a0114010c060e1608010212010e15091501021504020102030306040911030d02150a0621051e0105060405010b03010f0b16020307060207090515 74
    0x701c2030388448403046010085a8800700a019031004041088c5a00e8000c0c4125036001c0c02c0b24044011420150340c0700d08500c107030f41041000400c201c1440d882c098807042e905480f446815070907401c046400407100c2c038500c001e015062514003035000003512004101440d4405800719034010365561800060300301e1161a03071001803504e0210050105400302940d0707580105804c2c5a9202d61010400018000e0300162500f15a002010350140c2465806000011500c040040085414901500081d450b840000d003401c1c456903a82034511b0402100e410a1180404003804403280201180e402a60b240500c1d5910301101c4503440000309109203900030a010780d843d254281185da482500b1605104105079800c444c01c1c020444064a10200349100300380100d0301034000304e001d041c40020300c4111070043e040000482c02c100014004900c44244090445504901d06030350303280f800c00c8014000210010003580b40c0150b040001f80164005421800c0d2020010b040086403562141e0034444100c2c00001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 798817257 1250 798816007 798816037
    0x9111b0c120d0207120f050741211603030315060c12020712060506040510211a0a0c02120c0a0b0c0706060b040807060c020a2603030108100f02 63
    0x3070003030031003007619000710510901c2c10f1003614540707940d0725043c5001a0803000031242841c00012280b54440449c0721900d07072100301c07090709540509200070b583e244040024000c1c40b884031850904641641400c10055140044d245480849102286031004a101c01ea00090400d081001920284482502100c03407070b0310340f00c1041c5030640d203e404411520401d0000c0d805030950018011841144500c420b03807062034002214689442000100c4402420007421040300141c02e2100105071600c20710403540c1c102618034540041d00d00040c43c0f01400100d072010141181c2446000c210a41046d00d0710724040c0c080d81c09060401d00100310601030b0010070316641d8096070401e8040348054400315040b01324441c980b0310740035158462405540d01d55000111881e0000f0b02080007250074492100506041c3c582500c015626800240309110940181c081c102c0707401c40c01d000009103100ba40300e101503080c01034030348030f40c5e484201c103845801c0b82c0600c8400e5810040e1000250f1940d108031140350103d8215 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 798818507 1250 798817257 798817259
    0x3030324030703060e0601180902010c03030e07080a050c090912040608070e1f0e06090105030a0e07030f050a02150306030d2307080d060b09060409111b0c120d0207 72
    0x40c500312010103038200da4260040e031001002140c1c0c680118000941c07014000e01540d4900020300c0000818144184011490901d6010060380d00100b0300309000e42501e40407805801c2c805641c1d041031141d03400200c091041c00e60440c2000030100710400c5610046490085654400348590340780c0c00441c480c0d07010484d08000520055004029086c4c00994600e442c682000b820030214111541e6444c903641024410a0b000c43c000364441c2d95006084429194a03040111a10000c0d02d2400f000e002c450350f00740c403403003c200a1441000354000443e003001040e49011200e0922686642030164203030301071443c2140c04480c0c841c40b40201d90044e0700c0580100401c12a00c40c0464028400d0800d40380c81c03120840442080110740e4015203005070045900c25500c100b20691402229090303449129404802e000c82c41096075007005550854070154030100d8116000480c0529034884c7e8450104039072102c10281c1c500340c0b070005e81c80317030552007da804c4601580044580c42e0b442e111b1020301d400690100e48 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798819757 1250 798818507 798818551
    0x803010b070501061208220f050d0f1b0905070302162901060314100f05091e010b04060e010c080406030c0c06140f15060d0207260414030303 62
    0xe00707107030340114000a01d40352121143c00d07181400d5901561540e0005c03e114200a9945c8030b40c100600d00381849a104a2a014500362a110103209043c880e041410302e460510030303420b0764120b1503548003c09a0050325040c1444a01019500803103072094984000152100e00900c201c986900c01802d1031a442260340d80e42c0440e941a200c110900c4200c3e24078212150018074008a020341203d807004200c04060044e010110b517402002004000b01c1c403c410040da4841006100564000f598806455902c140c6070301261044211260480d40103540005880001706026000b500c04607a0303104d40d405a032800441e10308046802c09000c1e039404100400090307020350b0181010280c0c1d070610440c05100ca4440d20102e5404000c0d8002c01f601c15002c00030003400b0081840d60102010b09004550035240300401ca030f0f401404c14446103d64005080428844c403907240019034903008c2e4248411542a420401c61078000348141c0300c00046131040410903103408800d0701d100d43c244c0a180c1c0d843c14142c0b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 798821007 1250 798819757 798819779
    0x10c0f0f050c0703022701180e07030b0a091b0303030606121a0609040e010234050715110a0c060210020705060604050c0f030a0e100c022d01090302011401050a03080301 74
    0x1829407044810a031103880b004012860781e0023000341940320002c00d0f00c030058880503541402c0c0380c1720071900320401c20710000e4240c6600782d412040d108000a07290b102480c02040007000700142085070183c6150010402d035060304400f00b603c1d55079a6001031342410402d0315094840358000d0f46088001900940c2141c1401000b4000151004001152114601c46030500b20303403100301e804400002e001040c0e02c18140d0341468441d41034041048001040070b87e21451784411542c05503500c05028903050141a80c415840c401002c51020140c8040054625044101090038071640e009801160050010290244261404990060083c001c03e595220801004103030003802c1302c045520612100c0d4103240d195000d144100400c5400103103032128030004618201300240d04410403414250b001020b291301044200f00c03025040117440188809403c1020f41c40024620700d051586000607100030305505412890309045103d800a21903602c40042c0110b41c10240405805080c0800c0104040a098 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 798822257 1250 798821007 798821029
    0x19030f02040b0d0609050c0708030703020706200c0601064d0f0c1c0b040f1506050406050f1f2705120607020715050705010c0f0f050c070302 62
    0x22100500e81a25140741c81100d400c541680f200207a6222000e10041006104091300a01040300e6982410881d55403098035200080004040580120303030f0301d0030000c640c0c0100700d8102003a07901106400d1150001c0300150041c2c1c1c000c5c0308038417544000241807801100c007900e05000c2800c04410444541081b55a0010301641140039401000300c901e04901000c0050180c0040d0600540035110f1035103007981c42d01c0480c800d81c5204450480e041c254030702c1001c40c0608203586c0100712000c2c81c0d5640c01e00c40211950030401030203204420b0051300710b140303a45d4070603010740e00115420446151140c080c0149102c0d940301c0f554012b140807201d012003046d17a01c11100c0602c4549400d030011040040101c00c82e1b070414502d00b00d400d00300301d000e000740d1403c01c1d0302c1210010301000405051500300c031f000756902c0c014031440030a690541c0d45004c4103031049085590142d0024001e10a4030040900149607210b05044e000c002410302c2500720390302d40714508895100d0036400041480e10b0071a000c102c06e807550 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 798823507 1250 798822257 798822281
    0xa090b0721050903040302100206100504050601030f1e141b250b010e0f1308030702010908031609050a0810150513090309080115171608060402030d051903 68
    0x4401c50403000c0d00c01c50300507107100700d03001d40165032140e246105208100fa2015003140640d00036008201c0444603280c03c8800702c072411280807615846420041e1b00500b03030900c000c0c0c400c0382000e0040301c1603040038290090008985008200b0b20902082070380303405c031065500c105003920f07681200d000071440801034240f0101803061406150303074a111400e6900c11241046031780c084078000400c544103280c01e8003a80b100e00032084001e64580104090541200315400400e203507000700214401c00c0c801d6010006013030340400c002d5642e0078407410403d00741c21192109070018a08040c003044c40e0512400340002c4900ca00010040c0003609040440549411440b910309280e64000016069480f0015003030041d8645031b0004c2c1044d01800c00810024081e044800d1981c101450300b010860a004000c081b50580c8036243c41808062403110305202d0107000c0322860450a0703038085030003a400302d551806a0b08c00c80845e4540102b80ca020707501130141e0134148449a00404a0380c0c00d0710f001b03411902599035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 798824757 1250 798823507 798823547
    0x5040c050f2203060c021506030d030c05130305010609112104030e0a0608191b030906060b070b07080a0c080711100c02011e060311220513020102060a090b07 69
    0x340b91140c000124807503610990781103031900300040302c0c280c0500280c580c11300b41c20000401840c06a0200355100b030b8078400030080550b03802070080c3d0540f25a050307030880113812041189441c1c0c1ca0a040d80601a83d01688160310300e02580c026074192050200ca0355099501d4006c0d2640a41d01c2c41c0d00305040005005806100c041560a500380d070302c0110076400752516440c2e05405003450340e00701d01c0c4000c0e003844911000b41340c480708008040b85c1a200844030f08081c174000c102c0c038100317107000d00140c08203500c44801114040340440410809074041e40c0f2400c0309647e04616544c80d91903c01c04d480302950510042100c5038007089045114400884450800000b140c4d4824000c8401a08541029140d0710041c3d41d2103080d03070207180802150240c03890180390107210480c199100d403901140702d1000c1e94030584030075041580b00404c16001049544d0155401c00180c5001c8c40504110a2140000c81c0140120340000e4106081442015410307071b082402c2440c2075135028000d0380c000043c5924044005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 798826007 1250 798824757 798824797
    0x8040302030d200c0303182b02100503100b071a0702010516080c0d0b030f0f2d070e070908160806010b0c0a0f02060415110705040c050f 60
    0xa24100a590220481c5540e0103590180a080b146241216450320310820b41004d61004240d076000010341e0107e04580c1c61000000c000100020b1031800c02d1401d031840501700c203076034001080000c4810f000880c020b540350009030459031421284e601c01140c0000700744001c204240001c000107400b0300724541c4202d900c015454035801c04007100c80001c99940307005039111001c00c112241558000c41e222a4642800112400c0a9030400001e0143c202c8803409260b48852042042c1e0702003080100d03043c55407040e00c0c82e5203c0e101e240d68940100c940d800c680810641d06405c00e1062080b003400c00d1900d014050848281800d80054941078080e0503002002000c25020807040b80600100300d100051140010895281c180c5d40c600700380059010014825040c0f003201c1c4000c0303000c980c1c1841c580c4d000c2d0240c04074681610006106000e0340d0880d040d100c00c0b020740414815000507104031882149000c4440307c40c1d0301e00401040d2800302803140005042884400b40507241c92000c1e206000e200386100c9085 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 798827257 1250 798826007 798826009
    0x5030d051306020c0c12031305040e0a0b040c0f05010905090f100f09050f070804051f090b0703020901021029121f0e07060c0b190203100501030f20030408040302 71
    0x70340c110303089903112508101450b06580c81d0586c01381450b0000040036500742000311611124a400e64400c140c010703916420320800642e000c1c4120180698011205441420681044030300f0000900410700e21028940c80414917600071940b8004403000240b072440d80380e8a58522040180c0050b15603611805201004500c0101980142c8064090143c00044034600008102e074211740c0034050b41c041c04090024000445d0003c2001d041c1b464103d402c00030018039a0b03200b03400501410002814102c4803400b80050107074950001d02c07032400241d084507411000714050700700302c03400340c407407255440401c070350f10003015401014198807180020010321454a03101d00c0b440c18040d01c0c0c201e13031106503580202c125249c40b40f880b85201b0546940000c1c00602e0401c00090282074101e04094584e08000c0000f039000c00b50752070300042d16209840150740700e00f0315281e2808204041e004060100341070503400a0114040e100b2910141e080402c0d00071000d40d14107100c20180e00241007580d14842c204804005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 798828507 1250 798827257 798827261
    0x110315011e081b010e0402030c030f070e06070f02090901050907060309062304170703020606060313050a0b07170c0301090213090908120708040302060a021305030703050703050607080405030d051306 87
    0x1c910309a5684403c00c1c0a880005010b4159100c24510031403040c800c0c40049000e4805680e030110030f0301c60a13040f03511442d10964120707403d910080d9003e040081c2a20802c0616640e03490601d10a84103124a5260b1040807800c0c0c600031100d002c000da01020b130400c8002c1c4680c01808010b070050000090078400d1240d104105400a088450b00d0300030308007448204400c0c050841c017403013a080c90310b03810600c07aa68003e403600d8000e003685100d42c2011000c2105485040e0305014030301d9204085803406900d610380800401000c59800d004514208006801040041c2446211ba183c14107018510380c00c1a04080c02508085041091580f034518041140176440c412048840c5c011262180ca400000152580c0980000d0031002000b00d4039060200180e00003501c00c0c0c018404403405070300ca015028070054100d00d160700c840c2d030610481e1000003c0c03140200e2060f040d130340501d09a800d01d40e1440416619081c0c01e560041580c3e004201071002c2100c150301040c0c010704a000c3c03201c420301c0651280c0017 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 798829757 1250 798828507 798828523
    0x916050405060301230102031201120c0b0a090602010b010c02030606060c12040807050a1a03060d0809030322060809151005040c0e030c0906181b0c030403110315011e08 74
    0x3030070040c0700e61030082c035403c0c041744450380400b4402103103469407030b1400b4420a00188580030b92880c83c0a06002001082c13403258003d401d2102c0100d45840f24800002e202152030322483d005035280500112255100350760140c0b800350081d0007040c030760300c0d640180001c580c40850019010b000314100b2038401c90f0100d008000514404009080b050f08040403c031038146158000780017085220814040300403c007041d240d118204480040310b10a02d070408400e80d108407000980d06000002d0007418a6441c000b1134650140c4820034070102544912003902c10850503603014241c1d50000c0546011317405196001e42c2e00481800f5005081c90352140400c064503100b00080c0081081d00030031004034101000703646800742c401c540c2404141030041c0892038841241c0382c4214451144000249240c550004408090480200c065a1224410080c0f5241e42041c0000c64180740d401010b0003c43c60300003000401d407254000101d49070b03460520980d0b1140c001e104c4090840c603800c00d00007000388003404854 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 798831007 1250 798829757 798829769
    0xb1c17131214071a0d0609020d020409060801060b0910050706090f03080a11040605090612071107060908100515090703050714070804060c15050c12090c0916050405060301 75
    0x5654221902d400800e01031248a03601c880e5114590412081043c0e605030340c0100c010040e402da5443c0c0d081440c0300600100e412005419000161403102c4000982c0104212110510100b0029880b01409401d8800c0c5101704030212405211844031403070040454400310b8601e08200e45014215500c2d00c09840038614261101072105003000d00b07054010b0074203036002c001c0500c02c1080c2442141401040c1c001d60081804109010402c4207480d11200100c40515844000300340e00c45c50520402000401e2941001224ac059001d000600d20f0080b81c0034403e40380e42c00041d040c05490361040a0003008000c0080b81915010b803c3d00140d6100d0000d00d5014107030301c0c2d801041c10b2600001c06412100c0e0802c00260036001044810b010808540035202601e01c0f0340b41004240782103080015114150310044c04025140000f880640c0844400500c0c081500170641c609a07981c02d01c40a458201c100d8a241d000001c030800524241d00e00030200d11804107604041d07040c1900c2e60301080140e082608a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 798832257 1250 798831007 798831029
    0x11060d05040f03030e03090a060f020a140a02010f1d01050d06031514070918020a020111130501020c1c062f2203150c02101a040b1c1713 60
    0x741070613814020554180360440c0258509a06c11022500d40d000520403001008071480401c03640c0385c42404501e00799500100700140b941f8814001588074074805100300e01003500720348c0c4243d400340100754140c0400213081501418209800054859a001c0510382c1c2e1038035904c000100004140310341c3d82d44035513002000010306100e9010302031503d07500600103e0034860000d00030000d0b032a5042d04144003045a400160b111491120141c0c052700030110a1440d080f008540290b84580a9092504440c801da003100c0c60350028a0912a1042c1483c0c0d0000758009600009004205290400c0d01441c0c050811003915460201d841c50046610210100d00d01d100001e61045aa0f081118000d04e400100c031340c0c108040c40c41d500d52a607440c101402c135450035251741c0c024010900074050a400c44180c407400703020507a5480381100038141000d01c018495403510710302c81c0302410840140c000344410720f40c524005180e6500c580d90175614440008101020401481401410626800008050410340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 798833507 1250 798832257 798832283
    0x230301060b0a0203031902031506070807062a0302120a0c111209130b090f10030f060f0c03090512070c051302040305100b130c1e051e07020d11060d0504 67
    0x4c2c1c008000180c0e04070b28064010b1080c440741d20016400b070840344002b162202da8400390303850800b013140240c0303401824451404000224a4000c583c2031460b80c00f0040b0540c01410000405908901501c24903203812402100011540c103207a9004918452007030800c88849009912003070311707110319a841848907540100720b4900c1360a100f0300c50600400307543d2040c00120748039030210342c0c2d9420003030010b0220030070400800c6091546428801c06581c00c0b44072928500340a040800141c506a061040203170301d000c1c02c0844041c480e00c142003180c0d502c0005828900c11000f180f001940000d1001c0e0f4200c004c1c4030300010182e0396031403010082e0080c000c1c050384940c55401e1040c1003000c4400407880d070606103040e4508542e1400c42612140c15004070003c1c000790139000446410328140080110740320f01c0112840c4c0313140c015010307140c00240842100b000c446e0b408035903086806010402500032120b002440c0002c0e110711640cbe5200c6c1405080c0714108503180210300b0654000b42c4064413407001c000d1f6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 798834757 1250 798833507 798833521
    0xf020a030605030604080d090f0b090a03110613260c0109051921110d0206180703020a030b1510180e011214160e06030d09230301060b0a020303 63
    0x741c4401042c0482c0949400d02c1c103900c49061034072400c907001039401d80c0c8004160801a4000c0e2115840c0e401005400740340c038000e40030b40d81d5034000010a80100f070791035511110304480000c3c1302c7c3c8500c65998401d41c1d9040b1541d0380d05803400c401d4003181c13042c9955a0000ca00341c01c22201802e00603826100106001841e070a2103400c240491409100480318030502c54003091301300000c0149011108124200402d0030041254202c0808a11401d54002e440704400b17165400110729000e0b4401d071030340c900d0400d0b02d806c8481e62107a0521000b9005049803104001240600001642c0070502c250f00c0c1ca884850000080c0701d1000f03c1e03482030046420b03000308036080782441240030043c00030540709082d954108090390300294030040b00281403540111103800c5030801400954400d5558424034180030b070300e8522421900e541243d08600a101d100d11002c4034a01c5070303140b0700440b0000d01c1000c00b041c0300031400c100034031007043d20300d6003540d01c40000140004080c8010041c101003940616281c0c20b04071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 798836007 1250 798834757 798834761
    0x402040507030e061504060906141503070c03030b0a1e0f0605090f060904060b0315040b0d030504030224030a0f23070f0e030a030e27070804060e010f020a03 69
    0x241c001c0d800c2502e4010309441aa00000c3d055400074910038041c503c0114117000280541002e8001c503a04038140314000401d4100c9480700307000d0240880300410708552610b049407442c0000c449a000141250515801090117684a0741c0401d5024021031451034650806d20114001c40310f1441c81e444008070100000382d0f410310310b00d0140446190091801034110001000e04070040d0b82544a160002040607590340c3d507034005401460303000100d580720302d04034400580c542800d00c10203000300c0c200b420440440c905100c891b008260306440360b03401e0508540031301940c41d1780c82101160244112400d84803401540c0040c0d480340d440010045480034800048070142c9500c0182c0140c00d03112000d044010720721200c400340e8000223501d0b10b0030900140349001c580c0300e06041e802d1034050060007180000c1c0342d03000342d00000c259000d54440b4460403250306401c00005656030001e161446082c003007882e040c46028610742003402000d001c1003098400c81c400d400c440102a081304190b500103805018280c044c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 798837257 1250 798836007 798836011
    0x3080a0f0807020304262d031c09080403060213030c050f1503070905040e2805120a110f16061d040b0a0b030901060612050408090103050c0409110304020405 69
    0x6071401520741c0c14841c40181d680d01841c00740302c2c1220b800c6100c2c20f816000f240c1841c5510342d440d40442c0c801405804951995200d81200310103440b405001142c8044400403c0790440c610030b01800d0740300c1c4154001c070f1004020405044415440810000012034518005404000c5d02a866a03480510b5440e207041100340540c04213000f41100010b40226940b40407000502008100c030240e034a40e21850111010307095900600d501030f2400700e545a40603000629511800c0507148100c5d16005203904901c001c4025035001800b0764813070000380c40304a4031304011f030130755803110305051007003401380c0c8801400c0c01180a81075005501000304010102150758011005000605000c0d1101e4040307020312418001250840e402207445408101d007a0b00e401c031400c401003184032030a9072281440000340740602064854040001c1006010300b00d841c95610555008951140446180802110064003d002e00611086003c0800d20000645820768021860b4540c0a07520050f60ba103000c0c81000100e03000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 798838507 1250 798837257 798837287
    0x60406090c0e0d020120030d0b190b130905250302030c04170705101e0e060403021c05060720010b010e221802040f091205070f05030403080a 62
    0x1c10035005403054118240d03240d640019690107000590500050710200e50800428071074441400d01c100c024030300400507188424404000344426a1400d013042200340003400c040d600030503020420041117083c500181a00740c2800c0c01c03c030750350f81d9a100c040c044a404443c030426a104034500c1c003015880810381402081c0181c00d0031411400c0c03020445283d130145003c4c41c030b2030081840c0e0040d016038007040344130000c1000902c56000201c1039140246203070680f03100c1040462100c490400c0707003070056903035406a01c000b50503507040c00d19540070010601e01c2004540b1000c29031000da900401d00c01e110306480b600340303600c84003a0111a0410752254464064036410350740d01d054115001a079009040000384002111411501d06a0707494104850229560700c0c80c1031450714661707080421500304100e803031900840d0100000b82e41c5c803d0300c501307640309030328001c24107001c000c070030501d003030240c1e001d8603055005600014403c0429a100c610b55400383c0c1098800003400f05100c1c0003a580404901e5200003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 798839757 1250 798838507 798838511
    0x1c03080907030c120201050403050604030302040e09030301030b040b13140f070504060e15120607030903110a1101050c01202d09010305040312052e08060c180a060806040609 76
    0x71454450b45800b4440340513954601d90301201d080c05682c851405e41d4081c58212064131024103040c03401030000d501c5031140580e40c0504000041d04440080256030490340c00042200301da80c2d9960310300c560068001c0507602c10000c9843e40c0e00124200351415003901d410710000b84080a07401201c3c9150890720b500162142d41859001d100c9007a81c0000140c00101920f030501041312a0000100e042c007da052102c00380c400d130700c01c01001d02d916810507481c540c020380b0354000c0701c41505215902ea004004000e024410a821060311a502c01d0005100035482e42000207002101d02c1d00f003d808441581c41c200698501041d580c501240c0d51416031b40340204003281e081c08140440f0491602c1c01003c05a1b41495038900002c0e003410b005060f00e030b10640504404010a00d05282e07426150112076420002400340701c85030684802c034000b408030070f441082000308810354039460440b400d035111003030700c00e03150800c40160b49450320b51400040180040b034491002c24502401844100c0c0d50907031111000c43c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 798841007 1250 798839757 798839759
    0x271a060406080a02060d02091503060a060507050316030909240b120406020a050f0d0f0c02060915190c210902010c0602090d050f030d0b0307321c03080907 68
    0x10340041d21043c2c1c154140c03030040e10307446e0220042000f03000e186400390b004041d0510304028442c007000114071079441103601008681c0c07220801c030350300d000340744000313202d41c0c8100300d1f01c40724491200350710000f20311078545202c22580b15003005050307034014000d0789400101c5c0c088101e141c0c3d110202d484040c1100740d03011410041540841c8400020150025040c2c03070340090f1240c00140300d00121a80c102a403171904c2e64441c9140607440c002c00b0340e601c560890034178280301260064404070b41d0901a40c2c960009029007500072442c0c3e040703110040e01c2446003034410402c0300403c01c0e05015031411407560780c5492040c030028100641c00100240851901c591800d004803005030381052207000165040f0b42c0050729100844c01280045408110150841c403d565540c4020b03c000401040e05880e1804140310a0b4100700a01d41e44003214003481c65100d110440d8042c60b01034409600d1a003052410805849903620b80100750015000c0a9480004e620358000505254200351580e4100d00b016000380811 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 798842257 1250 798841007 798841019
    0x3030601020a140307200102010f0506090a1a0a080a03020601240e0315011427011e03060504321b010c05010612050601050102060c0d271a060406 64
    0x52088000000e04000206802c1c03a42e4400c20029078803c03690000075001502c1c8048191b0700d00000b4800c41500640c20841c41c00105d4040e809898081c4e01c0143c44100151542800d01d009411205000c4988103420748030307169180d445201c0034000b05464005040c80141500b002402d00c03105030003c00c2d0500d8000116a8654946030761040104224035000c0d08480c6602e0000e8203000f100300c20304400980c040300100740503000c24003005800754116410745080c144554000800040d03c09084000d05c02c5a004210006064035040d900c150700c0c0b0300e80e404c107580365640d000c11a41c082c1c0d4203a40c1c81a40184689402c440c0580042a4003101d5042c003400c2003508140039910f1158161294811080d900840002e9000e96075880009500800034800703103450306d8440411300d10003c010340302482800000900781d4004154507014104840001d840c1150340c4641c2c0024040e014000080c907484800541e09031100004080100741c4115252088100c05148800100340060032407803085150540070414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 798843507 1250 798842257 798842263
    0xe03030705030d1505060a170a06030302102703090614040806162a020f0603010b070609051e0c01020d030507050a030e011103190c031a2422080303060102 68
    0x305010005000ca000e95049a00102c00d40c1e030741c0c0c01740740c001e007000c1344040030250020641905803404101140840c1e071a401d41e0410b40c0c440d48009005a0020040b0b0008101950803401850715004000924207103210b9424021360343c103c0e820340020795038031810311443e0392108029140350340201500b4181801c04001503142c8030003400051781d914400003a241040d00881203403200c207191580e0041d07414200300309602150f601e00c008910132501c07807140b050240742880a4034165440501d02c50f080007041d0383c54600070600c590060350248104400c40c040d5038061001c0d031902500000143c40e40f040366400281c43c1000009011043c1800c0504100c0c100d6440020f5030ba8014142c9000f0901e040801190340c018850040091000c03080001003210a00090340726142508100004000c07500d45000c0460455510520312a002d603001d1007041090f2910441541c2c81103d50074088132003c0c00c2500400c1d07280d10007405c90301c81d00300418401c80c660881154182c0100201350140d49186090030000751 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 798844757 1250 798843507 798843517
    0x1d010603020304021207090b033f04090c05040603140c090f120105130506010f05060717120f15030a080d2301030f0b07031e0f150e070e0303070503 65
    0x2040603804000241595542e41800a02c42c013840103543c1c0094403202d00300003800da9860002e01912a45e419050b03c0e80349903a0622a84070226904206410080040000c05030030205825040809020119403280f45120303081c3ca0300d8840e02c07020380d51881c02c400941521000042e010a0004050070840501d100700c2c101c601c602012180da142c411100f60001e200010640c0769010658601000c101c051810b1082c50308070140208200e0b9076603a43e500468200c5c0ca814012690400b8050165100190498040e07900b4996110001c41c00c100e030381da5100c0d130303c1e03d811a8100c040420039814041000341070402441c08101c2607010b0801c0e0701998842c0710301e1307124404400d40515569891166420444400e0212401c1c00c1e05103182a035075030342050135841d5100f07001502e03031130704131004160b065000380310350707545502001b06a841e03a000f0148804010300308075421481c00750f15140800440380c1000e04a50182c0607400c0d1015660401100041c268012403154501a620801c0294041500001610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 798846007 1250 798844757 798844769
    0xc05191d010c33110c06091c0503070c060c020c150f0f070606050337120309080d112d070b0901091a0a0b03030a0909020915040b0a02071d01 62
    0x300d8440d4103518808a40c4000041c81c0d0040c0d00d0f040241c4c0d0501c1c1240020041c00048004480c0b0503110204121703114100000b8450f55001b4507100611003a0058000d150b02541500f00002d41c500c4980300d050940d4100083c08005800c82c05501d00986804c681d0700e4006003070b407002c003400e0002d00b81d03050503a0312501070540800c2102103190760420901c2d4000c0340281002505441c3d41035803940b10403002c0c2030101c40000b007241c090484100440741840c0c0c0c0c5502d0f1604a440442c00e00c00981c0141e00801003810141d0741917404100071004441540101195440c045042c10b940b206015a800c104100542400511005859640d0191841c600c26030f201c07290043c004010940341c1200c0e55006080c82e0200030800071215881a0840e2034000001e441943c20340c1052020403415002c060b02c0717200c1c4003c1c001c00f2504051007801040b40aa028207240140902022400907001004500e550040d40c00300c68040000144c4660099060054038010080c0c05c0000c00c6151120750a815041c1c0140100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 798847257 1250 798846007 798846053
    0x20d02030a021f0f0207081308010b10030c090f0609030303140906010614070210050910210c03140103080c07060305100e090c09040c05100203090a03060c05191d010c 73
    0x81034580144d070016044940400045561300b0300c80c07a00c2075030742d0050000b42c0c0c03603550940f0303000955040c180901042c1d9038000703090703404520560301c0503001408030241c13860820442c2030003c11201c000e480d4000141006441d4428a1459445c00800340c4481c0034100340c0b0000d030b90003400740c001c1c00010041c0c1950752034185141c202d414201d0001e404c1c00b901e00c000e03602a0950b00c03400300382a08100181f204001c2521680e407602400441511207c1c0108070342c1c00200703007020740c000f01e0b1007003a8071607030fa0450386182c040355a5000c50101c110303255082e0815980c1c0b52000030100441d03c400c1000034001d0030305041c01e0000c1d29041c01e07603d64070b90750f5126104200c0b254400007000c81d03c0511408510b40c00040c40c41e034990420341401c00240c0180e008080c015404c40d03d250b0412800002950710b0340d00020110440141507540d20409000488082024400c0c144101c0003c0007900600303240c035280382d94a02c0c41c100f5040c0e1300c0c00034882c1c0800c0c007a4184050f407480840411890441000341c22010250 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 798848507 1250 798847257 798847303
    0x150515041a0d0809030f0303010e0618090c0906040603060f02190906050d050a140412020d0c0c12020f090c0904180f0605071b030809070609080d3903020d02030a02 72
    0x42410802c0f104101c00d61b84c040000042455040c000c84280119400c2c0d030b9252014180181d2014100303015507008549622203008466079107002c00d40968400030240003c101165281d8408c0165190b000207004800d40110305c0c00280802040d04581e501d01c1c41ca0107204080c90268058410310800d00b00152480d140c8000503101070240e000405041e140d071017040068a0a4140399000310340d0b00c0c031608018010000c002c0c101c18401d00c1150030380e42c2c101c550124400d02d00191143d0f400c10380c504c126080802d0040c2c1074900c1d034410b103c0c40d20070707581c6412807503079404401e040104851020100314120b144400e440d1012072400452240c0c0d0b02c1d40f2840c00911600c440d0760590308244039455501052218800e071004065214404c24000e00702402142c04446d12280700f514640e515002e019125405424691020b034410b41d10501d846c00815450b02c18111009125011040442c403119010002c00ca003d404142e810405451410101c3c03001d103080201d102c03402900c0e10300b520307212881c43d414010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 798849757 1250 798848507 798848509
    0xf010902181e033915070309080d050a0c0305033d090501060e060d09062a031b0f050c010f05071b051207150515041a0d0809 55
    0x1c00c660440e00080c1908001601c4115000c8100b45800319640240500d92050602c034031508031414a034038000c01c112901251141d100600500044203640d0f0180c401103034a11a22440380040410134020350f5204002c07414001000e213004590401d440400c0300420085200035401071408550035030618003103640e900c451007154801d6403541c01d099140c02e80b00001c0e050b203504026480700403004445450a92907580c400340e104a9030b013440340d000030500d14036070600e072803901000500603400e07081400222070740741e0345034041100d206080f81c820305e0030882480604230122090031030150300a40b800344012800000c0407078004070b441010743e0502440d9012040d4180c0600140c030710001c207050081040c2900140144007404090344c010012408a842e205401401038980400c416000001400ca881030038107400201e40c0a042c0603210341d64100324100080d15580159401943c00310035544c4104100d2082108442c0c005001c0d0b00030040c030002c400b0381d43d01e92451603804540c00039056511070300c800d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 798851007 1250 798849757 798849787
    0xa0f062102120708090f0a150207031701090f0f0b0f0402160213050103110307030302151008010905010f06050618090606250b0c04080616090506070b0f0c030f010902 73
    0x2030b441e000780800404110f40c07583c0c01005207105414810458603410082d40d003c54403034103d504054140200c0e1407a22114203030030b40040940718840d00d460800c07803203030005103050007900380c005041c02c64841940201d031f11407034019100700c02e88400080241040010000e2100b0300c01102c0f41c0d014a4000c05d42c845c0c0c0b14040e106002031150090124600584200100c100a0209010031926030060011141c00d60900203078050690364587c005100c601d800c06000c1102e500c00801e41c440c0c00090450100e50390300d083c0500105244980700108000607444011000e4402c1500050300403e0705001c0500300c82c1001c0360380000c05400b6114966151211808a40301d4441c80744108404100c040100012700d071003105e20318845016404483c40c640b034091042c00688158400c002c455800701700803e805001500380c09542813518284540707400d81e9180031803403a030042d00303060b121007651800308100e41c000300703000980c0301740301c00d829920754542580700c51380400040c02a401124bc1c0822450301200c060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 798852257 1250 798851007 798851017
    0x70807050f032a07060608060106030603030f121805010504121112070503040509010308071a0c03061c12052701081314010626060108071208130609050a0f062102 71
    0x4603d0a40d0b13070701090400f01c01900b414400d600d11031180d0000000c905e4840e100c2c80c02580d92555480c1c6903038001c640100c0e6099018171034840826600c09004500d076803500c805022461007074001062501e03080c00d000f41c11507508020300003484035814508000c00340108180c007158410344585c2e500c424080c00c1040c41c60207603030400d07038005882000210a000449000e0301e0b03698441d02452a4010402088450b24030041c0ca511401c110300b800860322524003581d03c0d218103029001101e00718811500ea403900c0400c15681c500c00b1410026481c0340784a950280140072500b01c0c0044600e40c00d000c40001c00c001030041050031500c0c07180d00303035004000038544101c1c41c004040c002842178030b840740007040034100c4a040c42c3c1e00428803102c500140302004250f8a0488000030040d090580c9003259000b1150400703901203034240c2082213806980070136010340c0341c05044c40d907550919290420381031003201048d81d080038800a0f4400410001e0a901001b40d58440702c048449092450203010030307101074010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 798853507 1250 798852257 798852331
    0xf0c0c030a030c171303021318080c0d020309060f0f0d02040609050f090f180307210801050612162105061527030c030601030803070807050f03 63
    0x1900000d0818194040110303601c40b40aa0021002410714001c00c090502c1460035800c02c45600850070000351804c0c00c8a000c00d0101d4090100b45404c9c0e130505440846c02800c4104c40b50b07400810b6140180703208101144100070b00b4002107150544880009440b8040c4020740d0303500000025a911040c0c0c1620706640c058002d01c0401d54031075454030740140c4008528029180120580e100d0501a45031985a6601644028106a40355101c0d50000700108000801c40c1c040d903c01081140300103403a028403180d040858100e603c440d00c0b010003008100d0781e0180c1c0400d11911007405104603200890643d00e81103441182080341c400202c2d00c0c250340080c00e2310855130003114490f0031038904156030f800c85803042d030085500c12850b00781044160103070300404801c1280d48481413941951540b200d8005040300000500705d9841a20100c0002d103413183c240c104495900010080c40740c81078000d0103045c0c2105050510030300346070400320840c17141e0200800e402140c66421003500c075032a181062701e02e1340d840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 798854757 1250 798853507 798853513
    0x3060803040603230105061204081605030301090501170d08062202031005190603021612090311030309091906080f031b0601080a080304050304081c1806050f0c0c03 72
    0x50b541001a00070f04861402443c05603035802e070400070b6080200101c0c141d8000804140c240706480d80110381842c0014030484105208104640d0755000c400c1d0401d071b5080c400c1008640d29070404425000351003060f0310030403c00c15281224403442d83c01081aa014221614080c0703526541c5600088525020390362201d1040100020f010b03110415800440c0706003d0542e100e04015584c0301801420070102101c0c0d4800d01c0030340000d104241c400e80080c441c0000b42125540015440e031035030b9807491411400c110102d0b000540c00c0040208800d903169800da03044002e0750070101c031040860301c2641300410b1440710101e02c40382c00d11a5421980080050913000c002c0742c03442d0f06030920603950303031b4072504000b6070300c4030b1710000c1c1d8a00f14000140709050f1800200580b120440c9030346e400d1400d0300b01900c202c0c0c440c0018400031400040c100700f0b41210300303004814055505200300010301052030b112410403100c4240d500c144021500300c02241c0c83d900310910686c0e90341c0c01545110382040100d0001a9141c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 798856007 1250 798854757 798854759
    0x2a0a061107061a0307060e03070f0602010b0a0902120402041107050105240901030c1205100c1d04050603071505070f0c2409060c0c180504060e07080a120306080304 72
    0x100e000c0026180051250400300520620011003040512982c40390701d42c541d10041051041ca4821000810710300006011243e600d034071500d4100914485420200c0141c2d501c4890b4602031810070503010080c61a16811860200c14403814640d804000f08064080d54a03034452030280d0840394100c0d10800e400000030407050030302004c0501804da45105107841078040c0c00d111040703842c0219459040b00d501803441c54000c2d00c0d0061f500302e480341c140d0080d40c180c0035802c0540e01d90302c0c0c00d0048218a0101d617845032403030700031540c8000601c0303800700c2d000d07004e1032400c070802005881c0001c2c2d007800d9034801841001c10b0410880100c1c2c0301d03c541c00c802404078014554003010814507c036980261410f8102d244d21100e81c1822002501c3c4e200100200010015182042402d010300701c14520140540c060034000750b201d110080104001c04980f509030359a8000f00000c0c03000512410700d03980c83e034401400003240341c0342c03105940d052002005441107a285807455081802540b03e400200094400d0f65121b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 798857257 1250 798856007 798856031
    0x30207081b0c030105060f130b010504050d0b0a1116030309060f0606091511120c0304090e030318190809040b0d0b04051c09270204140a0801022a0a06 66
    0x303000e142c9085400ba60070500860360300c2c6403210b1050140000a008203402441120506024060454020341880004c1001107016202e02900707041441c05802c1c1b511440c00d00e0b10158080b90304813809000d248030103000e90100040b0000c014805250503140c0451100060701f850700080c11101000910380385410301c00150a500004400304644a221401c01130041c0c54030159025410746003400b926800c0011aa544800403201400c2c0030040481180c2c00c041c3c407000010112844201244c2076580301004200700c0000564001405400140261070034208014010090144401004004590105916050791039542c4203000701c20000301101000c0707003103040c00310b07004006450598690145ca0344c5101602e40c140100c18803640107658603e40686801c0d151036001d480d00790b02000c4041d54000b0540500c0003400648060a194240d105030700212108100c010b11043c1c0c810220750340180700031904501001c0340c0d919006942c1c0e001c80e05400e030081c0c2082c1000d42d00040108100d141905500c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 798858507 1250 798857257 798857263
    0x801060206160e19091401090e03070f0305160b010311030f0d1b0c0329060d08210108031b06150d0812190c08061e030a14010c08061906030207081b 65
    0x403408551403140440d92321014000d09031165010501c482c0d42c02080540001190002307c03a4205011b03142c12410903011701c281d4003c1a0026206444450a0000510a001070302d824281010011001041504040d640064940e003440394142c0a0080941c80f074217031204400d84100c16698040d202ea030303007070340c403490b00340c40182540f040f00c0060412036000f055034400d034002141c09200e00905162a1245c59a9152110b0388000d07240390036122102a1001d40a03160390007036001e04040805140c8418030422410013402e00c8890680d103543c805e8081c440e029032841c026000d6144150b407951030122541c10816664898000c200261980e030400b000b464181003102d0807800d4a0088003813184041542045628000c00c0d682d107603104039450034402140c215000301052000c1c024040d02c11b050303d10389540403840050b1055800d941d4480c540c00d000c041d40700406a9108800300e40300801282e510701ca90f03c42e0b803254040c5000b4580d0000d001c10a0244000580f5070840c4061910280084001c4c10152 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 798859757 1250 798858507 798858521
    0xf0f1518060f0301030609140f150c07030806061303080301090f061d06041d0a0516050102070e18010b0907050c3007060204050303030c0a0801060206160e1909 70
    0x4000504403011040349014400c40d001d403031030300c541d007401c503401d64440400911050004450407143d4041c02d0400031410f1241c4140c104520b40500001e01019500882004005086081026042002c00c000a400120203608008295003040d164980000c00000c404e83c03640000c5c1032420040000251014680c100d000000705d0004e090051654451806520313000d0003040c0740300b41e80c140001401504050303100740508150b11000d0300011201c0c81600b8100040340e44181c91a0300319412802c18101248980303802440203100800d041c41c034080398a017a0306000b52024138442000c1d1944142c0c11706c00d4100e072071090390041c01c9030101d090411002c0c0c5940e01131020311101e402001e031400001c0344000160034004900b0a11280d881ca180d40384000b8960240c001141c90b0343d400c0c000070a80f510100041d62090000d03036045541c0d002044005491100c05900c02d4046500071820407a40000d00b810307000d0184214202100300c80c40303102c0040d111810050b20307406140002480050b4022460f00001e0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 798861007 1250 798859757 798859777
    0x1809051e0c031b04150506041418010b120928031e05040611070f0303230307021903031e050a06060804020f1002100f0911060a09050f0f15 61
    0xc461255a00c181900c920b1504003c0c0030503070100c032891059040640164805181c001062030146486600086881d04150803401600300f091060381d11381d040400744244000154403d140c40d640c50f140070a074140c4903845043c0c000340000b20111300300c8202044081803000c02091003203030f951110f0006002c8004910307019070004254007841150200310401004104d0020f680f04c41ca05414030009407071a42e2004400e0449200c1c1242c006501c102c6804000c028621981c0d8418241e505006081c4540706024070a821030390302007040c08a0990005110035840d001d2140000d41c2d5059810207030020283c000f200143c0c1202603804400b9242e099000600c40c048030342d01006040d1326050216180c0104540080d00500460200d50440c940002c4010320b0351102d204842060242901680549201d091510b1a407034545400b00c080181d175070143c3c1403000080e00c0417400c0048803c0300500c1d4032078510440b4020310b044c49070100242c03121425043c0c0402c028011a6a480c00c3da800e140007036001868603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 798862257 1250 798861007 798861013
    0x4090e100f050411010813050613210206061905040e060a0c09050102031605161205010b060a08060f12150a14060a0b0c010906060b0c0c12071809051e 66
    0x5110303003010700e1150038002da0300600342143c2c9504100c010f5171041805425502c0025502c2e081e41c0004904001140c41051613440c68080c0d85000c2c90454540b0556414401c49100b510002001d040d84c00142c050340480200d525941400584051181802454001640141c00d214003c40c0e0f0072130001b115401803440340c80c200040c4280d054200c60300d400034000c2c7c0340160810400d001041c4080b206003107115000d8025a141d221030100c0c5252121815400392170114041d819a02c2401004c1c819840c1500c025960300b45400300c0400001d140c451300409840c400c481c1400b000c2116142c060b00301004001c04400c890345800402c0192404e020700b1545c4040c6603052668010000c10562a61406810040c0c0f04110940c14078049440c1a0070020103602e40c1e6603103503040c40c0426860700601c80103022681550380c0d2008180001c42c1403907400023940d805220014000c5041000004410040300c10042a051082500803181d20103450701da500035041d407090311100385401d08050070341e00c8410380100803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 798863507 1250 798862257 798862271
    0x20f0402030606070f0206091903060e060f0402041a1905040f090305160f020604060f020d0e10030e0718020405010f030c081308070b07022104080606011404090e10 72
    0x100800e030301c8202c4030301e078000d2002c0c000e05001130f02c4034030740c00780e054401440107042c40310311300114020b07802d81440c0740804282d140041062003c681f045240c031003d002c016140a18154480d0900a40041c1009000d030b07558071034200b0a4048048400e4000c00024400c4400b010060000045042c442c021984a01e18001858940120764450b0b0361070282c0c162501ca00307100320f21880f05003200903c034040d03440305c0c03100c038124005135110703401040948210307200d2440325422104000d160034403861041c02440b274220440301640d9a00307a0000c03010322003840c0c00700700884800401c07400d2400390380c00280c1e244503080ca0b44d9004181500948291502a80c07003035800c0320070305001c5095403100035008000c80c59500124001c4043c0d900c80407912805228050301d8200542e540790f000000403204000141c12003002902407805404060f4140e810100c0503c0c01c0c46d081c6400c0d940c2f58400030f40ba1318103000e000080c00303025030540c01c1528010140c010007001034410343c0210325201c0d01c401603140c0c041840c12807 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 798864757 1250 798863507 798863509
    0xf15031e0c1115040b04080408010f02340620040305011b02030a120506010c050f0625080c03070216030803040606090207080d0c021006090b09010e0103031e05070803040f020f 77
    0x14480003d600602043c0166849607200c1c2e11072100042e10a5a200c1410080814008024000c25a00d0004201d005a5400715512018035400f428603100d080350461442c3c007290803011a400090498124000040000f030021590f4220340d0303907000c500c18010000c64000280001036020380b007042c1e400b4915000125001004903102e200e01e06024010541125500c11b0b000003030341c4400d60180c0c0c1030401c1d4a0805980c2c80d51807070100a4182c5d001c10340d000340f040064000740000312064404414010922030040e2002c050440c82c0c1c003c2103008820404000241c1e010320030025a4007000e4641003005400c0c2d00d0b414600040d80c000c55064908078244000010000030f0761003210a9950031940403070602e03011680c044050700c051860305c411807081c11914181042c90b8030400c8020301000800146044150040c4500300714164000c0759a020240010800b00b500a8001c820040369a22007510b50300c98480107540c02d02420b1703805412080701200f0023040201c0ca403110a04a802203900c3d0001840c840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 798866007 1250 798864757 798864763
    0xc08060301051005030a03050d090c171209030c0105090d120c0507050f1318022d0d0506060123071202160503030d0b06040308210a05010f15031e0c11 66
    0x102c07030290946d0103101103802203849030b0b02420322104011001304468601da102d02500700c43c0340d00484034030848035001c42c080100c1040400001001c070701c070180c180200707040026100e000b0301d24403e044c003a0000300320600c0c1c0c1c0c0354850500d50a50264012111010743e0600505590b21403808a41c90311880c8000720b0035181500c1d00d0241c2c2034000340000d415031050640c01014007071118544901e55045001c520050341c035041850000501c01d0399124600c0215590547c1203211543c007680101e202940303000c040f41022540651028007800d240c0368008071003900e0b580100d0003050b00d0044000216404c1c0070400e442005c0207541c3c00d95421604c2c0003008001d11140c00350300d44902d5600d61300c10480b4240c01c0e1513582000f0030010000b82402d0a090f0fa940f60040b843c0e2155040c48107440504001e44151031207550141d42048425104110560428021001610080c085c481004010440510002e071007900b001c1c0081c64858040e100300c103110329113803014100349ca1041000c02c1c1003010f07203a00f039a000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 798867257 1250 798866007 798866009
    0x703020d1106152704050d031401180213081002030709080648040303170108060403050702040902040c080f0a0c09051504031a010330030c02100c080603010510 70
    0x142c0311111030041d194080103811000c42e4071400e00c500f1650240344020303281813140ca00c154024806010184210702c8010b04076580c02a5512582c1d030000011302c0f89181c644020181c61050141c0140d0b207078285c62083d40c1890b66940071035903d200701c00341c0b18400400b58000d1402102c250700c42400f00d507181c2d01820b403a090f080324250303407070700d003101c00c0201100c4150f4108090f070700341c1a43c031040d02c1280000c1c8828000e4003045007240c2a00083c4c10410035500c0f030038505080701708003200c801550620f4409070b294440a00040e0805c035000c260038083d96980c0d404089426801401040240181c650141800c0000c40d0440c60305464a80000e502425601440c86803444503035440b0030241c280743c108051300c41c00c81c403000041d080622000c030001d42040c80c00c0c81445514940115503600d5440c01c03007407555418680b00821600512801562000210b40c103075210309a0601040034044000e0032413420b490b02062001643c200620342c1182e40c0c0120f0464000c100aa000340070603543e61781c40019540d15 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 798868507 1250 798867257 798867271
    0xc2003060a0902041d0316020a1701090c0915090f0f0f0b010201110f090904050703050a1b05065d1501230c010203070503070e0409020f0f150703020d1106 68
    0x411103000084283d8200d0a011f038401001c5108803501c440d040400000202d20b40c0d05a69510b100b140c0c00d012132410340000910304924107004090181441c2c800f49001c0303118420207146c50703500c03101c007108a40e0440601c200318081d040010550050100014208521140d8003651900480601c4180c007842142d0310b16140d01241440c00800750103103c030404000f081520789009400c4003000180e0240b1a945c4080e02803001c1c004140702d00841e20481020560005119400403c00d00d880c00d1030416800c04142090881a031030f0315503050240e5402c0c0a40d41100344030716a040e440242520705d00168814074a034105425030349680d10200e400c2001c1c50800384ca80032403070a00301c1c001e0010007078400c002c150814222aa08280310880d07000d0990f00142c8003680407900100800c2039841d40309010025606044030203014004264000c140f450011600490042d03400000c540840e4840030b41e95101004a014000eaa031481ca050003134580311482001d00005009100201410f100020601e0040b56 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 798869757 1250 798868507 798868513
    0x601021203010b0702180a022a06010902030702010906090323070f02220e0a1403030403080a0b0f191d100e0709050316030212010c0c2003060a0902041d 67
    0x400c003030300303007034544c00c54942241d00180d2194042c013504c0100d40306c6406442c00c1200580c0300c0301c0c0301020b4400203101700040202000c4c602d02540451000181c66030449034240d90050362901d0301d0b10228094030104001030304030340c2001c2c036400401d503000d142044107141414540c0a4101e9106400c1580c0c42800030150a009a4034400d0000d840d00503014609408003101000d1486100a8100b05850301c0303043e000b886030401908101032002c00c5040d24038030600f21000d107240d80742c03945e4040c00428000d011012015918043d242e140c0d2a03600c031038914010010041030364009011600070510070540910380301c00e581c6a40141400c40500f000034000c02d134066128407001d0800806500d142c000803d80300070081e4981300022035440a2004090300c91400491100c01803c600500c81a4200d0b0b41ca094001c3c0c1c03418441620390f80c0d00c2402d810302c0030b900c4035020400710054082d2900c036504500c1c10070303810700900c4c007030105d04041c0c1e51144154601c06e81d0309000380d1403015500300d1429100b140741c00b002c2e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 798871007 1250 798869757 798869759
    0x8160c12030213090209010801060804020d060b131113050d03050a0815041404030305070228020a0801060602100c180504051021021f020c0907090b030a0c08060102120301 75
    0x14058400291803000309150050408800700c0d0340e01c107948000d40c042c100070740d40011801c04559004000d035015084034180401c140c18158007040f0f4800255a0240649580307401c240e002d643c407500724011300f0340702d044184102088403510400c01e82c402c880c04901e44980c1c400c00542030030000454118160192a602d007012205003040e903011400506141c000340c5501040c1541e80d84074450024032014654529241d4545480e002d012200050071860542d03101e400c45c6181143c10180200faa4400c6021500780f410540c8040340040280e07421140017035080480214071258005048604450740010510600c403080f1401d640700705268401202096210205001c20f080c02d80151303800544400799024015a140c4090070070040c18200d90640348550407409041d13180c106007021040e030382d90501c0070200804140295507607409948aa01445401e00001d0905015030341c0d05c0000c00912003555070f03918102c01c032400240340d102c2c2100003003403901000c1800303541300080d01910860641c0d1795524507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 798872257 1250 798871007 798871013
    0x21e0319050f090a26190f031b030207030e0604080a052a1005120a02210105060415020715022a0328020607060e01060e04030503040209130203060f0708160c 69
    0x12038158041d6046481101d8401c5d04e0a50b02c0d0b030090400815650340c000c40f6101741d08000b0800000c0707004410400d400c240134030407030510b0507400151000182c100165102101c3c50107031100130911116a40c44280498000380c4440041401c501040c840c105582d22450000d5503140e0070340445400c0e204070a080040403499043c00124070b03961000c28148241000c402d48c41000c819501140c0d141741c1d4030b80101b4101141080d404071100c56001d030040f4400c81c4d60408004c40d005000301d00c643c030041c0750070402d0300c0c84190003407220760301074012800010002684a02c01964031402c000030300c50342c0313407145e0040c080341c0400c40f500c815202e100401600d441c0d1103460b0600c94240f144c80e600910320791019605001130b0780d0080207240117441110040307281d032403054200382100d10a91100d13114008000070030001a5201007125406541151501415160b46941006c0c40c00d0544000b5018071034401030202c100040130403948102510381e19a00320b903485001001c4610703c01c4550b0070200714040c0c020000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 798873507 1250 798872257 798872273
    0x603140d051612120c1806030b010e0906041d06190c1d01050f0418060801060608130c03020a03230c180c0c010519060e1504021e0319050f090a 63
    0x302d061030040080303084880400100c504400001d40461a0001046414004540221b00422140c01d0410a58054000181a804000200301c2c4038036242e80016855660700d61100c60003456001c3d596840c218010b16a0ba82d80310240e448074503944d5a0100b66110091900034008001e4143e5901c8006035250b00c00e14903425103914105042c40f8003408070b08009030303451000c0c1c0001c04040500383e40f21824034086008440194110b204d507641401c1052082c103401291250f00b18590b49240403c500b050b0a0489507555160070007540070040007400001c3c0a65001c83c00b00010104050340d036160302400c0895a250108001c130f42e000340ca0a210307400e200d164044419803103962441c0691511302d224900b282102c01c22200c2c1070100d01c06024102440d0440e116410161104081c40a464148507506104e201d11049005110b10b80024042a0701801b270030070b4040b05005284455140d0070040300f55502d00803210a445026450304000603201d201c0403070400d00403412030020f0000150140c0b20040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 798874757 1250 798873507 798873533
    0x50d09140a062003130f12050c12150403030c08130c0611030d0c0203120108010c0509040f09020d0b090c03011422050a0501021207020c0a140d02040603140d0516 71
    0x1007141d1115103c958444010302c004c1402040c0744a6100681e41007a2071000e00c43c4440d0050240e6800c0c03c03008400181300003403914005a422214400c4d038044c244212850801d2414859411450701c80c107110030150903810141c1c0e003803070588594960340d42d4514184100a0aa00003410381141002c003044198012841e4040c030306045420f0b81c3c6811a0000c42d1030688460641c0700c1c005a1000802c80c010300d40c0c00070418050004007000380103240d02100010018041d440100e07110780c0d0b4400d07800841d90b005a12440110b5809013080e4009266400c00c68286001103032224068018000c0707480c00c5240602c24103035000460a042109511903512451200c24501e025941101c000c000741408208100500014288160300245e583c000550000b508500041d01800a55028100352441c03542d41c00c034810107681c00340c00d035192200c041d075000030707903103003001e103019400c1458020040103000d014150003200c00401411119803107903469080b0361034400c04405202440c1c3c03d1700c12200203075140003020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 798876007 1250 798874757 798874787
    0x170c160b07170313060203090c091806361f112a0f030703090e0408091302041a09030c0d08070b130204020d0b0405010f080a03050309010612050d09140a06 68
    0x139042910558174801241d1050702c5541d0b6aa01c2480c00004501e406c1c01350720744c81064170310504461046200942c0e91160042d041d00404040d643c2d00c4140794419910b89150f441d214900b940d0342e20b04071511207813100004a107509201c440c5522084082070640155041e2403440d9034580c2c9805088005490b080ca00c0002c020103140b0482d0391030709580800c1202d10204194030000d036070b135a40a85070140100a80c0e03408480c0502002c010040814810016104510400d58031208802c2204101000901c0745400215588600f0000c031205a54400080c200380002601110a840011030401c00c41c1c40302e001c001051810100580307030004200070540c039081030b20020508550021350380058143d070010003040b02d241e580d45510400d241780a01031036006003200e109400205080001c03194498070a68030140610600102003404030030254018070092941038005072410b2028600252109600c1c2c0441000495682c4086510003429001c900c0d02c01c002008a0b03103c1785000c00c203841c5603812000781 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 798877257 1250 798876007 798876031
    0x40e060301060b03070206011e0509150a0306110a17131209050303040303110c090601080a09020102160e100b09060a1110060810060e060a030609170c160b071703 71
    0x42128880021318054440703a000b8014540c1000d00e240283c19102015001d01c081e20282040242c550440e2560003c0b1882018007840e180703100800d8405100e81d0005000901c1e181c030501611107950060038009089984210a540300e40548070b41d00302d000d41ea61030b600480111a10000386094035140107092490600703000e05d50780c41c00082c0c21034200340d00076404100840141c960007102031040c42c1070250115140000390500e400004c0c0a074138020050780205136a04104801d40e03000300100129612104100c4152031b8031200c402052340000d90ba405102036120a02041200015040d189504006803029003032030159002190b82c00c0700400301041e00d00402e005441d00c41ca41e4008c9002a100c0b900c010500d100c0c400250030122035140d07026880c02500c04052000503954241c0c007008032a000321000c1030711411800c0505252221b110948030880c030000ea90201d82e100031070b40c901d442d40200e4514090503621400c030b4840b449642d00083c07110421001d1220039846800142d50031080100345 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 798878507 1250 798877257 798877259
    0x31c180b030a06090c0203072a03020603040609020a080d020d120b040c09060e0a050a09020705010e0a0f03020c150a080703020405030f01050402040f1b030509100504060e10050c040e06030106 84
    0xca980da40d0050303400e04501511650140038018050040000301e4a0760300c011441c000f2540c954139505c2c010380d0380c00440c0400301e142e480f106041c0d405483d0003454005154540c1d030305042c1f030114000c20369184200d01402d031102000614200c04145084143c0caa07801800b441d48180c41c04469488070b885040500c655103207404403407074580b031042c580039041c2919400d03110f9080440c080c0c140c551096040c0d110702e040e480e0500c101e4542c5501c050484014a04c003603194400ca20780107016060500f660700076480b9010480003400621841c5940c83c902030340a03a4070381304c401030501c401005104e4010210040c00c0003807003155440348180f203501448034500103051503110000070381024007056031801941c1d114000c3c0000c0d8505889107203420f09e524842080b20b00c00e4401d0040050244110440515039102d00190b40a107081c01382e4248a0035240c0c0c100304a1800e460648000d04180340b2420b80361140300111020503001d4454107000d403054103400d0303042038601103211110000062405030595202c5e40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 798879757 1250 798878507 798878519
    0x30606040306050f0406110906160501020d180b070509060a0e030a050304180b031b01120b040f020409050603060f13080c0a05030901180f050f21070501020c031c18 72
    0x70030a401105200840c440751706103400d0000c1501d9411180d038035900010086100182d642804850703801e14000781c032120503085810310b50f0090181402c502105801e01d0351540c02d880c1281d010201c02031081c00e2956581e21209412602e6028083c402900401d00b0000c1c158454003544e0717056030f02c2c0340040c00c40300004001d9803814103541159100011140940041092094060041140c3c40d00305900a0403d81141502c0080d066404040326060108904221824414507048900c142d0406030080c4162244148280025400761040090031461b10f008104e40740340214006008441802d8140803e4031100c241144941a080088403c09802c0002e0101d112091003218000c0d4042e50103192074814040004d4450800c103c1d805040d042000030910410803d08400d209450090725890398205819000c95110420400300802c64440a42480b4138003000084d8002a101d080c0c0c05d50352044000024940c0d1a2002094000711017002003030010098072603520302c0c402403103043c1d074404442d039600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 798881007 1250 798879757 798879761
    0xc080906250605090d0c0c030201030509190320030909010b1c110703020c030a24060b0705010f0623041a060706050610090b2d0409090b130512030606040306 69
    0x780c0120364240c0c807503081100000e802d1120120407041e42c20032609800d4640e481c1111700005000c020306041c1d684000c14502e9200b04981c508020105c4461034900000d400c1c090101a001c07880c00082c0b5203c85444249a51b010081c0e41d01c640c4017810f207030040d90800750b40b009039411025a0b004112101040020880072501501e11000e6444080e0b07951000182002070030300319400c2d00b90b8000c1d401448a10002450310014008108034082c640b400c0e00c291811100241c0060340c04803505580106c0d2076800e00506610914000003c420f040101d01d03550945000c81001031004107a1401400703010b1426410250070040d50403541c003032501c1d80c880c800310001d00c00d070304020000d80b5080c0d550000c004890400d228104038103c600e051019081c0d01d000c0c1c01545500c90640c1800d0706030307401d91002c0700300c03c44110ba42000c0f02c4401811034440b80c503a00d03940010140c00c6001da40307100050f000f0841300d02400c101124269003220107082c02000c000c0c1824117581c406130555420010030480000410424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 798882257 1250 798881007 798881077
    0x12020d05010e03180f03060106021f1d100f050702030403060b03030d0216030f182c07180518010506031306051905250c05010204170309100c080906 65
    0x100c1d0384c040b6280101014880c01c84401120680242d1125006018850f0002900000c9507060100c00080c1604075224001034aa4507401d20500c0003000a8400e01e01d0380400c40c6d0103149407030700c0100468840205110305907001a41d071040940c004003c00d00124807617800c1503158400c0030701203c0c501022554040c00b207911101c0c00540700c1c01c0080810081581c006000d0348041d00e1454581124103944070b090480505500c03c200040081c0417810907000400c560f01d09401d0880c1c41003056604c1c101c24040c1c0140f042e480300a000340400b140202d801c2c0740140d00c0000350780005500c5801a030074941885941d82c409442560700d3381d000755214001a040d0b0140740e00c18048100c01408103241410303000c5c207603180a0f0001441c2c4500802d112000d15460808860302d010928100c0042c0c032940c20094028451a000840c2c805101e60001c50408130000040c1440001500c0800030b51a07401e10403110500c0c080b40081900000300094411481c0c00700c040c0404c500c10341d00071909004100100003018180f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 798883507 1250 798882257 798882277
    0x50c0a1722030207080703030e150301140d1a070504050f15030f09030c0a082a101a0d050a14030309060a0b040b060a0801030311010603020102102c030c061012020d05010e03 76
    0x2407034540e20452b050061500079128034441c000350555040034100415011101f00c92806203003111a180d05100e0424501048080b4441e00c116147c01c20010040c0540e0050248030b00900700504040a24180040807000000c800c13000b46003580c0790300031665507011000d450b04c260f40c4000d224095100006000c842c810520070b40304955650918051081a240300c8010032120381064091243c032128003080601d0900e0740410001518018201e00c1d0310360303814103001d5030340200f10b4464410401900083e280d012602600d59401241400c00c8610394912007100c0d00210b540182000c9000700c00550001451000010404078200c01ca1601080598100040786000110042e00400605801c5500020000e000c90001c3c02a181141c00103980d4075020b0410200c800c0c8d541c03c1c15100b62004882400815100214140c0f88059000b2400d540e43c120a001714a940545004940100c60304114542100c00643c07807500e041c0c4039034080102610100000351880d549890003419403210500c014510100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 798884757 1250 798883507 798883517
    0xc1009030515190e160801092307030611092707020309010f18030b070504060f0e0a0308070501090501050916090b062506050c0a172203020708070303 66
    0x465410700c1840c1c000b100c44080c2c1c407030a111051061100540e5a2400180c2c420340010402d543e507456428940b103408800044c500d0300407400400c0300001034001d003980c140549000c82c542404040700c042e00c2d2261842c021003a50040f80c0070400600560045507928507907242e1203061005040c080798050084186102950403a1071540740c0102c2c0100c04140c002d004e9100445c2011003440c0041d20848241c121181800b101c41401403140c0b441441c4600a0340d4000c40c1c0d0381950415400c05002d58011340200c10110703103d80e07a45200365114502001040c44001c184003607213032031a111902c003580040c1d415941035499442d1080483c10901079540201c0c0c070100189020101c000200c4042c0390726411030340c00d8505100d4001b2240c2e46100c103880d000c002501e500c1912100c1100c4078600000454030003016981420100400b8181110240c030ba050040e03114404039200001643d006410200d03161004900704030107147c6020504480001071601c49d0045400d001c0d00d501c8014a81201944202c00183c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 798886007 1250 798884757 798884759
    0x9060d05060306070c08040603110405040f020415050906040312110a0309141203040b03070c3e0109140105040e040b0402030d0815060a051c14011d0a0207050c1009 72
    0x100b02044a5075014940f03240c05046240711b03540380071807072083c0c0c42000d082580310740041c4404020720040780c004203c000d00800042d8003407440740001e50450f1048114810161aa000740c01d40194111610b060008128618160035943c801c0c040424180c00300341044544d041c50001c10004000065506000303444040050780340c0700606145046502d0424083c2d00000d2160510381e500100b40c0c0c0c01d0b5524008120b890796101c0d24105c3d4600300215020700301208040031041401109290707010b941c01d00505540c044074007040c0c181d1940308444a49400155400d001f04103810305800d0480d600c4405141c010f02c0c05684011080d0005402d9600380d903440480c8040c0310071440c00304910f03900f55144d81040030b501c0c5007140b110b410380305040c07221601903100001c607400b1151047c0300302d50501900e0303d00403865603041c0c51403800510600241c03032131000400001003421702d1805207040e11003995419180d007664984880201a4001410071a144d205200c1c5000d544d5840540320110b4002d2582e07844070031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 798887257 1250 798886007 798886009
    0x906181a01060c0c030b071e0f09060e030307021e030a03110c0901083004080303160219060e100e0d031407140714030a020a060e0115030b0c09060d0506 67
    0x40c10103038000020b003c003460f60303500010701d103081c80c40489800c000d0911031940c0382c280036214140b904070700f104103480041c214541d16400c00c454074200c000b40e546544109031030712400d0758600311041c001c50389903206000410051500070f103102851586001403946003802a4086841c08880480840106000150000a40c8000c2084190b0000100c80c05089549013842840c0c84180441011181c0d6148107203500b1312440b2403603080c001c0141429000e03681e49d91000d000d912030300150f400740104854002e203801c48500c002000d200340c0d401d041d0120034000c010f42e02d1200414250f103100025004500074505d50b04a503129001020301d120014000c030400c07031000202240c800c141070704002c00600c0f0520640a03440750310500c1c1c1d60400c1c03070050ba450030356080c41e500200c8a0000c00406110025242c102158040b0700340c0c0c00188503840070321412001c21569070031390305001c0440e00810041001000800d60443c0b07015044250a040e0500d00700e5007401080d401c2d40206582542e030768445081c0021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 798888507 1250 798887257 798887303
    0x20c190815010b04060c03050c0d0903020319030e0f12070e0403080f0106210f1b022a0103150e040602251505102607050607030c06090618 61
    0x5101107001c0090303107540c102100180f181c021030092008100c020f000c83c40406028900302d48000701250212086404c5030303d4001d010348406d000803400b901800000c10031000b4190711030101168142c40b808046c2180c08280103c030700903604c0b07c1c1e510102452050062a1040c0550006400e214602c04010700d81414050480b540c09065845200180d100410401e44d01c00c1c0034491042d016a42e0000b8900702e401800068440c58205042c07051801410042607600c102c03480503000d1480d005c0e01d07413880100241050303503021001c3da100a4580c0e0040c1c440c0c20b6100b5405036001040401c8100740c2103441d208a01e07140801203c1c12280b1682c00076241c541002d401c020300c00004860000c0c8550b1032440c0e80c0c0c3c460301d0794101040c80c10207501c2d14046083e059203280300d48041c003100034495002a944007160040030010341610042809601008a0b0754180281141d90054158a5040c020116a5542c2c0b0050050090030b07280d11b41d655040c6a50140c1581407900721038042d03070305801c02c60703404519840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 798889757 1250 798888507 798888523
    0x1b0a0e010f05071a090105060a0608070c1a09060a0f020408060415060e090f121c0f1d2a0117040c120813050307060c08030603010f1b0806010c0308011401020c1908 72
    0x407103004149d0f020001980e0141e01c540c4d02009910b0145411942803400c40c03441050701105003000c2c1001d00820010450000d01e0314814100c0c3c0c903087c405c0003000141c2508030f1096016080554100c04002000300d0710138109424200300c20440015055902e00082e0041d41003a50b40e044103401c4650b4454500e0410800c00c0441c0c0840c2d0510b41c9400c00543d504a0814409035550369040d4035a00800e55480840d48007991108211540c03140384150850303080d89822540703a00074010340820341d07081041c0715261444000542c040e110140c40a022003242101b2400003041240e20048030500410302968913004100120322402126445401d00c100103c8140306030b0704907a01070760000d4010002d242d8800940c130081c5801c0f200c840c0d602d85481001c130380940a00c04032081000d05000c1c0740c01070207079104807014450305180c2c0d81e003000d6261342004641c1d01c104c440018000071070780d100501c003101c0790945280403204140115600e01454101103046803001014040b4961802d80b810401040c0c2442610 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 798891007 1250 798889757 798889759
    0x7030b0109061d09010b06031501140c0d0503190c0c03120c02120d06030b070810060306030506060108071e0504140607051510120b1b0a0e010f05071a09010506 70
    0x10080c281480c4083d0008440d901c6140300480c0b41c20042034600ca020742c0144021380000c0c06403a40e9140c041e240c00d2a11a840c140b240c002244071030080e10142d490400d54031105078440203001c1c0e20040c00411503075500040c096400354240174580c0b0040182c64403409440308095140c40a02c01800d05020302515141c03880c0204103401c0c000c4200d101580414944241481d441645865a68900c4c0c42c80041085410003810250640d040c44441a080903140344956050b142c8003404603107803d000c506440340c071700c4000d080d9032028002c201c25602990890394012030380d00d00120180c80c0d000c1221116000c40110308085000000c1c10f202c800c20f500c25903c401b040a48406140860320354801daa14003a076081c041d00e10354640c0215a4140d60450103c00602142c082c040501c0410705001d45c050000b6a812202c5d900075141e68000310211400340e40080351246ca0701024509101c00550f283c14103461100308110042007064001421910b01d09100740c00b082480200d45410000e16007107442c00303003c031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 798892257 1250 798891007 798891011
    0x60806010f0c021f11070e0a0612080702090c0c10090204061703030a0c170403031a040c0c020f04021b0604050f0c03030a27030302030712090f050d020315010807030b0109 75
    0xb0240e224440d4820340f000748038000c00c0f41003109101c221130301070741c12074070300c0d42d600414500043c0c80340c43d161a540546000303075040100c036513900e41d01e1904618881c802094100e05000400240ca40548203992041c2c00107000351410a62411031820803c2003040102c006589001000c15410184920781c0a0084080307058a42031000b001692f03240402004440820345460031142998424420043c00110b00d42c201c600b14186407401070098420540410140102c00080b4a40343c03070280039501980041d6100c8604108543e002d01041c040134a00b03098110b07408204070600f442e07005400e0300a21500e00b001d804981850b00d090350801c11a140c4820340c40d442448022180d0b9808030842d1003c07011400c08010750070042c0385403660140780c0180b0040d110360310b0030000203141e0080f004042c020f00c101036101d4007000001003552601400d01030340d40301140313502043c0b02c00e09080d10004081400107044401040c100c03030340141064801d0700445056002040100100a1508055805484003102c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 798893507 1250 798892257 798892277
    0x60703091106030115030e060c251205120a020901050403020d03030905060c0c01230c0c010b0307091b0807140d060b040f031e020d290f07090504060f121b060806010f 73
    0x2820490b8001c0405680700c02800f00a40203000c070000b0b00d02c2d9503641d44100c400d0401c6004401c09005504081440520700c37503d0345c0000c900da0903d20840e4141e050507120241058119024009982d08440c021401d144d51400c1d10340101303001f080303680d220342030480441d0f544550709068603080d5250a4104101020f06000454a8007001d8841d0313548051301c00080c94030b0304182411071703015006100400e03416016403440850403d4540d00015402c03810b46601c0c54a030488400c08841c3c0c3c1508036141000101d08900c481c285d90075074402065010fa200e071000c0f070002e895010f500c199902540c0020984645204208108001611748289601010001885a00f0244c02048004400d904010540340401c100320803604d000e401503c021080100045c0e51a1030180780f0118610310035590740010401e800e030006054a00340c001e080540c2c1e4541207503007005140900c80003911218050440780c000201c180040c0d185e000c90303260f50080c02c080c2e882003202e040960001d0700601e06554008100921108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 798894757 1250 798893507 798893521
    0x220501020708010603051b0d1a0a0b181b0f040b040915060503220506071d0303091302030703090f030e10030603021c03120e0604050c090405060703091106030115030e06 74
    0x44606d2880c002c0304681ca0b43d0040c090001d0103215030123100034011404046012841d2040105843c0b061820341800c0084400c0102086460304007034034050f540c400001d00042401e0aa25140074003044220505802c101c0a12400c44440c0c10540250485240126040005d603009000742c60703038a00d00f000040c4c1d00a0809100800505c0300400758000040c0201180c03062088488400100603000800e0310810708043c80005c1140c8041d000b1300e0546640d540031402c0174600841200c2c0141030040c04100300324100081c200180d00b0007012603061507580c40768400400d001d40d10342c0749040e119035145d0b40e0256035441040003200310103400c40700309881c0c00020310050700e6940300400e2410070569905211082c1d49021500f01c40300b00b10700c0304c1c1d05042072000394068500003100c50040b403050058036413001c801c100b40458404e00b06d40107456503000c000407586460082c0d10156105000e000b42c0e25100d4441e01c0440c2c0725510a900c002072020f10718070701007207035940351062926000c10304c0c0103400340b070070502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 798896007 1250 798894757 798894763
    0xc0f3706030c050706110f2a0d0f030f0902100206040b280f0f0f06060912080a110a0204060b0405100903030206190f140613061d0c22050102070801060305 68
    0x140c130050581d59078000780304107a503140c0142e61a860003010065515484105881c2d08aa80148444260400180c00312206e060104aa007142c01159540d042e500812900442c054184000c2c00c400007035580c80e0440250711503001d400001c4130300390001c02050605143c80204850b0060074540070b500070030035000311101c12880c181048090b16101140c00c1d200407000a00501025460505803483d1803c0c1c201c0842d880d400120031941907845040069030740d110a00c5810b400b51a00410f89002003045002d074a001d89440904a40c600b411a007103c00b4541c04901261060f0b04015040f9202017010400b52400300040c804121240c581103082c5495aa800303503644102420303445a07146025044560104a0b9200d00502010403006100f03105c840040b400c1514002d84019000d07e40340403c801051019000300001c650a0000030b042d4180102c05107502d0500240081d201c2c04010020300c4015100034040310b0b40006070030001000c551030700001914081150f48200c0391641031810420101e2808 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 798897257 1250 798896007 798896017
    0x2100e0108191523030601030b28140a0501080321090a051c02150f0705210709050f040c1407020303090307030b040201031a030c0f3706030c05 63
    0x3861480c200700000106000c040c003000041c801594841880000f1388013a5003100513054007441c5000001d0445107024992210070900001d045200341d600455011269107003140c1201100d0300f5550780310f0342c40b0420041580d4500710640c060076145c070705000000c0e005103e00c0c0c0c010300c100e40046250000540010080c11907507a10382d0501b081060002d9426641030000480030b42e8807409a85503008400b80150501c60901603000c010b210710070440c0000004145280d0041d441c0381c1c0003010559901b00102c81e5540103041150301c0c82e51300100300d0100d03001041003034003034a800c1d00d0307408020b030030502070040c904201d64807144124100201d9140d226084001c06090404004480d83d442076180040382c594800d00c0ca190b034061044920020030300039085452402036100b660184040c08207200b0304d0024000f812019503040d008400000014a0320400e803c440300c03000781115042c481500c000512410071041340e500e514018900005142c4c81e1001c500c8041d04d0581010080e500110400500034021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 798898507 1250 798897257 798897271
    0xc0f020a021216090203040c08190f02010e09010305010203060f090709030212070b0301032103090b0c030403030e07081b062811012a020106051c11041802100e0108 72
    0x20707181031101d04a05000035201e00340f0000c40c40c0003060341c0740340c0c1c0c44c02540100e03400d4812060741e11011a03201c0010503036a00b4007240640211500805864807541041d4002e0f0490601030056482a21915107aa00c80c0c0214021400181c880c50b00d6820302640c1404021003601c15802e0780200007045400403400380a0745d4054980700b4244200004080c90006140c0041d00c90840120001040040107624000c10001e22081030388540d0f00d0741010b409664451340014486400c030400a0460700c0c140c000795500600a10f00890701e007030f90004241c10003041e45c12480a9411800d542d501014450324a51018501911801d180c0b40c80c4515551130703950b840a0f6540380c043d10301c01c002c46e0103225500030700c49030f6082802005013101c40700c1400300001c444002c03c1c50440c0c03094094058640103100d040120744018140388002c0c000881c200645103100a0120783c101c000d80103801d2039131204e105940e60400c1100035a8411407040c01040060204a1401d00c100702d590007011129990010590780c100c08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 798899757 1250 798898507 798898519
    0x10c050f0703030e0a121701150e0f1801060f08041a1b0a180801140f13083106020a0b0403200c041508190606030b190c0f020a02 57
    0x1e46811005070101d502401c006114041307901c002e210501501d070350000442c2c5c456068020705c48000b0058284248a96854140d0880702c0b60b1129004a0003112441c00042900c0c81e81010780c00044d80554010780f90b0004941c40100601c421a00019038002d9038106040c030352807e00d429500d000e80e01100e00020521800218041074031144000d00c7e501d20801e191404c0d80c0c0713440000c1d1000381110090006044070f100b121600150400040c45150118600a83d079080300d81c0d20105c243d009801c01400f14080c5440d840d900d2804a040440a80081100c0001c022034400e00040700c014060039200340e003c0c680d80001010041250002504004c1e298000e544542d0341c0e490303081c02d82e00d0b044da079030307544405014404000c02805c00108070005840021681041012000e030300324292039069002d640400d80c030801c0c0b0f04540d40a52a50000c1e110311030f00c03010410782e0704c1c2d0351100081101581c0c14903041101a0051452038064010601c0440700d91a00030360010340743c20029502e5100c4d0750701a00070f01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 798901007 1250 798899757 798899767
    0xa050d030903210e09060d02040b0111100209040c02030c0616050d0e010203041401051014040626100504020a061b0803071101061a041a0408060a060314010c050f 71
    0x41c001c040070340040d600807010129107950382001604000070007001d03100041e5400b1422410f032500c55003450007035801805065088402c1d44c01e000c0101101590f8034140541c120710b41e1001c10041140303071502c09000e0405600c03090300340c0902054400140840d0f003950028072401001c18000219658070100300f410303080e422950b03040295901d1280f90f01e02502642441d403400c42085054000b98080c13441560105c0504c0120440182203a43c1950b40c7c4014081000c2c0420007031440b0150303810301610003800000c080e60b582a036030100758840e080e05484254400e0403e904154140080405030042010a02c61480c00b41d0000f21014180e0050000b03100014000f94610041d40e842420b00a500c407051a40d00c2c2010305018106c016010b8900809601f452804100006100d601d03890300e517083c02401d406d0038109218100802d03601c4c5c81c242c29100d020301001a080f1000c010450080d0048100042c0140c250f0070010368040d100d004c0c0c034020f40c2c1400250781100b0750040880b009007469051058440e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 798902257 1250 798901007 798901013
    0x151e10030c0e01080c0f063709051906050a0302030901200310050a03020a090b010203160309050a0b16030f021218040c090b12060406080a0b01030606060e0a050d 71
    0x104903a003028011250068000c20310310805003010341a2000c110803251480c180b1000c0140940c41c40350003682210080c000901c900105108042441c1d1318217030702c50072a219846001840c509140c0000f00003601c506410846030401042221402d41c0351180301c0f07075803400c180c4041d12500c035040250040660010004001c0c030ba00303500c16000d40e0040b00109200031110186240c83c0e800580340280755890b0004c0c006034030300e0b00100400480754041d26212483e890724110308002c00015802d981940810000c107105141e1010940080c11300c03d03240c00b00a00d042c00240b0148038481d8001001c03292080010440e04c0550300194100f180c6d05184c16540300755040012404d2000400c045500b9003408210204c05110302041044000c00941c0c04102502c0403110480300d4003054031031090184801c0151300034480103c404240c2c4090003810110341540d80350780c014603103001b9507004d498516900c0014010490180101c0c40100b00030328080078a544420000740000a043c822180700784603181c101420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 798903507 1250 798902257 798902281
    0xf07030815100e01020717061911030106031a010c0f14030f0a02010204140a06080a0911060a0e040501080c2107170307060c03050f04020402090a1a04030302151e 71
    0xd81480505000c100ca40c8651014000340d0b0307100c4901e1301500410301e000c80d0004070040c40010134640300c0000d18841c1c07205010840d0b0715005c92500b00580d5201ca01d100038010b100da0055000b40300566000030401c2d5140182101308241c90480c6040115117102a800f02d08600c400c802210b0f003049680e202d0344c520918480c07661050841a54070fa0300041462003840d070301036010300203c03643e08820010b4002c140301000aa01c400d40a0340d0049114200810320000081c0e2000c010584904008201ca242c0314000a5564102d400d10300001034076000d414045084c94050340d0b004284010003404032004e5400095202540c0f072002d0b031000540848011240700701001400c0042007070801003d86000900c00701034496010b480251643e0b03041007921640e20b031092240074400d01e9002901e40c065201c907400c200284d804000130035404912080b0100351004071201c0c007240c04400d90052541c95185240103420840403a00c42002e1074820741c00c1214510540d040705200e0a9030796030180d041d41d145000c400c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 798904757 1250 798903507 798903541
    0x218030615150c0607180308040e04110d020907110705040515100806060a0c03110d050d061208221d0103060509030910030209040207061a12030f070308 67
    0xa89441240140103261a10003540c0d20011400c0d282c0c200541d68035403070b0010520601460410703950240d8002200300b0720500d0400d01444a0092400b401d560726194041140c210b83c00046804916105002c1001460689070050a030b042c0d91076082c5181680000e00c45c040018110001d000085421841a01c42803004002a01c40180304200c0340c1400c46045800806500c4e00ca80540e04603104542d940303002e040f1261091000401083c03820004072030494004407010703011014000761010020300c20009004060703550480e5600c0703070f488410b824285402d071004c135405494481980034190010940cd241280e814505901c4644464032000707080f0701070200d45078404c0002200202c00d420300d1801400c40c15040702d00820003401151074050b4910703142d1188840980d400101e00c031000b50f040c4d01030340161070007100050006080003119207880060b9144420b0050580464960b0350340c6528111242c5000c001c000310040d401d00a54031001519440b9000c0042d05100d00b09000601c012070304a0242 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 798906007 1250 798904757 798904759
    0x1f0e0a030501050a050103030f050301380d1a0a03020a030611190f0207050405070c02100207090e03041a030103030507110a0b0705150108030c0a151112090c06070c090218 75
    0x201e0303031130940c40c00b0004120a0000300e0000c0c0f1640303486a1a44d00ca941968141c076400f1b0740440e80300b10740c1605100c10300b0340e0f440c0c00d40d07404c41030040192200c861a00604030340581400c01143e1071007816405010041d09641c0c01c0e2050b84041024400f6032030300690001a41d034440c0340011040000d04805509000e41192095550308901c0c1d00340259500028100250803031f50212030446460344108400e9038412100d22001031103004001d40940ba00d004c0e108a50140e90051350001602e40b4884015030f1103100c40800c2950001030100f0480c69004c0c054840210ae0b07040407401c40d41180e4000b8054401c0e80e5014007003e0b03220f9042c3c0c030740da615410014014212416007a9a400051400b5030f111752291904c1301c2c101d6000800011241804002c880e280f122820280c18880081e545010742c00b244001000e90890340c6190342454250200d0050584400c50044131440b49071101d032542c60105149113150084506201101c00100c0c030300b403030310141c0780462800740c1c550042a11180d1000001040e0b9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 798907257 1250 798906007 798906011
    0xc0507050411070b010803090d0f03030b28090e060105012d0305040b10081c0905060a09240e0405070210111b19023003040509061f0e0a030501 63
    0x41c900314509000100115481001141e240e46c0e45c85848a44034041c6a02030f44d00000090064030018504000b0495041d200307040c000b03000d00010010690b9403600e400618600d1141c819100342c580150700308100100b000c00d41c01d01000b08400300103500c03a14184504c505100c10110707014554002c810801224103622007848800c422460401000380c5000d031016100b4101200c0801c04640c21141c1c180306407000d00c00208400000c0c07114150040d00d05008000410140c1c103808030321692018001d100c1080196680c0c5800707418103001c0007181000104001c0c80b01200700000004640159200c070b0030001c1220000381c240e130b07000c0d41641000c0e007038504224843c0c60400c0c0745042600440c090003c4031036a545141c0408242900c1ca41d0310140b10004500c000004482940107113071041011441102103540003000d9540d21103820790700001800441060307000440c2c01d12080c2031188a80e9031000c1c6c00c03142c4d0107500080c40f60480d418644400750710100405c1012000b501e841701041341e03008690050003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 798908507 1250 798907257 798907271
    0x1a03150405070b0a1809020306010e240f030717070f030f141602061317071a09010c030b060a0503071101060f0b0309102a02191a0c030114010c05070504 67
    0xc0105108105550000803d018045228020b0741f0036a8030524060b116107105402680410010b2002e101c7c00b0400d00c070111000514800c60400036141c2c5071140803c060300e074181154041d000d1046009243c2c0d180210703104010005600114499a141c2d2605000a5000810b01c401018150b400c98802400c00c151090200c0d42000000e5420307401400e034255441078450302d2600500111740100586103980c0e00c4c3c5d56200d0102d00304004c02e8020710074208915003046010810304408011581d03403100e80d540d205904c0c4500e4043c0920080c4840450f0a0b52400c1d0038420041c015000280c200010415002c40c00c4c1489403007540010087d00c5100150310000d5076900003120240e05c00c0710342014034004e140b550110101d032401784a403800c1c260007417082015115501d99001c01140c4455404500c00c88032007200d00080449041000c2e030040d0644c000c00040141d036811030070b00113042815000c00c1000108030040380f0f924440003401091034031000b280210700b0128a003210940000e030b485031a04030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 798909757 1250 798908507 798908527
    0x20c03090a080f060708010807061103070501090f05010b09060904030e03070e161209020d02090a060b03150f01020a080d0902060c01060b27150a0c0f080306041a03150405070b 77
    0x340e14032019003c00d08640c1d4a59a0f8003044035080c900f8480e458065000c00403d20600e4000c0c04036220801c49001120306040b0075440300f50a5801d40300701940c85d40004407208050240038040c01e00a000103885110703c2e801c1c410302003503000c28021f1000d0200507000e0705000c055941800080000e0609049422603414070099582031600c1e02070b21100469141c00d05144031403050b0040107001034000385410074951880d0284a0b80b0400104400380407580c80c031000c41c3e1000307a440614002c0b109609102000302c0c030f100030310440304002803119040d036200455020004248030102c07001c5494036600419548550300c0441d10b140290a032141540d400c0007000b00d9070424480152031000c4a819518110074042c0d1402c14100e0301030301820741c012450300041c8401c100000000d02c0481ca161400012210180c0c440302030001101c00c04a4005c0000024080103180600543e18144840c07849040500301c2000002e41d42c49007030700242a4174a100300000c0c1030110600480000704442c50300b0655814a1103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 798911007 1250 798909757 798909763
    0x5090618040605150d0503030414030c07090c030c02061b090d1505040308180d0311312102120f0a0b010e0f07021b030f01020409140a140109020c03090a08 68
    0x10713401d40782a84503900001d95841c3c13109010703c142c2d800901862568807036480c0c440d2400418044048240710070409885009010400c600003484c44a50000303035072070101001026103001c419a03c0456000c1802d102060704407017407035010300c445160040e50310700c060000701d440301122340d10103000005101460504d00c03203d60880b6200e03a10030303a5601c00d19230780e2038100c0301444100e2001c281d49522150300311080501a6004150810000d0003d90410044280c2485466208258110703800702d41242c98248030440030030031014040040c1000052074203114020301c010280000270f40b1410601c0d200704403086040c0709003802401003a0079620074182c1c0b82410070ba410350030301c03c41c1c00c411040000a62840c4c0202e105600415a5078048c08101e0b01408403851a0381c00d05084503818010201d0550044200b4030050008042c00180400c400e030b0344014003412a0340040c4640c24850a081c4200c0ba100b44072201d490543d0507140005880d03180072121589580076240d4084c0c0c02c802031500128001d8400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 798912257 1250 798911007 798911011
    0x31e0f0a030323041a0402010306270e0c2413030c030311030a08070c0c0f170c04021602091302090a06051e2b05060a0606111605090618040605 63
    0x44180e500d502c090007544460545001c070350207003c0c0f900c2011381c81d00841c44140f1700b50300540140340120300725803101240803001e101502c0c04d8441041d044441051052140540f000282c2c8102c00b41170128030520104001c800402c03215645070030701081c0c80146040c2d17482900d201440100042c5502c540302e01c0c05800b0305199010540c08107030011080c00d403030400002107031140041d59070b803850b598485882c15100003181c074800320b80c3d102d11000c0100d2501c518544900c01001b000a0501107143c03c180c55505021791a41c01c28001c500401c003d260f4620340d62202120355906450180550351080e04c6661292070b0840025403082c00c10303046c881810150742044e030580d101100c40c0307000818021559911540740b5808550085c20655120411400200200b25000b0f100150300e4554481c85d510142018021548241c0f61944d9a42c1401101ea0004c0c1f0f1062105c604070040104c0c0c0c080c1812010804c419102d0700740b0900c80c0000203010b42d00c5085800b400ca81480c18105a075080c240350202c050729003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 798913507 1250 798912257 798912281
    0x2419180804290d05061215010f0b030f040b1003051506042417010f0f05092518090f0b01140a06080f0619080303190209031e0f0a0303 59
    0x14541040d0070481c2c0c0d00d81035403415407010242460b0418100440d0083e00008194550040c1d8840159450396030070720034240d01800c05144909a50b0422200780280100c0b03400405d0144d5042c410400e181c2c1d13100302c40b00c3d04550000e0b20240303160380307903008001d00c0042500f0003806030040d50705044500304230b40402c6001e03910803a014008030341c010b0511040f44101d11040a405d20710704804201c50080b001d0481c00100c01c101c00400c03a01c0381c00c07003843c0a40c1d900300b04a09400c2c0c1d4030402c00226a0040c01014804840e074010040c10904202404481c0c10341030280b91103007025003010421003c030ba544400b01156021403801c24161007400c0445025609104600001d14909210070359450306e201c1c44820b40c0d480d030b210010540c43d80130b601c0e0f01c5074078001c21564114455040c4524400640d9400070010103142c401180d2320b140c10341007a00c5c0c8040540d03110a5460040c809000030355030101d0100064030182c482006064080c01100740f901c2a00ca546445500904034848189035041d0826044016 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 798914757 1250 798913507 798913529
    0x120a05010b0409110111032109070504050405060f0c091f0201050703020a050f03061c200f010f050c01060306050703060603110a0c0b100803040b07052419180804 71
    0x9407110500c4142e8142c0c00009054500c0048003109642c01443c5030a088044402107031705280f071000b102c1d00c00150203e080c03500002d440040101618080050310b020f00f074103072401d01c903909107641d54590341da001415980f070110b41c580008060900d5401a40c5c3d080c00000c0c41d1000140000d0030499949074003403820001035003000e0001e95114028001c80b805506555106483c090401c0719944154001405056100303c03540b02c082c00074005c03d6051200d241c080c103812016501e0b0440169031612558060a006900c42c0030341141aa0300b1442c0c1d0921408203003007060340c44c0d06200003035004013465040203000d145800284019a503050340401c080e1085130300d040001c442d0401c0100031030b0045182010009080001090000d2000e05603282c00003600740030000c03070545810140e421a0080d41000c840c00c1c0b030100343c0b82c2c00d02c082040300d003c0150000302854880340c407401203e180120700030309413900c02c00304500c407080703e40b4607900041c0f642e40c848001c0602c0c2412849c20341c040d80c0c4140710751a160f82d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 798916007 1250 798914757 798914771
    0x9080702100f080a021b010f0b09100f050607150501030b10051e0402090105070803040f0201091403060f1f03110102060c0c061527161704080d0b120a0501 68
    0xa8002e0394800c0a0000320748409000c0e079501034140c0301a6000b809280c5000c944074102c9044410300340180c5881c500a020040b4509481c0e00c14000340e408000d1030301b081e00014010801200b80c041e0303010415160b0541e80e0035607403030306424440001d00c40c09607111401881c1000004c14046522141805010380056800b10701c0d07900c008101c171540f103284540284c115144418069460715600400c01c0f124107051807401d049094803080055001101d095400242c80307802c2008542e400100103000c0c0c0003260f28001e005180a0109903550300040c02d640030702002c400030910820081c2c0f07101d07500c48040c0e054440000d8407490443d01d00c1005280c12070151007110045006420010207803212403260000a0050760340d0040a0700703003590014250768101480403c100940540080d05001e07003000300341180031a0801c00e0461140b28000d004007000c1000207660b005181c43e00d001c0054206411941050700c510360304075000c0003403802c17000e0340d5442929034281610718480030984800c03040c00303900200195 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 798917257 1250 798916007 798916039
    0x1030b060703080f131208010602070506040b07020d08040801021b0607050c0a030806010513061d03070609090207021302040806070e0d170c12040603021803150c071509080702 77
    0x2405601c10040128814400082c1d001040813061503203c08040030408a01c1d2840d1500c07a070501c100f0f0641000610b0410050182640400002c0c1c020603058030158500b40c505a003010380c0d0300a158000344180c500c0190340c0d007441905010385014044400085686100100400c1c00f1010251b034011b80502401c1c000400d214014001c0d42d031072500b210701a1004483c1a5001c4030042e9004101030b040c40740901400c400100e003482c40794094030a9440b00990050342c4031510004104d81d140d118443d6101800500049600403814421140c07407c10140e100d00c20b5100140315182d64100000759540301040004d52034800007841d07405041c95484141c9501d60b5003003488000e48580c0c50141421100030140340c0240e100000403c0705414413800d41d55a90003082c0d400b00c040d40070f940540c0c0080c1d008110341000c41c108180e4101940c1d42103009140c1311f091403004a240303d030000c000140d42000031038680c040c0050010108410300074110108003090b070610340035106420005003680220302100e1042d0070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 798918507 1250 798917257 798917269
    0x602160219030503071509380903180120030322080720040e0d1d03060408250b101409060603090109080f0316021605040c0905090a0b01030b 62
    0x2d40f900403019500e0104c0507220074078409040f8000c0b520075035075050014041141e82181400004828003c10480d52941150f80001e402e02c40c0340c4803c00c0390310002d2001c00c0000004887c407400078060f03405031444500005031558a08510640c4541c122800304c00b186480100003148075450381b50744440090b5600300850b515110b004001805e40d8801c100340340105207002c2c503140c1c030000d401010443c800c51040101e0150f551840d0081125030102140381c012503000521103a100d085880601e00325410500040d0380c1c7c10300a40090700b002000148541019404c008070454260742295110f00d8240742d20b8440d042e610111110000222440008104250196209101c140f8010a603e0040d01c2d040c042203820350020300f9107110340d942e0310034400009801e00301524000d12402062900c030314120501020705a0109040303401c5403c404001490208404d282c0c0c801d8840541c1d00084415025000f902c880d0f91540116a206600200301b04240c145a000300058a000b0fa0301402041402d60074008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 798919757 1250 798918507 798918509
    0x6050a060510180e060604050d11041802010c23150115110a230708010e0106090606021c0e3003090f060f07121206050a0b0f160602160219 61
    0x940404441c0d0130081109010ba0103504948028145440c0558a00000c1d154854180b4200c0701e1010201c9880141d00d06441000041000344009c1028116640d00007440801c54503001000d0465400b00e04039286800602107003030990240840d58011440d402103c4500d1092090139000c0080c0000b0030149449040d103c10082c2c0e002000700340e00511959119a9100e255412000c191320307406000704011410170102c0c0c0181008400042e0420050a046003542ca40b90403000c42281080070030405903900207400e031a0302400009042c4080c44c0c185040390341490003500c140d8044064001e101d0f0100310209020613030800f80c5400b01c1c01361031a800c803584a000e20480c0ca640210810080046800c00200500441c4085000e5518150709a136940101c0208000050000340001c802c03000034442512548019210407107401810070701d411000d0451344a12049041c5140740403802d01c1000000c000c081281ca030717014034255218800326a40317203e0315182c01004d07445034040149030300e010602000102c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 798920863 1106 798919757 798919787
    0x9030909022b0609060e0f07053006011707091502030408070e180102070f02101707050a0e01050304110d08040b03160909020a080105040b060706050a060510 69
    0x4c1141c1154000464207000c201c14012155a00800e4540c0f004441c174080b07a880503d900c0500e0f800300c101e49800045840c500300f50303802d00706104040d03100f80801c1c1d030703025000c2199a0401c1501c0c082903c00e40003203460341c0c00612040c9450120100700380014011030b03103019605ca41d6545070120303e074000c401c414030200c1132244100d100d6000300240f2200500a5041c0100c81d2600d611000d00c1c418001c0c4240130b680d00b440c14a44c014002c240c0b1511304c4805d4610203160054000c1d006600082400300055184c0c0c104140c2c540c090380680e40115044582841092094400d0060320350326030000755540760b014040006c000340c0e580003c504c1748401c640d81c02c4104050000c06003180c4295080400300c94014407911401039407101c0d4440c1114412070300032480c0c07070038080860031a12603003d010300600e08140820442440b03903000305040b0750301502c0710fa810103452403086841c6400c4003900 = true := by decide +kernel

theorem cover : BRFrame.Cov 798741007 798920863 := by
  have h0 := BRFrame.cov_init 798741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 798741007 ≤ n) (h2 : n < 798920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
