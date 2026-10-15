-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5187
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:02:19.73623+00:00
-- url     : https://prove2.me/submissions/4280b6a7-1337-4143-9684-bb5f28a87bdb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 932733812 ≤ n < 932913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 932735062 1250 932733812 932733817
    0x10080115030c02030d0f0507080c0301150507020409020a030c03140109080a0e0d0c06090302010e0d02030604020909070e0403090329070302090103111317071202040504051e0304081204030f0206 85
    0x2c0060041c1c074984a2a60a90000d9035800862441c22584503c2849070903680a4145035001c1e034003040460035075040c81001e010407a000c0c81001c04104003c5030f0032041d9a216881062680c1e402004040751a640c1d240c5840c81d00040c1c4821b48692003010f40c0c180b2911418010003000f168002d85581c544460104103580540c224079445410140030810000060150303002076010304011f44031202094074501c0014000b41d00045294064450558001e006880006500d600290304a030a045030b80e503044c1c4000c1c5446a2a4411034400d200e40701030009168100404c0340a886c01244551140d101d118900c0f01500100c10700e44a41660040015244072310940c080c101a600500d808100d003403143c4816040c82d0040640414050003c440030060081e86501d10590400da40340a00f40141c84d040000506d04643c0d032010740206c0d00c410010381044024445101010040011070061901c01e019aa0f903d811038020000c1c284101c120800c69008142c0651701103030382c0512458018030b43c0780d00740310713554 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 932736312 1250 932735062 932735081
    0x1060917071a0d0623040605060909130b04082109060601050d0e1c091a0a1202120a0b0a1d0103121403040825020f0f01020c18061008011503 62
    0x701007801640c00980544c0203403002800307480d08441c032088280d100340c00500303201002c0e81e1085180180801c0b030b940700c49085d181207150032103500a0aa4030024000c0d00c80304544402410040c2c05800c001c20011044017a2442d83c402140b5a40844802c52131800c0484094916260560158002418661080008281400c4c0540011403500d1103400707140d28042c0d40354035076500071020380d0328501c0c041d90110030328004003c502c0401b00c02030f89042c0d210700c0510500c00300c1000c002e4074000309403000c0350540403500d40d15542039501c2400e213402d4100344028802c54020502c584014100080c0403884000c1d03003003448c08003103400159640b0310f076210f5402030079410002003070050182c080707243c40340d0150245200d94040d0142caa40c0c4c10902d50328004a04440354800f41140b204d11a0030056100d150104481c040c0a0304e000c90054281c00c010307032601203045c03803496102c072101e030f50303058110800322686001d5034003078841c1d4440108100050352040da00340940740b5050440c07a800075210b4030a41006041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 932737562 1250 932736312 932736359
    0x312090f0304030c05130504230102040b030f0a051f121b06020303040c0b0a14070c090c030902040b060a0807081005030d091502012a0512040b0106091707 68
    0x244415040194155045a8000d1300c510b0044941041903040107039203c5003940ca1007000300100c1c0381c65030f0788140b890304c8088074003482e039402c4c042c40c8210708095040720040c100d022000d948900d8840c08080d0000c900302d8030314020030305150209540320008284415046404000210007038240829210b10342070f2800107840035000414101d04003144c018042014000c65400740d43c0d42e00c1c00b800c00508216199000402130701080002100c02607100102c10314070074400b0f90300c682c2c46007241810900da90442d0848180e80f85000305280c00290180e002202003842a00e080c4804580341003081118020464601c3c00314002200249030544105840c0703034402d0440c41142801078940c0d0100e850403c1c009051808a4004d80c01805440031154000f6090081440280407907001035100900e0300343c01c0c8240c512040b10a08094005030b02a40550380c848490304106406440d182c00c122200d55001e10819000c103001c8031010549801c1c0c0400075088400c048000c010302454035020511031911004040355 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 932738812 1250 932737562 932737573
    0x70f0203093a0305090f040f020f07050607020c0d03050c0a12090501030e01021309020f07061e051f0603110c1009030e10080f04020a0302060711010f0c170d060b07120207090509031209 81
    0x101200b5071019140c0400e6000c02b85848009a1070258a0b0107000f03046103055501454004040e41c0d90303421041d04490341494038688038071280c02c02e06d1810404072070003030041d8541401c15080e243e02001031001c5072000d82e8240b00d01d11071450030b13600301e1080107289807464445031014007000d51f41c1d400030080380011082d8030346070000b5030300c1e9481110280d2240f140340d02d4515150740f4101d8100e011380d5400c051040c0c04a000c26240d843d421040c0000c0388600c005140d1140540041050000c1c1924101003c1409071081c10281c542400f0042520200440c04a4004121841907051402040103e4045c0b44c890500381c0c0c58000307518048503c020000c0b680440354040c0400140c5071103024001e001d10600c0300d8080b02d0380da0f00003d441c01c05c1444185080000442401c0c0c0070440600840344011030100ca0b03503586003000e5500c4005496070f034011410401e0700142c040100b0942c4061800c00d900f081e82a903803025229402c0d50f0580d141034800c4039840e80b00303003c15841e000403d0b600d00e401040f05411100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 932740062 1250 932738812 932738831
    0x17040b12040f1e0b0a0c08150604080d110d0f0c1122150902090d030c1707032304180203150913020a090504020603070f0203093a0305090f04 62
    0x11000160180d82c0c502d0b80c07043c40700c5010040e46000081d04505111820b1000d0201450002c00703056005040041001001203040425100d210849002e0454003090f250811064800540642580e100c40c26091041c0801c41e04580e110300f42800c08c00807159110303050680281c551040240c1c017454440e900036030300294901c00003082902c07107101c6da01e0301d10b001c01c0660000401c0d40b60303d07005500001c032241c01041000100c4e9541c00074010070507894200681d400600d810003110031120581203120110f00054010281508001c01c603070400e4550b0402007640b00b0b490f20080140c01584503802903021810b0440010850503005942e04c4040c072500c20100300c000f200011a01401a181c3e024200c01c00310700c49055003041548080a850281e00500c500c1c10568040b031658400181203100300310001e03040344c582038070074022500c40c00002010401c40d0300201e61818800d40503112502c40d400702110f43d1409a903103085d2803404194058076000e003000440414009142d00340891541d210b65128640b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 932741312 1250 932740062 932740073
    0x2060a1404171b0603010909080d0609141f0909110d0303020406030f05040b1614030903131202031527100c051801030221070c17040b12040f 62
    0x4000420380382001d00008030740342c4412400c100001103004084803d400b009400c03901c0e42e5048a0441d4a003210000d01c0407c6420110f0240c019243c0052410b0b06002000850300f1898000020411a580900c081601c81c1c07000c1200340d030b2001400c09000c00c9600e808101c4d442007640301201c064000d49030b0b0482c000c1e4143c00216a08039041c1c0440110303030301060500c50b103a85846174004888502c0c00c00c20107420203460310258010001c0c01c0042801d004090070402030700c0390001c026640040d0802c00e071a42070003c0d003140c80b0b03000038030800102140503400041d0244513190010205030050042c00800c00195119000c1260007000e28403200c2d8510042108441c03090140d4850040e94006081c12801058060017030b500000d889004002080c0041c0440c3d04180305450526042403c005940d8401201040c1040e9081207454010b290f1401c1001609030f0070154042045106d03030840340382c0380303468008055180924061b101104205011700c0c3e40384011300c401c06c0c0d00135006074403583d41200c050303a81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 932742562 1250 932741312 932741317
    0xa0503030c071401092c0c0a0e0f15040b0d0b0916030506270406060b0306100f0c080706090302010506120309040b1f09060210180204091506060e19050d02060a14 71
    0xc002000c0c0101b11840c003a001016110780140c030511003e17141c0500310f400100f8610502441074441d1482c507050120503500c030710340b070851040c584841a4455030785210915103500102c002100060400340030761424139021769501d00c00c22050580c490b810b40100030441c0103040c000c03c1a500840b00c0c2c058000080300340a0142d000698000c2d07100c0300d0349013519004040e110240d000c0180c1c11782c203006105e11a5a960141440c076516031401e014108051041161010041d8170080c0120070002143c0c428003020b0303001169154000d400a0049441e02018002800181140708a0300d0700140400c09903460141c000c10310300000180404021203c1030b000304c003a0f1850070032030070204400f0b070401c200d050340600090900120000d400c211038405c07404040710985204100134401c03075481540104110600c08419080d035100c1d0010044030303445482c0a07040d20300110006105801c1c0300040082900b20640c24025100040d06040b01e03040d41d42d09101d01a0080c08800d8148440e20460044c8500c11402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 932743812 1250 932742562 932742599
    0x403121d03360f100210050411011e0e0d03031d0109050601060c0206030708131410060905010506070201030b130944030619080c0a0503030c07140109 66
    0x840400700200e0041c07464414000703030300c020450b107820301c0006101c0ea039005502090010035100c50315008130751241242411101480c880d001860581440103010031b006083e4110b81e03080e25000001c0c01c0f8100d45002d00c401400c155000604800681a403070304007a43c5086550344a070901151030510381c00380d5040c00c078030410701d014640c6d9501d2041701808000c108d01c500422440c04c02c41d4405c1400d03000700e0740c0c520000b131524003448034120100d03801da8141c0360082790f0a5005501c4000554000034860744499066075008030340d40c1132150100311b410140c41490b04139000100001d140075150740c0194050584001d140d82d00c820000d90507220f1802a0003148007080c4101001950b40d1300da1000c46901040130381c800b1034040500001c2c04c01400314149010207603002680e8803a02c03642c0d6140041c20119400c0c0d12214005015940042e012000140851452104442c0c00000e6074a40c002d140d540d001e0512a80f0603035204400400540f2000407030700c0c29000f810700d007440856480c1c82c1c01002862090070f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 932745062 1250 932743812 932743837
    0xa05161505031b09371d16170708070f0e1309110d1407090c05090d17041d0a0c080c090f120303090c01020d090e1806160210050403121d03 61
    0x184401901032812a000382480e0740005c030441c1501005565003603c020061f241c010742c44803070065518028803c0e0f4140c1407035000c1500d214644008024007018054900741d02081d14199005400c6000700c98040c60544080c1c107150380c511100129402420b48be2005550312a14031010400340d803241c1120b001071901071210346181c292894940341c41c10710240e22a00340e00c0d1911b520010069400802c80e400c0f0710049800b038035050000e05000130141540012034445100002e0006040400c603a210040307404003c0940815a507000c0c4503405655080c50b01e000000d07103480c000303107201e91501d010703241d0380e80058000c0f0b024420800101c1c091000448030111107034408020403040036810000610144801e101625040030303405c00107880d141841c010b07100c241c02c4142c00940a85510312040003c100b45204861039402c00314440d02601c124121504010f0040c000f20200003a078501941d40215410381d24008101c040866010082c51200f40a11181c00036250f008800b0744108060104445041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 932746312 1250 932745062 932745139
    0x6021b07030c080c01050708071104050a0903170106090e07031b030e1b030d0c0303020c07030c0501080a05040c14011809020301060e0d0f030807020a05161505031b09 73
    0x10b040544980c01541d11a2030755034000700c610003450340c1c0315050b40c0940d41d02c5031546485290700c0c9040c0420410b80444550009c0c42c1c0010042c100501d034101c00ca04500944900101540c00c803001002c00c87c0900545020038400a01000f00300f0108002c180e214409183c00030314403004401c41d41c00c00040300d4a01e000681c9034508021840da09120309c054821401511903102e0740c02c000401c0e20f4641401541d001e01100c1c40a1609040c080c0d01141c00c44001e200075540005d0320fa00c0d08a040c0885030181d07070f001468200018040e81c81c1d5104103402184c02a005003456450082d11a9003550030014680c1008840701d480110000e80206c21000740210b500d01586941c180140140843c0c2c4c080002441141c00460074408100c00e43c481c0548a50145001d81c000d58402c102a4a05080c4007002003592048801c3d100905040703120070b20a840707c1524a60240c900082c01f01c0b0329000c151b8010101e404000d02510021142c0001041c00c10b002804140444551103400c00000f14030032842418490403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 932747562 1250 932746312 932746319
    0x290405010c0f0507020109090c0e190906210204090305040801020c060612150406020d020f0c01090501050601030615081b0f040302030705010513030308060a09021803010c020706020d030906021b07 86
    0x40b01d005200007071510500f8220243c00080c100000380c880d45a0466031b6204504d02103204110f0202802c0c4058411a040001e00c1c1d10350001a241f4401c0c41c01242ca04800031403240305c03c11100c14111800c0300001c09080481e001c00006001481e421010b01c00c00f0800060485020300203000d40300009000381800c0d20b010320902c034003813510300d040303041c80c2e042070420054510044983d1a04660800001a2180d41d111040002481505046800c415001c00d01c0c80101d101504580c112a1080c0005c1c0242c0c2c0342e903c019001c1d280c140c09000340100181c1060200035110701442540410b4200200300c400c200d0140c002e10f00e50001401c610000c40029007441942410000703030009007001c0c60b00c0d5152102d4140b011404144500005040000b1080450345994a4920141c00741c804031808640e03402d162841d1a103040d2121501038029400c0c00882c1d07140a0021412000f03c90094000d813a40c010a0030088004200c09042201e040d9424004a8045001202d4980c0740d600c4a800603c5200d04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 932748812 1250 932747562 932747567
    0x5221a0307140307050a03020d02091513060314010b220f08190b07050f040906062604020609040b060c06090d020f2a130f1e05010302030a290405010c 66
    0x1110448015111030030002d01c13213a82e90040450b0034810083c40c0060b2546144440075002c1d104000b0f82950050f85808044004a04280101052503840414019499540c0020350582d04481c00e02c080f40c810000c0100003a5010300c0c02031003d290803102d03071001c5129001200e014415030350054420b83c85002c60030301803280108100e009000c83c00c2c5500201d102c0c81c1e603500724440c000414010804c540403421a0304041e005040e2000341c40e07040006c0c00515212000146400542c81245101d4002c441103840d03861041903801d401140c01400540c900300004080c080640583c2144603080681008005074505003032015500030200000500850016a40c0080c60803850000003081d0740c10240d90601d105140c84440c100072003207600011124425000080c00329000101009101428240c01d20140c1101768820590000000d20030343c0c3d19070b42d004d4076108072a802d00000b50075501892404022950021076642d0242040508032060080f0100300d0213410000d4404032403c3e07450f200c240c400030341c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 932750062 1250 932748812 932748827
    0x6090209030708010b0a03121b1506140f0f01090905160201243b01170c0a05040f02090d0803040309050d0210211e0f06030305221a0307 60
    0x24154024801700b011080059601211403000921105003801c480c08058021a80d4804120207000c00100c240310320b0400ca11008041d9a11540c80d900c0c00c1070200308206150100c0200c3d4102030300d0b4501902c8088280010007000038015814455400000680400399008040c8500c0c0400495035107a041a6000703400c2d140c50f2120071a0100c0e0000c1d00c481542d80c5040410120782e03521441403c000a00c039440700203205489103901102d100c00c40d980b00180040b180442c101d07007800204151030000070404c961070781242c10703403035910403070214040220340b9164204440c038144040c00140341985900016090580304079044810600120070401455040501840101000d8603c00d282d5030103a8005528510611f1042041c480c3d0886201a1008002054124910a8001000a20410074208440359121b0b850b07001e1450420000c03060444031806010304807036060700c40fa404e00560f5810785a20348404490b01d02c003c0a840c90019000121120040d10391070100b600b90703600e08050b080200402c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 932751312 1250 932750062 932750069
    0x7061b05091e0d020a09050601020c0a0b1605030f0705060f0603010203040f0201050a030f051e0a02040f1a1c0923032d0703030203180a021c080706060902090307 71
    0x100740140d441689441642c00c4080c01c40d0008944403424010000343c0d4001502da0280d0031040c4c04201140682c299885a80212002d0702260321019100080010740c00c614090380d07080c00c505020f021034500d030710010801c6070b5201d0000c0e00d080c030034802c640340c0850300a00c80a840704d80c064070034455036100c02d00c07040c0c4c0c000b181a0020f51640c0340c1501e071604000a041e030001c1c10400000b5201025903c0796103c1000414142c3e0148214201481d050f2062003010040c00c80341301c00d440c04102911303280d108032012206090072a007901407403c1c40b540e40e1184240018032020b0030420040aa56114850078080703d40e00ca000003506042500b01a0410091684c8010340202c00800d43c0694410000542d401080c003c2c6c25001e41140070904080c000ca14030020700b100031004201e4008042d0150051440307015500c00300d0f050740d4000240b480c1da0300140d01029400007120b908060041c2c500c1d00b40c42c00d143d4007499499180420654074082124260760088814580c0842d031482145011b0010b007008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 932752562 1250 932751312 932751317
    0x60c1c03060e0412050c0601090605030118020307123f05120402130917180904030905010503040812070e0a090623010e120705010306060903030203030f090c0607061b 73
    0x1e4240005128004070141019140c212051a220105481042100c07142c103405001c0e20781c5943d440c41608041e2806010b800e00c65401c00d58924000b07400e00402c00b03a100c0c0c006004084251820040080c1c08041500994a07990040003040d006400c0e498210060804807002402070b000e10dc80e00e03611001600d0000041060030812100441200500c0d03170342054045a0307602591442c1c1c03031b46800401280c140100103103480390344840d501e0071640c007501c000725501190400d154a400b08028500404076001408034182c0c5a041c046540301d41d014541c05881207600e14501001401e607880322007400c40c0e4800014040c0d000b603c106003401240b4100800e107070b0000344803550400e129804418100b21031071600340c5a8811840040e0f110f895554681c1d0800351001c01c0407918408034a8480c01103002d1a03011034180103000450a1040000d50100c94041d4051030a41e11810380000182101500550440c81454107520065582e90000d16010740b00c1e440008605400d02c003005420340340e1040d10fa05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 932753812 1250 932752562 932752571
    0x2304030809060f1512010204080d2c0d0b0403020102091e0a0b190309020303131e05010c0317090c03030d140c180d15110c1b0a051509060c1c03 63
    0x1c044405440b40c4c140068101c9681030350b000c03103158190081c001c50384403807098441c1c1d0010b240840c0c2c1140000031001c40e407a1400e01c0c1d80c80303880004603020b0007069000ea0000300d50000040800c1c0c00281c216042482403001528103480c5400140a880e504080d00000c0d07480d00d1034441207850700341c2d021401841c2d681241810141818a60403404000217800010301d0b8454594004664052080b540c4200e1895200415942c03104400c0c1e000300000301c4071403122140c0f0b4102240d1980603d0000034002c0e8155984000509131095070a01c02d580505402d040344544000120b15a405201500d082080c5d120001040f0203500c0314583c04180140048000500c20405038040c80c0d608128201040d50660b01076580d2a401d00d4119551031016a45070480303450407423521030070380d0118002d0000c10030401c2103480c540700e01400305140d10804c00145500c201640c01c05c12260a0429502e0702000c0308410850409081e000800c49c04e07404820510b03010381010391440c081500d1101e041e128500e040c078007040b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 932755062 1250 932753812 932753821
    0x20405040515090c1608040b07030f0c0b041709030a060f0f05090d03020c0f0304032103181103210403061407080114040204090c020616140d2304030809060f 69
    0x440b051000b50074245603007000120117840c1d544600e00300b03010550203603109071359980c0c43c00500030036080140101c000600c014803822031540319400f881403468000f00300d001152030f582c0c0c4040d42030305c50106200740c440062000c40755641c0c092001d80780740d030300030803002c42d58803501c0354480c08580d15010205030382c515003400c0c0040b00360000b40034410100203003070050f5103815601d9851f14001b040034043c415480001030100c00c01400c0d110031408040002c0c2c01605c07108141c00141e06603a03003980040140502210418042140080e0300c20401c1c50150554219480d034214101c50103d52149803506901c00140c1041080340d1481409001c41b0011102c07410790400320b40040c0354141c180700322004120124a004010b903102d9044a00915641c40c00700500074110b83c019444100031903400003c08400361000f6103040c01069621705103072000300e41c913140508242184004007580390a150040400042d0a51100010b190144c020350103a141c8804070b15215080b0391a040000b0708810705441e40d0420300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 932756312 1250 932755062 932755069
    0xf09110a050a0f05092a12072c060d06030803041b0e0403081e041202060603030c030d0f0216050a0b070c021309110a090213051807081302040609020405040515 70
    0xe0064078401c6404090649540075010181d41d4140f200e40525404a9824011217240d98020150008076031600307e40b0ba80c5407501981c015038054021000c50b031110707400410344030410020030a4200700038403541c00c00c4040034150701210b410350801c8903802d50010038007040c00700c200b4075004c160040c1c1c480c081c03070f007810310321111120900a400103040c03000410200d41000c40c80340c07003545c2c4019210030206041c0340c5820724035100c00030b500c80c585c003500800001c2072450074040b049612840310607004504d040724401c0a50010a288848614102d42c28400f419a000e440e41c0000f161500a400401c5003144601b04264000b201034486814040e070300307440d1401030710b0310584610002e0080b403002070880c0300c81c240b04074146e00f06c24038a82c0c0008c0740d4201003640c0b41d050340a0002d050541c0d105507115038480f0140000107504070345044030359140c140059881c1d84100c05055018412000d4a064030007240d0210301074440da60803040c1c0060f00071070144024181072280d1580451481c01301505e520416010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 932757562 1250 932756312 932756339
    0x1415091b0409240209130b190f0b1e07060e060109140103120c021221090916050418090611031306050c09030a060902121c050703030f09110a050a 64
    0x165241443c1c01980c03040d1514503815910b180f0005030000456a401826450003022500203051064410920b1014100300e003e04e40e2040d144040f500060715811312001030304980102c51071640803c3c03003040e01001d502c42c80010b000c54070b104c4c0130041441105420784a00300038058124840c001d1400c40c0d50120480b092a40504494101042210700a1013000440326507035102006904540c1400c00c50802d41000030328000141848400740140b10158030741090743c0e1040c0800c003035000d848000401c0c0b40d94141075882443c00c500d420030510302a501c5041c82030042500d03182101d46030340c40d20b21405001c0d81c1d0041e03490022540030918554600f14800720000c0800881c083d00160742ca400040d140d0a03400c0031500401002021030f106841c8900e080805444041001c82c0110018070a4203401c080002d80003d05801100b011032141c071120300c0444032500030040507020151a51a000201252446100c40759401140d8401043c2c0d00c000c113200c40b02449034042c0d8000c1c0f4000004000c06071a2001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 932758812 1250 932757562 932757593
    0x510050a021914010c0e040606090303022d060106031a0904020607120e0d06200702101404030c140321070f111503071205010609031415091b0409 64
    0x2e10b01d00b884250030035400d00003a001501d08190320344843c80400d5500300f100800070000840c0c007840241d4a604046518180600c070003809a4000c1100440c602e100042000c0009450f1912400f0307078400350710035071a1034020b0307104a001c65640d50821039500c5414481c0300c0c0d14142560700700c00d241041c3d40458628071590744c000c1d1a00c1816400316a900c2d108082158a050740140a8040110a82000c40045c00c0380d404550100140010b12031500400800352401c154005200800c184000d08060b500e42007a110344581c2d41030304200110018100310340d10405480c050b000c00c1422101070f0241032424840c40c54807400f070354042602d6850003007180100ca08070fa80c45410001d041c0d9551034041b985003c45039803250311811b04080c0890080800b40a03505c00ca92039aa035599485810580e042112000e02440c40002c04001c800d0003c44d103410b00c0c030080b8480040480c0c8084811039030070890102c01f5035002d5003580040490540c50741d1540d40320700c02e140049400704462003e075510001c00c801d5421 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 932760062 1250 932758812 932758843
    0x9151b0f1d030303150a08060c0912010605040c0e3f0f07080c01270302060c16080115050618040e07031209030b0115080c092103040510050a02 63
    0xc207020100386400c0c694246500103011030340c5908140b0004000066554102401807449000c0000c2c13154001500c64007601c03052000a140c0821842442480200b040e20340e401c035900c490000800d915140700c1c400c164105070303581510106c180c1080082e0001f007031015210b031140991802d1036544507000e0103075041006048020380d401154a046003001c454005001050080b5540010543c070040b80c40c03002c181090341c60f0030300d007504103805e055a0b00c210500804041c20641c8140018240704004140400b080c40490300d40a081c00341013040c02400c0c0d004040302d651204010005911510442000b5100464002c0e06140d003180c2064035400c0c2040596101c1c5480f1007410b6101642800b0002c040d5030001c008001c1c01d038041030054071164952000b01c0300344902c50000500c0f4005c17a00081303050440340d03941c800152209000a485a0040e03e0303030951000400c40c00c00309401302602180e0842501c00040e58950f80380c8000c02c0441403002c2c90382010f0242c100b0041c0c480d1980401da20280d01c0f21013 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 932761312 1250 932760062 932760077
    0x40308190e060109061703030405030a0c0309030609050706080c090d061d070807080618060f060f10090302090a02030603070b0d1e0911040204050f060904020c0109151b0f 75
    0xc5008003038410078030000c1c92070084000100e54465940c1001d0140d40305070040040d4504070860300d6690b44000c640141003600284140310080c1d03c5558030703e1000d4002d2030039509558498403000704880040c1402c03078165126800c1000101d0304480c0d0700303521111318200303c1d040100b450082203e0001c2c2140c01086642d807068152880030300c0c00740708041074034254119001c1d1030315290115650011802640254440d100001c2c03ea50494030713403100001c80e0000a0300194032382440c4d061441d07c0192126501140c10780050b6410f8403a142111081c07900b666586100502d1401031001000c40a003080c0106401002080000d031800140b00342224415800c0720758841440c1c01c00f10040c0940329441540c58000c2540004001e06c541110349040e0140c2a414905004401040220b01c0380d0321a241e0015900e111010161038000060701c41011b014002514001440150b07608546d0030707900c22030b141010194841e2586c04c035481841003041301c40004c0c0c0b440c0b80311150050108070f03038800f9140812040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 932762562 1250 932761312 932761351
    0x3130b10140f04021911060619090c0207031b0905130203060c1c0c080610090e4317091c03090f0308061008010b03060f01020a17030a050f040308 64
    0x1140d0450b21603071045c840c8400c01d01d04401004000c00120704014078148502c8000c03445902e003031b0a5401004045599180005140031030140c042c04041d980c210550040f45400804501c0b40c0305c194440e119141d0000e1034250510340380d841246d002800d9001c0300d081076244000142c500141c0300360441c8919402d01d80310014040c0ca1004200b94a500050081c00c01e5005503400b0b0300054100e020340e42c100d810000c580c0350124215602c3e0618803640381c09003464000720340000384045900d6002c1e080d51003000f00c4441d942d020781240800f9030325070300c40019510400c8810700e42d0262480341391070310104c0241e00d1400d01800c0703a962041305461f6150b64006503506245210701035032010038041c0e130100c001c800c11340650a0160001000f101c030103004404070042c2c82c20b568807644002c0c1c1603600a004070f47c21512083c06001010b0002400c0a0540c45100310240111380f11002e0524116854036015650b4a0400f01140503100c01800f20b2200720104400c0c0000640c000c40343c1c6034401031174894050314400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 932763812 1250 932762562 932762569
    0x110f0105160e130221060f0906100507080f04050f0d12030f020408191205070b040b0903070b1503010c030e0a020909010b061206040b0d080406080a1103130b10140f 72
    0x30f0816000080310700c0040c0810085145181c280e0383c1d580c07005d40903500c954854080c000d2540c102e090b06a8400d500c84002241440c020080e6000724415192207410400349030f5030200a40d115450451361000c000c182002103180c0b004040e41040d02c181d44c0c100e81320095075622240038050880500902d83c45d800300300a050b5295050798020303e2440d04039441240f100c4080c0d550a0740c40c1100303503020003621441c5150300e0701840171184059031010600c68140c8d501d858400002401918114141c0810080d00d4086254000c0d4140200c004000c401034003051a130405003103441155054043c14140450803081d000046502c1c0503860301074405820a03500c0820041c01032902002e075660160700032400e074949031440201a0303c506015101000030f002d04030200004225036080080c0290410001442a203105d815001d070026509000490548262420141c01d0341085034146039002c0c504101314144203050707503103903080500d0400c0501c02c6e6090100120045440000c094060345070035200a81d02e45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 932765062 1250 932763812 932763829
    0x20f060a0e19110910140f041401081b0102061501030507031118011803020d0807060e1b100f1202070507050d300f0825110f0105160e 59
    0x410728607807801c2038040f0701d0080003103204040024020050400094060030501c00300030103403080c1601001e803caa81c1801c01c0115021180d40a8000e925018640e10420525000e039019105103000703050000400c071054605102c03400c40c040e04552041d400e211780240150b0801070a40e40c20301c1c0125040d901c0180c00c1c2c0203807034089903012018034000b03001901c86808409402000c0c009a0720420b094180300d5070203e1405140c00080d600c00b401d40c00500028061000800010344200d002140b8200720a2500e802c01e0318414101d0042c6410804503a11441c025140c2c0240007414100071150104502c80104034802985268110641c0002c60f90240502000341000500c4000c2041c0c141c140d280ca8108000e5104580940042003c1c6c0c05403030490710131109180c0030290507911002815140c81c011988000d0290030040d20340da007403540140c000101525928080c580e911100c0854a5100c00d181c0b03442454501040d030360b45480248070820750407003c40d401d86011880c1048112495000180990 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 932766312 1250 932765062 932765083
    0x1103040b130c0e090d0c1205030601090801020c06011d090601030b060a09022d0f07080d09060911010206090a030203070b0a1118031b09060d06020c0102120f07020f060a0e 75
    0x2d10580b900164010003812801d02c600c07072801c19182e1002075a41c0035205c140500d0401090b4006e001c000c180c8403449000a55400901454900001c980d0b8401c51422079129548000d1560080b50050041c1c0d804540140c0d450004540801c0581c80d2a2100a89692041c000100044140c8010502c59640c06000902800d20072008540d01d56011085124423003510003142e004c104d43c1e08440c0d146d190b10304140d82d505602034180b40c3c944003daa50b0005103500840a0740c00c001da0b11038085d0f02040003403007489415072046482120f050810400640761010050518425a010300440300c00a42e0200c04c2d0fa0840c0e600c054400201c0d00d80b15002e40180419840362444d5071000b00d42c0048000c14100607070f1804030160251107403150f0b040d4203007010402e0300012541280e07240001c200b080c10107046180505000700001414031240d41170032070981c1d204610360b18031a4001018840984502c42100e81c000240380000c140d0702c030707070014440d0722000002c0c0301010007595482c05210200052020325840e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 932767562 1250 932766312 932766323
    0xd05090127120203040f17120c0604140c1509040917131508070509040b130204030c05120d0518031911090c042304020c0604030f031103040b13 63
    0x28140407100400e126680c510541e0210b0400907140c42860000c03048800703840c8680d0707100f80f04508090416900480541070fa800510902c940c48a580820030040c1000c0300f010806002142002d060240302c441e4101140641d50300020060211559260b403109500011035190544a1100f04006401003001c002c01500b00001c011a840c4402314140050120800d009000401d482e240c40300c803007855000d40e1500300070814440128140900401c05030140501c000c0000c2030300314000000c100d04803032102d143c1c10340c0c2e82c004c9424020420026501380203800d0076250ad007200c0c100c0c80e01560b0f903503113400b10714030501c213000901004c00340d01d0140c03c8950041c00340071104900c1d851f1340c10041c242110710081d82e40b400b8180a800e040e150424119000d60078007100c05041900741003140d03801118410354487c00c28100042102d164032180050036090312000c1c0545007928250401600a1001d110705604052030100d40c0c02c0d042c0b02d41c1060f2600a5005083d110103981c842403544221950311401905 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 932768812 1250 932767562 932767601
    0x501180e0a1d1203090609010c020c09040212010f0c0906050f0405040207080403050102030f04060b040b0102061807081e070b040e0112020a03080c010606020d091206020f04180b040b01080c0d050901 87
    0x300d00510004c50041812100711801030f5101d4140e54200c940c001aa4030042c1c0002c5100c0c0d1042c42e1800c0c003207800600080c40c06d1041c00d046d030041801c4a01c90990058082d440d2408098959080014617004041078100b6034903006034114510b019104600500340b003507501140c05424004241c06440c003075a03018008560368180b0034181070707051604440c12141b15052100701c00c99070409024640354002c06800500d01740c5c640042060107000c81440c02c07880b500c25088009010b072401c120071603407558030701100703011058038a4816007032207484e030001c0c0e00313004041108000f0b40c43d66803800d504407600b40a6102400c1e60601c00144011070355880a82428000b048001c1d1582c030651082d400c449c1c4503003c450348000c82813015104070a440c455040c840c5908030909020659980060580881080211746015280d000d0b07421441a019031402d00155600700e800094140b610418400c4042401d101c1c64038a00340002e07075028441d0300d45420301c01d601e61004c5855104250414841544603510051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 932770062 1250 932768812 932768833
    0x3050d0f0902090f04110609181815090d0f09030f03052a10200c0c0604080f060c040f17010618090b0a0504022b021005040501180e0a1d 60
    0x740e029411746041d9010190052048590718240088841c044070191040d51004031043d1003a0103e20001d006030b00104807005000081c0c0030900421030091006001c6140c50304144444a2a029010031008180110724126003565070300001c85008032940081c0d504004c9449150803641d074003031000c0b900ba504803088c1c12413090080460160640710030407000c03110034907107106800c815600c0800b02c03114804100c820a0fa2095020402001c10048101c1120134850101340030400f1075220b0350110415030490000c20000035018850141c0200031407148504140c146016990365801901c11041c004c400e003030f9011150700c02900b12400410004204007044d000e481003d0700036000201c01160303114002e0001072503074883c900c1101d001d41d0b0090440414158a004415442007103120701108024079041240c1c0180d030b0352001d10512000f59690f007602c1d1854200050080400945255004500c10605101419800c00481d5010082c180e0109072501a52040d61384e84a6042d81c14400d809a00c6814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 932771312 1250 932770062 932770081
    0x70c0e0603010c02010506060a20030301060324050105122206020d15030b010e070203073507020112050c0c0a120e01050304050304060e180403080f07090303050d0f090209 75
    0x440c85003600394000d1000e00f066100890890f04125810750b4440d9060154400d040d108440910b0141c00902d4291642150102e5040c070b150000d902c42c4001a89920078200d00c1d51442d00f1012804ca000e0f486001c4031402c1100181c005d0290f90000000008110005003070b507100c082e150054442000201d070030313411450502c80301030751060040c3c042c1103050a01450b41d035603449000c100ac503500841c3e00e144c3c7d40d00740811203401e818080c150034218030041c440f20010a4003140c9042c0201d82401c1d000001c3c1882c207141d001c440541d4003c01c125a0401c4c006100580d82011410000c9907490200040650310704a4020990043c0d04500c040c500c00c1e1143e00c0308012600c005003210340c0440d00c40518100454004440c141f100f04d0f8010074540083c403040084901940054061450040240ca68464080342070b540950080b20243c0003e18404103010350300032104600ea800041c1c500d00b906085003945c4020f44544550048031544d10703610000040d00190541c000e444090380280b00349500e040c02000e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 932772562 1250 932771312 932771339
    0x1051e090f0711030f0f0a03060305061906090c0509040b040e0f011e0501210203070b12040c05030c0f0913050307050f0d0203120402010c02011101150e06030304050a1a070c 76
    0x32a03010605100303031465950f600100303807004000b40b0b108482c80d09840d201340c90015004058444103250301ca11010000032014400d4510540c0521039650640408400144c2500e25650055070f2180c03510000d540300d01d03800740c203e074070000d0140c6000c18a41c4203a0040303401003268203000903d601801b1210120304a0640206c650b5149058201d005440c041c0329800c200c0b2000c1c03181c0100740c200c00700300e166011040b1801031034075030004013581d0f00c03180d079000088000c1c0d110200000420862500300003c100704828404c0240405400909200d81c455004c84c01403041484000c0c0304d00c3c0c4510000380d040f4800c1c1480400d2541c02020741e51540b1603460055502c4951000d140303418080c0300e0341d5150300b070720000135202c1c4e40490080d409450b8443e0b40054540c81d01780d00059041051504640a40038800d0040ca4954003503001e0740d224191400b2a03060080d040944050706c640c01c10081003200e0740c1d5a03034043c020ba50144900800b11800039000e04414420418001c0581040f40c80c00169891303046817 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 932773812 1250 932772562 932772571
    0x1c0b0702150a060b120a0216120f031a04021b0f0f0601150801063204050a0b1c1d01090506060909011b051b0a0b04020a0e07050301051e090f 62
    0x600401c0c1d292506420140c4199009a1081c0941402840c07008108044003a4001d600810018500f030b1407040d680d480403168200031740f48e034a01840c02c00d1a42c1d0340140303036405400d00c500e810098120070b20f00c0909404e03104200c0c2807186c2c1d0007251000f0ba510f21a5040488501941c040310000180d590880b6240d800301e00d05030703406000c6c0c0400042d001e041c40070994240b9441d51313204040c0c1da090040654515400714001c5403200e80601c03141114440b03580d03c140d003500200d03030100d807110701d070004024080301d058001303803544082405a90300801490a040e40030b10308540005ca0300ca00800b40c0c1180f448441098403005601b444c07800014010003113042402001c041d1178401c829940c9081c0300b07090307078400c1a14800909982c24443c3e0030500c6071001d4000c8407010000494800380d201d10b52841c1107403101080d11005042404e00c000c51406001c4c0400030107142c0c641420920f400d00d40502640014810070f0702a05c0c015042c003440401c011084410040018045500d905007510032000010080701c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 932775062 1250 932773812 932773843
    0x2030a0f14010602060f07030603080307020a0507050d080f030402241804020906181518030105070e010219060906020301030609140c10050c100e06151009051c0b0702 73
    0x50004041d1507245681d060b151240c0042c00161100b2a6003001200003c00d40c1041603520000480000c4821009501501140d4002c01d20000181443c44c00c0501a9101500c11005515070500003088082074940c400e8181e410540c40c1d0b41d8034004281d04000b0b0203000010140c42140d5254500503540162040c00b2111401d00c5d600c101020521080380300d05003406034011014090310301c103044038405400310b464010f00603040781000000744c0444ca811100d859034103040c0e1002400d1181c142445507a0f4420382d50300d0018228280d410001c0e48034510343c10300f00103500d9900611010320002c3d800c2400c910794400c40441d41e0350303900d003072003030003089034203c01c544680c900341d001040e042d000100308000910080c0100c51441e00c000040c0e42540c00f03082a25020302581445080c513219620800009054000240c0b1540c03030f111961404200700942064815864000132040c0a41c2c0700302000f0a0f41c0c01901c00e00c1da4900000e5088041c50b902d010001d045403010f070104a04654081107a103014810304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 932776312 1250 932775062 932775071
    0xd110c150c010c020102040311091503011e110a050f0307031b0f0206060103090b0a1e05040c03170c061b0c010c1215030b0f043f020309151c02030a0f 66
    0x1060f0403800d0340b1403484080c148001c06601d0400c18540000341c036030411b28003804450001a0708010071b00795807c205462400760b02e0400341d4844502140142100c0317101e5016058a006207092000d030807400303078141501d10050080000740e4498029441150101210000700101d4030200d2001003510810a8040b001030086501140945d40070380101c0c50b510703034000d41e242203950b9500040002000d4030400f841040c0040103040011000c24070615005034003170440e41002e02c0c21801d08400e48564014074919034030080100ca8580400881d220782c00c058800e940707600007140365280800714040c42000300019481d1403000b05807990401079143e03026000140511400030540a40c2e043c45043c1c0c800540300e803000303800041c4900d900380442c40e440f52050000081e07480074400301c0391210103c00642c42028004035806104410390503116010303000070384021072a141d55000800e4460741002403000308050042480c0410b1041c01000b00c0700c2100c0c070301c0c0454985c034003000f0004c00341c40e01c0d650603130b003a034a031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 932777562 1250 932776312 932776331
    0x12070e0412030c0914010903020d0809011116030f020a030209150102060106020705130203181b030c09071b02040615050d0606050717071a04081201060207080d110c150c01 75
    0xe001d0000f01d0b80240c1c039040410392030801e880300d4080c0280e2600d41000050740300400140c1c2c40c0c45603007880d140a103844c01c0e240d0b14088005081c80301c2102d007151160340510201e22204c68100c0701c0000b9680e01600f07418001500c1d00c04200c0c0f1b0801da0700003d43c402100ca0400c080000815910084404241d007124140c0c3d0781ca00f0243e0b16890380c0d010300c41e00100034560414121110b0b800a42c2c10014002e021200030703410740300d400e050590501c40d008040e500184050705610f0300304080004150100d441a042e4102030001074051550041608400d03051403c1c03040c199a80c82d0301c5007008100010700307442002e100240062083c0d20512500c95083d1900f0f1010030100e101c2c07000c4e106003035403022121078050f402104448240e0440c5504440c108a041305584560f02c040c0011406544568200341d1107950368081c05440c000143c200c1030131584a414100006000003d032490700800c2400c0200c004003103801068100113001e12142e17004200d4194900803004c1c0320000704107103030140000b00400e01d207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 932778812 1250 932777562 932777567
    0x80a0c03031413110f03030403031d06090a030b180d0c02031207080a1202040503070e010608060d0c050f04061d18061501050a11060c2d0d050612070e0412 68
    0x7019074802c8014510a4000c2c1c00240d9001c4a00000c8a4002e11340e1403080443d00c001ba10303540c82a00304030000b1702c4600c00d6075000300728480c605a0340c2c41d00306c400350b0809000c1404141005a503100261155807840046100355590403c000c00083c41c82c0103542407010100009030001000d26000c03402441030000b001510a0340a090381c44c01b6502c120540e18003055980202d80103200c2d0003001c0d602075820040014195002c0005800a240341801c03c6000d40c900038014240702c800030080c50240510180c0400004c140000d00d40a0341c5d001c46175415040002008100101015000305240d5640002c0e05684559071006051051400100503680104400071030f603120a804c0d1800c1400e40e80181d2603802d10742c01103001d801420031500e8003400c81c1612210b810702e0184144c85030b984505001545103000c2051240109020b5101c00e003003540000c0321100800280b04101c5007003001d40c0e490300400c0855690100201000e4440c004450100b5110304240700890707003d440c211703010920202e4208601c3e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 932780062 1250 932778812 932778851
    0x3050105160806181f060e0907030b0f04180213020d0c090e192414010212030c2a010b18040f26040605040e06030c210307080a0c0303 59
    0x940182c0f0440b80801c200780e0200890780054074000300d011703000021842045822100100800741c82d51b40340a8a5100800d0100c0c4550291100d810142004416240347c0c07901281e071b03800408240e4000904940c19881c031071694105080003540130803041d050503210001500a01519443c100301000300030382150051390344000c28450b80b0b1561101c540041e07039640c5d01600c40380d070307983c5000800f0030440524840a0504103c20790f0b8904000e850040521101408030010150f4413401c2c002841c4c1181c4e10f030071744031803030000a05111141c02c0c00604005000320303080c411040c00d2130701c2e94840d41441c4069030460103090f6200c0c460b40122102c0c4001e42604020569190180b5040510b030502450710741c4134050b030300d1a0100d107400c0d460b950080b01180516039600600050225a6445880f2810300c126450230740c0b400303480b132072203580b2800010340503035070b56000480054500081d240d4005228050340d815401041809856601c000ca0414900c540044100b24298840c0c0c0d01045120000c00e44c03040d503103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 932781312 1250 932780062 932780071
    0x310020313060504050307060f050906090102030709090504050a020927011e020c011514040f0e0d051b010501030f1406090c040c03140405071a09010215130b01030501051608 76
    0x42403124041c00454156404190468042c4041e40c0c9014160307224030051350840141140010b5a5208100760070000b4454190056003c034000d40c914204010014205901400342e120422340d6403000c6403c001c2c041150584055020705140d1051911240300101c1414401001c40000e40f007c10382c2078074440c180300d28400c17852541c000fa040d421000d0a190001d40200520504a660b2001241e4104a01040b000010421101c3c00101080e8040a000684241041b040001403c207204844440c0c004034008020701c181d464000e442c0c18003020310300c081d81c086a51140c415440c200003c000e2001c3c5401450300540904d220040244524207196601c00d0200d56824264002c02000d07081881c06800003003040d5020701d0080f0340c0300c1f01c401080110380b000350b03021501079000050405c4542600c4020b0075120f02c594084504214403200041d4885d25840042480388940100040d041242c603900400d00e2500000248002c0d82c5920b442402030509440300920b030120900480c4080c1d03c103011081c802c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 932782562 1250 932781312 932781331
    0x60507020d150f0e0c030c0603160c0804031b0609050609090a0e070305030d0b030d08070c0b041e03111009080f090a080303070c0201090501050301030317060301110c010b03100203 79
    0x41c12425110040d2150030507005400c5161241c000880c0b0441034041c003c01c0c0c048104c060100c89102c10b081520700044008018091a000d0081100c00b08000c0035506500c00355090903032060701d0700e28040169210701c0d08002c202030410410516042140b0030b42d441680ca00341c903020a550340314010400613014550358241d0040f00000080c9000d0030542008420031400022606950746075690702c1c1c01c682100012081d2144e1b181148480751804100000f4620080c1c01c0c00455806c0c01d2100400b01480410050000c407000f6020a040002c001007180d02c07c0882c00641c84056100d2400824480f50030201c03289500c946c1c1c0654040081c0d904c200d020065100040d41d10304404458174000703a4001e02c84695204a20090010f1100c40c01e00003144125200da590314400d603c4c40c4000741140480d908140d0420405100520001c0d40024540d03200d80b00d60340740d40d500c0d03031344a80c000303805400090302c4400c02100100740c0078a5000d054120135040c0508400f92900324190004010490000300c0d9985031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 932783812 1250 932782562 932782579
    0x902100804080a11030906070302012003070804121214040b0c0901050409091b062604150e1e0304080601080f0c0907020325031b0b072706090e0106050702 68
    0x44050040c100b11007000308000c1506c1c01c0610507000203110350072120059000d80d44441300d00c000600060801403c60020406460650421b0000203014001c01040240300408035100c00480074010103500f072016011071020f2162010110700020701c0341090b41d080300c200d110b940214031424000800c0d5200b140c0706075a600e050a14110118001d01032040c002e54903811101140e07151a0500044c1401901454450040400d94032000464043c2c02c020801b500c09038020511001510001382d04003038448168001c00e250025421071402c0400540d107014058811400740303203450700e020001e0402c9031486001c0d03030b1050780d3f504141a1a030111a0351009190003500d003042092400444444d0808640e1040f241410400b80c5080001104e4034131801000702a4840c441c100355101d406884400c22030016004450740c90340d14002c07810300103844202881140c614200e4403602500d1252424030f03d0204011300c03e540c8010180ca203001c0c074064140000441d41c00401c10307501030b004540010754007500851 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 932785062 1250 932783812 932783827
    0x6060302040c091a07021207171207080a031a0a03120306050111062e080a15090f0602030a02070209190e070e15040609090b060a12170a03150306090210080408 70
    0x200c01307174089001240e0000c200490401c40e11010000d1102030720340c0d60740744803039180c468849030300e010245000240c5184041145400003844072041e28100b00300d504001c9240400c060109404c0049407078040d03044040c811000003400380004044520401c2500c0c10014a41c4641c0111081e030125002c550440d4070090204010070300d0044a03c0031400352400c0b9500c540382000070f1885481c015408001c141c0d204000d004c00f13000c2c032200404040b208600b81049858416513407146d007848010300140c2450341c0803000072841225a0100d07046c03a94000c0070700e8042c0c40c1c00001e04200500450f50b00e144a0316019035980850800510320080e2030662583d042141d80f501010407421420100c02a009521114009040319aa01035805100e1045030a07455a142c004148840d08445500c4410710702070607151500071540c13119941512110701e0b4610303070b80c8080c40e241c158050301b4003440d0280b0482c1c00480000030300c00e403948100601d41c400c56103c60410039000b01241d1520f41641c011340840420402c40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 932786312 1250 932785062 932785109
    0x16150b0f10020106050907020307061a0f010c03030609180c0905090a1104110a02030a030c0f0f0e06250506090318040915020a030f050a020a0f0c03091206060302040c09 74
    0xd0400e0380c000d02c00852101d48603004103007508419600e01001d03900204140c0c0800046005100c0d00c0c41c080d00701c00200003103460008401042c00c2010506101642400c41c0034503120741c201202409104e54280082d01400c0c040804c0f160b501c51003559401c00c041008250040e44d07000300c81c01070140d40c3c0202a0369482d0b0311240000c8500b03401d6140d0140e42e803094031030b1401d440000b50050700181e802542c2c654001000144c1504c1502c00e00b4000c01000c4065800b6003a00400d40c03910a41051500c010a81000c1d80442e00c2d52013000e189103101a01881c1c920b0070450003d01034070b580ca120b031064900640701d00b86190b950b40101c4030221318101d1030030261650340c01d0503402500194042d01340e804884041c2421a001c03131f4440480c940c006030f00e9a82c408884d454601030141c0011025508510b03200030390700010f04c01c545041c4014200300510b200300c0249842000c184014081e14624200c0d000014900a001040548403c0340520b0420a14982c2c4034040c0c1d60f09001c0f070b0350920030b10040500c0d05516 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 932787562 1250 932786312 932786329
    0x105070b0c090a0603090209130203060a0e0102090a030809010230070510050901020a0908070e04120c0c060302071109160f0c0b0f01080f032b0e0316150b0f 69
    0x700415041841800036603900c401c10400142215200004c0c200824014404621030007403c6524403046041002c005807030010300c00ea80061030301c0f0002102c01403488081e0182c0b040c040042e90100b200c55020081c440001c0c02451018030036000c8804641000110300c80d20809441e034a03503102c80c2ca08824941003280802010744a1007071003a10030300d0342d40104074001ca502c10b459582060f9400310b03404c00c03600d80000b0160098503031107006115076480d00e031501039500c0c0010300043c9081c0e5090708036904140500c0c81c80700d6103a803000418030001d0303d40400900a40042c82c2c1601c010101c071080c032980342018400349004200d2011612405122980305646080d41c00007001c0402c03580110030300c040340065485a0103000302503800b52155140156491402491086000c3c1c0c40e04100b102d50121300c000c1710042000308502010344403054250840ba4010182d41600102c24000001c41c100c0c14038213400c2c0505018455442202c00b098002c0c04403084945c08010713503400c04c00d1034080c21414074020b4107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 932788812 1250 932787562 932787571
    0xf05010c060b0907030f0c020c09060d110306070c1725020f040905031e0c06070c020303070b090303060411160f020a03080a0f0e01032009030f160303090e01050105070b 74
    0x502299000c0058080b600403a8202c4103000020780d40c800e0651b00000500580005540c244005c1402080441c0050803003180509443c3c0700d002007c00303500400010221811901e40001c0035a521440e15a2000c0c20311640342404843c468201d0031581c8018000f01d064401c004c80112900007905e46000300300021001c886401da902c5103044248500981d15805656042031050000d903841e400c180098007104100343c400447c202e1024042c44228038400603101ea80542c580c40d0546894070b450000c642035110386a0044c208801c880c041022400c1f0000042d0300a450940d401c01a58030030304902d648501071f800503e10100000d00780c12011a007007103810b04806000030b0040480390303600eaa40743c459910003c42032020403901071440f0f500c0b45d081a10214104002c5c02c042c0500c8000422281d0103240c1d80907405607503030303010070300318071549003000303041c1d19001060201c0b20144c14071000c0c0e18902c403162004800045c04000049100602e0322000703412070b08180c54050621390340c1c0d654107040180041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 932790062 1250 932788812 932788823
    0x30e06070501200a111203041b1a040e060d020603181911030706180509090f07080c030c01090f0b0717040608010e13050a080a05040f14030f06010f05010c 68
    0x24419050b15850703c1ca8181039103240c0048a650700201d050140c01c098003801d04000b01d402030030020400c9580c40b0112130b0b005602540707603c8890382d65030500b104ea4203540c22110760303500c50410808504400c40001c006442c0c90b2841e1055607507a050400601564030400250400005d00c08680c0b6298100d002d20214000d44d000d4a810030701081428040c80b0507084192080f03500801000d41c1800c0500050011746910b250040203000d20742d1214040d03403110b01c151402060341c0310004502c02c00500910407420015800e40f85010b80e04c4a402e5610608402194824028150311200c1c82d8001e4102e0401c903054200004002480d119500310160400d06080e140980d154610700700d0518494002e002401e181c1c0c0b10a0300d0355040019891082c0801425125940c80c00c007680e00c0400d00000d1518080f60340030346490350f900342c01d18003129980500c2d8492001200190b03400305055003920000000c030780c8180d084426040310003000c50303a502c0080c81954200c0c3c064400510055101da01001056070052 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 932791312 1250 932790062 932790071
    0x4020c0a12200a0b01120c05090c0909090c031009230c0a17241609080a0302030c060a18171b0105060f010305090c0d1a0708041101080103030e06070501 67
    0x118200800b0745040c2a40360425007250180c9020400e5090585000d480008103000d144816030b550700b819078185000701841111100001920140090112510f194016000342c1441c1440440c40d541ea06404448602c64001c110a03042c1d83d07141c40c410004402d401102039011100e0091102454160f10416444540140f1f18003041c5921009940310041603107242188082a03141056800c1001190001c222280b00d13080e4095030401f04807845401244407960003039400020601038407001c1a40d07000c20f295010f0360403400305040c0c000c000340c102c00c08030b00291151a0380f501c80ca03004666041440200f040d0041d5550400724540b10160091050740065903481d10405e00900c00a502036132002c0140342e034540702000b01da401c140c95004808902824240060700b818451304d502c0d00b05042c0424010394455204030305002551350ac118040d0040080002d00303041c42107005002650846d0190b884028034881300c0c0565101301c808904072900350703480c0c91408001c1c81c20001c442d030000c0003d440f0b541d01c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 932792562 1250 932791312 932791337
    0x509011b17071a0106020d301d1e0d050c010b0301050a051e010b03130c0b07030201020901260a0203090c032b110c150f04121104020c0a12 61
    0x40100001400f60710701c1c00c0c030702c080c9001a0210000c145c000108641181802208158100f154820308188a440884003810b1001508205444410307407080030b1030405004000b40482030342100e0525480c502135481152500d40113118001b4001441c0c14250700c04491038240600c0b403c090703c50076002c2c00000c12010180000a400d41d001540d82c294016507035818042c40d45550060b98a02840c0e0740740c02c0d54a9854140c0240c860700000f844426100c4030403070804204142140c1d507401500542c1c441c16221420380c14024000d41140c006140420400500d100e410003100356203141c030150f0403001207907a903902d00890000e9000036241044a11561503081156070b0180f0134803a20550302900c002c00380341051045201d020811001c80709109118181d4900250046915082844190b407200c1c0d43c1504800000707458802d504102e5141c0e4004036001c1040c943c80102d01d0035240c024200043c070484034400304803c0307100b00441140310354040e407403400000d8181c2459085804407820302c0e03095540d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 932793812 1250 932792562 932792603
    0x60a050a12091b060804030806090c040306090b150a0810020a0507080a021005060402160b040c030b0c0a090b040510030b030f010903020c0301050108060702071e051e01030501060509011b 82
    0x21070b07510440b80c8032094003028401041000f042e00003007035107281420850130152000723000c0060162149014006d5100002c0300300032808110b6004540c841c0e42080700440f02e051045510708103640307188281d441c00c400c480851505201c207400f9255000050100320084001745402980440b2846042c00010b00080000c0303080030024094005c000c1d00503001144460001d182210f000601c9184118410700443e950050f00101d03034000c00d03500101c452515242c0741008400000d0039800100700e1000c0b10700300003885010102070501c10724240c42c1c840c0e9281c1c0b070700d52001c2c290090703003d1503401402c4e0381180442caa11036044005080e5024040e2240884851012429621040000c0c2c02503031020544218030f0809110f0036005081d041e002d000b8608051000a403525504c1c420500c8102d0b83c0c400c01040440d010030075200034400140003130f18010010000302250380c5c651809501003071500c2c00004815005104031395050340140d5403015803800c96001c0072038500c42c494003a1081081900c460f184d814 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 932795062 1250 932793812 932793821
    0x30106151205071103070201030b18090a031106070e0907170c090901050a050d02090a0f0c08071701050325030506070314090c0d06051302150a02010f0605060a050a12 73
    0x8000760740d1030115180300d942010a40344003030901e104118441040c0141248040103681c0e1142e8246800b0070800050000030744148040480b050071041401c0a2008040380010600302d110700c00d44916001ca0381c0380840d240c80304000c031200c03008144004408103542c50a10f0045500021a0605660310411417010a040007421100015043d00c005140e090038a4008550b500402c1c003100c810f901542402c0211741010340d1140700030300519262020034104107258001000880385e40d481001a09041d010051420b541a2140404541c1600c00c4886001042c1c1c40c4d54140e0304081d0003454040440c284648032903400b80c0b80b8840668501c0c0000c40080d00510045005444a41c2d01041c0c640c500020f150b00c03c10040c18464260303001000c40030b9152241144400c42d42d40041000410340d0f6030600c080003602401000a5016a880d840f1010301441600940722001e03007540200204035150b408041213406500880390300c0202070211686851140c1c1c01440080c1051a1031643c2040041e03c01007540e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 932796312 1250 932795062 932795099
    0xa03090f1a100503010b06040608180a06020d05070c020a03082109060610170408030406021603110f19150b06040303030917040308031b04051201060806060306010e07050306030106 79
    0x4000d0303401c2c0054030040014a5000c1d0034100d008002210807800002d4441c8a188a40d0041c0b068010000e8414807195855100400021040c2c03003a181c21803804400a5005cac826403590185007001003803000307101d140c18088456024001901c49421600c4120964200403201d00441031082c060704100c000d0b031030f0303418003480b040001844181400010440f4940c1c100301088100500500b05910f164800310701550000d80001d091030f500d890b14100b14010b80f250030803003680c05000c203944004056001041010b480c07030312000d50321104031108450b0307114400401c04001c00c640c50300d1140080350054011030707501a403002c030006100541c90007240703658000d648180c01013a40d401003c07041c00000034400740c03400701441d0168074080c21981c0360285400042c0002641079130800d68510305000800c2160f0103001d00620011408400c0803000d07002c0c003014010503145009080100701c2c1801c0005001d816100b001c015202d1f241c0c1c07040c00884403600300402d103940c55074840d41c002034021021402411038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 932797562 1250 932796312 932796353
    0x60d0611071b0b03070915140703120506040507170901060302150a080718120f08030109020403110406050102063106060e06030f03180604030819021b0102030a03090f 73
    0xc0c424541c2109042c80095844115607072420070801050550000b6404255402e1280e04408200c01ca04115440003e410200a00d9000050071b0400c0c1604401c200d522400da044007841241e40e0b000901068801c01d8400d540490000d14400c114040b03001d50303403503126803860300014005903207400151010111014a90030b808000481588060388503803000d40c854030900700620945410009003141000901c40c140380400c0c4000000c08000d204600300b01d0a40d005424031744c6950f1034285401c002d5016210071a03881e40c80700110669420203010700f104694050300a0310740350740c0700d98048404841100c64901401d030700c28190009103000900070745120303008000008035907003040340010110102a0a45101c1c4c0d005191400014100104454003080d40c2c240f005900004600440c1c40750003176810040006a01080c154000c5524000013185400302d035088070014031891201c61490388400300c1d0a40180c00c00c1000315000ea00036002098454864103074640380c400310740c40d20502005810741003441c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 932798812 1250 932797562 932797583
    0x220b03010510030501061d030319020f0d020106120314040807062c130e070b0318070509040305030105040b060f0c01061a0c0601031e05030c06040c06090e060d061107 73
    0x80d0704120540881ca0000c0c0e080c00c0105504008014011500007034050b1f44c202e4941e410b040c2591410300540340440c0c10900c0303d603041500000082e455083d8030b0070360380062050865550310a07105006040885004100c00100101d168600712007640807050f60340200c58041000080b40c1c0c5080000c4c10041203075540d000e0015886035001000079002d0480504242c00b8220320b983d0340d030303900b0b004901464003210380041c0768910789050030305190742648401036000c2d0100800101d818a000e489014541c0d6009a9012039102c00070080c2201c0151400f40000c1da0900c014007a9040503440f01c0200a0000e00a50610071101c00c2c0c46900d60001102180707076511050200441c01800310340b0080e05407000c407a507090510706e80c04d075035035a08140701c050203140f00c0300e01041a202d444c121a860080d00034080e6955040c4041910395610070648088508a0800100241480c4159130040990700e1190000e509602d40c6030800900c1d8110000c02d6a01e40c1d0740303504c440a00c0c1130b82002481501e100b0303898880e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 932800062 1250 932798812 932798819
    0x2030a030e0f09010b03191805070f17190c0308030c071103060606301311030304060c120e120d02010b04021201120309090c11011d030f220b0301 64
    0x5603102c0b0100c002e9000d0a1100018000d21425100fa0703644800b40c50003220300b90180041d5400030b0005801c007102c0005044840100340200440c0d00010760340b5180c85d1030341daa6928034114106004d440c60340100740d04480201c280049510345d400c00140d0180704941549512a2105545a801919402c0c0c020380f000503040204076049060240c0098101d0241c4218640304000c45c09510400d2542035080145200e0f07480035003030003c03291405040c42c2910490a151501001030039003030618080d1041a00422404c5007460000221000c0d02c080d6510805030002542c0c9a810a1052490f10010320890b0303102e040d030030b45600c00c0d04049010104010200000b480101a00310b402c0c262120b400b0b43c0c010010703441850000c0b400141181d010b104001543d121604044070708d4681e03070304101912400c110b14606111340c8055954032a5048000801c0013508405200040b04000108586243c0041c8484040307807407410080c00002c0c82841c00c2e480c80c115000301c40c2d01e034000680c1012074049004001032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 932801312 1250 932800062 932800069
    0x609070e01052817010c08091f02040801022214100f02150c04061106040b04080a11101b021501031101050d0e01050a060f030b0a0b1c140c030120030a060302030a030e 73
    0x108488200c03810f08020368107008c84c4498491885a5003d00a40300303034200c81000d402c1070740c12a002004880002c544965885202c5001c585c001851084081d04007500424505110314040181020041c400a0713162140341c0c6c1950a001d54200380e00540c0504101c010f20300c11502400d920444111172a6a640c508180004d0524481a19500d029520000400000400e008400c030b8225400859007616030000c004101ca07111809101c069540c000c005002d091480781360007441e110007031045c48181c0d40e84040001c9983d2a84003112101c0c20070f005004001085882c10408110744040c501180303000d40c00104801a120200d0004071203079558030030007080b02a00c0c070808000d00002d1420325003540c519100c64808460203003903a030b1035594400c0c50600e0381c2da503003141c010b01090380902c82c00495181d0404c580c9200741d08140d009580140300d8004000c1c541032280450740110000c580d041c992084100d0300b003c2d080200a114100c0d80ca540202c00b5075020043c40244c0c0b480307170340d60310130b2050a5000d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 932802562 1250 932801312 932801321
    0xb0402030607050a051b0f0a030e09150d0f021c0b09060c04030201050a08060301182102160e04020321180f0a0902070c030b10080609070e0105281701 66
    0x2c0707000c1001c1800007500031680103040307a240c401507071610b00c5c944040e103c0c100c0c2084000350322404035101c5c8860000405802c41c10710130102c0e8080303501440c0fa55511461002c902c020443c510340c40968010342c10001034100600c035001c513002910781c04216500d00c4040002c00c1d10800140d41c0f0343c03104401c00183d11010440140d00150300c007000c0d4201451031380040c01500031500d44c94288034a60b400150541c40c2580081c80200620000c0e80000501d400e01d80d185008a6081010301301c0c6000c1910031250001502541b809030b5400e540049614203264071141d0403015004a81c5809000303503d11070300e002071070000c039812003201c0c0895a40d030b110701e03a804580940c2900c040c05030311004600c0009940b50303440e030021070f80e91800144c2c3d03418191801128078100fa410080c0690b4000050184901c41d03400d03040306a5451604441540c2c60b2840d045681c0e48062064488543c0442c005002034106200701900b00c4051070480390800980c01c1c00c0c00e100f86000c0d04034403c43c0500c4031114207201c209028 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 932803812 1250 932802562 932802571
    0x7060f0f02161506050a17010f0606030f050702121b0f0d0207060f080405061626160306050f0f0310231602280b0109022107050910090504090b04020306 67
    0xc0c104482c1d813800000c00c02201643c85681e074462200e05038100d001000390400189c11100c1241000902e03100c10015000304a0282c008071918070341070000d017013140009042441c1c1012603030741c1414280c1e9920520884c42884060a413107015820040ca0040010040350300b00c0340e0300380c014001c46401c0c82c10040c6403140b0040d143c01040382e54014840442c001080c9150403400000201410311140c020503508042501d45104c8200c0701180313282030554050b00614002c03604410304407507e004540084040d81c03941d0151550041343d8040164203407404009441162001806540d0000076042c0018200c80f1f00c201500f0b00c00c1d039100c03001c0b07004810200300c071365002e0301250f90312480310b03030703242000355907140419808031407044580f8a1142c2d06038082400c06c0c21540203c00003040c2d84c41340c83c1031010350414450308603005003808a2007803000c42400410f20422407950b51505210403081040405271040501c1e400380000307600301096071b89a60040c90301c2c1e580541051030040c24144180b61a040c0001c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 932805062 1250 932803812 932803853
    0xf0f0501080d1e0509010c02091e130507090917040e0103020102010f0218150f07050c0301180302150411090112020906040c1d06040f0e070e0103050c07060f0f0216 72
    0x100c3c841c0c1e1020740c0380c00780c03404200780d15045440b85501d0006880001d6a42800f96000c902c010410a0450b105800f407134010500f1440082e450301c84140001c1450b54080700100150000d1034240207042a80d400440c0e01401200001610007828109119036030081c0c03c04400207a07003000500a550b02401103000e451050f040c00c6203030402d16a032042d81c0c0325441e0a21071180015240d64410207900206450020858001c030503a00e02ca140b52407581da407640c031440341c002c0d428400c507200c044c940e00114101c1c40e50150050440621059000d21840030700410440e100c4500850100c85502e6180c50345000c0e120b5120401002c8506004000c3c69000003840c051059041015210825034400184c843c8950b001c0072040c103803039059000681d14015500092494240072500160801001c00d40390300400345c0d9100d000500b4404401142903502c100c940c2d541d261010000038001070317000c2d80071190940c000c10000408041f144140400d90727100c050840120000c040c1c050007440044c0c6201d5250300c0e202c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 932806312 1250 932805062 932805077
    0x6020c0a050a053003070311061b13031e02030c0915010c050a0b0a0917040b030105010f0201141014180a05090a050106060210060b0a08010b0a030f0f0501080d 70
    0x40c111100c2400303854000e00a44d850500020015800b01c42c00310f1400e4807454001e800e43e882c80c0c0d070341e8222120a43c0002c0151615800105010688900614501100c0307603801003d07038a10102a4011010a081108410380002c0030540044403200b020030203c00f9500020751900401d03240001071002075100f200c0c904103000b83c040d040a8010040e40080c20200e40b46e00b420f05169040628000000d0101c03805002004001e406561100c5c000c1c074405e015601822200100c400058040d0303000703000d100001040180800e6000f203112030380404071480017140b05072001a002125441c02d031f43c201800e00d409101406600d40841e0080c4420400307840c0c203201c207055850899122100900303c44106030303955002c108081414090006150b4001000b880032039074a110003903992001988050300340703240c040042400c510f0901202c4000c402541c034521907900f4250951007541c003941d001c200741950b85d200780701110034034001c0d0b00b4000c0c44134200040c0ba41c90040298204110400e0708400c01a11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 932807562 1250 932806312 932806319
    0x5030c030c090a0b06160b0f090d031518060e01090b0d0b07050708040602070311014b0804020f0a0b0f07110a1214060702070b030a0f0903020706020c0a 67
    0x69640c01c0304411100d841c11902e5441c5080e0040a0000c041508004001800a105100341d020304540e03a10503c03038240c041d600c400a0707641d0300206071502c1c90a40c0010303480d0403040348039401c00d02c0d0700803c0d020713010030740c942c0c800002c0d9800308848480c480d9142c030307060708100e20000d40481900400c01d821083c04101000c44c0000e40034658242c0090501701c000d00405c40f40c80c03240d03080c0e40c100b982c0500309680d65911054041d40e94034052000310f40012101c1400a003952092541514080c07140c00f00003a0411340800d08624680b2600d0900200c032000c0d0704800c080d00080050104c6d00303130103450703140d03890800e401800b640d0440c60410a0084610641c00c0040320000000c07540401030032214191191482d203801e0101006180601d41c0c400c038483d801060032201c001048451038410015192030803c02d08600c0d840da5002c03281c4c1c1c00940c01c038410410920841c1c0c00115170018080d0780014510080040710002c4680000c1b059005910092060046503010402003158200848094903a1880d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 932808812 1250 932807562 932807569
    0x20307091d04051519021c091a070309080301061d04050703150801050c1207050403020303030a0c030e0f03090111030d0504110102120915180a031b090b03030706090c080f1605030c 79
    0x220503081e10b1704075500084110581ca0900c050340e000304442e9005006502c4c40d8140125041c8180341c0640b0144034030750120745410b01a2080402542d80b112100d13007503a00c1c00fa811744500f00029403071504161100d08105940d612440340a1041000d510001500d2620b55004125020f694002c100142e140105021401030501c3c150703031044440541c2c604141e50341090032941401a984002e4051001006006204a0640214400c00c0c1381c3d1fa401c20030992480706840e0f0382e07507404051840641040280c0f4000394800d00500250060031800c80b807130b010000c2c00e00c10440ba81102d0a43c1c1080c0a01030751143c40d80e05124034031004810300c1030682030034900f100103a8800c0d40f841021500501c0000e01c1c45190300021500155003000900342c260250f66410401149240110703442042ca40d20301c004160000e01c1d00c50307140e040c4005001142400ea50b81d0742d41001f4400b1071010f8541c80d152035000158420108201e504d0040c4c0301000e000c884155948400ba61b1850341c0107540b0903000b4000c214843d85 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 932810062 1250 932808812 932808841
    0x306050121050c0d050a0f060b010311120c0a0e03030c01050106030c0507031e1e021b0604080601031103030403241505030c1011011d0c0a0302060d020307091d040515 73
    0x114101c41d1300c119504540742c214039041c3c541c100104110789004d2480140075055000803960070f800c1c2c034103000041500626001c94030800090b101103402003000700c1c41d0108a007025018120702ca040c008195050f06c000a85103400440740611541c1d1200d005120055160040084c8400c0300c4c1411400c04280742c3c0c026011039a1480460905590641d050404900c54003a01d903034005201441382085403a554000c1d1281e524690380004c02d075103000c0303c1c03801d810100100c03800c8401c0c5070054001a401d560b15003d04802003c8595450320041c00044081046a0056400114101030444400014501c4902501c0301d001520b0810031003840104030503100400c84034003401c1e044075008100802400d040d1a504100700a04206600c1c007031660040d840d1a07040b81c02040c4000044504c0300e81d00750b04100c600303100c600001790001820301070090490315517009190825090704041021548850740c140f81910b0300c03404a030500c05030006100c1840390034041d40d680305030503017610859803400b0f41c60101d180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 932811312 1250 932810062 932810083
    0x12c0307060c02010b090106030c090e011d1b0a1215050d06020d060312051b1915020c1603120e010e0f12070e180a020d061113030605012105 62
    0x29225410b08080034401c2d805040701c4100106a8009942c452800500401030069081d000c2086030102184016840400b2070481d000c2d5050340085501c0c0d54500d40070841302900c088211201240c15640c01e100e01405440c0b0908181d84000c640e10031444100d06403111003c140d41e9480c2482000c2c407060303e44000b02c02c15550880d01c00340c0c2e200c001143c800c004103400d03400540f680c43c58080e0f60340306a5210f40180310f651003030786102904e04c1c0c44102440c2c89031003664602c04004091580240000c1c2c5401101c0d0458040220050800418040c03541c24111f400c405040e1100c00700400303008014030106560304e0100503143c426001070382100060b10000c0780d606d0b020322961041d020b420440d40d034413825115580264081c1c0700c07021b40e02c5681107090761064a900d130f10030b46101c0a1104082e400146d02180c40d4009100c580c2e00c40a81e140c0301c00a0a144600b090503517400c00031405960200c010039070045100e036100080e41e42c945a41240f040c0850b55404040f66041e03030380c0c032000c5a800a5001200c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 932812562 1250 932811312 932811323
    0x5010306290310091109010801020c010f060e1b040b18130b0f060310091b0905030d1b150203090705010906090f0b0d06030b0702030c0613020102030a030e031b012c0307 74
    0x31200349045c042070062070a20741179404000500040382600064016144401c0c070700000f4803500c0071580506040c0d030080d000749130810542900007a410019030301c141d00c0800c00081c0b0a40f8040c2c4541548034940d028950070340d035010b41203400044c01e003460000c810700c002840104000580d242c000299011001100d294400c0c800403010500381c42040c1160740c018030a824080001446141c1124180d19680c0e108801140181d040010107050108440c142540c16580d24000010420500980350380c00b8076040d280706590141e2010141d40300c0c070040d40030f00588001018400d1811000602101c000c1d00f1110402810101c00c000310510b034800c0038199244100840c4d194001540c0c0360005009950003e80286190707414052265004001040100c0b550030560340d8079a00d81d13103107100000350b0800090059000b00b0040035401d04c02d9100c6032030340140c501a0307403502c4d100074080a5080007103034140729603940d2a400307150001c0d15048083c01450280c40c404982d6500c0c03035617113a10b90080044c06040e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 932813812 1250 932812562 932812571
    0xb01140f0607020121050412091d09010b060c0106050a0509070c03050f07060e030714010c0e120c04060b03010906091a040c18150201051005010207210605161b0507050411040905010306290310 84
    0x1c400c0800e422905400dc0c0140109840b94901941e00f4043e10351482954001c5a10400215072400c101e038000c1e1107100170fa182c0248840c115178007141c0c194007480f810701180c40c05200d4200007070407030302421020121807070046071983c91504040315401000f21a200d06a0302d42858591b100707411003400340256104407171071038000340e07042c241c241400f600220042c0e00600c1c200300465810040000f660585442030400c020f0107442d03625001c02c0310454514084045002004690b5a28298104004444592510003800740082000803100745460708000c94008145206a5113640e0910074264031111192014040702c2c03038900040d488555502500c0c411003040c2284022080c0303031410310030805501020422091500900f400b450f114100d410701d0004000c006400c1e46060202c015030241c9401801034002145003c0801005182007920101e0010040c4800600700b112845010700941c041e246c040340b22158207010540002040600800f0011940e5031740701c140c1c8001501d4080c00302c040d103002a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 932815062 1250 932813812 932813821
    0xd1523040906020409050403110106030201140c0a020a1815290c0d0302040f0b34022115010b270303070303090b01140f0607020121050412091d 63
    0x802038940d502000c0c0c10b09000150000d081502d5a001034820303802591444c4008041c8510a404d840c81884082d0004402d051010b440c24022002400e04039601d00481c0ca401445038041202403c6592010031007060f4070390b50701b160745898000d100382c001d00798240c00740d12401d00509050902d101e0824000302ca03034419000940b9646101182c00c00c10b10101180c4000c0240b82008001c4c1d802809100036121500400294045001054500c4400403e9022041421ba440c00c0380c04000e071011101748108400300440d02580b12803012080504009485035220840f005a640c5800b601c0c050300e569a04091004000c0c14002c0400d8681c01400280c80300b8002c200da242c40720780c40380c81c102c0c8a541f40c00000303070303c1c0d04140d05540f0501d4000d105d64180799082c0e0380c9900c5c4020301d021020499802412021510515181940040c50030610504012041440112602088030b400918414800d40e0354006c3c0401e2101d800d4000d500c941d0f01c0d160010949081003480c010300741010300402161015100401c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 932816312 1250 932815062 932815069
    0x60103080307020f0a0c1503141807050a0b0315010503010605030c180a0e0708010b03070203041205010f0e160801090f02042003100f050a0e070c061506050d1523 71
    0x99881341079801c101e455100450900d0700f6441110300c80c0c400141001c0b40c01c602814024061800441d0750707072000f90001c3e43c03070078020309a1252941000ca411b019088000c90b103542e443e18400c001d0007240b61190f4684c40d18083c0540c0f0324022001060502109100403c0402d07070203000ca80d03026103103103451901c81e94050a440300716032110501c1540045003a5011807086464607009101c2d1074a903a40042c103980c1c07010300181034482030b20000c00503002004103112002c200e200c100c042c1c41c03040d000050740b03912452100d8100e402e400744034611908051550303c07091007030b41c500b1805003030024020004da024558407d101e0103081d4400034001c62721106014410080503101c0d5580f48408005c45917249090038400d100b07000b00e030169800182c8900300124071800d10305103100650f03841c0c0d42549540c1d200c00c0c20603985c407036410300215440e41d100c54560030102c2c0c002030400c0c000d1455844540e110700e107818506040e181d1004130030003081241a4101308032005060b0780000183c080c05894081c40448010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 932817562 1250 932816312 932816323
    0x12050303180102210402030606011805040c12150509070219060506060c0d051308060103020a031e05030d020d110c0a062310080d0503090705090c30010f0806010308030702 75
    0x1406031300e80d035841c100c81e5400c1c010081c0d248500e208800380c070129500c0b6001510041840892a02d1214124806008500301a400015800c85c2070509980945510300c0900030b441a05590a1059481c07410400460522900203500070009002601c154400c4031400000800b80d84009041d980c2c4920101e8040c6d224841103038040c0d0125401e58203030191280010313119610110f8001944110a000020f030482c01203601c2c2d040ea07038000c010745d40481c03450b11900410500341c0d141d08102c041da0303440940051801c0004051a6922550141c0c40303042001a01c1d00b03c504505000d04201410002200e100c1c80224100302595404140040c01c80e10208100d0f0a900c1500d40245002600c1010321180400d55107411080314038a400301c4203054240141101d440c0000d450038005540400404e20031480c00b00c034100ea004c184007000d58100346480a0440c1541c80c11000007504002101c490392004018030f407201c1c058101001464041c0d0301e40715055a6500d814440600f0100000c00499100c1c1d00c00e01c039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 932818812 1250 932817562 932817577
    0x80a02180907090503060109090b1609051305160f050702190b0d050123030d0804080d0f0c0801060e1e0409020901030c080d1812170d09050712050303180102 69
    0x5800d0051400c5030028107140c040e030213114824450300000003042819402140d102d00d510000110881e01c4904040e0440c01c111054242030204406000c1074070380750105000c6020120071004a05810a81c032504100034003015040d080010300f440d07002029402000b22a15258103640c1401103256484004491001310703086210203050000e0308091403541d80d0081c030f068400783c814480d694a0381096083c0e015804041c2c031500f5401c403001040407103000b1480154054040c00c02149031511a0124000701c9410f031041d001443e682e059490b001a602000250161150f81450050616001c00103078101803510340c0090044074030160700d4695142e5400c001040740c0d01801440c42541c603032030045440c2c0780c280103c808901c0761400a0303403524400c264201c02b403441007410204441c00c111141c2060700040d00d040e600d04070905902c02508003c0740c014000e03440c5002d00013400c2c507203d19106044c0001580304408942d42e0302c0204000c913401008980d040321080c000241c1c01184450381c00e0182c0030703103903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 932820062 1250 932818812 932818819
    0x91518050a12061505010c08130e0408071101020a331a090703060e070c0206070b0f10090207080a0f140a02031b011802130b0307080f010615080a0218 66
    0x44001403031018240d0040502c1e21692041c01140007405a400314003040303100b0303035002401215248000c102110005c0c4481c04030803151218594803420302800881041d28101d4039410005031040030b1050030102d44c0411078092009d40301144d034070380341c0c000d03c16412402041d6101155202219441c2d040d8034445c03030744e0850b84040c0480b000180070300082185c0f43d016107019140d141d00003002c90348248614002e40c0c00291800e450341c0c88450f412038409a0400c0126042002000508080f850342444180b28000c00c0c01d8441c05464007442c80780c074603501503101d1419a03005015002c00500c100080e6041000103180c241e0070040707403204c00c442602d240b00030081c106000041c4403079001c2c1d0101c01400000072240050b50b40e031783c281079510300706d0b100d585070030001c031403035142040c018504180b04480140203035002107a00c64400001900b0b061803039000071601c0e803142c400495040d20a00803407004000401051031000d0741e80d400500f00180003000360404a5002880c0107084020b04a072040305040076 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 932821312 1250 932820062 932820079
    0x11202130518010602060105120706120b130b120307021c05070e040605091204080c1e042f070308040b07052503110105010f09020711121c09151805 65
    0x1048156042c000078040c0e90014010800007061a040041d4445001c1090200508040c1e2078144101d4210b85208030900700c2980301c02402100b613840841c00f21076040c8003800007680051000030800140c2202c0801070b8103030018003071a00583c0d181c0c00303c2070500c2506000322a507900744d881d00508091203900501c226160b06410700c010301c200c903400184500010700440c0c8842c0301c886c1c1007000c1401a0300c101300b1240c0c080581e0107101e041030b00c091031a048951454a4048407001c0c0068241e41b00c0b45070b80c003540030bda0302001c1203040e07a008101c280c0030817001c1c18502e00892038030010081d1000130009410b0030304403000302d280300703204a00312400d4810f541c0d07070202814035000d4031012130f900b5000190002401007191502c200c0042c842c0324102c4907650803400160b41b074103074840080e40183d002900d400042c5075040d5015102e140d04603401b803903c20064605843d009040d102c0c00182d1103201c2040040300602800b18000d10b44951481ca0410b0514849042000603131170700314006508080c0e04604003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 932822562 1250 932821312 932821339
    0x61308031201150c02150d092f0616080c0307020a090603111e120102070506090d12020a021b041d0313140927030a050409050a0b0112021305 62
    0x1071112906036249001c0012001c080030300210b41011285201035404415000035040110351b84000704100ca403d4400840d40600039180d08058060700c070b5288003001400120380364004001540d440c0406000c564a9090500c41700d01846074030080e1000828540000401c001c0b4141d0070000c0e105076a90092626105d181c480882c0000751096200869607000114410b001c1458016480c0032a40850041c00541070340003001c003d000c0304c200303c4009003554204102c0010413420701020748176441d00001440c1c01d030701040e001007400003402005a520307441800011100350b808504645103c83d0480004000c035140310004008107802c01d00c0384980a88049041060b083c04006006140341c0100761001d080d1f40c0d004849030107507094956a5110440704001038401c01294468400e1050550060f5a024070741c80f8803d29661007261042c02181005c00c04203c03906a03030059a51003101c16506110300d01c10000041d28410345903520003842500400c1c605112000c01d00003000a100081c4292300c0c50b0070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 932823812 1250 932822562 932822587
    0xc0d27050304050f0f032503020a03060c09060c0f02130e060a090b0a1808030c040e0a060f0609050f040519020a2006010e0f0702010b0a03051b0907090506130803 71
    0x401d1088500541031003030003071300914000780140c0034404041d001e00b1042e0b140040c10700303d062601544a40b141090100400942c45042d1810042c6104907070010703410f500c2d030ba0040d05190301d580c0070000700a810035064002803031400707001c0300d20b80d819581500b1140140810754060005081c040d802c074032681040100840103a00400d64160040340c40b04400c0c3c0310582008243d4580043c028035403041c50369030100140d03000004503401880c100d20a42016204c42020302c032804282c4446119035224803080c048042d010009200800c5c440c10f210310b80a180402103178444200300f920701e200d0b40d640c1c40040c0c200b4035840340c0724080849880f02155107820300400030342000c0d11003000307240c4c0b03117036011007001c02c041c0000e0083d0603202030201001e407135070301c400380c107621042d0042185046548078000aa134585030380c00142c000e540309101500101c0a41038907100700300c1500c842d241c424501c0e0070a00c0080c81c5c0211801042e58016600303142c1c2d07172107480316480b11440c05520030307210303484001464541c030b0320f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 932825062 1250 932823812 932823817
    0x70507031428110402041a03130503031f0b0304030801150e09071205010801090503040302130b1504050301140708010909030c0c0f0e1302100503040321020d06050102060c0d270503 79
    0x3d2041412512079143c010603c8204d00507401030749240031610004e5410b490140780a0340c0d02040c00c1500300403405003036491600f142c0041c1d802070303500308200001c00032103001000000068100755000c1c0c0d0039450700da01c00801c0700e901840307483e229844090a00524500c10121034000704c070064000320403070403c5040108800c0c0c0003128410100e00d84000400d8411040c0510984103420000450415003035800b081030244001001c051071b6a07803080030104070707240c4807e04414800e03c840d070306407103070702e000185420b40b80300041c842441030242c0c00304600e582c0c02100e1203054171240000044c006982d480c2c2a1000311180704080c00d42415800c2c00102e51201001440941e603c000c44440c1075180d448401c40c00c00d201d00e80096000354a80e500c981040d1081019691090003403900781d000714071030000140c000040c281e00401568002920750b007444c05a00403207004040038030051030903103008c08001159020700c03617880003840e0f103d405003c80c01e0f060410886009038003130b172007004d04105490318581e40e6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 932826312 1250 932825062 932825143
    0x71214070201181104050711010f0911011107210501140105010905060f0d0f09060905060f01121707170a090315050403120e01021c0b03070503030705070314 69
    0x15801c0000c0c2c1d83d81c81c0c000681c50711405900c040c0401440ea090b0081002402c03005000c0000c0040c07184410720781d44824000c2c0342c48441507880c0051000c540c1e08211071f071004030b4003d090521180500310745040800060034001c440c062180c02009075090060039100780002800a0850f40c20210340c4100b00c085100d4003030403110242c80d03c80c1380c01c1d500c20512609000710850600015002d2085144e8200581c12030644d600080c2c0340081c29442c07982d181001c80d51240010f5030180d204030100508400d07500c5a25014000c842100c0e01e5040413070399445031308400d0200c441e4240360003142c814100040d590504007076a041417200b0743c899594013802080480d40b440141c4a01e440f0244000341214544111360080c1d4055035501c20341080304180c0c02c042c007130b401d03d500d80e1590700b040b00b0400b43d903828048450b000c00694000c144400352100301071604000e80c12480c1f00350070401c811000650002185421240d0044842024241104a4a05156408007401001e6000b20180c42c0e1049801d150507600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 932827562 1250 932826312 932826317
    0x10e0a0e1002041409071806030b130903021f0e0309060d0209120a0302010c0e060d0c0c051204030b0108060903190c0b0708040519083f060306090604110907121407 72
    0xb140e40b01903003200c2c2c0300e0400c80865089031b0102d0043c402076100e80c01161800c1030140030b80103030484540307000040343d40c4ce40d0240c005800c030740085550200070704400340708034610300401d0002750100c0440507180d00c03614120900c20729000443c8610080590151a4414001007805c042450184009174440d8a2520101c0065191512001400703002c3c1c0843d00502c9005840d15040050416015005002d20400e00307040c09507848140000490401564803c00a030103c5580c40e00d10b1807620207407502c1c041c0c20246c401c0d0041020000210300c000183c1e401303110a410308051849500d1010b40d00003170280c402900c0784000c43e007000091604000d40b14001d070701c60b5084030300d50703078681000205085050340000c0c03801004008210f010183c03c08101340c00400070305c0312480b000411041d11521071441c01038082048a010400807103103414004282d021024502a040034585a40ca850540e0ba00d10301c1c442c851110540450003480c0700e236440f101044241c030070070881400910202842d401048410313100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 932828812 1250 932827562 932827579
    0x11401050111070f050607080c01320f040f1e060c0f0305040230101406010504031707080d14040203010528020901031b11060609010e0a0e10020414 65
    0x58400002a0507011102d1308071021903840e040c41d080104a0b800401c095a5029043c010544010350a01c28440341d940d00c0d1500354840c0760080c0310b07400004102c41c002d0048460013400c01500e20b00503a046540694403d4001d4805000761030802281c100c0359030580c10140b240200101002040da0043c41084601d86070340300280c40446081301034440132074000350400c001402210710856825035007400403142040110801c03231401d0781d252800e03c001c80c84500c055111141c800145c10000e244907013204081c60480d161038115141d00041030060700e40e1580300b80000400030103100c2010295110288403d60600c203007000489900c00a80041e507040c0e01c80c3d4a40000720b8030022403170303135020a01c141c6003050014a8208070380c02c0c4002e41013444441e05140d01c030181c0d650b6151100075401c900c0e0766a42c840fa02070481e2020000c0c5428002440b00b4020318500005018800381c448050b41e1100202c10003083c8517072a0302100c0e00b00f9680c1c4960b041241d00103e400314a0201d440f0103044041415515100b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 932830062 1250 932828812 932828837
    0x1050f0307120531060b0d051e2e060e0a09051b011b1a07090603050907060c0605060a05062b140117031c060602011a010504140a03050114010501 64
    0x403051800c1d40c4640ca21400c002038034070f0f400701560400040c940141c00c00100003101b00c01064200c8181041140e1540282142c1603089002c84c00c813000d41001a8000d02c28289200703c0456002040c10b060900d5600340d0100b04405011500000054440044400703181c0c01c051140c0c1018040400e4100d94a0181c07882408511040c1344c6080342d00c4030165240c0c0000c4500c002d100c0c104841d50304e402e580740200201445d00b0806010142c5005c3c418a0307649201a0b407800c00000d00300c0710b0207001e038a61900315280400a0310761101d03402c2c840300c1d0014030005194403000c0020b05071500e160b20090304510b0101da40c001445500c0b4101040181205008849104020490040341c0d203409005140d501300d48014852000c40d100d030340c05000518011a450030122003072110f0001c410000058220352076540900c40c962342801802e9880383c4540007030b10070511a01c0003800a0165021706a5a1401200c1c09079031942e4580c900f400440d00030000b0014140781060188801800340981800300d0384140303401c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 932831312 1250 932830062 932830081
    0x8070804060518041506050f070c06020d2601030b070e04050106120f110d0203040c12050714030f1c02100906020705150114090a090b070e1f17040201050f03071205 72
    0x301c24607405c00d8072507003141400420341b250782060711820504802440140002100c0346140c00c007800143d0000c08510401050040c001e544810b00762010303141d09113100841502591180e41902c1c5d001321a48040d5a44030011550441300303003c050340c4242004000188950407200c00c4140e090403034000e002a403001e0b80d0075002c3c1c40340e0100b1404034100c100101003c1d40321507130203550810f20810a44150aa95010719901200400c0e02560650882c10b010410300d9600c0070010400d070010f5028010342c00728000c4213901c0d802c1c0104001103c031722201103005c050b0710078803a001c0c020024480030408440380e400c02e14025040194210340c1c40c85029001c3d106401440a414102d4559010f80408010390f41d052205042015218030241902da0a1550010f611034a0740c07445200d40c5c2d6605602410560204008003010400c840c42e1115518000199140c2c408041200c0c116050710410322030720b0354401200c9501c2500019114014017000340300da0aa804135001441c020001028095600ea44620 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 932832562 1250 932831312 932831321
    0x11012709231b040b07060b0a12080703080a0b130204031401020405061c06030b0f0402090708070f35010e010b13050409060b04021603030e0607020601050d0807080406051804 76
    0x40110400c40c8400218602040c840031807115502c2011a810503946030401d62150b0072902c0700320340701515034000c0785c030b6801c1041d045c400030700e80d00b0790664816030640c40715101445900c00107000c00800d6030000c3d44052080c0c1052428078005032144a0381104d1030041e07c0290843d0008880c02c3c0d95400130040010306c14001d59080e580d000b88100e2410f00c5440e08130000d010400c500349032941d15248000081081984042e200c0d00403820802e85500e0244100084604020000d6091010003000c0c840d0043d0f00408420350000d681c0ec100030603605503184654101e0b0354a0b16000b014051703d5599000b038105c2c02c105c41c121180d440301200705989552900b070803030040401c1c0f904083c80c4c80300200b141f860705810a00c80c00f80294400280700642c800458140e0b40203410030f0307034191040747d004000c2583c54450341444004000c0078001c01e04048000944941041c805c16200304040000345080c4496103044509007988440340790b07a25035403180080c0040c1c000c503a400100c0c01b0b00e000c8020304c50506024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 932833812 1250 932832562 932832611
    0x1b080f0322080c1905030319030f05040b0112050a1707030914061c02070501090309082e0504150203250f022a04111305030a0f11012709 60
    0x350040300c888205010842140c4c0894114042c03014a000609441c14001000c06032403a0205002903600040090309582100082d180c00360700e00002c1101083c49032902c1810b40e20701244011409400b0305140b0b14008480750040c050b4140d000d02800c02484201c0100700c014400c1d220f403c5141e80d9072a05152070005c00b5200c54001c0010404050400c40c440e1001c02c0c20b002c0a5001030802d002a141c5500f101d013601d0040b07001c00c0c0d00282c203100d160010030500f4903240e00060300842e032000d42c001c08450300d5601c45e941021070345c079803001c50300308182640804e0f200741d1350b81011501c0785400d5500440c1c4510085c101480f40c410300024030003031446402445c40a02d000d400401d220f0280f08212001c0c082640004151240d0f11010341c04c640ea00c9003e0010340c04907048605455a201c681c016400000300d62003030b403095001c1030903180000c94460014903001e80114001c1d500314540b0380143c41001d1a003001c11221421074002c25490098000c06200703890800d00308001e92449c1205280400f00d6035203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 932835062 1250 932833812 932833829
    0xb0303040e0604050a0e19060e0a0201140d1d0606010305180a03081008161802040f090f0b0604090c021204142e0f020d0c0209041b080f0322 62
    0x40002d01142415000160010304454002074075800b40307481e41d82044c04e00844410903080c0c00400382e040c0700450150885c0c900c44000580030104155001034000400c01d180400d82500c0416140b5458100c0d900004518a605640310200c50349441c6281d15920110350040c00b0929000101d00740514201d400d2403014a56002030000ba40c15450980d801c14008100d6422102104000709528106001c20700288088040c0208150b0401505200000007090a98001c51041c00200314200310740710f020f0129040c01600013000700318940352901500d513040300350350400800140002c2c00c580c0d50b8850080e0310b103541d003038610641d01c04960040a00c210f100d101400040c3c0c2c0000c24981c681203042680c0355211039550715240340807100102d00c4414040003000840c2c4d00c12082103c8c0364041c01040f08a00e25803804081032541a40010305d14500034001410011984403d8000c6081007041e03400075140307031030884200c03100038400700703590398807038000030241d002152520610b1641145180083c2c42000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 932836312 1250 932835062 932835089
    0x6031404030804150618020c0f0321091908030610031406010e010c060f09050f15010b07050a020307180f05061c03050706090309090507020609100e1f09060b030304 72
    0x645909130994404c00603102c04642d6003000285016841000f0002d00c0701c0e002015884060091000e0300300060b907416110715400400c543c4038130110035140340c00e216000ca484500d0580781e1020191070841158048000e80c02e220307080d2401c0c8241103001d140b1500040360b24004d401e1180340c044003526180341c40050b201c000f40d0b000c15401e60082070106009072040c50643c0115106840341e000b51407072654050002c40c0d940c900501400414452044c410080000400e01210340d8490034107d8101440381e82680c0c140400d030328040100c14032420b264240c0040c2180c2145071140c00e541c03c031400d0040101946d900e08103903644074144a004081c440d100c0204a89070384241e00c4419200758500303a03812030030484100a8140020b05a109603515140207554540da00c60514441004a44000d400c4da015584050304000c0400c5c00001c0d00c14001c01071070800314419a60700e54092922141c1c0c501280450129001c0c076004a001e035002451050003801d003405555196010f164030f03842103014004158411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 932837562 1250 932836312 932836321
    0x2404090309031101020109081b060106050307120c050d0c0f1b02090f040f151e052e080d080a0b0405040203071a120c0304050f010513020d1a010807060314040308 71
    0x450720f201c20700010b0002103041040381d0b030780780310b1a88844000e00c50014210312084055204119242c05007126052807403960070841c10107040100680f282c88556600c81080c041c1591292060b0b5a00614840d802d02c01110042000b50030301d4010b07a41a0002060901c080000e048045080f0b0815a0050091314046e254182c11024074030008000307907900035111801034005003500301d0f49003124025100c000341110920500c3c11002010398143c401260a05080c0038030740b15407142002c400c0b1080d0034200f003508501d041000e00c0645580c00780c1954001c4d40100350045800094642c85020b881c00b0820070745044c5010130007114000d070b07400381d0035a0240a003841a403090351861010300c81d040c1c030650704255801c00c1c0f02c0302031041140c080103103950100600003008401c01154003501e05050081c4901d203410001d50781c3c00704180318040d00c200c50001004041c4039029040545080710214664000e60311801c0541da00d00c2d8030703c180d40000345000c0c0c8104081400d8407080b0701450341555081400d889 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 932838812 1250 932837562 932837573
    0x7032d09061a01020c580b130c05060705010b03010204120209010806010f06050a03020d0213290306100905190806100b0711030c0a09050a0c1409011b0b240409030903 73
    0x200088402030308204003034410b1b4802c450291000895408105020718000d45183c0718080c42e4002d0551880022290941c00000384403004540c140d031000da03403140c2c6484080c100503025050004a10780c055200081c00309490110740e141c0c000c0c440c020764400b080744c0d9039810340c0c40d40c1d11400d205420804100400c00d1101622580040c030a05c01c191401500b442c04201d0707900d080341d0058061007401c9803402e00421144c520800540641e045054150402e040c0911200e80c0620005010381c0c0304e41106114040d41038003a00948024080252101a9801d1007400b10a0a0ba109004900080c41842e00007040c03940b500400c10240c8090b012081e051000554070340310030a9220405982c14010346210003265126020040010a4891030114003030501d4001c14048640d440350030782c200710000151100344c150f420300f02c03821031b1002e182c80445400c0c418103526116000751740051084c0f05030f40503c111120b035044018800d030422100c000c40300c000101040112045180010003040395480100701150f03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 932840062 1250 932838812 932838889
    0x601030c0212031611060108010b090702010c080a0b0406030c0803040e0c16020d210c030f170123100203130609051f09081006080607032d09061a01020c 67
    0x3030041c00d0041c400d003010174026041120903042a0030681d90b500480e4041d01d0510046600192180000c00c030030350115034000c02a1500502c003016140e210003119074191103d92240c0300450300103141404e481c0c1c5400c40c140c1c07698054480c4400c0e000420003c00c010307200d00780444240108046064803500c07925403d10200c803140144c04c0d59010040c80a90481403011400c0b00c0300c0e00c2182d036a92001e4030341890040c1101c3c010314411000c001140d01c1c62005541411942d0b41550496408041038400b0405c08011444c598070645801c501d0310807418050076000070141c0142d0b016401061f004948421003101d0712072080c45890b510882000412010311500800c100d186042407425195141c1c90342e0220340741070391280034006502c0d81c417a01005000400d01000d40c01c40c07103914061010614158880d40c0711124440e03d00800e03001c901c2070f08040001b9500014260b07038000350074400080080542842d070828483c3e094090b01030f403685a8980c2c03402d03680c01d00340c1c07080300c0c6900e00301528081441403058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 932841312 1250 932840062 932840101
    0x6090901140102190302060601020708070602070b07152d0504020618180c0c07090501121b08063102090c09041d03040f0603050c0409050705130308030601030c021203 73
    0x1406181951040020110b07400c00701e0313500079001000c040c1081400289015200d9200e07c41a0304050b0080c403030b160780812040704803040b600c900c2da07d4802c00d0402c00000e038100000541054906000110001d0070342c10b2419610304814115840e00c1600c4141905544044030000d40c09103042248070308400c0b409104120b1180042d001d00520b40c060500451145000d407038500c1c180401080d000107859003040400302400c900d82041c085545015441841c100003403e004200b08560302d40c03900c6005003440c00320020b18039441141c04c035041800319a504030803001030b03289000f00c00e07110480f003c1014202d070010752030b4050800c2000c1e0303031100300342c0c05203410054a1039807007600d0781114100b0400b40c075840f90001040d1406959214601201520503a0301a40b0410903d81480e04006034035480d001a1021079200004c0440c082c2e541120803900c43c42035200744111a14070410110034440e4800103188140000c0c2c07420001803c2c415002d80c1da503030705108402d0240b8001c01c00116510049020b00700761 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 932842562 1250 932841312 932841317
    0x70b0c0316031b0c0515160b0613051303030b030303060d0624030b07031808040b07210f180b0403021e13020d110403021806150406051305060909011401 67
    0xd0511480400403d040c5020707050703ca00f00080014403076850002c42c03c0c210405207076291458443c0c001c003107860800240b00081c0602520030000341082e105e052096181d14041c040800052a0056041c80d8030701c0070352415000079240490a2840f4140001140e014032801401d52044584603507a0101408000315a80110300700002d9200d013800035440000040d520890f00410545800000102150091881054015038190140000c03500050898055540d000f00d81d03551800c0c1428851442091503040da101c240820b4088800380b5401443d01c03a45946642e00d180030311041281c00d0310220303000d00030441c111104000c00c10042c5848002c3d110a00050380905c40700d151810005003030400004001d03451182c0004101d540c103103943c454148240851107455041c00c0c11a000f06500c507810f0b02426480707030046404a90310355540b0030181130340c2800302410303691652603010003082500002d039800450158a81c011a440c076010b02038801c14031015145480c51707864051038a9a038400741031490305 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 932843812 1250 932842562 932842577
    0x3060f0a030615063636050106080705070203031303050c040e010203070504060c0f05160f1d040303050406060b1908010f08190807060203011d06032a0604050d0506010602070b0c031603 81
    0x11600b984054480b052505490130000390034101c501c4050810740c0d200840340c4a4071f040e00503c681c0d0781241c8002d4104a05291407926040e2070300c00300e0303d5813040034141d1182c941041c1000080010000c2c1e0381001c140c055809001034080c0f0103c0c17a09070b000c29114100841c40601041c1b1115200d40e0895001601500c0c22544030010f6407601c0f81801c141d03003800610f01c40b500f2814411440f29040340720050030013403082da4000000c0b840410580344081c00060815403500301003424004550440c0c0060710490713014540d11901c402c54807011199031303070006000c18081400040d5180d5000310050844484001602e01802c010b440c40440050b511411640b2990900220700811150720155011381100b980304c544031290f11100090621005081520940c0000030a00d05160503120f0000007a03070742641201d2018604002440b1402141c001703582120f00407c448061080005205049950310b40954900e9615999446042e21804400c000c542e8010000c1001d42d1001800d40c0110500034a05507a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 932845062 1250 932843812 932843819
    0x90b01170c01321201060f091a2a01020a021603050604081c0c02150c03040309030221030d061e0e0118090503180102010c0c0b01090203060f0a0306150636 68
    0x103009130030003040580040441c0d801400360642110419007400d44034141041d05a181c014100081346441d0003040b49030401203002c02ca103201d244e440c4091160342e0049910544229400d03036001390859840c0c080184601452060014801c5080b0380a136a00300e000740010380d8803504ca510701a84070050010307110140c010300c1d40d5171400740d109494080d4010750140c41c00501d403400880b08143e018008100c411010010310001980000440c0c08036541690b04504810f080c5108521130319403200301d07529074040081c2c03410f01c5e01c0e020f9208606986200350071140090b410f952588000b000350090101c50365040c00103208080d038410703100b40c000d0911140860700f003125641e9a810364001e103202c2d01045201050030f41c05980c0a004030100722549150510600506440c3c00c6c5112006100c0c0c80c90442d40080801c4141d2a1501c25440841020346101c542d943d4030704c3c0030801000200902001184000c1c8041080c1e8421088802140f111300c5261f006603420004e00b4001d81c0015400e086500b18070310000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 932846312 1250 932845062 932845157
    0x15060307050d03080702060a0c0503061207090906020d060e0412050705120406050c01110a0c060f0f05041b0515030403082502070807050402040812070312090b01170c01 74
    0x120302c0d41c483c0c0c2d43c00c0708a04251030007910f000340252001403514140074008003819409015242d2208088400c80603240f440c001c280d0524455800400c41c0c1400c00e1106c50506c102c507001050065034900d01042030179a0f400043d80309000580b801080c4c05040c6500c45e00d040e10407406030000760301542c1926842e02610181c0c61244c0d00ca076000c18040303100881d00d104d8a0388280300fa00700300c000c803106080c944102054003c0151130f010b68002d009503501e0412443c02d1b48594005145500c004104101608190500604180c006034680c0c459103440c1e4001f148508001c11580354101c01091420305686441e50103a42004d00248410200b0812001d55140382c511a00c41c02e4030400310350060500281894903150510300c20b41c0002d07002d1401000100b0281c080010030081200e20070080340c1d11410945000c4030b49907080c4424500305401d10340c9010034003083d548018125411288040c00d1100034140c0252907200075501140070511060715510241801d20081702c0450100d80099140c940d00c42c0c48 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 932847562 1250 932846312 932846329
    0x30613140303070e01030c0306030308180f1912020102120415140408040501180f1509180c030609182009091507090b030106140403060e010f1d1506030705 68
    0x2a10001540074101580382e50f01b41c0700c0d201c00400e4920302404000c1c150344018154980c00341c4114440390230350900000c028010700180814030011000e807114203000300d16280842c40989002d5903050003a0190301201401442120200c00c12590307048150b80da02d44541c84014004e030f4101c0400740d100c480c0084504c2d03007028940d03c158850300d65580c8132428040010900c015040e000907003801c00743e40c144410360362291003100303c4211000ca120004190fa000302c034212200d074010044400000000c40300421960014610181c0700d0ba81006038964508446087c0e0f1a09100c442c01c180c5003080300004543e40300e00394000e020702c5a01e900c1d9110f40e01e2001c50f50b00141143c496549030041c070070000308086581405500150185860842c03281411041c1038a48411300c0707010305202c412aa101d81d004020390030b41d4021501b212040010744040c04240d4068108504241c00e124503100c880340301841d01210a6518040903070042c11201500482104d8410001d002c16601d4450054001030350b40c0d42001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 932848812 1250 932847562 932847571
    0x8040503060f01170304030201051605160e090d030c05090f0622050a091401170c090f0609061e010311120103080c060c1207050a030e06090f160302030613140303 71
    0x3900b0a40c90481e4490716140c03010410011500b04000030030160380d00105980000c581d03600c85140002641c038090b4901809604941600500908000f1303e0500c9912480d1040a0715070aa80d0310703504100c0c0840440d0380740282070b800300c1d070b09128402c25030612901c18060391101614440c9020810740c20481d01d0014001001c20034445050148003904000d0501d9004005a4500340b08400c400300a40c00d59040501410b004000c1901e80200b0b00a810003001d0815040a0030307420351400c000200384810b0714211400cd0164a0090108030181403501861911140c0b007150326a5200781c00c001107014050440e402000f60304207004900391031078881d9605d4021403040142d00e03580c0310401c442c5428031000400c080e0020700140020203040300c40c00398a42d804007007032400603500c00408100350010641e4003003401e12803107038100f00803c8000c0010420311b5500c1e550100c6080d82c408030902c2c6024101070000039050b4201202066540702c51800042c010341c843c8103d407400400811605145810444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 932850062 1250 932848812 932848831
    0x403050c1e01091a102120030f06091b010c0204020a0c0210090305030708030903160b060a0b040f050418050307050c12030313230714040c0203030118090804050306 72
    0x30920304000a840000031402440c401481d03107807800d860000c220345030341d12403203841045049500310444900d2a0b000c01c00ca507c000015103241e40b48400c07940001041081c5e5020384039001c0d134402c500340001a0148a0b000342d400602c030065014044050b00006800c40ca03040c8142000d0b80b20040ea224006413403000c500f5501c022080807540100180000e81002800500c402e48400344041003003c0111642c1030b822074200e558a4503082e08a91952044040d01d09061131000301d0a420404000e181c00e000f1107041b01c1081b03480707849480c00c1140380705a102d08000c02041402c100524203240d0401481c4280c0740303420350f50640d40e50311754504591025804681e00c0d0810341310000a840e0403000684038100c1c0c28000c0d429841e004e140f641c801c10000c640503215100040101c030600302c2c9603683c0e03001110b02c0c0c03040d40c10281ea146821000c03200102200f92165003003003003114070303580b00005032412540341c0003100e010f000b180e128a400034110301c501921760100401000c50961401c00a1500444244 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 932851312 1250 932850062 932850071
    0xc0209090a12050301060e0405072006011419090e0a0203030408070501021009081206040b04061409070302030f01061101020403060c11010f1802011803020405042001020a08030403050c1e01 83
    0x601d05452070b01c2205403400c00f8031806100620a0544c44510f00d4103401040d0340014845e100e900f03007643c400d036194013a02c02c05104452902400800840c07924100e81030b0404a0030600310110400045010380001141d140b001680208003544040e00142c6d5400e070f0b01402d445044c1c02c103402280c190b40c42a00400d5850740000c00400095904110700d16040e030003034604102024256a800300103201c1c515004101c1000d51011522550365544511680c88004004212250340d4041c1c41680c6410741603851310595504002034417007130182c02128130a10480d030b4100c0303050b0308000068440b03184034151044159401e000200005201e031090000d20182a111507103c001041503480c02c0d66601d0f19500c22a600700b092401d51039140c800040c4169130b0900301200850500349255104009a900180d07109080000340f009010102c44082d102c5892000390004450800006a0740e480072204010a040f078200b0018000c00d01c02c4c0050442a46001c0c01e449590000d414401c0003203041490020761a55103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 932852562 1250 932851312 932851333
    0x101a090a120c032a06030c0e031605041a150705030918060f01230a0507060501030f200a030204021602280e0105090c09030a0c03061b0201020315100c020909 69
    0x14000300030b130030420f8241c0d40d1102c5070480310405260300b50740c4100d50602d034076821001481030294000b00d02c009005022100c2c1c2c003542801c59008003080340700701d5000302c0c41c0140c420345e1004502c1c440e05d01c1800141c8034038207080c1c08414564060740090010b4403a400140602d00b000d50350000c52000d150f281114100590404100300462000e0f002400e9050114448411000581040080306001c3d0f442d90aa52030f41c8a520040e910b82c8102314004150038030f00000442000000240415101d005115a0401481c9040980300c59000d0300b40d029400120300d0341c20401850560002c0c0740c0d000e51301c0c0703110020342074076400b242c40d20b00805030080d88603280182c4480ba01c01001f40e810000c2421440e913004c55458003010480f074030005000011000d0780000c40e840252010010388080c960b01440f0948401d649007400c000134802c0c0d003080e040f580b641c00150080d0902c14001e80380117103440d54140c490b0045120400c201946203680d85001d121a20b24414090b9a40103030300c602c9051040d01904c011600d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 932853812 1250 932852562 932852573
    0x8030103060e06060d030e01020c031608010516090e0406021902060f0c0a09050d020402070804090b040b0603150d020a0801020f090405070c030903082101030317101a090a120c03 78
    0x703600d80340c2d80154001010001c1550b2040c1c03003c6103554250502e01d00181e02000100d0406010401d01a054030640c1c00d00061094014800d10454610200800a41e110b43d41c1c50112444000380140000f044608240100388603560703000c1d00a44140c0c00103142002d10142c1ca001c807070303c98601c0f8015030408070130022071100311b00c0017541c4621250a02d91820380b01c9032000d0400811801041c0c060618007000c042103440c0c0c0c0d41155a1250481c40046c0c03115500c440100c0a80400c0380b40900650800a94030502c0c14500d0035a400780350782d0125140440417141c180541907000d140b003a61312002094001070302640130f100411044541e044116690180344052101b902e00c05822a0104950903c02c440031aa0000d8610245da92110300d240d900e0030316900005950b00c09003012041e41c00644000070405802c018070300f4051b415000e14030003030341c0c03510b030b458104164510441106001007501150003880c4400108a80c000081841c0e50007030300d42c0e0403181e0552132260115018100c10406206011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 932855062 1250 932853812 932853821
    0xa0315050c030c160212030c0610051503062404151704080406050706240306053d030c290702010f0e010c140102032205030405120a0f0803010306 64
    0x149031810300d5103542083c0c511a2024842c03e852000b20580d0f40c01c4104c215075a072407400c030440c0442c000320b83e06d035002d0710b612680f995001c1c1d4003400584d414034030000d22414820174442c0d040c94851070450035a07881d0000e00644603a060074100040c0c44403500c4620700b10600e0080c0000e40428038010038054003415028041c048508010111800801d04100c00981d5000486007130316200d1411030740350b2210b031810102030301c1e08100100300d0803103e1804541c1d10704103d4170501100d000b05400d000d152180b9000304038483c140e0046c2440c80c00a03031600c40000300103000d41c0041e03800185010301d500c1d90f40d480c2c80071101255042892040c1c1001f00e22800703904119600d0616060213404246000d04035800a045403020003082c400b030043d00300080c0c806a00824806510075000300c03c000c9c1c2200b491030014001e502c00c0311208500039651400c01c08120400e9251006540c0c400002d40c502820201000100401030301002403910800c04141c00250720010f2410680d03100300740d101c0d202d5065142000948 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 932856312 1250 932855062 932855071
    0x105010803030619050d061d010f090605070c0302151e13020102010e12031b0706050a0e060112020f090a0204080a030203040f1202220e0a030e090f04050a080d06050a031505 76
    0xa083d60341e00f17210395a00c40c4181421554401d00006940d41c0e0804000066000c05400503425442e0000c09803030800da507002810794621840003001159100b0703070282c031680d85810020f00168440d4010500c030403405144a42c2042e80d203456207071044600300c040e0601031011216542c0314904e118842c003c550702401f0350a0304103241006042202d1a200060320780d4040103188820030ba20019514002022100885080d640c10100034021450051101d6014103448903440034140f2409000040e543c41c00701c4860402a03004003400024000302c0d0030480780b14400740540710145e41c00c1100140c00c520030494084118030030380185d80ca40c0e20300901c00c0310030031180c0c4c400201003200350006d01c011303036800000c03000c50700c8103101c0d00c0000410001c00c14010426000d64600382d125201030a028940c00c1141c10340d04040844000fa007030b6071208980c46409105070340007000b035400540d03028002250742c80604448041c3d0000001c00c0c6a440f40080c0303000640343d1080e26841826440e22184070114003900f03030b02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 932857562 1250 932856312 932856349
    0x110a090807060306180f02040e040b040b0a0623060409060f0806090c090c07050f030301120203070801140f1b0415080901060f060c0203031308010516020d082701050108030306 77
    0x4515242c400640141c90041113517100b0703542c5508061140069040c0c40c05040c6071029208146001d10f80000c0c0081c1c10344095502d07041180000f0f84100e62402580151141621403007000c19604081c1849a1425020640d110030244404210a0342c00e00c2007500a040d0011540100740c40c4c201401d0400e000030707042e80e4160704501c844100d00e40305c1210054010800b4154165107044a00b4590300705200014000312600002000043c860086c020110040d03000702d0944070b00c541e5031100705080b9482c0100070764040c0c4c010000190084107503420158420702140c901c006801401400d4001603026411840b000f9460100744022b0f81c2c0d101558070f074400c24900c000c01c101c41c10310304034040c19540d61040c6410030100505840454030180107a5402210a40280d80150303140c401d4503018010444521212101200b0f41003049480083c00900c940142d884075a0380da2100180414240c03890118054880710030441008800024401c4500074051040995101d06240d07040250399041000156003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 932858812 1250 932857562 932857571
    0x130506010c02130f0c020102040501031d070e06030715020114010806060a15090b07060b0315040b130c0803160b0106050405060d0c0201061d1605030c031603110a0908070603 76
    0xa0760410440c1c440d00c0e404a580d580707a01c000f9030802d00989101900b085400c3e081000d9042a0398054000e002660b000340c0b014001a007508260100c854045000c40b0160780c807503841040521a04002240c11a0010701943c0f4aaa181c012140c500c04102602c3c4c0c005039912080c6a1a01100351943c070702506044000d000341c0d003080f000040862213907000d244101d8100b092801e207a1806101400000c104501e4429120181400c00c040107245014106009004200c400b41103d02e03403034a01403203a40e1040b0180110b4482c68244071700105d040104840110b000d10000c161100d08001811130070b50012444040c503502c81c41c00c18160709040e1710000a02005220600c400c0d9182001d444588181c0136000030f0008044908902400d02a44a034141c00c2c030040001d6424001842514491044030407401494202c08008446500c41192841038060003800401d0020003600e074180068440c515020800e86400310300e01a15500003c02003010a04408040110700014424803004003a40e080421 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 932860062 1250 932858812 932858821
    0x70b031906240e121e120301120f0503130b0306030706080c070b060a030c061d011e030509100f092006071e0b04140c22090f150603021305 61
    0x24480c25512070303900144144690340c169aa00c40c40c5400040740c0300e4404440d0000781403080700c02117003005058480c82e070180303c0307681d440e032041072080b00d040711034506185d450301d0010344801c03500d01c5d002002260580010490180c01165640d002c00c0689200800159a400d00d02c0c101468040d040d8046000d000c512410010000d14031400d80f091290400c00d409010b5660350001107031145550030060900703058003800f2070100e83c4000f0300844440f041d680c030200c0b04000c01c015a80f848546488900e5443c1c20448600740030320030303002903400504107030444909581041102c0c041d98010044d400d40b5943d03038032404040c001c00643e4070244035440c00c1c401d0650683c2d40003203142481200d00c054400390a046414000920703000d00000f0f00d0b50040032003c13084c00d103481c002ca0440b4007030900d14401e100384900c12171546014500c0b1209181208656004100c2d19091280600200441900c00d96448108a00450181d038030561500c2c01e48d4400050903425072040100d400c44246105894501d840b0410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 932861312 1250 932860062 932860109
    0x10807050a09033807270f1e08160302040906020c060718050603010e01030602070515040c0302010e0612070e010203091e01090b030f0a05131a071103071e0302070b031906 75
    0x181340365526a5500c1b00d05005000072407010050303903201c400010010300700040d025401120090591900e01c210300724076542c640f00207549030588042042d4444101404100501e000d6201105a80c03088a001d414441c1d0340a420b801e100302142c046001c0f803000b100c120b11200c901c0c0184000b80c41c0440d0864210b50400d14070802e0180140401001c06030f00096010500c4802c1004120000f464061000300340790601e820400d503c114401240030842c1101ca69102d031929200341c0d00710500e80024000641d4500c24201e488036400e00d0440e055000030400500c05d51200c0302144080d94081e108034012240d6200010300700c00050b8440c45e401e40c014410b2008141e040d81c0a0b0b40c001526440c04100f40e00d40d00400000380d8000c96000340303e0200c07403c440d54000342d0141000c0c843c202940340e165210425912060301da11420500412088034940d81910003081c19400030741c6540a84115070035180c8500b8051002d50003658019200009100c060613070461502400c0b016215042a40424180c9c1d0356a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 932862562 1250 932861312 932861327
    0xf08060a170a143c071715060d0204050711300c1e0c09130b07110a2402042601020405090105040f09170a03050c0405010807050a09033807 61
    0x40c1032810000f003003041000c210640c442c00b40d022810064400c00ba82d211024150018604144490b42c0507047d0700f001240325010646101324005800780b1003034581f607400c100c0181801441706041c020139511644c9840c0d03080020625280714007660303010010080202c951500b01c0075050b010b00c80c200700890341d041100031660300d0281d10080350b140400300140003e42c0c04c1c8255650441c0c0c02885c0c1508014406861445020302280031b452080000d8660400840300707824240000d0109a10048401c1d0008550040342d1055041e0311000015041c1580b8850050b41d20551201d4904441142003440b01444000b14515441d0301030000c6160a14080c040780300e02c001442118032035955140640000700d043d4020300316055022001c40321409003a034100507503402254030800020718100001e000e0100380d03800c072425900140c4840081e6950042c048507564850042d0307404110303500314000b0000d0001c2050349c84c60101c2108014943c10624a81e01c1044c070346501d0b143d221401c0c0c000744089603420109 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 932863812 1250 932862562 932862613
    0xc080604060f03080a0302040905040c060e0906010e1c02090a0902011d09010303080a0b0a0303091505030c070b091504060501031509150b06090a0f140a060f08060a170a14 75
    0x8504e611202c20748410703802801107a000544c41400d040c00c00040104800c01c100c21b642e0319803503000c400c24200e014040d5500c0704407001c602260284120307020728a001040700e103401e5807101e18401c598503a40d0100f0014201034a0302018151a404e03d04210360b0007007098011100702c00385998401740844001090641e0600c4058141b001850104082d40b045800c0001008000b03000030040035a03c4c0f6004141040ca84905070440701d00c0c1080a1a2038030a600710790203205400c10b09800d100142d2502003031000003818804861103514018101a00d42c032000d584110b0244400281541c1b450400070102040082c200042a191180040005104020502c2c0c910b0500d030000541e00c4421010610304e1107644c601c40c1e440303640c1800020b0074034440c20004044da00749000d0070740002d074601c0500121580c2406041c01040c0c80e1000c2c82503440c480c104155028000500c8103220943d40c003400f0031a000f90031124903a940201031b148051000303e0b226811a082d0440c001c040110040b006020903021403031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 932865062 1250 932863812 932863823
    0x81902010e0114071203060b0406021018020909010203091203040308131e08130b0702060403060c0e060a0c05011d0d08040606170703060b1509010806030f010501090c080604060f03 79
    0xa4140314141d100f018900100c10340c01004550300d070040d04011080e40000c81101001a007002d4003c2026410081070f501200c03160380082010480d111550401b03400e050007015180d01900104001581e0342e104e40314052440d41000503940c1c20210f80e51828a8403181e084003035a403040040c000000c0e80700390f0040e4426070b07041c203a00c590070710b62800c04c4a80ca15201121180c800c075200755000c1c050150f00a00e4403806080185810f0f60f40ca00078180380b4011084040e51005040c4010808106c1941082d002e500c0b82d880c0504664400d0000288e1503040038401a0014120041050401c42c00b4400c0c601c508401684e5200d40c08098071000d5500c0061040c1c010030440c80300040350401c00075400003c054242c40c04c022420340c80680301e40c0d64407040c502c81900c105082400c0b6500a041c0850040485250074400500e40f0030410300540f58240d002d485581c0501c6501050034007041d00303200b450301030503800e0300200301c20780c48840003016120003070032503031203a440e09400f0021002d82510510071030b644007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 932866312 1250 932865062 932865077
    0x605070905010512190c030b1f0f110a021504080d083304090b07142106120105040308190b0f0d0807120207260c04020f0c01060315050108190201 64
    0x42403175800b490200030321510040d00703208002d900d1507095000b00551b120f06544a405043d400500c6007030b03047d440841640421003100e03500317440e07500c500c8070080050070740b60850703090017000d9020a4402c949401074500d08800032805100307141c4207001d142c2d1340840c1d83c80c3c0800d03582450074060517003080c41c0e0004004001620a1401e000040030303490100d80390010010000c003103060801c0c0c4045841203410034002020709010140320f501940c1641c000a40201d0802c0100410440150301c00078040d00003903000306043c198000f241024065148554400d5944142c181440c0410501c1e0001d0070301c590240034203100080e4000d845a9070b540319500002c540c16180b0100e507041036801807182040c054058152180b410b201d1680000780c0100b213501c01203002c680001a0b101000c01c1900030b41d542c0c0306641001030486814545600a4903280c4140c80359207180c515080c0c201821104554002c6a103500030542c0602c0350401880390a005121413405040030001d0b010071900308402c2e0043c002d0521900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 932867562 1250 932866312 932866321
    0x3050d0e0904151a0a090204031e0f0b072115050d030804080d0b06030c0901021006050f12010f0609091202060405250302040603030c051e07061413030309030605070905010512 77
    0x8240c2c803840f8001170642e2003c00d4440501001a41c4240020380c1c0c66501c3c065500880d4000c1c000d000f112136009105620302040303580d00c994007290b0190100042094480b01070a8500b210f0b6403007848061031010007e008441c0c01c0b500c1c00d03c44510b40c0104d01c079076030103901c070004030390010343e56540306078807010096a81241d01c0030040108a118610358209030080100242c45612070020700e102c81c2c00344c080f5031040c03004060fa48151031150080035042a030a114511543c10070644030241688200c0000c40c2c8000c070b95036100c04603125a84030740c2d4004d4032000c5a0041c807803d06010742d0341c208144060021031400392240b90703032426003001c1c40d00348404440c0c5d20400c558040115402440d8010800e00c015a540c3c1801404030100210a58982c000c0240705000c0380b5800024601400080c0043c1c504240340440035107501c602d01542030030144081101d006003241100c080809180309440d160441410340c1840e0040b503800401c0881402080b4005020380c0e81c00605491400040c105005401c2da035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 932868812 1250 932867562 932867591
    0xc1b130510080a0f06110f0702040f0f1b0905030a0b07050703030b031006180504150c02010b12070e180714060c012c0303061c0302070f03050d0e090415 67
    0x165600980e103502400d941c00082042101340501083d0203045e007404818482c400d8800b6511500380c8118410f102008802d00600b0a9003020414401030000041d5a09140c5180f0064a49410030151041c020844005080e03400403d218040e00040e801408050010f50f90b1954038800581003600748034000c01c1e0f1030200745c03080d00b1014817640040c0583c0c03000e19215400ca400380800c0d0040b0b50941c0103502c04140520120701c45c1c01c0c802d503000b11401d4501004041510000c180c1404c10030115502c920480b409034640c8000388012400c81c000400c031480ca0300500400b84030000d0550402e807a507540d42d0342c0070101c0c0000c4c0b03070040d29048403030f601c8400d804c00c4c0044c2240c411501000195401c1c14181540f03003a20b41510700d9085941015001175110b03010340261248021550981c0c4203804400c0590b0068901c11128012480381c012200b03007a031100d413102c400c0481a40103d40503030003140b4170144c1940c84080e07440c83d01800c0d1800c460f1030a0a644900401e440481800b20969680240c141c4484 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 932870062 1250 932868812 932868841
    0x1031410020c070e07021b040522080711030609060402060306011707030e160501020601180e03030c030907090908030f071209080d0513033c050c1b1305 67
    0xc00032081150380710b60200c5920340716103851140500713040c180000520010b001094000030428519404d0a00c2c0d000030302004010074020300300448800c1c40424071403ca240041c90001580d0207540384948490280c90182040c0c0340201c00300d802504004144050f458000401030381055040f00c80300d8aaa0319000105d03045004441c450400c0c4402c20b0510480781e03003503032001c0e400a401c0720945000c1006100440c500c4000e0b88a1a40160301107001041101e01001002c0786501c8055400309540031107a00d46131458200769041c403800c841c0001800443c900800114000f491156000e0000d031b005516889a1400024070074421461a130b4000f5500350712400b5200344001c064142004960760340c3c101800c142c0c10903081048007134074000200d80e0451340e1030f004032442981030b610f0381c01012400c900700c0c01caa20051b168803600e01141c01251501c3c4a0b611062400c1c50099440503152010703550380302d10707090405c41215401031180c02e003483c2d07a46800f40b0214042e201814041595200c5a25401544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 932871312 1250 932870062 932870083
    0x1505060d0b04021606050f25050d14072006060a05040914010e030a030e0606150c03120703021206040903050306060c0705103b1c022e08040803010314 66
    0xb030b41c406004c00c1c1042042e500240c090342c0d000c101c800003559007007125440e225020078200181c42c0c040c4c0301c5a01261040d0020a480b80e0200f20101e107204c01e1407007050b007051007500c1650114040c8405582d0003280c9402c13030320410044d04010142030a041011038440c0d182e074083c0601454441c0c00d40c03014403516243c81c03060100a00000c0001c2d5080c030480d90b4032a049181c804001a0401d0742c0c400417480c00095080c0103400042136500445c0400c18101510380c00100a130b4540e0100f48441084900040e001c540b04500a8801598a001302d207042003007040c0040c50203106078903002c1060003090384041502e40c06003042e94019940c0c12054078044c40c10350700781d01140e801840004e10f04c00c8642e00c6900211030080e0518080744030601c0d44003010000b460160758100d00100c52a0494a03441c02e00411590041c100c4205401e0800c40d40106c1c41104403d0002c603020f13404c003400e406400030302e2080900d40c00340c02c2c40c15251a081c10b64584660303101c10f02c0050b0580d86800928252045d0900803900c2e00e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 932872562 1250 932871312 932871337
    0x90a020d171306021b04150e07230a030e01020a0c020108060a05030303090a020901080a211205180d050f0712030617061b0f0d0518010608030d1505060d0b0402 70
    0x1290f81c410000f03564980320640c1591000140461460038203150080c113441071a51800411803901b02804010030440041c20f85c81081441d15002d9065150505141405403000140903644c0f910140058152070040000111981c810051400d060340d00c080f00040b2a542403070580c42545600b00002c10a1201d40c202c0d9506020000910940d28400691840c0300c501c00e640a100c1680e0f103ca580d03458600307162014001a0030982500600c0d0740d68040e201518806051014001a0402c01e44044850803106507440d180f070340d00c1e4001944410480b0002600161802c0c614000d80464451564022190010040c0c810407000d450050300940105001c0d205c0598250300b80c80341c25a105650780d00940f134998101031540194140100580708880c0144164800d40e440e101c0c2d1280c52800800c1d0080c41c0024401c400403441802d500d0a006603070040460388000d40e2100304603d41801111401003603200b00e003402c0001005191100e10a5982c0100c2000e000114000400081030291003825101c0344c0b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 932873812 1250 932872562 932872597
    0xe0c3a0e03071103010c020d030b1807050d050c091018122306010317030403023f0c190c240201050f04200a0e070215090a020d17 57
    0x100d650010107821002d0003070004808048000d002d140c200c4d0344281116005800c4403032440e6060340a50054400200c02a045505403950003440d07030703001c0b8001c0c0c42c02c6000500028009e050a14280503981d0402d22202d025498441c2210025a80e030703c214603002c0511a1000765542c1c40a04000258010035005840c40b100300910301d0242040c5145401c0918103840007040070140401c009242e40c145e0341d0202501c5448804400c6012a84d00024001c03400c500c07035175003030260b42c420920350a800b440b40104500704842000c9800181e0600039441101d82900900002307424070b900140c641000280c100502c00194914204940241116001401540710042014805012140b480901840c05500803c003036210500c440b54071072002d50300541100c51000c0d81410002c000300c001901268000c000700e50440e0750f010028140300e8110f8465000d40c001461024103032003100f66542c1e1099005014102c0072009500117900700b102d541c03000d0514180554004031840544040315200d809264141c039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 932875062 1250 932873812 932873831
    0x81f1d01020a0f08010e1302031606021b01020a0807030f022a040c022a0102010f090b0109140702070b1804020c0106051504210f020a0303090e0c3a 65
    0x14082d5210b4085070000940c0c0590403000a07210b03008050686907101e0450b81c142d11a078407440041e001441e0140c1c0e08d070058800d108143e1842a10303901c0101900c0d00070703240c120820f040001038441c1c01100c003810f54014800000001c0c45500489011aa0505200f488180744000803803510b040c1010841140c43d40500d0103880c1c1c000c00301002a0b120702124207100038007401c00100c0c0c0b503000121215010580328010050488200540850f4400041c400000d40714118844401560761000301520300452101c0184516612070044140a4401d00030b140540c0c100b00c50000d50320004c910401c080404040341100c1100070318251141400c50040c420342d01c1d00c0407546102d000340358610415201d00ca8180b1107403940e5a016003550111550181d0b09103444001c84400804085007440403034648508460200040c0d075119035100281d4080d546500b200c1d81040b080000d5458040e054000ba07071428007240c021440b83c508500070481943c2244807001c850300c034007a01d0301e000d000e40c0c89158034100007001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 932876312 1250 932875062 932875121
    0x31b080a05161d12151501030e0d05180a03050f010605151606090f0c15080c04061110020f0c1902060a081806040605190501081f 57
    0x40e000e404a84410419078544119814040c840c80400704046080d0710312540a42c481d14109101910b00988403c0202c404101407500304503250004800e18003415060141e05012442c80307410381142030030100f0802d0500d14010f40d603294410504420000000f41d2000d6a0424001424808001400d05481e003070300c2e45010394941c0708800c0403008540c030703203140002d8914044032a08a41c50020201c6450001100038816000001130000c0c3d0703005444500000006000449802c012406003561175400c80c00c00807000d000c0c20032803903030300d04110898042c4249289800129411960b00b810700020301c13626030000c1c3d4101151042d00800c2c40b440404ca40c1d0040a0b1f94006005d26038242e00ad543c1c0d00d1800600340041c1024103180690407641c184000b101880c09840100e8203c00d2020b00f400365000005c5c1c001e483e10304111411503905444205101d882c034001c810245149402d070780c0505c240d40c10203801c59540c00209144105888040341c00841d510701c9079200b510001440307240024098420000c1c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 932877562 1250 932876312 932876327
    0xe030d02030403083d15020703051b0a30110a1205060708190603030512152b0503040305010b030717030901140d0218090109020a080402090403031b 65
    0x68000c01c2269001800d004107515044100c418258045009140d001700020f42c0080e07a504491248000c005001c1080d002c00320004009521603070041c4240c5003145020ba007070400c20340d5071a01015002c02c0d0008959502d044110541e400c80b8800f00c0c900c904102c0700d0418102d0310165141c0d1198030102d400a1000c4000c40c1711128a0540c2d50b4941d543e80d5401301465003508410203041340d0005c1001c00c82c0ca5108440c4150000025504143d030840411500e00840f00b00c1d500440102c1c20025002c940035a014152a60140b00c2030500030340c000442001c41c0300d4040c402882200c4400d040b0140c1c034402c08640901c548150840103e83e2915240c2c41c129000b070101d44602c5100344504080012000303031251900c45400303907240185091081c0c5a006455201c00d01c98a0780b001e00080c040d00f421200d56201078072440040b40040c4240150403002d0045042c4103820112850b80100034000e43d041c0c01415a581080d0305448946182d80e0b1800c00328010306a44005041d092210a03182058903800440d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 932878812 1250 932877562 932877571
    0x30403200913050615090f071707020a0b0105100c11010302040f030b18010209031509030706020d050f15010c021e04020406050406111b0d020d0b0a06030c0506030f0f0a0e030d0203 79
    0x1200d1032505e40072055100c40a0740310180b03902c00d49030301c0010700c00c07c00d0030055504103c01e400c046051041c0740284070701070300c0c0480c0d02c480140e03c041d40d07a40520450b881414014078094815060400c654900101800368800024107060b50800c5400c10f80e0348658110303001032681d000c051181945906e05001c8010041d9507101c0307801d0201c001211208010320859024400083c01085295000c031002c104a0750000c0c00b422040c08140402e03c045940750004100b0005090700010300c500c2d00810006840c4005000c0b11403010711a01c80a09d503980110b080500306070111104803c80b0740c1481014540c04580f42400c1d00320b400800c00103001d9400c2401382094842c107031280c08190441183c0265189144803c9000c5000c0f5a10944154140141110388450016102c85040719080c1c0b1030100e05c4d074066440b00c880c20b0341c2e01c0080040c4880d200c00781018142c1250103a10b94106424075211010000c0e080d4a1044c2648021408c90641c941c018500c80c0041e0b401d41c2c3e1100340381041f03034009400488 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 932880062 1250 932878812 932878823
    0x20304170d0e010e03090a0510210f0e0a0b1b0702060d02030103050714030d03052e0521030d0e0a060e100b1207090c03090203070806100803030108030403200913 71
    0x112084c491074010003942c1c9041005465070f0b403190b1411040111501c1108510b80c03e024a02006200099140300c05042c01c1e401c0b00c0c40450082205050001202c500d000d441420341c00c62400c0c1c50009400c0322016420006690003501700300480000301d00640b040d028002d500035400120040c810240d500a1412680110265000c0a940700d0700892020440340c1d5056050b04100e01390864903010383c0c06141c01204800b0850721079550010070390750440c8a008591005482108100250302e402400700b1f64000b00341003030084404840740047c4e40da000b40000390000944804502004c4103040266241c0950010b030140001d15001500c641c0307489404000e5500c0070706251102c100703402c21403e590442c01c800c400401190b868014664001c02c2c0d4002e0140c20581c8413220100541d4013080540003600c41c03003024100c28208484200004001070f48104115041480100448140070040d6000c0b00e8000003441c40000180e6100160801a48991680310301594140841a4150fa41419190b8444d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 932881312 1250 932880062 932880071
    0x3050a0b0907061407061d011e0e070302040902031c0504091a090f370e0d0807230d05060a051c031d030d05220302060d020304170d0e01 60
    0x804140b0386594180c02035a000c951168a601456000c10700140417240c060b100c001180d502c04200703100c11001000c030070300071a0b441d0158120302840000d805912007580c80700811805940c4009a62251200e00c00603100e595910400401d54400740104520030f21141c060031040f151940014060307402030300800c00d1603840c2501b800c0c040d01d04900d0441e00001d00412030b14a075543c11602d260030440080020500550440340d00d0b101c1061840b00664060031032000e140301d81c0c00c140d07107102180d2280301013107100ea00c40701180d441d95070083c0304107400a02034500f07c0c2d58945031600a030385071b40c69803688210300f03540003034801c4c546900d079480607004450489042c5000d070b070b0341d10070040c40da03164a000e1300114180f0900140041d0180c07414100d829040b49440540c90300000c00241040300f624005800700e403001540008036844ca0b0020502d044c0c030003111248507800c58011901a0007a1503031202583e50000209041c0401540b00a0310500040e0546544181c1c0c0003030382015140b0300c100c140842d03003030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 932882562 1250 932881312 932881321
    0x30614010e06030607090e15190305010f0b0609010f0c050703120206060a0605190e1c170a200f0105010312030c0302030910092108060a0b0304020f040e120403050a0b 73
    0x318074070340120921b84d1500461802c2403030300900070070042d00c0f01c500c0c040401c090407600e40366101030f1140c600c110b0200c06482407444c101a4207540548400d07440e4a860061800e04554a6000344c9080403402c1c6003c1c40c1c41c031040305069074051403a0001800c01c1c807800b8000810131180010070880031040768250f680306d8a4160600c038818403179020707080109005000803072075600588183c1501c203481d4548603032448003030000b00b082c2c20040000b0ba1a54003c482d05001401110100140f031800060b005174900350b000f14008000c22695031715055a400c003240e403075019030420084800040510002000707d941d492800c1d4104450f01402200800d040c07681103000140640f00b583c0c42030940d0700c007515524034412380e000c0c014909030700111100100b40015955400d441d01010401800940b80c0c00d2080c00d005040055034165a809000221402c204000068441c00c0100c0d01c0f00c081500c01092106200c08244c2c1046940140f42e140580e0128002050100000d4803a242501450010510342c64 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 932883812 1250 932882562 932882569
    0x20307090504051f05060a090e0309090114120304080304050105030406060302040f09120c0b190e07080d03151d0a02091e040b040e03030c03041502030114040b01030b0d020402070c030614010e06 85
    0x48903526841547c0610401c00b152858010514150000b02a00d103402c80810001e14411020380180002c01c4055192a255060a00002403c150501c0046041c2840c0104903076503403003207010301410400040045401c200068200402541c0c1c010400e209200b10594031200502e000d56054038409000c0301c5282003035010340401241d007030304850f00441699400304a29444c842c642e001410b080da031004820180b5000344992000790101c600a014051901c80009064034544200b814038520a002d0420110b800d81040c3c03400c034410304903603085942d100010700700280100c811140c0c00c0168180840c04600c80c2091041c2c8515003100c007004103110300c0040c00210385607400d0a031065402000460b03002c54085001d194004d11404c49060300150004014080c5d800a0780310801202a1012044030351519001e0140700030380078641001480c1881000584442803003501074003c61b0b00280d19000c0c04103c10920020f180c1028050040038401c0c41140100c100034403629030f1095a15002c01c01c10324 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 932885062 1250 932883812 932883821
    0xd1b0512060907171911090103031112040b031f030519290612030d140711010c0516020414010e04020a170c01082802040f0603090519020307090504051f 67
    0x1d43d00c0700144100c5d044401c00721808014000151550045102000b0040c1c2e605a0000d02071446540c90340e01c0600c1507121a407900c510031110b44107040c801e00050000c1020300307082d207038030841c41507200c440050138941c0c0110144007908090454052042404000340aa03c20f0090301c0344120520500480c2f041104e188030410703001c0b130510441202c000310b103103494042003440302441c41e5402e89203400e20110150702160b1301005003000f010152020029003682010580404c1e6500000a101c000c4141c2e1008085110710340340e41d1410144a98100117540301c60f0300c241d00d8514006201492541c5802860306030a20031035089100304160100815500041078010700b00c0c4030038900500203d581c40005407803042000340806c55490b60309031514110f854103040c4e00c240600c956001a40c3e01d082002694805030181c00c1403080c54100b01c84000081c800084010540300000c0711a40303030310840c0c40000d0130b040315940200141d90070101804140940814040b6103c0e044c0c54004030752260300c844003010341d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 932886312 1250 932885062 932885099
    0x303012303071428030311062502010e10050a11040f030201030b1201020a0c03120e060a020c1c0e01030c030b090f0601031803090915050d1b0512060907 67
    0x1600120001c0000360071141c5502c1000c03d000b000020340c0c040c220203800001040410070050f424055070100181038020320042101060310015103200d14016002200710003100c40d446240c140c12100c4190350038800c2d071101002c5100701c0e064506145904d5080300103400c007500c11030b02c49460324030300214008000c000c45080b141d0030440f500c5903d10f0b540064005203200104a0b4201403048042a1004000c0c4001d000b4040389403602d001c2c20082d400c0c0200101c80e0990100b01592914808603200e16000620681c0071080708805a59406000c50480c02d1003c40140a4800701190b20400c1c40f590304130401c405581c4083c0d80401c0000300164045003560001030425030840010030202d441c01d10800c0440d640194181800b054001032200124104c003032513070003500012040f06041c42082c10354018100c4071461000c004001d01d04200014a84081014004252003220512080d404101452100080c44014200c03000c2e2540a0b00d02a199001250b049025008640b40483d080c03012495a00c240e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 932887562 1250 932886312 932886319
    0x16080106120f09020402030103052a0d020405040501150807150219080c280b0c0717070303152d14010c05010b2806080702030a0e06120903030123 64
    0x544600c0e4240070041c40101c42880040d0346403204480036840b140003e500031803181c80201240e000026a10046d01d00c403000c0320107040014210701a40d5501c109000f00c1481e011500081d40351101c0c60411300401484031040c040000c40b09000400307601c00b242c58021900100c641d506420000e480498a541c60041d0b524084032918440f200414840c2000c1c12000c5400b0048a080c51804a000f80b0304100d0380940c64070b403010400351601004403600110b500030140d248142d041284595504000f5101004501c0f072440c000301d00d10090602c01d8010980003800b14418142e066190040981d81d9001d6082d511450f01c061900d130600ba41c0500c201c00e08480c100101c205004070030358011a030b04880041c09550a648414100300070b03039503c04a510080c4078610701c00415810b0301c5941c040306080d43d40101e0a2108040c00c100c11643c0105c06c0301c40030031107442d01802218540780060241d0103225404014115084100031a6145c000001c42c144c50900441003072480350169641c0789070107040c43c9281c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 932888812 1250 932887562 932887577
    0x20f0307030c0f0302031b24060310270803100e04030f0807090f0b0705060108060408070605060105071a070806060708180324060a0b19111c030516080106 68
    0x80b0342003410f0b2a0f030b0b1030720a1050301c1c5081c41c040c00005400d010701c0700f4210207030480c1381c40320304076440020900400300c0b440c09091802c1c545a80025219604022462a01c070b1315410420b8880f25243c0100328180d00640c1c0d203480d0707898603083c0740a06400403540c0e401c040d07407662000700345985c020429a1041c1c0e8169079400c82001000c100f00c401020103800351080c40080040441d040c1000c6040310082d00242d42e00545503101410f0017450070106030f00102c9541c0101c010301004c19000000c80d00c2e0507400c9a4040f82988401004a076680300e000700c050703c00c480028540f07045d0310003c8034181c0516042c2c0e80d4080151a954100852407284420081010740208102450074025002c60380d550200103095030040341c8d440250040c0100d02c2424004041c201104000c068680525040d02901da407480c1075003031218507209850202d0a501e402c005108038020400c2840d0002c0000d08809144400d4140307512008110207009803e013a20185248000a01140c4000d0b00c0b030810f281c101c8050b41d40d02d02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 932890062 1250 932888812 932888837
    0x11b0b04061d070b070b1008030a1d100809010f0c120b03010902030303090d17130f05010623010e0306130b09121c0e2e090b040b040201020f030703 65
    0x10040480100b5100c80c507040714041d11107104240020002042007000e2161380f14428036204015001c010088504562401414031810b0790020595031181e0b00e500f819022030b2188007118003802100079070540c0c008980d2280a8540c1d6200c04a2409250844024462014150200b4043e1098160400009443d907046901e512400c1d0708040c0c48004050000a007604043d00480d0940c1d10440f203040c1e065105003111130b80c01b0782c040c80c4800c01007180a0a0b1180b170900103040c074022245c28901034010040f540c40801480805c3d44007400402118152040c606114440488020020807400b0b0116441d40c2c0c014a05041c04a8420702c10400d41050003407401d031940d503130040710f10050941d4520740300321060381000e4800ca900a00004000d03448201d40003014948042c251a820440042c03140c000c007403100c104251188456000010150101902d510f020b402c200c010044017001030f0104450105000c103210900c081c00740200d000780d00361840d1484400c05107917030b1310071b440c002170014403003d6084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 932891312 1250 932890062 932890073
    0x70302010203250506090c01170108060103020d050309090108010e100213030602070309151718150a0f1d07050a030b0103020d081b16050a080c040e0c06030106080402011b0b04 77
    0xc0d5695030070740d07030315504003c01c50b100d080c074040d01140d19000980c802e840700c20503503802c00c00d4803454588080309a02550704200c1215195401031000074007400d000d006030820803400344240c91a259020f0a040b04c1580e50b250f917607000c0d14656016580074059001004880c5103540210742c1c002c1485540e5111051860780c2c0c0c60000c0d800b8003019003c00904980214565022046070345a030390700360f6207400002d6446c00ca201102c1802138040c0c10403581e0800709038004900800c9a6440c28650152003943d6034800c0080310103410700b0070001c1d003910701c1c1030814400340c910394503042040f01990088590907a26030b41400b0002d1121301005d0014200c20004000528111480091551156150b24100001e82c2d11500b03103140000216081038000002454442410203000300c01402c0c00c44100c09464a0003900b04c0d103442c400410580195140c1d080c0608034042080500c40062000d4103030383e503d6039501801041301e00c0580303080380051000e07030840c02c21601e5625882080c40c1c026110910396112983c41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 932892562 1250 932891312 932891347
    0xf210402041b05160602040f090603020a060c03020a060b0f030d120e0f100f0b151b161406090a0e0f0c12131b0b0405280b07170f0403050d02070302010203 68
    0x100c0705c00350208404240b2030a58001c80c0c00034580c0403008070b00142144108480850300c0c1d00302204000c4946503110220313900040c2c100f0fa85420200024480e2504030200d1401c0c0030182e025a0184a001d0080c682c803940408010f144d00404802080302c002003800c0345417195001c0c4403e4440703030700c01c41c4000b41406041d40410030181580c9400151515000c010480c2d1a400003050307016804081a101c0508030320185030707001c42c46200060080c0e4118100220003900c1c035802441c00f41c43c44d9801c1d0b805030707403510030466140080007403c00100f15603806088110310400c0f5109a41910200c0200307103845100720596003141915201f94030a80e80b01402441d48400c0503801340c2d00e21a039881d00f00111401e50b00306e000640708543d0015641e60030031080c80321030072a00b415000c081d515810002907801d2502d0045042e141c00c1200c00365a90800d0400c0300d44084082940c140130500000c1e40b80c0b0501c07006c03004008991240060b81c2c80302405160580e01c46900b444081e0150704104414800350b07400340107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 932893812 1250 932892562 932892607
    0x1b0c0f12032203050f06061e030111030c250f060c03020d0c09060e0a03020306040209060d06020c06010611150601030b0103200406110616050f210402041b05 69
    0x101d0b070800c0803003410701d14101004500074046841d41c220500601200b030046540d030808000041026040007008110039103101c0c400c5042983c0c4601240100795021b4116513031404035883c0307482d02c80c10002c0d00d0000d1540070000f00300d41c2030340070002c8500300e00f10190ba85400341c0c1c20083d640c1c40419561142000340200048420806500304003000101d6030724490fa00c0c00e004ca540d030340c403109410102c000d04400c442d40788071842412418010401603a0001ea000da0150b4160344461003520740e01c001c41c02c1e2109411001341141e0001c1003d0550102c00200f141c100e42e01035a850300c050301111001782d214071000d26000803841110f4009059035001c0e3b00310200c016010700d000958440c0d869050211300c0456812900140340028040140540c80031240f540e4a1010f0301500307042c2007550355000400b00c81044082400002705040344150310b60401d40300044841416a1003628254428150260b01200c0c128401c038546083c001d8100c0017084441c2c5038140301d484052400020b40c064a401e0015510b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 932895062 1250 932893812 932893849
    0x4140a081005150603090a0c06030b0d1203060b040b071e030c0b060a0b0a02060604050a020a1e140a021c0807020a02221b020c1005030c090a03020a0b1b0c0f 69
    0x40f83c80c0141d03c0b408000d6100e003c0f80c101402c40210180b9240e80321080ca68815810141021581c00041d070380c0700c0034040c0c0d00b50310200350043c3c03155015060300580b00c9603000e11514400032500150100b03501d80200f88083c8034001a0401c1d00200400003115107055002800040144007a5000610b090700500c1d0000001480c0701d21682d40c44001d101d003540100f50200050f0044400d012090071f1900036070b40c1000c4040419030400110040040103000c0502c0480750310314184003600e400a0094a9850748070501208036681d915603208060b60311458201118900150750310000c24252203400b486000e51016400391003034000d00c0c0c01704a0b9600703c0d41c006010b445d02e0402c900d40e01a10380d20845406c01c03402e0710304601003060502d0190030a80f1044070140940c1240d4030001c54103034044d0841e9486254003640d16262070700e82000c240324100903080250403c81c2c4800100310201d803400a410807820f0340d4000301a40b2440002961640c103d0907101c1c2c0c004c110541c1e44291858104041c02e440100f00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 932896312 1250 932895062 932895091
    0x51602010c0b070e0915060f0d02070c0b040501020c12070501030c1b030804021c1203051e01060302040f050312070807080730020303330a0b04140a081005 68
    0x3a2a0700e000e1140640d1540081004c40b440e0b14024105a46403940c400c0c0848655802c0000140100d13045100b1841c00d003d409200140d44031020700c003a0b044d51240c582000441c04810307102d80580da4154020701402d80544100d00c0c0c00e03851850089a2101c2d044008406411410f00d42001503010740611844072003440090250b2081d02c0f5130301d11900c451103009980b110810b060500500449807803101c00b074020b41c08041e0300c11300072900524950458480d42d240014041c0d54044082c42c0e5014100758880200080100015401d40c0c1600588240c0380080100e421495482c4100340d9660142d4901e2610440180500004500b190002d408100e00440c0100c1c0f03401c00c0b6035140d4140c1040700c0c0842d041c0b81c80c00424035482d2102c888030030220031050300003180f445c20001c603d01a01041c03d1200140c401c0320720f504c1c9000b40b486d49010310100f007000e0007065281e61103040c508140e42141c064003620b45c246801c10b00462500305c500008542095025000c108a04440513002d0140108045500c4644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 932897562 1250 932896312 932896337
    0xa1b080d0c0204231f120b0601081312110606040e060f060a0f030c06080a0603112101141f030206070311030f0703030203040302070911040513060b1b01110a05160201 73
    0x14846130078401c414061410f90121450071201c8403070380e0319800540700607110501501c000b40015640d9508070100b42429070760344e44d42d20842070b0780080c07c040003094003000d07080300303000303076030012414035864a8040554000da03403042c09110844241903d038003007540c032240200d502020600360054010b0406402180010b0f21840c6128148940350300440e840d03200d0990400015030300c4002c054000480c01414410686540c5500ca210320780700310011303c500300300d04080c020500300d0403400300d0040740b03a0001d000030fa03410143e6200502c6c0c00ca41d0038100701c00c0704120011340c1d00c0708603104003940c0d8024200d03802e003074280c0c40072a10a182c84814214520080050180c04d8044171301a00300306100360f40250303403890306180c001d050141551100c00b103541445d40702c2c8403581280090746c041e514241e40000b003844207540c8050143c20740754401c66001c00002240b41d8146204002d8002c1d400201e4000e0104001c804550086445450360390800a038090096040800e25032001c00c54403401454120411100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 932898812 1250 932897562 932897621
    0x50916030303020c073c1203031e06060216050a0602061801090506270a12051602100c1a0708070c02130c08090f0a050a03080907080a1b080d0c0204 65
    0x2d181c80b403032240410006111440d019070074241b00380001c10054403446190035007805881c0d010240007028141c68502031400150141d4084d0a14a00224184481c0fa900c1c82e003e0340352400100da0410200600b9400300c1c1070300b44080301700120740482e4001e0520b40c3d074078240c243c805041914100d5465480b03001080104000700b00c00c81c06030485403c00300303004450389036074065a104500503040b0340d085045070f040400c40303210001c60396405a05200e07590b8019585804a11069250002d500407228250100c1c5150b100300c0010309107225000d03002c1c81c2103102907501006441120400c000074000c0b40010b2000780714040c3d0030303e0b162000c0d10150395110450050340c240d407200010140000c0e070007410090b41100801039824002c0880f0040c2c5000741c41a02c40944403c040580602406844004601c45803020440d09000700000c009075420410345140c00c08a0380c108004a003400d000c00d40020540307020200c1c0d03460300b0f01c0880d10352440c860000c1d428440074281021840703900c0c89140c0c0440c4140e94 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 932900062 1250 932898812 932898839
    0xe0304080a060f06090b0a1a041206270b041b1d091b0312070c0e0711010605090f06040e030f0a032301050a0b1305100203030a050916030303020c07 65
    0x3441060082080e140240c0c1c3d0508a40c200d60240329250f00708030b154190b64031542c030103900759840c02444540d10354140d111801d4074400c03940425009100e0200d89800d11000d54800084081c00e1641d030b9000c1c0c2e050f4090890f5001801c00041c02c080c40d00400f1400107070760043e0000d03440d0300c802480e040c5c850f0b540000f0f5201031420406482c0c00d0019608002d0309180c14020081c0322500203411039140000c0303401003a41c8488070b202041c5e0403400020484240143e2007800340040280c060603202a01d0844001030042d00c1d00105140150700304800860207203429410300d48038441c411002c010719a501c0c400c000242002ca95070032990b002c208264414480084000c10310481240c40102d456080c60b99281c080d9040c0c0d4a5800380416954010700180e5036071540c1c0c50444494120032a1582017446900c04460016032055034031800900c104104190044040d51182c00e81c06401c125695842031110744800903510510701c0628115001e200203802540682003e100a208655206480301000444c10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 932901312 1250 932900062 932900083
    0xc0c01090c150801060503070207180b030307200306250c12200f0a120e0406121527030201110406050415050f04030215090d060606020106090509030d0e030408 70
    0x120b4180000d850850b42003a51280104010b00e0210f256140111000b500c418441c09440c40b414071101d01062040c290350081d0301640802070607650764800e01c1c03500c00b64401c007e00761010110303052030120265240100c1d0f1035118070782c1001c100043e40060729150b469141d107254400248469828818081990600100b140707000c991101c0400501507035400003040c0502000070225400701c4004400c020010800f065501da00000510200c1c901010a403a04145110115041403910710300145901c5000b030205d442c00c0c0074003281010805d8280400d03043e00c0070440000341c0522020038100090407242d07070704505180684000621050a0450450304d6440f03580118005180442c007400880c51120251481d00f1950410910b030140c00e030801c0d601e5018511010388190460741c09502a81101011681343c444020802035400b0a035141c1040103140d640070b24001503190520220b950182d521907940180390120045080c0f080f1085002c0c040c2ca40950b03514054001070000240e414810044400f64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 932902562 1250 932901312 932901329
    0xb06010e131e0f0213060c032c101125120b0402041d06040b0a0e060717090706050405150c0f0f01141303030f0b060c03041a0708030c0c01090c 63
    0x800b2101c003005000e45003d4044006403510411400c0030810368041e60100712502810021103e0319541000d5603880440c440c0b004294030303541c150020400c00008050642442100d4110b40401c440008a500180d10020243c01d94841c40f003440208454524205038412203220540c0d4482d1110826056040f01d440c0480c1c078000032000f03200440c503050041c1204100c04044042c8a4128914015600d100c09000500104a50808520303202410740181c0c07803070b42600c0d0484105040c008401400c46011100c03211440f102c070008912204408150101101c0b000e0340d496080a040000304008044250710b03c0b03c92a608111880d14100705001032002440381001510f100d40d03210369401d0944400101001e07110716001c1c1008440355588013030701c0d00c6070303058900010701d50f0907184241d00801018a580760700c904042418101030b600040100207540b0400925124030180c1203e24405010b03401008001480a00000790742070b510703001610401d09210b00104040d40c40c5e490300c950700007150f00402c89 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 932903812 1250 932902562 932902601
    0x9140f0402222918061b010b180c030412091a0901020708070b0a030e01240f050301181214160c0512071e120b0402010f08090c0d0201110106080303091006030b06010e13 74
    0x40d181c11281a4009c80a070703c02e0407a02d00c0c0590160700a4400100014110060010300d500018807900400d0003621204403a80103444140710604490303081110014014812024041140341c0003080c0c010848148040306820101c44400682c06023004003030052141d076882c44c060101c08041d8600309848452690450941c600700511700c41d44815039042907000382c1c144003514480130381c6503400715507250708418040c1601291f024200c0d00200190004504084086601580031000e03240d94492180b040c000d40c1c1c00e0b03035a54814002c40d070a03100d080c0507040e00a443c00f04860b0140107105440e400c00344102241d000d85454840d44030064042d0251032050840081104558000d030040074050320b141000c03c40713807030082c00d0355568041d1802d600d4002c1003c004484211790003024044000102d1200a0000176180c01210307640c0d800803640c1a0f014130a84086016280c05481110107070798103c44a803c007030307079440010b541d541c01208465410036446184030a0720451481000c41c50740c140c40040c40c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 932905062 1250 932903812 932903831
    0x10c150b03120a170a0e060a1505040612061d010e0c0a05031b1314041101170f310f021009140f0402222918061b01 51
    0x52a00700d8956014965440420521141c0c03904041d100c1300480a00135a4040c07642c45818040141002400300d052610941e000e108803420a908801610340c43c031104122001d03511401c02082c0c0740f00740705240401d1401010321001c1521a040b01807100350078111501490b400c02050390840781b4020781c120068000a40802040ca00640c0b036200070041100101001e04186180394142d580310900f507031140e0100c0011040c1c4040303d4114810000342d07003101840f9443d060421440d5580ca4104a40c00107015485c000207030701c4803000e07290040c44612583c6c2190360b01c04845209042c100c10792150240d071114444c0f100c4c4005800c5000750305114070700d41a2000740718410300031a540f4140407101400200481804000164144400c1d99202103403900801d0b4021404100203215041e01052101003001d40d1000c66a12a00b1641c219420a070b00140807030106051304c10860a01500500d401c06c0c00c01c60020300e60045140c00d444903000030b110901e070900400300070b0984070701e010074043d040e5191503540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 932906312 1250 932905062 932905069
    0x50609010609020405011d0111030706050a1103010308030f07170406020a020f0712061e1812020c0108010303030509101a0109050a0608040b04060e0304060e030c0a0e15010c150b 78
    0x81000b8840c1120950505040c0303000070300b68400300599003131201d0074041c000c00c0e07685c4a1142a5002e00c02903003038039035480c0711382003e1020300300886020052508012088a500c1b1549003264100c0303401141003821900c038040081a00c00c406820b030710810000c50032494220f2011485d40b4040c42c4a900016900e03001d40034041e0070425541c00e20105900318000403c413000da588200402183d01c82d1000641e03040d03082d242c440f5000100100b281e464a0544081162118903541c40e0040340110030b01c8101c603220a600f2681c40380003860550000307041000400010b4020341146820041c9142651035801c003194040302200c0c1c1807460303c0190030b9002d0b070328002c558200b02124007a060230340b0031008041c01c000024100c048090001480408090300240500c001680503245030181481178035600c80c1e440c803000b407007010411070b414820f02540c1100466464851307129012101c220b071040350b6031313612044143c29091142d08924180082a0314000c000b460b00300f1090007000b40c50100045142c803c2c0c1c00c0c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 932907562 1250 932906312 932906321
    0x1c0503090925080709051215040c051503061e030316050c040b01020c060f0f160302010b01080105010509030d0f020c06190e10140f1b011d0a0b0613150305060901 71
    0xb403409010058041c401403c0c0c0c00494901a14010b03144548040c400c4c180741440c01310400d0810a40308120b0781400b081100424844044071301c12180b18201d03010b402c40c00743c0507107c20b40703000d548441707040c00ca1501074245114280d4a840000d00343c2c1c1c240409a14072208611a10404641075004a100d80361b851429105010b0008000c0c40241755004410001c03802c03500c20700f150303820b000c4000701c0d0340c880440c2c6c010125842c41c1000c44041741c2416541c5070190280c000d1285482c0403801c2d55001003000d51242d0140ca60f6420014010300d25607030410000e807003000b241404541180550ba81d400116100c0301e00404041407001030116840c0d000d00b100900040542040e14411440300e450110581e9110050044069685205590700c0500032001d030010710815407100751459001c1c0b56180c8428041d8042c4141e03485e10009209246044c418850300c803081403100820000e200e001144a81c107000030860002024128000f800202c1c00c2c1c00ea4407641000d52044070103078401c600300142628207014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 932908812 1250 932907562 932907631
    0x5061b100b0319020316090e0127200402160605060607051c120504080310140a06050f0c06090304081b1f2a0c141c05030909 55
    0x81003190604081c0002d03207402041c00c005010010100d00a004c2d5601801102002d007030300fa08481159640351241d6010b0480650050420b500e012110a040445c0c0b48030010034180142984001c007034155900000c00c50a900c203011b14041c20a03882c0f01640316440109090104400031a031551913603c1c065003941c1c0e00900d014000c0f40144092000204005060005a512141c0402140103031200444281c42d414440011030381c140003c0c4814042d02c0c0c030055002d2804044c080c55507a07102d004c10602409003489140d04032060020400c585072040001d0700005030314000c070b0740c64590050340161400c54243c440003d19000003c04000b06c8104010001138100006d810854451890001950b40f41e101c5045002c40f040900900c8100c62181c80101300c5000c0070380f90369000c100820743d10b027249110002c2c116400d48035180c0200c0c01600c882036240c072047c8000c04403030200003190107400000e403200c0300c2284d8510050000340701607541e62041070310401d61211505801c0a050854042203a0300c0706 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 932910062 1250 932908812 932908843
    0xa020a060506191503020d090602032a030c0903030d0903050307091d0a0e1e0601150306031709130c05131e090203090f011109012615040605061b 64
    0xe140340c0300341642c4805604540e13443c0c0c0c01030b8103e4a000300a8020344a02c04900307149500e014401010003c0c580d014501890325401c946c0200011169250351600c8415030a250484d000e1000031914201e220040219040c00b906032420907038642080403d40f60039000440108202004000b00960700142c60b5004101c001d0780c0294041ca51760811000160281004d221a074445641200c180d40812049441000000b12117103541c04c42c0b00c1c1140c40740400e002d8200321144405010040074070900a10080d05d4205d180f002001740f0101002c101a4088070001c1d81084001d000e401410340b0174844e409500246448465840e189111032980c40303051500501315020311503400d04c005c0800004038078140c410808005039a5203d0300c120340e1400d12001003a451540c204510344450104d64006480701140c2078035000400d048401d030a101c60310700f041e0101417808280b0005102000d00381d4642d060131a0140c4006000b54039000410340ca1380c0700012502260360781c12000e940c00e000c20041c0d10350861080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 932911312 1250 932910062 932910079
    0x40207031403090a2913031d0f1906031d03121308030a020405040b0607050a030e0402040915080105060418030e15030a090c080607020a08030c120103140d02012a0905060a020a060506 80
    0x261f401414902c40710840c040d1100210311400c203035403556513a0403e811001010040030020040f551103403ca45401000c0000b400d002c60019042d6030442c1e4040ca40c50410007550510b0322207040110100c000829004a091840140e8408280c4840c02140941000c0402503551400c1c14144815108040c209074041c090800c20280411004201c641003542e26140145084500f403001501038055500f141484030320300710b000740d54020f9010380f090440781c10740024407040d56901300308030403261440203801f42d444402d0080c0000034800c1d41d4000440d20010810030241c1080c80c00000e1f560011107034040907684d075040840c1409650b54140006000140c010019803911a500a441d0f00c074490004220b21008804640b680d81040150340044003140e003500015a5a41465010904030400300315642c0070740c0e6919581d0900c1801010b0035100c950315621200703c085c14002110052411240d0200440000d003c240c55403480c00601c01e1000380d034010800240076052074021900003030402403040280d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 932912562 1250 932911312 932911351
    0xb10060806030607053a020d0b0f1005030c0c0307110111070308041e030f0b180a210e2e090f0501200d08010e0105040207031403090a29 60
    0x10070102d5010040c1030b902000c00794045100140d80350000c0c0388082e2546c4e41c001c6200001805036000d016683c3e65508144046043c1c1d005001d03116240d00c44098001361080c2c2c4007031800c3d02071001990004c1003040043d00e0820a811140e00307642214000b00c0354840354000b21406503a2102001010002c0301010301251491940d5224240c13081d441402d9042070607102081c9203083c070b40380e03e40055400c20014152100149051803581104603004040c140039907050301c1d03c1d4840084c1d80140168816480254801600c030680b00244034456038204002d0805060202501d40040c40c3c0c1048201c1545003078800740740105d03c088904024024810030202c124108036a81105d010344007156801c0c24607403c061703131054210506151076101c1c2c1e005407141800d139000d080d5000d02070728100d924003034070320b240c513600e403400c02042e071103550f00180000300101c0c4c1d10300e058075000700113540111060040322002c2545039100d02d085404484c001c826030102e845c9040c0140c03001c500896100300e00b0740c08070020042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 932913669 1107 932912562 932912567
    0x6090303040e01061404060206010b03060409020d05010e0c0409020a050904050708030c0a020f06070834050303090609070815100b0715241e030b10060806030607 71
    0x82c100c180d41742d0701c0002a055400340c5295901500d816440e000803003509401c0035007100e6000742d503100143c0059540f02483c220701482a4004152130102501090402d05813040c103a000d039050400301c030300595034050700d03600b60342049405040984442c21b105152584580040d410752000082101503200001000107240c0d100b164080201407001c0d05000385401103500041c14040c1c05d000c1c990048000100100502c4603592200c02c0340d0b40070b1281d40c406032480d440107551079000003082c020140b40900217258020398070710042001d1450062802d41d00c0540b8240d0300c5000c036409021614500010251000504070b000c04292034007000e0a09440d2000c0001000a003d8a4810021031001c40c5009201d011400c4000240c50030386032680b070012200020515a0bc001d02011000c40041c1e0f04105160040040000440700f1a0034a03102600d8010080c0245101c5c0e400714042064480c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 932733812 932913669 := by
  have h0 := BRFrame.cov_init 932733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 932733812 ≤ n) (h2 : n < 932913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
