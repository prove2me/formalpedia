-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:35.295755+00:00
-- url     : https://prove2.me/submissions/c4d2bd6c-d3af-4637-9f47-8dfa34a526a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 632553956 ≤ n < 632733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 632555206 1250 632553956 632553997
    0x20604030f0516060f0f20040b03090a08070f0b130c090203060a08060702070e150120012306010f02012c0a060903050306190e150d0b10140105 63
    0xa2190300900351445400043e020718015940d07600044690400003980995210b0314100840400ba110b0902c0f103400c0c05c1c1207020803032003c40e08512244078502410407180340c04000b14a2141c000c1000d410116801042250384624074100f0300c0b1507d8024404035405141c24000400310307840d04101848103917008039203050440c101018000a900000d0096820564020002911a80810155009110b42c0d00070302541410001d4008110300e0007050510181144c51344a00703e82d074807003060b2001c8030300d1240d40c4642400038502240503084c613181e204d00100d03104883e0038a5004502c40c2c107005030001d07212040703a5070b014481a4213840e48950b106000300002a4101d2041c2d440795524444003072207600743c40000c0d03403aa41d034900b280c403105d10550005001000300b01c403c1c24a010f02c0900d82440c035a2003403429117095480025810010041000b0031007110740b810f0b0030740700c2071b0080d818558403503072080c201d24008040c551101180e2007401490880031401000d594094421a511080c0c1c07414852141c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 632556456 1250 632555206 632555237
    0xb04051c180302010c24020c2b140c0109032a0b01060f0c080c010219050309061b0c0d0f08150906040203040305120106032f1602150c010203041202060403 68
    0x18000c00e0903506101b5140c0310000d410124122260126502d400040e12104001d03003a07407030402445458002110f0a81145898403840042ea1449540c549000081e401c0c0e03080e00c103030310340c002c0759001d00c4030f582410054010150007a25071130310100075072100007202d040303a00b0b000c1c04000300303010203401c0d82d45540052020070b01c100e4884117043d140742000da401030100d541d24895548041d450300c03101c0e540803c0d02d04081c0078140300300c42200a207140280c11803c00511241e02c0e07c001508891020160705030b594858080700050701c10031590881541c01c8401075042c0a0400101080c0e441c00199103c0001444280e0810300000000c40180034400070355203100511009601c050300a80030700605001c0440c1061035290b202e40a46681d640c00304450b01a0300c080c0084c50a4842d0b062a050801c099012284840c6810f607265043c1e1a0608104000340d4004910b140e020b20b50303410701d04800000d000c101c682054000358003d6105c3c040c5500703901c012000880e03d80358103990080c00030f10034454a4540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 632557706 1250 632556456 632556467
    0xa080f1501031a0d030c0506010501080106020712020d02040c050a110610031b0909140d020d121a03160f1a09102601091a28030b04051c18030201 64
    0x7401d07001554240d024079070800140c646511303020224000303802e541c5602c040050501815005120070b0074004170780d5043c00300294540945d401200e422810b107081000c19035640f210503410258018004025040d1442c0e0010b2031035000c01d01600201708100d5003001d00d00000910203224154600010b8515130035991030303d804005c2d58401940219a420000c00d13480018440d05108030b00c00c41e103982c00318812005803410000421411025500010a40d020301900005030b4040428070b800006610316061241052020401e02e0a82d0140320381c1d03141d01e0000044103020800c3d2103404020070b2450366915034011031a0f050017000108401d040c4611690380c20405034440c1c04904504010120340211100740300403003080120002c5c91234242c00104140400c0e8802d10705190000303082d0561440d81c41c0d02003128210211000d1130303a42c55208015a0004052550a020356440a0000e03e581000e042280d5504500c2a04a1085074020b44070b40d0510b0003450303109094003490b00d4000a80e40707180c0040d01e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 632558956 1250 632557706 632557721
    0xb100c030e011d060408010e1507020c010e010c0c0816050d0213021e0c03091234170106050405070503040b0604020f120906040b101206020c19080a080f150103 70
    0x14042083c440300c81d00399201d00c081d2002d0a40d400000540f16500c800443c43c00075030140305820f440a00041c850080d50102d08100810020b080c154100100100102e44011091201034610541c400000c644100302083d46508181070107081d950a030745440c100801d90213403490080d0300176405100389600c4800d076000b0700b040f20a5182c4003581c818040e4640b102c66071040d5038203038440c1c00000c0c45000c01c3c80e00b00d201e40b54110145c00148040800194910100c0104200e0824216001c4200d0f103403603581c1c03260b0a800703170449120010706003070300580044c06400d8130b002d02881181008002442d2500c10300a9a100f140c000d14507011603202c0400f440025070040906441d0903d00300080d03100d9070a120141401406002c00410440c0341c076091030108444084e117400d03112520207204014001e5004003400c036494220b00010398642409035040e02d420085a00320740c1460400d01e034141841681c0c4090003210b101038460250b19540e162900002c83c0c41180d07064001c5012070412005944240e01261 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 632560206 1250 632558956 632558987
    0xf0b0418090203011d0c01120902090402011202092205010e06010206011e0302220b01140a0e03010b22050601030533060d0c0e04090803060d03050d0504060b100c030e01 74
    0x700170b940030301140c400322000c0c0055074069014500092440d40d01c02c2220340c3d5050050007c02106071142d0001c1c141030405440039040141050410b0b658020703641c11200f40c038030000d000000c0e2858800213004a0300a80c0341e00d064552800c4000140071a0b0350219a20034023050b400790401d607086c192a40094408a89000150071a04001000680301c1e01043ca00946220600280e40102803201c076040e10045502281008032482d4a1070a224044050f90301c003202a041030f95041c08e41c103010a0047c007080000d0703a4840d52079100844c04000c40d07000103141103009207041c0007139900d420040d001d1380c40c03c1d2040c200e1004000140e400c031101a002c42410b40e6003984200750300034040030000d242c981100c000000081e40e1080341f07050154100703074405c16a08003a1001d100d607405603100d14042d4000180064040c22010000c1e40425204400319a4440204242008182854200300d00200010504280104149030315205007501442c039000e0080c0c1e040c2da513102d000c44d5440c011150301600002c3c41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 632561456 1250 632560206 632560211
    0x50f03190b0c0d1805100903020705040905030f0a2f0d050307031d0d1101060b1204020d2f22020d060f0e0921032d0f010f0b041809020301 61
    0xc2d080d04450084605410101c80c1c1c40413020102d060403030809040e28035640c4801e1800240b400005e8011403804101d6500f2500003849045600381142948118440c404081d0400541942c0035500100e00740c0c810041408002e003001d6100d00d43d01600715141060784803d030b010742045081284180020356210301e180c03401240041c581c45901c0d00301c407c248682e20b0030342c12529004940d01d40c82070341d0302c0e80d0040b000000c1c083c00303284c2441881c803442210200710103d03040c01c00003000d46d01c071500814026079110104d040000300c0e030042d4410400f08888601000305060300070070154605191150039141c03000c20100c4028142c070303034008001c0d0f11000c80c10483c6c588400002502ca00f80c040110010004550000c1c0f03285040d1103640d003050080e608800131020a6440242c180d6000401da03070303100414254030340c0c9100b0920a020400d1007000d6007003e41d2484081001081a0405e100c203040b074100004129410351070b0a08078a89009034000d00c0312002d4540001070301015660030009401340080e000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 632562706 1250 632561456 632561467
    0x30e060f0d18060507050921120301090209043b010b03030a050d0506100504060c0c1211180c12040f170301170705010903110a0b03070306050f03190b0c 67
    0x150815a60403404481210320321610703400612043d0b0040a070b1000961400314a040d41400025520b20100071108281a003d02c8840c100740d401005144a907084007070015840b9a540c3c0b094101941c04140010301550900c1e000c0320101d24590220303c03408624020250419107140c24002d1a104502c0c1d441c1410742d220803801000b40c4050004000c040340990700c659980034110600c0b001d640e40500707854019000307100008602640101903900b81c03100e40ca04904a103c55041482420b52a50060350f04480c100d02e289042000c40c00c0350490080341642c1c0800f608514a244820a403401c41301d81c00304030402c01800385c209c1e00940d022a401445550000c03100442038503905120f040150b40103400701340000c0180300c03984038001c8108500030708400411845050000080c00405c06100062080c08540400ca0440c0d50313520107807014100081810703403039151070302005001c2e0901d4401c5a004003201120102e0354280807d0003c202c098401c1400703800101c56803296042d00004001e8502072106115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 632563956 1250 632562706 632562727
    0x1210210021006050307050102060609091614120a0819050c030d0c23251208061003050c0403030f0c0609260316030b010203040302091006030b030a030e060f 69
    0xc2204031118a5801001c1d1030420104a408a50941e00701901c0390f8401101042180e0340081c001c1d5001600707440144640d16580403407403905160100440800224420104011804040610207240100c40d513540c01400d02c0c44041d25506e4440018141c50420051003e1540e03071401c2d8009044030a15105284c500310321003481c1183c0100c01042a415101d41608012590105034a64107403050034643c0001030015a102ea00c51203080f41e20034402d80d1490034400000d5240d6428164107030010f41e0452f0314801d07400e0003814842d08581441c414012142c1071400c541c481c0c441c1c41d11811102510515190641e01d09650270004103100b44100410100741c0301c005015070090b0380d0040d10500c1c42c1b2481072290500002039118000c5c0b03100111505204201e04080d80711401c2811512500703000511903030b2240100d04602c642c1c4c00c0a90031407035003400e20a510b4055012401101e1041d503040242030345802c00c160312414980c40140020701c0c007031190b42d501d14111000f07042007180c03120200d00d00214040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 632565206 1250 632563956 632563969
    0x9100311160f02120f0606240c0601060906020a0302030418060b1308060114090610021c0e03010c0e06070308070e09040f050c0603090a1704030605010b0414010302090108012102 78
    0x120200d0714000c1a00700d500840c14205514402141e015024005040c90f50f4a45c0e551540001e04040c403444502c0c04024071b42c0d180c007140100d0002881056955014407504144d034404082c80faa000080c51040d000500b28408926010807036410343c055490301c0c0c60160b24440c40303c84055004801030f40c400300041d4241d80c0f0170003441c0804401494506a80c6000e1105040401c16402803083c52001c00c844280b680e24400c02e650b00c10000c5544500210304d17400120b1034041418405916034040c0e4a100e1102904007410030040c80080f0005c0c020101000e00c11104030240401d00c6402c41818444040060f00640100ea4014843d25100460002c1440042e1000c20181e406445c15414845102c09201003800224600300007a602189541001444544d44803500c0c20080c0141a000d24292245a02002141c0007141c22040500c0103503114a0791425070790003403081ca1034880c501288040c2c254000d00035110002e60507122000c003a03280908920b0b02421180d40b464181644024040060342c614 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 632566456 1250 632565206 632565247
    0xf11071203020f0d05210a090501110702190503120c030c0106030804140a030b0a020a02120408010507090f0e0a02250b271b010504030c0e0402090c09100311 69
    0x9600030711001030180062424012641c4c0131408004007040743c0c07482d40001a440c1d2200c0d10007201131445641e071309440380005020403c0001c0c4a0f500b05401d0303122100409014149450003141c090400c1094059840420701e841e01c65141c058200389040a8001c103600e02810a50441d07000f070303e2515480c0034501d0308507900e0760401c45146101003000d0259a40c8881c050703890400aa442a0081d41503071601801403000034514044590002042c00c0958420300c510000b103401ca401d40303a01e80d91980810f50107400200d45a00006059010009000a0f10420300040340c1003203482e0301d2651101d10310400a54413a010100751001070000702d40d4404228881d9090780760241c40c4900150038203035544a841220700400c0b00708619070038503a0080c084085100118110403405044041c4190030040e660740c01560700251405140036000240d9885500f05103100e01d200b1270342d441c4a661090107500035030140030728140e0405442d00d010b0b031b1128029403004044c1140c584420741020703000c415044440301207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 632567706 1250 632566456 632566463
    0x9030c04200a02100b121c1205010e06031c1b02062709130c1e030b0901020d05060109080c240d06090e0604080a030b0a0306111809070f110712 63
    0x4800c0110403481300d00c141c1151031000c8994424001d40c0140c0c99030f46a502d840e242001c0c9803102503010740f2500540181c404520192000d0210750703910211300020310700c110703600c41c0a401002840c00842c207030b07581116034000c0d4545030a810000042c030304c2d00580c0954041241c0082040001880200398104266048450100b041f80340052800c144042c20308098002e4217581c41880e840c00000701c003002d0440c181d4030350300d9060168811001c0203200d0000c140c1d0015000c04410001e102030248190010200c85101e00820710807034403481c0045031040032500c92851680c0060825941600d405a4078094500420140000718058800c0e0990503904c0b454400014a43c0c0b0320301004000210f0080e02080b01d4128050b05c01c5140a880d50b180502c03ca0398200c0815a441001c0321b80b581d28884004041c5030040300030840c14508034180300701c0c0d502c914104150414140c43c0f02241d86001c500c3c7c0341c42069107944841011140c4c26080d5a07800d110540405030780140007022414516511035001c07240e00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 632568956 1250 632567706 632567713
    0x230912010905010c0827010914060703110f040528080d0816090509041502042d0302011b02033c060907061d040614041109030c04200a02 60
    0x41d1400c103003194201d82c40d600030300c4103c030b0070400b20001e018040b2100c48001b498050b040000759240500411402074000c0c124002a0011b800700000080c0941c0301d139400c0d4034200b00c1030030300c02c8540025004a41000d814079004000034031840c109103002c0d60310450340c0301c1c021200041c03005800e01520416002050968030095032040c040d640300748070b9030b0400f40300740401c240281303180001016105140281030051540e6400f1030100200c2245211148100c0039003152150f031903118850042c0118808078440510000d00001da420000f0942e0013203076816110000307102c901403d5103928410030a002e80c1c0c1030150b60141d0050264100c4214a00c0c810100403402c03803103010783d16030522181515281c800d40e010b4410411005000200ea00c01d07682c0c1c1d814103400018844d5a0b0a1080501c502d44a405c2810074200080800c10020540548501203900348075012100288441a000d548519a0f1503400001d80100d20300309035001030745c050052507412046010540f40811240d02c09031800c0700507403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 632570206 1250 632568956 632568971
    0x2004051f05090606030703050601020a080309070f15090905060111150915070c02060d0f1b09080c0d0609110303030108240103030f20010f060810090323091201 70
    0x5080c2144005020100c070810740c01d0602201140c1c40d800300a09560a250f9207801168887e0300810403000203a0703100c901240d032403600602158641c22075200e000b1040c1c21b200000b049c8440314a01c03a03140c444a50780c560045615161015000e0a0b0142481e0305000c560140c540b006141800079440c2c81c503140711400101e0901c02c1c80123250050fa41c54561501c021075051081d40c42e400001e0680740d940440d00e151711400c5140c103820092481d01c0d044039030540f0344019844208041082c1101004490f101c282e1180c1c0d40340304441c1c843c50300358007241c2d00c02011003941001a185074008036040d40a048840410400355020926642c801c0e0041107007984026000e0034401d80060f10b0b17089410800150803202e503d1940d01421304800c8849207003d10a16100313a0031807640c5c00d24100d9214407000000d2012904018603480104079600030b42e83c850113107106a9030700000324054000103591540d105c01c0710300c6420f80c030341c3c03940e805158155800e41d108000c5010781c1e50b11505000301000c0070200019582 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 632571456 1250 632570206 632570251
    0x11d0d0f03060b270405011a0d27021504060917071512050901091104020d0b041517120307120603060c0816080601081801141008070f0f03200405 64
    0xe5030002003a83c07141b41400d0050000c0300d42e0f80c0c2d80b07607a4400e42046058540c1d901c450711030081e044006030381018418006070520300d65404444448424000c0c0c5d10700c94581c000392902d950500c1180980c6010450b2648100180401400150841c002190175203082d691500c0b064a0b8400c0000d242d6000680c10030b50350a80000341c0d1040c140c001014000805c80070205595030340c04e5000302c0721241e01c0b4690203d0210070403090340d0801c0c409800020405c0160031610301000688a01601500ea03200000e081c0e0701d0b00086000404200655060003000d0031540c07018403c8440030090308009505540300c03a00040014114020b8645105c11b03901ca410051070030b0a010302c09058505184400c001d0b110040c0800c1ea60013440160b0050000b04c00250703404402035085014140008411010b080ac01042102e82c0314540100c1c415a45480140c0c2d24199135100f01030701000050295514002c0251010000201e0f0841c44449507000e001070518455003030300000d01100d40444150000080a89035809070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 632572706 1250 632571456 632571517
    0xe03010204080c270c0a1704080a0f180b031b03150f010e010c110d0c0909050f0607050306010f0e040c02010624081902041203020102090102011d0d0f03060b 69
    0x140c01100c4ca081c0400680f80e2158005428058035030341e101c40000035a410f4161144903426003184000c901c4003110301b400d240c0900c003035012318403c0000480312441015118424600115803080d1070100340405800d200003000107070700107040c1c0b0300100c0c98400410302c8801484080d52040315000c6460200940800c18044a00d031b481c08002c0c1004803401007200142e8100001480c41c580100b1018055000d2002081c40c89401050191a47c00040400285c082c00c40d0010f481d600d00c95801e503000300c004110041e95030407099603034a010a00c28000a144c40d4403568040414812502d089107041408401150444a44d114003c00503511104180110075180001c0069005120030000c41c02008840081140b1000f501c00140c4400c0d8001079400c2580c0c03078060710040c101c03c400305a00c44104e403030068000d502c00c2500c00c0c059420903510300702c01502a03c0115440c04054040d1940e060000c2080380c014200700d45500030f066441101003034002c00c5402070500020002110500c030444480081c44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 632573956 1250 632572706 632572729
    0xb180709090503032a1c0605030102040e010909030201020405180a050c090d0f0c050a0e011e1202040c17010605070b06031b010c080706230a1a010f0e03010204080c 72
    0xca1a003051400340000b0400000c69500080d00e44000703800700c03103c01c0751007840200c401c40e0150b0440042800d0791581c8880901480c002d44a0740100819945c40050500741d0040e032181030002845440100000d03a500c0d00826900c0b4440c0c8001807501d0f403100d001801e44003403802c0386000000c100c400c111403c07100384151500807034107104aa003070250385000034000118805004100d00000184081080008002c1c4400350100600504040d900ca000640010b10240300d12403889070300e101c0d44010621040386072340035244540024058401c4c1c035024807028101030a42e00c2e0801c211120000742812413500f446010300044c0e0b81d8695950710707a040000d1490009040c182c42a013124201d2015078010102c1e101d032180083c00c08820500d0701c0d0410000a00802001800071418402c6c0200a2040b01041000011010080424544400013100215404640c000000e004000b500c40050f602451a42d0900140b6161000c0e009450401080c2642c00c980d01102060340060700406552500011000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 632575206 1250 632573956 632573969
    0xd080f07150c0314070509030a1509120c02030307110d0c0e070e0114040e0702120a0207060306060e22020403020d1b0501050c0723100c050d05070b0a050606070b1807 73
    0x1002e04c520000d04e402101001d41180309121000507000b0329600c0c2031003460642034001c9038207248070a500314880c2c0501441081145d42c45106101c180340c1314041e0202d0240180c01800850806009a4030b0300250390000603042d030b1200803030140e00005145842201c0c054181c44a8202d681e04000001501e044102124a0705000c0c1c1105002e0b84141c5e50700550301210b8980031403011989842c401a07040a0301040e02007068040060740c12311082d0000b45207021601541e40c2003002e181c0d03441c0111026090031862350f5200204500c00f5014640188070704142d0b9440c038034014039260b80c1c1d9000440c00f02244600f1641e9070580c0e006080030112982102000300004e08102d41760840103108552a5803903401001d001c001015014410b00c0b00e420100914107402800140a41a0658001c2c02594014000720741900c210258940f503944a24103a80c0c0e62544004041c016071900d442c500058200109825000395051040401040e0081c0e20640a8a041c4480b81d03c94034040340240c0c04c1440c50340055 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 632576456 1250 632575206 632575211
    0xe01050403230a0c02100306170a020907030e0a1119270c020312091f05040c0602010209060d05340221070618020a350a020d080f07150c03 61
    0x800c003500100380f103000a034100d1781c243c02180420b031b041d030051079540c00c0b111a9a8a08016603401b4000080c440302690080b910510645e030f642e0802c03002d50340101c041c00d80f0f039040218245e00003000c140760156164402485089292400078814005001e9980f01003001c61088080341c0f18006001ca41300d415410102d41845640710990020f03580303114000240c80e0442d0703450009409090203210145006441880d1032042e414980450400307410141c2c0d040e2003c100c810400103c4a0052085442c20200a001a410b080d980c4040c5030083c5001003040004241e05000300843c0280c0001620b01400c1000b44130b558403c802500130701d17080030381c1e0070100708400c2200e0006d030104240041d02d40c050f600520104440c2d0b0701685000c4060285840290811544e41010899911030010300081038603102c002c0010405003e0340b4003c1c50301d10443d60500da0010403040c0050b0405505510301540514192843c0c6410207150b0511640000c45c00d68910b03041c4962815100c1050051404031034640c6010b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 632577706 1250 632576456 632576467
    0xa05010e0d0e030c0a05011404031502120a0506150a0203161209090203130602210a0605040b0603131101050c07030f06060603020309070e270a0c0501020d1b03030e0105040323 77
    0x3090842c4170900071306042c00051800c04136140101000c0380d024540c00802c00061010b41c4010f40c020303400c100d00c125501c0f80f07c000060f101c02054400ca40c400da40c01040011119040300c40c0340b52503482504640214001000310840e40030031041001c440c00d11643c0341205180e041a0010b041030850380107d200b2038010018402c0320303808081d14070001d940054005079104054030001c84000781c2071070390b004001c8024040040c9080c3c140e110000300c078404d41e0300344070709001c01e41009007032321049900c410518850080800450035565007154001e0b0306041603890200102400341c50300420340d10484a40c104289000200440c03400b0340402002c16040640c1103041c02c01e00192240e13058016402c0f0500d610000030707800200307210301200d01c500103613581c003013005401d840d02d40313034080d0400c00d4411040f0500f000480d941f000402820b454640e50710785e00b04a80c10010389003681401c01c1d0503401c05485022102c0600c10030b03c076035801184681c6030050305c1450404460351101d54200b5245800905011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 632578956 1250 632577706 632577709
    0x41b0f3c0902160b07030b0306090a0506040809030a020303032401050301050d020405040804091d010b150d0509070302040509160f1505310e0a0513140a05010e0d0e030c 74
    0x8510a66140007005030b1203c01088003107000c000b0070304010303007903480d01000c2c03100341a00340e4402074007000241e065a41076950044550f07600c05200c1001401640301d000040e0100d00318501400490f5002419155411410340000c3d02d181c0080d1000700d2030040d05590100b0a00c141605a4124442803e14070b0035903142c100069410712102e0000b81c01107032504000b80c104003c02c8101c8001d850010b20411070300240c000b6409003140d1a10b0250195844e046402c1c03840d26184540508410201c1842c0d40742070100d0006038007800c4081c016804c00e1240700000320040e40c890003254031418000c4c0051003124121031000804120f164445000e011929001b40052030180d4201040e402c01418116501ca60084549154040c10301e00d80d00c1201c00364182143e62454081d4081c201e64884200301055185d40e502c00d41200c41c141c900119502c0681e458a0010745102c1c0141c140c0200e950075580400c040740c0f180f42c00c0d0350781d5092140080e002a003035401456002040e14141440070790007454058240c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 632580206 1250 632578956 632579069
    0x80f07121107031e1407060f02010513020603160219061406150d150302150301030b250318060e0606121507050c0a120e0f090906041b0f 60
    0x30300211413100401581c03424040fa80c030402680d0f8020004032a1100d944000c02481200340742003c40040d4282000306200592035201002c071590001c0406186882d40c480c101d00a40c2c0c001c00690550103035080c0c9540340700b40a21050751844c040c4402003040a107260000500010003000b80d44914100c50010030060030300d206480d030301841e4410000e00e44604007190f141c202d055500c0254011000c011a41e10b000c20400954122449410050b00a80390184034184103111009201c0c4402c110800d5031001070b00c80e40000400c0d0030024050040c00728245c44400c1600d0404141c2d501a0b03001c081070080500780320201040d2a4031030030143c00301c10001e001e904003400020300407104001c0041844010a0b000380019143c00c0d5200044400321400e540002e0321114810581d20b104016517003c4240f181000c003141c9102d0034844010703000c2c81ea1a03540e01c1c180c0c80354a0784d0705404842c03000c0003c948030b4081c5c200d10700a000d080c04203a0b042c0d410220110309025803071483c1c00698100003581402141c1e00d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 632581456 1250 632580206 632580233
    0x30f0a05090109032703170a0315060e04230f090c030c0604230a0f0807140d061d0312010806181c0c1e020a0803040f0501050304080f0712110703 64
    0x91040c003902445e0f00c1c02c0144a40b025000502844610504800d80e400315600800f424101030b202404080031100310350742c5406c585c0c0302d40e00120f29802e41d01415481c2c55803018040c001c201c00103e0308081182a810301088049440403030408640c1c00f441007170302c81042400c413038041c120002d0000c0785403000460001d00580c03103050701e025540400881082c0e916840c04503906000b822602480e07039905d004800001c180c4c4034503580d40c0500500490181200f4280394480f06000d40056440c61441da80e00008100000b4101c103141c610003502c03403182c9024401000000c40110a00040b9410700911900341343c0c02030640c0c80031500094540c0c02060001c1100c41e41984c49421100c0c604820384c1c070039181c980d9004802820040b070103030f010b00510000b64a0aa41074000d0f5a9002d51a45034942180d50348202e0041250015500400700a02c0d842880190780c018440c0d04214100f19418500410642003c0c44c111a030710387c030039403038185680d0107812000c1a42041c0c0040c07940030700c1c68544d0302210015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 632582706 1250 632581456 632581487
    0xa050c0a0b07110a031403030411090106090e060406030606090b01090902031605070f0b04030309030210050403051c061d061e06190302130b030106090801060e1f030503030f0a0509010903 82
    0x20001c0c100ba2030303a071601a130340115008100c6d08442003204000a840b58411a0100e402c429100d0024090b0306007099249c1c1030b10040e88600d40600d082590f40c00e2103e800501c181d600c2500d031100030000614a000d224000c00080c400440c00d0b0440e0000036004000c81d40003c00c4851060041042e80100c81200810030100ca0900300ea844420b4100001e89206200020300700d001400d09000405605610240005000f03600b603446080004c00800c06a41e8255400b0b000581c0c1032100f200001407008200307426201e4208000307541c598642c4503907542c81421403044c50742e540307800410641381059a411440141070704a400e80d4107501c0b000240b05401016906004c910015403135200e405c1c000c2d030444000c814441031180c200c940d15144c40a155200340102c900103880da00000038618414090703d000c1c0c850701014031b451941d0f0900c034154061a41001d440f40d0300d0f00c0c04c200101103030b406c0c401140511256600c0c40d0262810702c4031b2400351040a040001181e151901c0c9201007a0302107900140b6000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 632583956 1250 632582706 632582723
    0x20d02040b210601030b0105030303130201080903070f061a2d0f0301140403020d030c0e09340201140c120912040e270717100501080a050c0a0b07 64
    0x1280001c02c000842d02c01500141031401c5100000044000640f18101c91259180c1841680c0b41c0c2c06040d00d07400181c1d81604100d2007403850300b00640c003500001740d001e9102001c403820509181c854074031206d40f0000c203540180c1e880c0903c16242000082010507210b0035a44420800e421100b9051510503c101800c0a50040400140150348021241d41115401402482944183c188403945040c05440480240c803070001d0040c011402801250600c01b5640c55810102c207501091000c00c1e50010300d410541c2c40710382d11910008544218551128000d940c08000c227625543d406400c483ca80561141c0200c4120100901803d0000448513044008510500140c681940b0716190420314080350012400104022510381a921940d0b44107007200490f0500860440c25440401c032900000c000441e04000802c1c4002c0d100c10702c140d6a142c210700200c82d0122402501103084403c02c1e0010b07413503500402443d005101c010040720440d881e048840740c01d010316020300d180992189000017400da42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 632585206 1250 632583956 632583971
    0xc080712080c0c130203070f140a050d020f1201170303101202010c0605090c0910030b010e0709032910150c110d0308010f0605030601120b040b151e07020d0204 70
    0x60301403040101c0010f0207050141c02c42018002c1101035001254100c0000310081404038845225030541c400000516519601d00700c00c2d0350080f110755001c5183c1c1440b4640800143e040080300d40010f01210200b501c03208a594100910055491fa030201e294119070300500c1401008411300e0b020804070303600142d91104950813840140c0d540e895485018280314900300c100240d0705c401059000c490b0700211442c814603030310f04450260720030b500d02002e089902010010300c032210424821640080460030024040d550320780e02e090b00001c805a150400401c0c8605a103042d401c452400d0b5004000070003129030103030600750102e01904400c40880100100440301c18144a4094000d42c95003001501280ca00c008500b80500314840a114040c400700540c980002c00b0380c800d20903240111016915003045500710b52090300644103221040d40c0c01a910101d0b00c1e60341c2c0d51a014020307043c00448040d62510029402e60001621611420545080810003000180e171540d44110f400d0b51304030340004160 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 632586456 1250 632585206 632585227
    0xa122901091d101d0f03090922030309060c110a080a12060b030709150206040b1b2a1906110f0d0207020f0423041403160c08071208 58
    0x41c1540c00810202e40109403000107011225046141881a01508819008000e050865495001001107101a0410b00030321800349054410300d40c0148916500c520101c3d00d220b0302c1041d100c200300e0101c010903a540300500410410307004810b0300200394102400c503614480300c8130343c4070070100800410342c0c0b10001c0c880501601608240d40c149244283c100203050712400555000d5100740e800310301141003180c00062002d000da0350743c45080d81c3c5901a0a041d151541c500031a880040c1c071a01c46814641021001c01d07050300050440343c441d2519822a10000d514013175952121503003401c996401658030300e0301c2050120b48003103030300740d101030002000c81c0012034820007802104025003035844005011841007020b0703000742001c54003c03560550700004d00000c100c11903d0810000c880341c207070741100d0f60707061100d101a2070b4464011040b0381c9400d1014a006415940000e005c00b00101c0402250418400d8003070801001e4958940100903580c20420b40c80c6408008460081c91800e00090b84801c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 632587706 1250 632586456 632586491
    0x70818061801151e0902040305030d471e060c012706050a2d1b050c0106051c12020c0d0b010618060e0f030304050a12290109 55
    0x600a4001403040d1503803134100c00c1100c6940c0700007400c8500c016080c017049900080c4200c0c0c045a5001008501e00012051000007406001c0e150300905210281d800140b600540e0940141d1000401c2444241003154400810f0408903141113001c0c22101103400b128050803c011640314408844a50303c41180c01002c034050054280c02c00c5025912030f0b603030600c0000c100414040c541c070482040c01103aa0718614801140c950382c0c0a20004034103009409241101180a19000840240c0114402c126004619103142241c3c4404000400000c1d148406000a01c900c03405403c045510b0030091440b8a404c0c40160b103098006005140d4102ca0385048a0003040140160100a80041c41450700344c1000401550300340f2412010403130300400d801000483c041b054042c2c4140c6c2c0c98000c0c00104e030030207100395030440c812000d4051100300300101e007aa0300e0284080090000c603031816110101850304448800c0312142c81004466850002042000b03580085415a5000400011040d14164a1420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 632588956 1250 632587706 632587721
    0xc081f0902040f1a03090a03081806010f05040606021b010e1201110307090e0636090a020118031e1a1e010f0f03060515060d05070818061801 62
    0x2441c030009001944000c00c8441c03104941c50f403414540c4504a914448000e44002c4450043eaa0425030783d0400007805a1170690b04406200303003201c2e466003c4103801d0b1500c002a004080e4a000d151000c00c40d42c80c044c01218003414841c0b001d890720b19014454a0250040c0483c024180100451003203d2a110254402c0c1e8a004250080c0040c000c1704d84000000d50050345c4d924001444e070707140421100e400610343c42c0180c4020f840c00c414100d05000d040d0388072103102020001003d1616903c055000300c019401d0103124090007130300070030419100241403481d5468050042404554080000c034803150620303c54510120807026a581080c0361003000c03000003180e031403403102100b02485604210f21001d1507481c3c00c1c40d5000c89090b42c0750002102103036007e200d508055903103032500f880090819044150403100b1034008901264042000075000c1c0c00c1b4076419060306584004000000da4040209500f24860b02c540700800810101e0305070300c0302d400505841e0790a940d00480003061509501000307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 632590206 1250 632588956 632588969
    0x60a0e131e02030f060d031d040608010603030e0a0e060303070f0804090f15051c030e040905071e0906061706150d0b03060a0e061311031617010c081f 66
    0x240034031003118074402034105071031a5008031103a00c0080c206042025603080140d8264440c00040c5400c1e80d00da076006c1400542c0f42d40c1194030b42e200050b184200f4051407002d50712984a881b4200024805d020348200d580d0b0168560511607007c2c424992404011116866003094041c880704605003862115072090780e0080d880b66203441040780352206980c0c0407502490100300703d90031060f514000c203c02100819840c03d080c0d40c00852407000030f401030702035145000e4058004502e2200c030b17445490500e500ea510808050f48084d007030060424441c1000300181c6031b80c0004200880c10312400608121091082009602e003030004547d0568a00764002c1a419030000d0301ea0755219226014000b8180200b80c540c024481c41c8041406014540100c183e134401c03a2000f00600c2c1c1c0c4000070300b581c4034040d00c4d090350354480785924401242c03401d01c0501c10b104a0074002e00100361401800c84292124101c0d8203005914204241500c0c3e41d220071942e8200c003270400405115040784410145c0c000c038a61200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 632591456 1250 632590206 632590241
    0x1a090f0c0f0403380603060619030209040f031206060504061409041d0c0303091e540a11090402070f03030b1c0308041406070914060a0e13 61
    0x6213036003407040c0b940b03000081d02c0000c4500c500c1d040031030540000c03105460056044d002400042e0b010700344041e20390300d40074085809115440d40d0b034020911414042da0b05403000c08c031070b02d180018150840d10254a50065603000c200483c6414001071240c091406158200300c1c0e80e24080400c069140159410b80c42c006004211040c0c40340205202c074070290410800500074030402c90300519000c0162101120080d1400f8410781c100400b40c034091145d81d030029840940e441c0c50304901100b501f0b1000d2200801308a0300c130309082d41c00300c80f5030705024804507005144a031141c1c0ca113400005d106441d00720158102c0820b40c1d80f908580650a4007541c160307503030001e1001c1142404c1c070401d1513510300d1660203514102700b41011070050010070030b20f400721131048020569000001920070f03001503500900882c2c50452411000c018581490401c2d601180080c175400c405004c0c2160002c4000f40c40607040350307d14502000400d0103000c00b0301340c9580c0c61003900c540e50309845014040d0042c0c410b00791014042c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 632592706 1250 632591456 632591483
    0x206091206070201060803040608160c120518150d050709082a0906060714030d02040b12070e0a090902130905060708091b09070c05030a031a090f0c0f0403 68
    0xd00d03a600d004441000c0190308000c0c002600d0707074002c422038040d21516540d20b02c041e50703288000c3d03240e80701c00c0c622701041080c410350660204001c01c80200d00d140269a0301503071100071440703501902e400151507621406140b8149000111058122881241e88803004500d80d076500c1c005813131510b850380c400c1505006803140340b280c00007042513002462200c4c1850300b001c0c0021809221003418210703005500800c04100c0b035004103000310640c02e904c5442d403007103a10b01442107400200307030b030030036030000d55030340c40201d01000c1c0c10740c40d2100c03583d003c0260f25249004a441d0000200350302c58034415124020303620442c0809549500145a0b440400c0310014050748035a0302e88a40d072294100e801200240050b00840c00d0395002244001c0124400c11078950b01d549400c00308000c1d0705024181a0501501280640001d8418805080c1c24459501d0010300c0c0d0a0f000c1480000d0011090b0340d078400c9092000700102c950198444540050b00c2d40c107841e88034001c40c00d01d940184039940004c0c1000044416 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 632593956 1250 632592706 632592739
    0x108030a030e01060e0f10051011011803090902090a03050a12021902060a050a021009060e010b0405010b0307050a0203220f060314010608280c09080a080405040504020609 75
    0x10a40011030380c0d0104441e4100701c40036400c0b10100e011300207600c9149004905c164850714441600410104404840300e03a0b1240052030343e2811b811a01302240900d040d0980201e4284100d0580800043e048407060f0429178005004012900800f2000f581c00b050b000b48540700c05400788040c540c0034040315074080507801d02c01080000e905106005118108050011a114290b6800140c2d400717003125040855006068a95821400c0280d0440c0b15a4006041000c01809564001c500540f000500c10001e5072107503007034a0401c480c00e1701843c1498010081d0503080021260300c841c0500c0c009448020380c000881c00c600c690020016026125103c041d0021003480000086400c0d9001014040760368500c1502564035011001480b5910480104207041c05914030a40c48030300090800f40c4001c0c0740307010405549001410456a980d02e08202480a4120103c4005000700e44020200c824059480344694801d9018945c0210303110808241151a000d0070b851403040020000b0808458101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 632595206 1250 632593956 632593963
    0x4060f05120316260706150b070206090906040204050d0c1d04031b05071e080c0f090714070c1715060109050105130305010c0f030c0906050328050108 66
    0x151501c2040300038000011848000221080340c040384090416544960f1070704030b1209501d0307041210b4224145411410920b011005203400e40c400d031000241407603a9074140a88082e81d070858140500200030041c0542c4e6003000356001058106c401c0c208554518010501070b000d9031340469005082d40ba07402042182400c1a00242c0364850751890704030508800f040383c4550140da02030f0101e030327940c04550407010741c002180e060280034130210344100e0f83e10305910100c60b5809120f0340170806050400d1105180901020618078030032203040da0307900004000502401405440d0f9020301a114603211f6421059030300380d81c400c0c0d801c64242000503a1300d62041907041041006810b06014100341c0305409655400110701450b07041e500c06035003504050054440f50b100103405031104840d880300200140003400b411401c18411f0740c40d41001c00c00c2c12009015500d14080701818480c03c2e10060003065803141c103590380301340b0040341100300100c449d070f0050465000402b0310407200d0802c0d0021070180c0001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 632596456 1250 632595206 632595209
    0x204183b1905030a0f020607080a050a091b0305120705121e0f1c0e0309100c141c0201021207031a03070806100f03050c121005130b010905190c03090204060f 69
    0x45c1c440000c920b08421040f40c0b60041140e20703402003030842011526407003903503126540c45442120000741e26032007034440d100f0b041c4c21160220080d90841c0428010041d09121115a20010000c01c0e82041e80982e121a21402c0c01c94212078440c42c0804c0120a429526a49450403d5000d01055417444a01111241c41d80281034040511043d0302e14000384016078803c1c10032442601010710b0519403002e0411544079004810316081004a0f041000800d0b50604441141c03803030540104081038000004250101d0000f1024043d03910520112091042000c403203a448100c500d00014201f41c41c2c183c040358040045031207034140c030403031001140b00c1100207180b50048510854041405984d4641d002c1c0402042c080100142c2107000e526403d070410880c8200c01d151a481075511040c0b4111602c070403a001180d51080c10324802d054ac50920034031040f0309001d0076a60348280700a24081462940c404c059500141489680d4010542000c0c070a0303004501883d8024810701c5400e50b80c2c030080501440350b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 632597706 1250 632596456 632596477
    0x4060506090409020109031403030f0630160b03010303170907030627031809060f14061e072108130303020d020f0c100e06150406090204183b190503 65
    0x581c04a012460451458401d1100f07042c9030701c102c415201c0b000c000e030300a400641d804511400745440814424003c03081c1c06442d03071703f16254896145045c01000e042c8002140c0b4040c611803001e01440500c04600342c2c0903a83c1100740801c04060314403100c1d42850301c0340064a00300da256580348042644c002c110b04400000005810241515041d00c00d00300d0b222441400c0701031101d8401001444c4044481d04641c07035008201310309003240e00f004ca00b01888507050050200d80000740700c208000038440c180441c2c0500f500c030100d81d84010000034180c09806400503c1c0407042041c86800c01d8400d80440708050700e018070641d2103c0740c146d0b00403803680000c10785d1801c1d07004440b0349161120341031054112016041c2d00070051034072240d0070706422110382c54010350065164400072405070040e000134001801a0030703c84031061861400c02088071400007000000c5079a01c62080b1303c42c070025803e40d01c0b02c0c805030040c02c903101031001c0352841c2c44903282c0700e180c0c150030401420b000d2041c044040c08002c2e80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 632598956 1250 632597706 632597731
    0x906120b09210d060e0c0a080a020f04080f24010303080a380d0c05060a020c0303191808030409020901110a030221091c02060d05010f080c0406050609040902010903140303 75
    0x407070780c80d1784c6030001e422a500300101d0020300c00c004001e8800c40381d850f00030041140052405002881c0300c2852352080c2c11814441c0d04c051500005c8842c03c02c06420b52107a091134845d0301d2052080000141e20042c84081c042005d0200814a0040c0581c0010b43c2c517448007140c010340b040380d81102a01441180c1d09040b008840c1e0b8242000c50a04e9001169072581c8070641c096854140010010342e5049035118074110700c035008100742c59480810081a43c0e0f175501c4026180c020710080b00501c0da00440b010712443c0d41c00e44204004189000041d14141d40034990003588a2a400c40103d5210000c03c2c02061230303200d104e0500f4213060b004119134840e1203480503001807951903480481d003544035000b04107400031406030031088042c189452586036079100810051410203001402c00c2036581c2130b000f100003010809402c001d81c0e40c040219483c52a002e50302400f6140c0b43c040010751900940242c540a507845020403c01c682c8034001200246a00c00e8100c3c10b01c0510b1505c3d40da80303400845d080141d862 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 632600206 1250 632598956 632598959
    0x2130c0216080c1008101e030b07170108030703021b060904320709150309080a020f0c0409051005060402120f041a010302030d210c030212010906120b09210d06 70
    0xa2140205511566101b040a441c1c01c1c900701408062000154500c030100203c05000b00c00180300402c0d00b40100455501c0507220380b0440100300c8005c0041c7d009900e554070401c000b01c0040c0d000710f610f000481e50b58880075414074070f072008240f01e4071840d4000d952080c90b10200019084901d1034540e0b00c10b15010110070011426603400c1c6c0d44c6601640c0c0c1c0c802084080c1401c000180c54078060b4031301c80d1281d1030080744400050351400c0a50308102a1b903c050707086801c1108141c1c200300585006041c08540c18000306040d5160319803124511210100e540c2e440d40e0000c1d410b5103564046404011491006101614240b890f256036420103403800c0f544900c060400610000c14025058107032a0002c0c09000084d601c8102514460300300c0300c1440a005450a000d41d410b00140f041c52800c1030036480159840342d002c105450b1100050b00508001d501c0c211007070198140400340a0032440d030040a0f0112a02d0b1006d42030f1804101c1d6690f401c803030300e0754600106402c540d07101518025070381c804d048c04120f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 632601456 1250 632600206 632600239
    0x10b031e07121a06010c0c03030230040b130509070903140604020f040b19060c02040e161809050303100806060109050102030a2601080a0b1302130c0216080c 69
    0x140b0b980c140a414107820030000c00d540801c0d0708903507800440504260403072180311365505501c1c845503401600503801c281d5810078079034540c12100c58103580600214600314610300790204180035a0040c44800d081c0480d003540c0310740c5042c03022400f03028001e0045400f4600814001d0035110103000c210f6114840c100d59012040c400942d0f680543e60040050103400c10751f405203c01020380c940504e52250040052140603030205a07a18044d02d0300c0d6952080480c4079006001c151030a9180c00030b004e40c00445a840c0d421040102c100580b00300481454410b0070030701000c1e000c2c118039800901a0301001090008103010841c608003120980c0041c0c9025645100041d52400c529105040c0583c0003005070300329841c03140c0c1d0550442d4602d03118184400c2e101103148091070109810902159002c8401c680c1805039520200358000c68a4400c41140c038043d80c0821120b00e62503400c3c1e04000e4a51041a507424002e0001c98001c010707422018562565a90509070364400d9542402d004140b0703501c00500d40d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 632602706 1250 632601456 632601479
    0x30d031805032b0212010e04030c1718010504120201050307050f03010906091406010c0b0604060305030313020f090c0901031e150302010905010c03140706021b03040501091203120509010b031e07 85
    0x211a0070900106d07842e02c030391f0344030502c401081202003200c807146d0840001c2011000160b861034182110f40c880c030440b149502e280440300003440c14044140810021a001446008541ca074286090742c0c603600c900c03c0c1a0399034002d00c51840700b042408000403c5401141d48900c0440304441000d10540804601d144170480c0f06542c01c5001401d0501064041400342c080d250700040e0280001412503581c0d2a03d908503001501c0d1110010311000c0c000c81940b07484c082c50403000070211080b01003410801104521446140c1510703040c1622601d5030788000e04141242c41040c031285600b848000140c43c1d6404040c01e007400128045504500c02185d40d511800300c0c4c010244d807503103441900d0300c01c8003500055900030300d000b101c1407a0200300011030b0041e4806803007070400e4100b0095440d0360802c0700140858026812003140c2d102c1d00740f901c0c0082580501c148500241c0e006001906031520304401d4050706840c1d00698142c403038148085100c40c51000c0c1e10065103103800684442031780f039482c103164 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 632603956 1250 632602706 632602717
    0x103030f030b12010207110901080622050a0b04080904060602010e12180604060504090e0114070302070507030c0b120606032a090d060605040e0a02030d031805032b02 73
    0x180104028911540030b980070100004000700303011012000075040509aa01c50300e401c603050b1101e817281b10071600300070549a002d042e4800151403d8a00600c04000d05505c0c10b9904100c2d01070040400280300040c006001c4054000c0c400c40210f1806007003465240d4408145c560150b03151410003d4210b00c10311031004808034180103400c0401c1c005a0340d400d1f642102c16407444803241c450103c00c3c1b076942c0703000400040450b0b8981640365441c00c0205021580d5024940d24564109000c060a800c9910540d642c1b064240c1801600e90841f41445841c02e030f030640000304000d014003800708002000314042d1000c0d00c24442d40d140c00355140424082103000a031707803c440f500c400d00300346043c520b000f003441c00082290140a41c2408031207070000c4c03420450503e060740c4040d6035490512450034240288280800703104000c10b10100c41d5408241c2d03900500d40000d04040e69a250450070050040c1b084581581000449480d602203072402c021514400e11600f800444100d9108040344450017901c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 632605206 1250 632603956 632603963
    0x10912080403261f08070b0714060106020d14070c0303031a0d0b0610170606030702030d06090605011d091513050f0f06010f090e0606041206060f05040605030703080c1905010b0f090103 81
    0x201c61f244c407029a03190b400070082140c0200c07074040c2d034518108041100e80d009080d160300030300c00a10b0154029205a1992135501d900c0302040080001240c1042c000d41d045a5042c6400581a00c1c0c0c00c40040620807484c102d00e074007038030841c841000c4c0640d13143c2e01402401b0803200c0723200201402d03c0641d08a24a0780070a65854441c000181c52480c1001c0039603440703442c50055034a40006118400200c800642200e808695958414002940d208841001091a040030f80c4400f040e00e00004ea100e0500a040540555807071103020410f45500511200a401036403007800355040c00055a1041d09003100c040080c41c030038070300299256201c0c01105c101d070005610780311001420041d51281600780200003940049040000081c1702c1e0421014440450050000080703c0d0f040c40c00e00c040241c00d0380c3c0850300c554103004051080707907004114881244e40c0030780200e07039841541000500307042c0c00c240d4001da034401740c00f1b4040902006400080031701c0e10450300018154518810003c400e4408c0c007015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 632606456 1250 632605206 632605213
    0x50a050109170309090c04090609020903030d0b0a15050403060f05061302030402240c06060f18090a1a19050f0612070803210108010912080403261f08 66
    0x2000304281850b682c200c0002200d00340ca02d0310100b040410075000c0103540764040484000707000c01c00000c1071302c0740d10040c4c86400c00c01e601d00300c90100040d03524021280031710f2410750340e0605d511080d515006400001c162000c021041c551900740d01a0a41e007103888103965032400c00c2d204010341c00161003a144121402480810f0900e6426602002500004c00407a00104080c1d404039203000030301c07545000e10f00c4030400c081e90303510f0a0701c01c141031100183ca038034001d4000d510420460b5803507080040d01013040e440c008449170350320300c111468080c100700050f000312201841041d1748444c1079000c5200b10340070079021020020300c00703e0030201c0b4404c0394140354620700da6020810b64074000410800020f40781048440726502d0348482070966002c001c0111003208200400c3c01540c1d10b4100c0d15004080540080091008a0311450241d0704111070600401030380000003820107004442d404c0c504245040c55404d0842a002844803032142518075030b0300c050700258110b0340c0c031107090199410f4a1002018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 632607706 1250 632606456 632606459
    0xc11010b090c07052d010b0109030803070c0c1a0909090c010507120e09190e060417030c040b13050f04050907090e0a1b0e06010c050c0616050303040615050a050109 72
    0x604000f5000054225450302582c0c4001c44012018207083c65009000d86590340c5440c0c904107401e0855121143c0141882920382040010400b8803040c0ca612080c1d509041c1a0790078140f5080f10703403004981100005485c5000b004000300c1108e401341000100503a482003058680104c029681d080c4100c2050004104001d0790300050b95416114120304c49504200a205114000240101c40e08551341a03603102003110410b06582240268122181644003414140c18182c42e0020654041c0d4a101c505030700000100703010141e185c003190010f018804d24542c540c4002c00c0c00e01006141032049078821206040100b0ba903241c24400c0b10b0140c03a1200050030608d1400400388040c1445c181295240d0090f40d0240c004201c16840b0300c0400c0216143c00104a41001d0340264058401741181e410800c00f1030504c2c00003007000400b141e00c00400c443d019141d0b96024074450780c8400d060002080d500000c400d03c020040c0c0c03038101c2001019818030706072040b600c070320501c60b40c80700c2407181500242d1500c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 632608956 1250 632607706 632607721
    0xc05010306080f0a020f12030711090c09030a02100e030613060b0a15030f0f0f05060901061b06090f14011409030a0c061509050c120c070b0103140a150c11010b09 71
    0x1807035040340014103a00401c03107d00501e03d041d90800c12081e00ca0845015521550b0b03c1d28499903075111944a00b170905001140300031a6454907442c0000707000c1c01c47d00005000c024019902030300c054400030100d501500e41044002801c1d00c01c01c030200c481c1030901100400e946031034a00c1e01d041e1020380380284540c1d076007200700300c01400c40b200c10b250900c0d5466000ca10104501c1c0100c0c001300c45042000300d1a400c0c110240009994140e00c20000c00240c400b03619a400101420840701e50b400c03540c0403850701518140248030701d106810003400341848642c00031010806411500d8400f1002180f2002c40e038490240700e8403440350010030400141138184040000d1b83d6980000303080c140c8580103000181e122620201240d20503910180382100229103c1d450507040e903580c580c041054101d4908103480303943c07445040310b01070100034206400101d0000c1c814004015411a268100f9005c1c0c00d90300002c058100100f0f00404107200203070b07006008031a420014000c0310400d00001d040c440080c1e58420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 632610206 1250 632608956 632608969
    0x109060e01031a04020309070e0f060604290a0816090323010207080c06061903170c0c031c020d02010204300b0106020d030509010507080a0c05160c05010306080f0a02 73
    0x1032000da24a040f52000c050754403140302a500c40ca440e54010240e490030003c49885074803004240d00c3c0e5561051040051a4a507401541c0c2207410240c00c146100180041c0b120800d10045808200c4e45408502071600c00e600c42400c07030040041600401c401c05d10040c0446046400c1d00011305211080444e1070303100e02070003050080581c05480010308000c9140da81d400664851120f0700c44962002041c440d0740d11b4500361a2181241820300030000925607540d4841071500c0000241c481480800d94041d8010305100d08202524014251030009078400a4800440b1002000400511440e500349040c60b00501c00c4605640c00d6510800e156080c0d0035079107011145a0800800c562240d0b011940014403131602c0e14043e00042e0050305c5c0040c40b1007802021150010181120b0b41c2c100001c1c0b1101a81024260790481c407900c03c00b01d90000c0d5080165102c1c071440b4409880d40c2c484103110710a00c0741c0c6a0240d01035650076682404110380d14031140f81d03a48400c0384071106031b0304160441d800514144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 632611456 1250 632610206 632610221
    0xc020f01110703150905151308130e0f090c040903020604020904051504060b1905013c02010b0f040b01021c09090609050421051204050106080703030507110109060e0103 74
    0x2481260710841c0c813981c58a03074824281c1d01104440b602e9007607180400c401807048000c49454400300c4000c910380348400c049008807100020300a100c0002c0c039010399200c120b0940c0061315802c1d0302d211840c2801800d0201e618000c580c800d0b010b0080484246481c0f800c1e00594103220f400d5070040c06075480750b400b00211960013400490f031502c20b14081c0729050300c61100451069000b41800119898400c0501410090750710100ca64806013000a0180341e0700310103000e00c0359030b441e10034800404004003500c0c00080c02102c800100d900011314500915030541080c050b041d002e44100c00032004400c2400705903168842654050b801c480a05241d20a000c1c02d66000c120241c034042000300c1d50751605100310b90164100784403040d12001040203001c0d091350003000c54603001140080c5910b551000805d01d00851101d00b24514200c408902400b0f825001000500051010b50740820707624500940154800c0008440c0300e0b65031103003e810766003d00074100c201c17409503c4d000141d03182c00c0c00460081188 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 632612706 1250 632611456 632611487
    0x3250509060d020306120a42050612100b1c0b04030503040305090406030311190312020708130602030a1b03080406050711010c080109150b250803040609020a060c020f01 74
    0x2030031031031107440300100100d04509008011400e0f090740e00307000230344d284a00c0c1981201c81143c00d101e400060903070108250200d05400e4000030303079622403800095014650f100c54000c584204800700e003144c0c500d039028070858001280d0701c60042c0b00303508820010704014040a0680b801040020300400d01030b90046910520034501503203408452400101191180e0700143d00065840c290a0342102d420004501130b008411300006400c850b541d0000c20f80130003d15410300c2d59401141e8082000a110280c80580e4503680c00c02101300e464120080d5642c020508203000118022841d8488216551940e00310541664804d40340d980c0d152145e0001d001c01604078810841c3c90f440501c1592001c1c130aa00040d600d507643d442480d40360540200681c0d100505c210b01c801000710082019001c040101e980c03c03030420041c0351842141c60b0300d1841260761000c01420341d400001c100003c0107c1c640c000c04034035100b121003081d001d8031040e045907022095407009412030002030301d0820a40c051000c804103040f8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 632613956 1250 632612706 632612719
    0x90c0b1606090c180504150c050d060305030a0f090f050103020703211a06040503061f170c011407050a0201230c011406040c0203031f050603250509060d020306 70
    0x1840d640c1c1c08212440c4000c01d45162043c544140022610750384200503a0802d003009008a0600d521203c00e100100465407400c07654810840309400e00400030b40319401910303075041103001e42c5e03400c080d501c0754440381c40c84002901480808000e40c0c003400e4100300361100c6400428840d402d090040d00254000b12041d000c0c880603e85544404000780020720341c542c0700c032101091007010b03480c483c400c9942481401d44a004207100520040d2800101c240d405003200200c96000310005030600586191074000440c03041c50101a030150740707400208414928820307680c510348540b01000c180814000e21b90014280c0c3c00402c40d003000341d0f02c0307285484260f4035160254201e654081800e0103080e8442407045c2900e0351a070307510005081c4040c0c8101c0d030101058800344006290f05000030340301d00c002481c3c001c420569140b440d140340e0903860601f0252401030482c0ba5a82414512004aa4090302c05c0e50801405c03401c800d075102d0310407416540e80c844058401d0742400805030009001c0d40000708030903003001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 632615206 1250 632613956 632613997
    0x10080426132916110d060203070819110405010f03141003060f02030103080415030f090b090d020c03030315040b06220807080a0f061b090612090c0b 65
    0x501141c12a0000d001840050700c03600034950040101d00c00c00e280c5200c0c141c60900c1038607050120507031002100c0e5480070841c03a0402d02000060510100e00101504451000c020040600e401029031409260200b012160840d0203243c00b00035100100c5042c48000c6080c40104a00d5001d068006940d096030309000c1041040d00c0b08420000300c0c106c0302c14004104107402001407014a10400d141000c0c048020351456045440f208801c0c801c0b8070540640c2801400000d0f030352446030344402e08601b20340b142403082c2000742c140300c04041c1d0180c81800c09c0e4011010b05e40c1540d80002a0051081005409541981d4884800c2e040041500070306582141d12500003499507075441008080120342d1501208002420459210700103450350040f44080e130040205204021000070124400c039801030b000c10340c0032403a00e0500081c1400c4098440d144d51001890109103070021000c0f029981183c1d6a62001603000c2d081030241e40c0e5411019100c5441c040b0107101522a090045c42540c6000c1803075070300903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 632616456 1250 632615206 632615227
    0x190201021516030605040212010614070506010b040509150a060e21010f0b031603060b0f090403210b0112091419050d031122090e070510080426 63
    0x41d411503003400751400ea082011249509881841d001e01804d0301c0c11824064400c21a8035100fa06001322018400094280701101036000216a01280d2000a40d611075070750310f003100c000d03400a003d240d20a222a00c0000c01c09101ca001c42c008543d070042c48212500e1070100b003a40c1410111120744d4000b01c1070030240c0d80802000792600e0307400380351f00d00003d41810040c0d0480125040d03000c3c2107100f81c001038400c0c2d410010341543e0009483c1c02040020b800c4501c080003078000040305020355040039051080106240d040341c0b084505042e403002000028008861481c22200200a11800f25040680b00701d182e0800f503004c001a43d1198681c0e411007000301041d14900450011465100d0584990b0401008405c1c050310306100b115080c18840744212030005d000074042d9000000720301d080710b1056001d01e591550450000e0030303044803c21044403a4000551100c48502a0314020040a514004100d10a0100c188500c0c3c102810031001c42d00602e2100900382204851110340c0030034041042c0d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 632617706 1250 632616456 632616493
    0xc0c010204031b090204031a070513033c0305131d0a0f0c0e040c03060f0909170702010206060d0f080a110f010603020328060213030212010e19020102 66
    0x20b5805199042403c00c40c1d0000c05041091680116101a0052201b0070019480802c48150100022003803050f41d0394150045466000b505100c01a44540311030001c00e0090348a00c0c8160f2184805a0302000d03800200078104805031344401c2c1000307120742400389000c40d100304060103601c214007421303600181d41d8032480a07813240d01c01e0426901554010512122071202d214402c280341100206015520022802034403407280c0091032406140c58002c080c007554400da016401414241aa08120b0350315030307030715400816054400b22021102030310200c10705076004090f603000da03905074018400b0ba620b100900414481e281c2c01101c2d2030340300035042c50010380204050071038120a566880000c4041811441c0380015501c048000c07a4980901400540c5002c02c10103403014031101e00803051007100702c01c0d042d0102c81d1030000e04030ba44086908841180750303206c94000c80b8000c446036545080c0120b01c0300d01b00d514070154922160b2102c1065050301038550742c1c0a013210f0050040e00c02c801c2a042a9000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 632618956 1250 632617706 632617709
    0x120f0c06030212070c020a0302012f0106050114072003070e0a0207120c050601030204020307050c0709020c0115120b0601030b090901061a0403031d2709010c080903120c0c010204 78
    0x402e40100e00b802030501490f020a40c004c075240350114820800d6000b01e280542c840c00040c0c10000320043c40343d40c207207007925148400610310380400030f060303106440c6500034540ca014180c00201007582e003250011151003502e20142d04242080740813064040403040c0d20b00c8030400703590103009c1c1601c0081c0381c201c03d4911138440c001c007503005a581c00d07041c03074100b0f80c600d044410001803219001c00702d408964009140d5054a40c10388006a494a50780000c0d00d00d40900c080d1040ca5100382ca40100b00d045645d00070304070712810f0000074003030005807440e0303540300c02c2a500a00c00b02080c4052000701003030210385440d40241c2c0605001860f03500047c0810361020086400324203036034490070104a1111961103950500710701da403220303061a08542d8028602c180a107104228400100031450300d90b9150080b80c1e0f2901600799803a01d4002049075002c1800000304c8188449500c0d10140049850180c0f004600c11100c00e07018500c1c1ca0518601c060542201820010008000340540d14010100740300130300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 632620206 1250 632618956 632618969
    0x4140d0206071b090c08270a11100e0603071202120c0306120d0f050c01391d040c0e09090106080c18060d05100c0302030108160e01120f0c 61
    0x407016060003c0d4140f040700b2030380402851458401d011240b1940404010740242c003808041c52500c080300f4045100038500300004204c2e0156000840c200801650940126202603035210504803102130140c4051540c22892500701404100117149148a0803060381a030300c44540042c113088084811000c2c15034110b444240314800007003031003031074600051041da05095110040c035642441490080c039181070090039505105003c10b60700c0b1605000c1d0000000c843d040a0800c440e195401543c0013001641c402c60f02803599010312610981303114400008600d280e2600111400501c4400d00005000d201503203001c01c16500161004c90b51507100440c0076004100c00070454609100001d424291409040f500c610f981080000d44103800c01c00442e800380086880300540c40050074114100312070040c0b070305031071441d0041c3c1c2d242d400c0c0c00d94003541c1070b14072043c2200c82000b034400071f100c0c18800c58003400207407805d502c004100c1042030040f1030903120b208003040d551100817a82c420104100541102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 632621456 1250 632620206 632620223
    0xa050706180905070c060f092f130207020a0e0103050606060d02090d080a1d180403050d020705030a1b020102071401090902160b100b03060f060c1b030d021204140d020607 75
    0x500c24000980148030381f11000d03c0301000200000e80d5580c480c40c5070b888500803030304010100240795401d090040700036850b010300b611303503001141b10b1b601000f5441494100e200310045940070500744204030380941640c0c0e1150003801a52100b0080007103a4206070a60010241c08002c000840d894031114024224070a020940c1c07210100b4034094002c40903200000c0c5d14080c1075200d8082c50366640440c2c4110401290041c00f151100d0404460a12805150b085800e000045420400200200411402d0420f58840c0072040348440000c0008245450103401030f03102c440144079034481440e122801a1050510004048c3d4400700348040e6040f54800010071031600c1301510a0100b001d07440355106a000d900b00c0141401c00d20742e0200d501001d00401c0c0170f01d886092100319511140203c40c0221148c100b07d44107415940c0c2ea41405140c1c000704e890103801030700a600c0b401400022100d00689405122038202802c00d1201c01c4100f017100801070b803104d8040001c002681f2110001d00b00c0500421b00c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 632622706 1250 632621456 632621477
    0x4030c110a092f0f1e04030c060527130b0316030c090b0f1003050717040602030426180316060816050a080402091801021306020f0a05070618090507 65
    0x466120795502c112490029004c100f18480b03c00b13201c1c1151122000c007014000410346040080c0968015900000c001403201c00e0041131a03908007019004840079400c070040d0710000304170103e41c0c41500103441ca8101c42c603921605a807075041c1d08290406a005022a880e40210054072501482c0d640e20665651801040601842c90b01c3d0250401c112426650030700529075000c007142e9440100100c0310101540c1c0c1000c16542842096610403100c041800070600e814a0306100000794004e40e011034602d03e1f2100e103035004122078034804800750001010309040201d0305120142519a0f018070356494080d0303040c5104903440381112540580440d075241000d0b03203441460850b00b0100740900c3e109128040c0107441c0031551022001d0b038019810b82d500035050302c0798142c00e1070b0240c0102d0507500650001caa168119001e01c0c105100b101c44550803140041503a890940e2500c0400310090040c0d00003130014800301c1e02618104d10700c80240354070203201c2aa0344103003408944080c0d075080006510140c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 632623956 1250 632622706 632622761
    0xf050d0b04201003231302090405010e010f0c11120f0703051204050a0b0702060f07120f0c050d0f0e0c04020a050f1206010906050a02150a0f0207230604030c110a09 72
    0x140e200414017058400509130130081b00110602584040c02441203500c4400141080740c00e400c6041c11182c040000c1c840600d07810b031958007401d2040452000103440140c09418070400090f91401041c400454a140540030601c642e06640524410750030300004024001e04a4004542c4a00c520701030b001511400426281002c1c01c40c101415071411075000d03005200e0100105503085810070b42d2410890a16000122050084c0c503643c10300c03131103c6203460510840716812074010510001001000c10070045518850002c03540d101d40f07a1501c95008500454803420194003c228240c1182410790410560203104801e617070014880002165a00051210b603581142200000d0710050070040c0c1001800d5200035581c02c0c0c04110510314120410204880c04002e6001d2140b107015504255076030061402c1403011055040c09044c100c416070305540c00003c02c0070403101d02441d419540c0300200441d5440b542d05043c805904c01d64050115400042c0e002c40d54400c0515295442c0f0f07070003160900310305 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 632625206 1250 632623956 632623991
    0x6020903030715061a03070f0f030b1008040c080f0703020607020105090901170d0804210504090e060612011b0e0a052d091b1605010203070503010f050d0b04201003 72
    0x30301004e85c5030040c002c3c00704150704109840c000c0d000341c0c41c000e0342c005580d910850280c0950607070306030403030042c0f40341702826540180f40901ca280500c14021004d0f42d03503030a00d5035443d80a400c8c0c0546030041034041c0014508680181059401458141c2c00d206420b00090b030b442500380c0c0504076680e20000045078140b4140200004002c09060403801031816460301500400d10f040e4042d01d12080a41080c21180100181c1d030160050441c204000d03030a030b061940e550807066441c5441000303a0a080c641e24101402040301030101c81c65211507400c0858801e03144a0308060344d29502c244200404642030f02c81c407074002c4645041e105060f081052348d51501d0381d08045020603901681514080001c4c0440154002e50300c07465601c1e41c182e0380c81e50501e40354881c58003513900030401d500000c2880729059001c40514180c0d100c2c00101c230483c507650410040703a11004034004042c90810380c0050085140428507403900c0401d001c4244040351a031002425900210f1660790200765900604144141180d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 632626456 1250 632625206 632625239
    0x9081b0d020c15121312030603021503010f0b030907051306090f14060d1a0106110d0207060e060a0201020c070305071806080703121101090b1e130602090303071506 72
    0x2e032409030b000c040e24000d5a0151242283c4d0902c070503200c0001c101140c01c10000c4081e0795030000ca14815126500134000e0144c030484c40160720601c80c80321282d0380034002c1002c0382d049aa00055080f001d030b1a040031030003d50001020b40c03155001d81c03903002a658848249499802c3c411f4a000150f15003070001c0030701141c17004542c903401185410410140240189140d80d0004000c0303c49404040c2d051626519102441000400d0311540320000039000350003403c0d60019032520b006407016003458013000c81e503844240c030a04c4009110201c0b60065401c0140090505044500c000340c5000c10400f1041d10308000c0b94003c4030254043d8000300030500002c4800400c10215000512081c1e142090705507580109000207021141241c1c0525440c80c059690f550301c810101c4000d00c00c1003a41d00f48005d03500001c03540340082d0100c0064000d0001c15410302c8030311813526a00144080740041d12014000e40000f04030300e8051200300150381c0491412102c10040c0304c81c024001c9110340c104405000d20003480b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 632627706 1250 632626456 632626459
    0xc0d0320030a060f0e04050c01081308070b09010c080f130f0803090d03050603010b0102120a030204030b04050c3f16180e0304050604060305090106170c1801060c0609081b0d020c 78
    0xc176000d10000a401240500315181e0034030b481025a1560084541030a0b650780d0024040540050450308010202d814544210741400c004c01c00012a15000c0e01d0007070302200d401ea0f030011510001002c0c44010307056010554041c0d00d88100c817035295030f16907080398001c1d12520030035802243c02240080e85030155541c040780940081c000b0103400c1002070b40e5002c40d02c042200c00f2402141c440245403081d4155001182c210701d0940180c01d01d4103019441c0c44031100702034054a4807c92000040b0301300d19101540c511500751150080c030ba026944100603000810070b821303030f01a005030040c00401c8000e00201030604e80c003103000a00b203094000c804403541801c03d0317103140c3c0003800204615a20481a070301211403034140802e040d03441c200228010002c0c0c0d00180181070604240f0401c0200005103003e00060644080700c140f05420030418a1010910421000591aa000100007442034000c04207440c0304404450501c0380b082004101481c07040c4900c0078950119051950f1158104901c0000c42030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 632628956 1250 632627706 632627729
    0x190212090a05010501150914121e12120103020f13020c0d0206062b0f05060c0304060b0d081606140c120f07020d030b0d20150c0d0320030a060f 63
    0x8095001f40c8103100074071523100c81490305001c0e0100c81e214103400b41d140b0075501c4203880c8483c45000d140d644078422039440e80c03014498158184550391005c42110b102c0151810030000c039038612360800140c130134100c03a420f800c1150980c0a0a028070a40043d007003d4207458007500d41188000300091030880004d00d114454182541d840c003100c00720403011400803000718000f280c03000c8d55081c8007039580003000000308a8410401086040e40501020303501984c49458240030103254a420080700764200c03980600070300780402c00030201c4110500c80200c1d03d03116140209000c80300000c1d041143e1001c444210030030800040c071180b00341102c41e030316038014003201c08103a45c0e080800d8003d581e00000d500720400c1c5661280c81c080c29965001009001d581d0212441d000c41c41c41c0d8103001a00030920102c0750181400e03d0f00001d03501005130645070070722500c07002031030310580c080d034210301400e540321046110803808610b1642d03900410000710312440401c0404144545804c6025a1900ca9a841145410b8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 632630206 1250 632628956 632628989
    0x609060f1d0c061801032f0a1b030909020a0c1a010509070c0c03020d0f150c1101090f0b0c13031101020601061e081b2718190212090a05010501 63
    0x84041208058028203180002d011601d0400b018050387c040c4030060668540850700d5408110b02c00c0052035180c1c0c19586045a50340c0f024100c0264580c911001000318410b50000c1c00243c030380e03074086e11404030b0030718014140e400503485840600c6004d00c068083e07038101c1001030140f42404800d55070802e030140340440d403007151625882d0040029020091242050303c500b0000e110115550f4118130f40c001c80b942d100105140d01c131400400b00e1021040110380c0305a0000001413040c441ca5400641000b0402d218001d1540c48800707101004004c02100001400035940724058030780c0841c007039071041000111502112001a14043c4141d00c07210401c0703a100b882c841c0003107074102c200e00544010700b0004055290b480109072003508440c4100c0240c900483c041065007461000c5411009006580d40405103c12003400841d00c10401460858407243c4085140304188121005040d0310a950044c01c0c03c2d52405003030050b21060300c502d101031b84032081c401d007030140038400c403801403408500e14480c15 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 632631456 1250 632630206 632630227
    0xb0a0e041e0203070306090203030f030703140a060b0d051308030c0403060506032a01110607051216090b1b070303030902040e0a05060601260403050408070803030705070609060f1d0c06 81
    0x3240c85000c000c01c4143c1f180914401c64a0070002d65010400c040f02c026101c1c540200b000b00200a1803182c003c0d0b100c103941c0851045119449a003051300c03002da074010706d4250b014107094050700001c0c04030361030b000d0090b0421022415820103076000d0203218585540d50392640c01e0000a64070003a0829110b80c118a078003607a24480950010200b0b01d15030145000da40302803006840c5c0025104401c4003502130340040140d0142c1c410000d240b4045c1d842c01071a0180c540c0091060801d848074140700c0442c110101c240311480e0003030041c014482c4882110401448807a640a0520000760b2084004c203489050600c210f240070b004900e5086203100062142200341d4030ba00741d80e41006003d46042c00f410303e60f441413082910700802d54542d80303050350700c10300e003014a070041c040d41c0540300d07403c03990050300804109203402004803400360106507507a40c101401a04c1c3c41d0028120a5001c482d45079441140d01c0d52205180a100c3c054a43c00700d01d00d460030003101e507250402c2c031121078003480f03000100600c3d00003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 632632706 1250 632631456 632631463
    0x30706060536060f041a130605100c08040f14130506011d040b030604050a0c0e04050a0803250905010f02070b041208070f0b060f060f0706050a0b0a0e041e0203 70
    0x1005200c107001019110100401c40503035100341130503041400c0c1070140710590100950350b0400f43d4140d408200706005054010300316402c0d4001c01e54840140204061458419041041010f010710403030341c9019a6a804030b03454998640c002c58025003408104103891a00c881c860701d4000c807114080c0241c1c81d180000078500c0762504103280424000b21500c803401c2d20385070b100c42459000a4211003450400d0b0420940e607002ca15022070740308266a03404218122141c80302c0e4000c5602c07400034000e600b00c565504000340c1004021600c1010002c100403031405117050400c0740c00e48143c40d000403180c1444001400120303400b1524040d580074a2040065102510480d03084a0a4512641c1070607c185040280c0e0b1141c000042e00003010b460100050040c05441300f80036400858203442c00c9084682400001d018104803500081000d20404000c144aa003203580c1c030008140000403100032500015a01c00700981000a40d046079400b08410800e0082044848020b0803545611864295002998 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 632633956 1250 632632706 632632789
    0xd0303051b071509170f070606050307210503070c06170a0524030a0503120a0f0c140c0a02030d020f10060302060403150b040609020307081302061909080307060605 72
    0x1d8440c0c1e500800c60030b01c110810020341000300240581c6c1e9421114003400000d400004081d102d41d440c02c14000384520b00042c1c42c0302211300d1581c11001c1921486501410740840d0901940c1e1404100107610000d05142e03010005410300d500c7d8444034100c119000c0043c44d01c0108150303800351411062042d1101e02480c00c40c40c0c4c162107803e03440c1070043c40300401d0030000300301740082c014400401c440c0b928840600b41248520480841082044001d4100c58180c5032a40c41001c00720321152400c620030144840188100540b840032a50518a1540400d1401e201a00310318016004903a0300c1119500a005003510000c0340c502c01e11116066400180700d500c0345110082c8a0300003c2036500c09113103550071070200c0400003001008942d070354003604400382d80112030080010303170040001940703142c02d44104400d0782d8002d803506041269040001414082400c1d04505201140d500011600e9007040104100b038880c2c840422150b24007005e1001d8402c52481012a002000204586d0000500f06006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 632635206 1250 632633956 632633993
    0x81f0b070b09010b0108130503040b0c03070201140f030c0c0a2f01030509150711031c0b04050f16090e04080d052a160f0302060402010f030b03120d0b0d0303051b07 72
    0x302008680c0c0341239890b40c89254004540d81001260b1410ba03454040040c04034039001380c9842c40b2111a54100103580d1042c603c0c03402107407405102040a41e401c40c4042c281254000c01140c0c070800c0741d602c440c10034007000c5400d41d803003441140f44c45c01c0a50f02400140102d040a0806000d6030401d154030316142d007184007400c13442c0041e0b0341c0000c48061051410482c509002c03000d0725507a500392001f10800f00d03008003d2140d01c82c00c0040c20502800c0c1441520700c209030100c04c0642c03d454151003412481c4d160000e9108020480788003007000c0d80303030440b064003d40c4a440c107942c4c0c3d08080b8003844151200100040c0001c1c95140c0034440440c211610080303407050480147d41e4408480000842c903c55140d0050103011801c031303c150070143c0008945010b14000d8960403000c0041080c114207584043d01e007144c00d03401010403c400702202d10047c10801140e40720100f8040d0750b100200d603c07803145410580c0040d84400034000604020114004116902d5001601e00201038854401710300f0384001c850b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 632636456 1250 632635206 632635231
    0xa020a120b18150f0726070f091805010312090b0f030406060b0706140a1107020915090c03040309140d02240a0e042406081f0b070b09010b0108 63
    0x2c1c4a24024070400240741c1110541140504040090b01112101103401d5030200b0b0074940b0b070007544c0d50010324208140319845010100d65449142c04c0340e4108407081e01b0380900509000101e600460348178142c2251803a0f2000085640c550b00303152002015044040c005d00100184c140140c2048001b100c540d410505e0941e5a251218504980242600d6010504421003c18003008000d195040307481741002080805030305403243d1170303120129081e0301d00054090318200040401130812501d180d5000c018040240c0d0b51a901002142c02020200c0b403448010400004100425030080310041c003800140c66880c1d000d24094000c10040b90013910701910070054a8603520210012010b8290a8020b40c4801912400408009828850070144140c400c60034542498818203c010310302034008040c004400206140020070b8071900806004009200d408450849007000461110801410449803141c0d41d500d040c105240341610107804511540d040547d06626070380e026404581116400182 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 632637706 1250 632636456 632636491
    0x102150903250c1503050708010f1502030408120702180f0406021602120d1409060a0f02100207030c2d03030218190303170103030f18030b090a020a120b 67
    0x10000b078410000001c0001032007610224107905207600c0f01030394500e542c80900941c0c840071801e488000c030900a0031891003c0c04020003804400c4243d82d281d24507a0700599182a45412525043c1001114446000380300040c2000c114100503445142c8621405040c0a4904180c50a1182c5000c06000507100c40d030041080c6801d080780e011141d44007580180506d051001000d40241c560600e041c086011070710b0303100002099842e440840b007040380010181c034039160414800383c591200c080c403c20114441c40c0c0c18110400d18500c0105000340c00394641030000b6000b03240a41c01241710040340010501038401250403460138000c1c414446a05083c0035884200304105943c40e9020482c2e41c0b42d0054104441031f07150f05002c803058060320701a07500e2080711501c070217204070075000070f100040006804202d176604481c480c88c58049140a21001001c0c05aa0f031780700c20101c00b0090710000c1031908600322420451814581990040c00c003442a864001520303141c00702600001415079049011603500f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 632638956 1250 632637706 632637757
    0x70b1318020c03030709090f0209150d0b06040f14060c030a1d15130e0705120405030d050c031006030e03070605061804050d0806010504050a18290102150903 69
    0x16a00d90342e0410044039107901e8840001000340c0fa103841488035151401c2158034003201c942c000c0722160a0302034100304840403200219545a40030840c0716030425952040458140c2d100c80051006001d001e00d1805041e00f80555071034120382c7c01002da0310940c001c0098500d880004003c0d5215040c0c0341c00c207008180e80100d200048400c01d2030b08103502c80311448110070601070038409080c200405840c1c000da07403078445444a0640c0002d44944d404140c0c28020700b100502e5407006035502611403810703a4107180c10818014203403107040e245480e030610003008200a44c0001003011005002524081c00451010343d41039032a48074900014100d01e44075000640c19807202200000d10348003022080c0494900381c20641c0c2c0f80c0002003101400200c038035002c182190710810580d800e4820040040c0d40749443e2403080c0021003844000301a14980301d00c02214050384954038503c0111101c41201010201200020304021040c3c0d0ba96820903081414001c0842c0008103a0305000345a00000030041c41030740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 632640206 1250 632638956 632638961
    0xd0206030405011e060e06030a0201080402090c07080a09061b02011e141206151312050a0f0c0f0b031510020708070618051819090b1602070b1318 64
    0x284c0e04c000c10104180c81c0c40454965000c04c0440b00550640c0030701c2c1e01c4070f03001c141c4c9805070004041d0004200e440414094035010320050b4200c80441c21a03403038161168bc94101c203411034600d50f00480c1055000f040083c1d0440307030105100d07244c3c08002ea2006807950000c2c01200702d0b0483e042c00160303082444103946008401846600c80c3c0101c020751603103039107000d1a50b503500c00c071402e502946040001c0201c0c0b01101041d44d01003807200b040311018504001500c903c04035089400d8445205018031000480c14842c0d40e40105801000c90038502c50034a1040e001d82c51203a8000d2196410070010442c03c524045501c040106088804a800b0b00607482d0807840d10425401520281c02070540c00124241c004601081b0789401e40950030006546808000c00c041ca001c140c1d4200c3ea0a14002624510400b0340c41c1c454184803280c0014001c08036111000600012200c00141c0c8403030824206010360100812401050315001051910ba003032900f540d0407c48034442d041250800d904540250300854 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 632641456 1250 632640206 632640221
    0x90a1511030a1512050706030207030c08130801051f15020c030d090e01050609012115030803010905160f0e0105040b16211b0c080d120e0a020d020603040501 69
    0x3000348544074203091500c00e004180196400715060500301c400500345101890040d807258104015080710340c64924198003a500c4564102c1c20002001c1080000078540300191000c04462101d070b00350710f81001007207400c40308040c1086e00d10308405454480c0c00c101440641d815288a0048036800b41c40c4000701342d2400c00c4580e0141d600d4081c0085d0340524075070142a0608444c22601c800320a80d03612410301c2918400d1112160000b0b031500081c0c410780c4100c000340c04000f0030b9404000341d070309041c0c204001c01c0b6403a90421228100b00200400a00255008150700131000000200c090030590101401140c4418004400d002c01d40b079042009a004034195030040804256590b81c1c1e44102080d181c481440c0346d0120360100c3c608101c44211041c3c0340b450720000d1100d4a44c86070040704541040158580c14a0440d010108424080340c0c101044c01045450300140c0c48403007610f4000b10485c800d07510b8040d0032045035404800120050b907a00318504800c0c0750143d81c3cee25541c1c1c03514200705003d441d85 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 632642706 1250 632641456 632641481
    0x2060d0b041b1d090106030e070512030d15081e12131e0b03182523010f0f030912110d020111400f0e090a15 48
    0x1080910b620240304815560341c0e0761400d6807503e11104807152600902c22840d02c106030425941c100501c10607000358040d9441c2d071005e0040303c3d049640c1d840000d01010008100a180d80c0000c20008680c1407540565850904191070701c69607a0306001000e41e40c0c05000f0070441c641c0680217940b81341e4450601941c800e40c0e001860560341c4401161008060762100c0c40b548150042c52a030840300305140742103420540d650a24440d1441c0c4603983c03c807a41601c0c0303c507000340600507003082d13107c1142c6c04000200702e01510031004002626040e50441c184441c050713108541400c018034018240e910081c0381803d14040e09105290a50381e1100300c004095a50004060f141c032101003d81940d0040c1015030345001240c11550440e500312001c900741c8410b203407141c030491001d00c401604501e80e00e889071810740200c4c00d2110307070810a2a4200c41915980e0900440454466042c40412040c050320000340640303030510f804500741800d030f4a0b03a5a00d100c2c006400c0d803804603e2040c3c61000c0d0307000302c401c0c00071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 632643956 1250 632642706 632642711
    0x160819060b0a2007031115031501030e030a080601030f0204080609060103050c03012a05190804110d0203060403111e0f151e0a0b0409030509040c03060b0702060d0b04 73
    0x22690190800d40d40101005004503503d03490710380351041000f0382c401c0d0711080301000c0d03c880c9181d0307541c1c0c88030b1268000a0950150b0501a54a040c802c0f000240d440748122036000710300b101a440c0094125072011030b8039030103908204190350119821601954111000380390000d05000c2c5030b0141d10081c051600020028001c8006001c4000ca000a011341601c0c000c0301a50707580040b8101701401c031841c22444a25280340304000100780d8081c442d492100e0091801c0141c0391030003002d00082c1c508a000002c80c0030130a00c0d4184801c2c0285401c0304102030a0645201c503c076801500040d566040040000b000c000c0c0b10354010700c0380c6400f071129080107855421000d08005101004940798154003910405a01c01c81503000110504c1e2602c13540a40c4014200304540d841490681500da400248900403203a1514030528079074546201d005005806076803291348401c501030420007a10285103ca074101400d0640a1104025100459075481c0c3e04a581036900c11541c13207c08003404004070410344c4680f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 632645206 1250 632643956 632643959
    0x6030319021c0f0305060f100e030c1c0506010e041502160203121e0703090612022520090a0b01210b030f01060b070f0501200c0c01030516081906 64
    0xe41080100caa100c440d91005c2c0841e03500c40341030000c07542d80c0e09074003603100c6000c0000003151401040c0459150f403024050310f08100800f000309849809400c2c0c5410341e2505251501c05000c414000c00d4094081000030448606045d2910401c0c02d2071508003d050f554006081c844004800c0c0011a400390701900f03544003a01c612000c00c0a5820201052a2040e421040e80d07100500e07032000c5502740c2d54140c840d01030740c0382004004c1350b03561070701d00c0c4010039aa402c100500300340c01d0001e06881400c1a650b8007031300300d12551420191000c0900112113040607440c0907103507503580300da007010342c0140c1c2c040c4005a00d04061004860051540c0c501d40d00c071050090005801c11410380100108600c10b90480720340010801d4030a0899186200349440318800748200c80000e48099454818a030140e0004511001c0c80c001650a81d0981c801104060740300246509401c0003d0108a040f0300090804004031700d403454500d01c1e0035545503500410428603034001048006007030284084032500d020200a400e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 632646456 1250 632645206 632645263
    0xc0504050f270a150503150c070b01180b0105120c341b0317090402070515060906010c0201020a0f0305040f0807060201150617061314010312080603031902 68
    0xb00302c1a982d000f0158100410911003141132a040e10448201600074080130440c0d001c2c805a040c0003034800da1043c9400c02c10701001c102d008100310f000e44120b074118000c1c520034458801c01c41b030540b001a81488400c2c8014111441c0c444c00e460780c00310744181d8075940c65036440d0701da0305e82403d401c4024001182c440c01c1c200311046c9400002c0100c904c81d070300074412900070f291404000481703884014000c803a1040700a80b40043c410140c101d0601c0900050b0419003280d80d45804c040800d020180340e013001c0010040d00f454522421600a8030a0078001010300054000135103c0380100c7e405400c0c28161080d050825200b001214020890f14002107402500c0f10030144d110031051061000560801c514107030143c00c001c105400715202c41e1940c444450002004161641c001845150b21405800403500440b01c035016400c8881074400c1500d9080d811407405c0880b540c1e04054000030418804208403251f01e00008852003101c0018010f1010303184084102d1030f100c10800503c03015001d010044140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 632647706 1250 632646456 632646529
    0xa0f15031209030506130f020a0303020c0415050d021216080303040c23010e03100f020c060108060103030c080c0106080313031a0709060e01020a020612190c0504050f 73
    0x16284105180d000d0458a00000c0b10481d00500000d022500a0404540b4102454400352003e51080e10507120800703594002075280340ca603520030340268100400041c03071494a44902d100520440d0b8055213054108000b14007084501034000340140780d418004000d00c4000c01000014001d0305864603061911b03000385503200c1d0416038044400c4420824040f0f2000194150241625400d0606c4141c108241d001140d500340d858a9180e058001c600346c500c00c101c4580245510760108201c0503a441c81491041d03480c1c0076050f4000065504a01e005100080e030215601030b00603017280305c8a4644c645104414014415640040f220744070001c2d910f451402508c441104032401002c1b9071003070103590203400100403c1101c201000540034a81401558003503c286425848188110351a012070b580c0412025800124401d1a0b01540d60400000c0b105801d0f09041080800d241408080c1600c0c3d4007805a0082d401150300c0f89140c01904181c0d51508c000c80100044918030142422084070382000c917 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 632648956 1250 632647706 632647709
    0x405070c02010809011a060304060f050a0213090e061b0c100c030b040902090609150301110c010c14040905042109030201110a0b010e09011e0f060e01030b04020103050a0f15 76
    0x103c1c0b142c600207001440180305081c403a484074900041082c40781e004114055100410460750790303540300130000e00d5004c940b09407480740070981170069890019003034104001ca00766020303100840c01d003004119003040110341a80c100303a00d17803108003031074489954680c114011004066950b115a0f41c4451644069410100324442503031001c01c50708810400b40001c3c0d40700101c000c1d40000d601004a20b060407c105407030b038000d1120903000c1142c480e841c000f074203603081d40903241010403003c01c80e4080f566080c400d15100700780c039083c01c3ca1249803044603c040303400f66210744034003150740d400080d06001e2040c2c040035222070b01b03055446c49c1c070781c2ca00380c050511030880c003083e40090511f420404c0b40c0b003000030b81c0303110840c4c001e40da0014681c6072060b035031844a030041075550555202d940c01008011851100085080c3c145408902d030318151580d20219840b9038010301280100e840104082100301540702e8015170282f80c0803415660b0454505c0c081e211400780d0400491800d00d55407010144c8507807580 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 632650206 1250 632648956 632648959
    0x70320030a110405010c0b040c27050114150715062d0612050a061e1e060c0f0303060b04230303030907150c0501020a091403011b14090405070c02 64
    0x15007041d5220794082c5010754081e182c086600c20000382d02107203482100c540d000d44658091013000303486410480070101d4100108071048540c0180461070032450080074058002c40100c0400c4252344800610101204c00400060307072130006491061012242103440349074502402485a150b51300b074440c0182000300e00c02050100309a0800c5107000051155000f03c0d00255038a040c1c0001c0000070703100514001d82401022039646200083d4005000d04554070916034094603640103280507a201003450000c80d20030703200359111380c084c0900c0e41c01c0100620180c0d004411400301d01c0c000e00d400c0d4001d24403a007004542e540d0100b0002080c514084a1242481c007840c00903a9a41000045c180c0d00d00041c4c40307040b0030341c102141c14010003e90350090002044149445003904509031950703422644084400e0000485503901030005d60f0540c881e0a00c4840150020003194104c5150114901440140a0100302000160b1241220794009540c44144c008108015905107690003074603a940d00601203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 632651456 1250 632650206 632650211
    0x2c011203030b0a03150209060403020406060203031f060f1116081c0503150f060403080f0405040501080c0d060506040e240f04210c080318160617070320030a 69
    0x806036420308184007822a45e100e40b40043d40003030b0b5100a00690004496590829800e0000001694443c0103150040c030060b0061070390f9060a1203012455144841041c0040807001d6007002040d40c00480702c22400124582407d500c2e100400700c90507e10685207210010480d01c10100d4144404a10801d18810a400c000910460350100f61080d01080300e06503109801f43d06442403d04014030207009500303005140910b06a00caa41c3c584a5401015408488003808074091006051503c200303809042c40e10001c0c040c014005000030807002040a00074170302c80d261350100c2e03c00e8580703410600c01e40101c4e0055070085009190210440b480c0c50f060460003480303010110708070140c031040c400d000b250850010704807540c114951101164a003481c8108000340c0c07580700800708204002550043d03c1040f1800186001c20b40990316000704402030008400405204018a64004e90003d440c1c00d501d0003007240599800380150300418003181c01049800580080e02200380e9400000d40c45000c03841e004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 632652706 1250 632651456 632651471
    0x2040e0715090b070f06020f070b011401030e19030e100302130905100b07110d050a020109080c0105040e090a0203031b1902060901200106060f1b0203072c01120303 72
    0x456100e0120320984454050404c03244022402800c010604140500000f44c40c104a0b6650202d866005a40955180701070701c0050080d4404c844d000364420700c00b40703020300c12031107440c1c51561507004580702145010ba21000a03410980200c00d000c0340242e0051106841c45115407015002c0e43c050f0180c503044040400001c00d1000191207654010000c100d0405501411b00d07500d028a5805080705481000a681a8803219a140030000214a120354040e24554000d8400540f18141680042000e40c0004d00c801c180382c0d0f070140a5908540c40d11154941a40b140b040103420b1400c0480041d416010000d00c01000035a11001c8403003030100403080b0341000440141d1a02202c001c2c2c00300a6000c5000c0240e1303402907104e03203204558100305102864291040110103421100107a0012001c0f070314a030740003100c003500164076005a0014581c0c18034000d401c0d5001039105c101c2805200e203c50303039105060301a03108041100c003507000c5500c0d4220b060358441001074810105250100c3c0001d051686 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 632653956 1250 632652706 632652749
    0x90e040f080a020a230c27070e100c080f09010903120206060111030a12020901031e1b080606030711031908060a0b1206060a0315030c0306110307050a051602040e07 72
    0x75602c0b2500070060180480204542c10001841000740203070b1240383d04801c030740047c0d6801c09415030140e612920b40790810311401003800381c880e07c41d01c0e01900740181d0600210104007030314129200c68000360781d150303590400940141c4510032141c00213020f680d00ca4401c1e001082c3c000482c58080c80b02602c42c021960340783c5410310780c1c0b4490342d03042d900010100e03d00400d5442c5143c0190810402c1410003107100c60fa003140480d103032600d101000e440641c0342c4401031100b01e0500e01c2c82c0d100780e0191074000e4840ca04840418581d11000c0e1000c81000801100c039800c180c000c0c010340781800d0048820070100d941e4101d00a240c15416543d50344109038a44000540400300011a0190b0803c07100c40c190070f60b00c04040007616000030030781c0d109141c1c4801c10756519403444000c0030051803044044001c05030643c140a000c44008081103850f00904006000255800c0000e903034007204d00f4074010b0fa0340d500e0308040701d50020510760700030b41080c1005400125142c002c20107030103803501c0d075070020210038010304e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 632655206 1250 632653956 632654003
    0x20313050105010f061b02011704031205060303070807080a09050a030606030c0b07031e12091505180a110402070605090615010203130302091b040f060f0906090e040f080a020a 77
    0x1c2288049914640303107074241e1b510b085411000c98014108103e2010b40c0c04d505441c5407104881c00c0f40010203100c110051400988155070300300d03034160010341c104240c42d500caa126105190001d0300381400030582c41d8216108031725800c0580700103070500040a540c1d2810341c01600300307400111074503408510301042c0e42d010320080d1051181c050740c400c14180280d050006d8501a41c00980b82003102e2180700c0c18110300c03540290711000340b00b44480301c02c9080d1081c84404030340000d0003100d8014a01e8100c1490031000003524035010b60000e0b04040480d0340305000400900c0b80c100018401401c1c501080003400001c2015480b5038881402021480c841200480c0c0340d2003542c9819400b480041418401f5003020703564594401d4101042c0f083c42048419030f0549500103a200880300b811012050019950290241500d4020740c01c0507038240e410b15031b01504505090180c5452102d82034000760502031042000c4a696810058080e592200441c2c020f4454030846001e9556100c0c198003061500000d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 632656456 1250 632655206 632655209
    0x40306050c0a140a02010605041b090b091008070309020d0308010501020d0c021e1801080c270112051905062d0705030702030408070b1b1908091201020313050105010f 73
    0x1d070f0301d00107112500c0180c541035410011912046650312000400d5686881c0f050425145104d00131690300403080c00300a04440045d0805e00c1000b0060020000c10386620b04940c142c2d0070f0504101c8241e07a0703100c000b100104880640a5408410409402d09050304044440e06031f46007a42500e40074801c00308290781100742441c0094012500000360061031418101311004150000d018840c4a8146101c0040d202000c1e00000400d4200e80883c0c46503140500649038040052900b1082c2c90a201401d105030041c14410f0b505080c43c050301c29010802c0c1031043c81010302c1c0035214410003500324117100b5580c1000b124502c0107001414580b0261101c0703000015103034600e20340e11138019665100304450903040904140e0640c8010f100c0402d407070400780941c2d0b014220700703080c1070348a08805407a491501502980d011590708030384030400500c800035070350607c22908602c4503541c0742840000316446440085204100d9417010080c0000024441c610a0030076000300700030701c00da0b600c0b418030030001c039044d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 632657706 1250 632656456 632656477
    0x150c030f06030d09090e0c15090306011707060305040809221808180d05070801020901030b0a0326190201050105030d030506010801090f06091a0a150e0103110f0708040306050c 77
    0x20388004021229031900701340040240a02502d9068142c0002310350b1070b60000f07514214448000c40d101e4058141080500c2c010410070140300302c10b65500645a8589403107001d550101907c40d000030f000c0c000014103d40c4101405400c001e60081100304c0c0031a14106e0440e03600d00e6a040c003187c4400c98171605c002c8070a541e0000e0315140b8203201309060a034030600313030101726801c0500b080c20000803071018020a8002d141a20000d42c0e1442110300040440d030801d1030345441a00284401e10203e00494602d860401c0b2519245141c000c0d860094102d86c0291202950b800e141e00b03e110350510741c10340026040310802d40854551802f036500c2078098400444a16000070b0341c0b04010482034000e6041024640017684c0c00080258540900030207443c1003221784294103000b0011002d0310305054010400620f17240716021a200f441d1070000b0021203181e041c540c105512008019010b14192044900d0f200b40300c00802d61b030715001d00d46003907660860b11066603100d1505000405101510701110b0b64040c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 632658956 1250 632657706 632657717
    0x314010602120309010e15041101091503020901020a050f010c080a2f0f0d0204141f030b030c0405040f03200c1215100503011d0a0201050903150c030f06030d 69
    0x107580810b06043c1c00040c080030481d921a01d4684500d0014000e000c0842110710396141c0350300c1c0c14141505c1c1540158001410000000b40c1001800c0110341288500d589602d40542ea401e00b00780100c1c5006e11401002e80603008038a003808001105500200e0205101c2c2c8030790f1004e035a40091441203030f2462504141c07004091700e261a50001c80001c05500300701c103880d0b450608890520030b00302504410442b01c1c4880e4005414010708500031b21031840a00c04030b83d90342000720400da42c0c0c110b00e07c008071104141904c6120950065070140b1400c0029140904204400e1900f03082c503602211001405901080cac1c4610840548282c850754003200704002401000c00074200802d2280d0440c83d1103091450303000d0584482c500881ca4030740d0501805502e0088014941407804043c212007000740356114511001507410441c2c0b2010620200c040c7c1c090800c00e84614800d00480c0c103100d07014106401c07580003402040f0b195489480a180950380f0b11401082a40e1483c0a15680c1d1806d007800501084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 632660206 1250 632658956 632658973
    0x5090429060f0306150d050a050f0a0218041d01050a020a080609240d14011b03090b04080705120c01020a031a1305090c03100b090f070c08030417190314010602 70
    0x1030404510170351352481025076240017a084004000c0b00c030295800c40c581511031041c000c0f840b0483c90440d4101503807103000c525141010401c02c501d104603808142c0690349650720401000c4014000c00b040d0128000284041d2900c84043c0c002580500c0b541c01c041054007005c0740c0b40303043c81c00b00b0b1031080c60f2003800f081d151501261880c10090b504884660301821280d40d0300001351302d1460011101c0c0c0640000700301c0340d8496481420020062488000305807410b14400c0105811015207138219401440340c9a48103003500f0103900f007100e00d480c00340c05200000f40c0c0b07182d40720055004110710340c003e69040140c6969040d61280b04400c1c1d0300c03000c5d8041d29444840c054600c1c951300454205104c0c0040300e45040400c40400e05040c4061408080355903584001801da0a21600c43c40d4800e58403000c035006407410020241c9020505000030b00b0340c01c0d0100000c1d040102c03840d074462941c05000c52598072403110721540703203100c02c05d25010000039082c68001c602c40d40f0220026810b94295401610441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 632661456 1250 632660206 632660209
    0x6080a141006030f0308161202091f021005130b15011e120e06071b03030b060301030b09190206031303090b0f070507060c05150705090429060f0306 65
    0x290440380034a2014020300a50944060780c520032100114404c0200240c484c079103080182c0490401081e00d26514400641842c41541c400c100d03a000310428880143c403642c0700b10201c4c01c1c18410012166103c10200d524090b803980010702918039585001c42231040f41e413012110000b190221320020800741c007041c0400c550440c40303402d0346071030f680c10316000c80700d0400c0341d492140c00032102e86e030100030880144d0407a20ba6822401100c00d4a000350005005a041c009801000311404103504202e1410101a24080602c80d4010840b900c5005247d075840e961a42031480d5195800d13a0003440910039005007040e02041102045426600108a5415541c07614051035044020f41000c508020b01d1150109036201d07200007030a188c450f0507000c00d44036800307850b0940c5409443d82002080c451720b10b18030b0000440000d02c40f40c012403007040550759134640d10b4085e68180180c240b00c60b802800c000318240424042240caa0014a004841840a12980040c002e40740304a150300302c045502000040ca06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 632662706 1250 632661456 632661473
    0x903120c06060f051309020d03081803040e0109060806040c03022112033702070303270b010b070309030f141506100807021e1c0e04050a06080a 63
    0xa0401a0420000d6040306607551400ca946a4108000c0000901c000340f100b4201048412440c0d401c0d00c0d4100040c1d003207500001c0e0700080b82040201000711450000d41102540c0151006d1540c1c04011a91aa40c4480a9550840e82400b40d95019860014001030249000604500964008800001071801c540070f01c030110400442e8010141094035000d62900781c10405030040401c581516622810001880f2400c1d8442e001480480c10700b44040e00c28681c000100482400c103014801a5904010328042c2c0150500016049003020402c1c0c00120394600c8880ea00b4181e881f40c10b00528a80c1c0399504242c0a01514a0150000300417503020301c00a102e00d500c2a45003030080381c0c4616512102a1400e00c4d11300030361030248102c0000020301c449810700c09400c000c0e582c11400d18079054608818025501c1d641c18440119803900c400494005100a00001c516200a951012107024030741d03a011f04050718008016004920740400621204080e1086400352144580030704901415074070345000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 632663956 1250 632662706 632662733
    0x11e1b06060f080a020a0f082802090408090108010b0313060207080408070b04031101020a0822030b0a0e0f1207080307210605010201050901110316050702060714060108030a0903 78
    0x3800d9694040c007041010400b80100000c040d03c50091140c1419841804010225688402c0541500d90018024204003149501035105c240098440e4800044460b1100011a44010750094107003030901061068060043c0300d100f0007078a40280990b6a002c6c1015103100403106902d6100c07445966800080054005154860042460701e007011340b100720b11360401600d43d1002900b2a00000c040081142c42202615140c0c4240003804d0507061f25140d022641c482d050203000e2815620050344180c41d541c030010340c061504140c20a2a41c601450303620000e100c10b04042c051889414410722a1140016107100c111341956905410507000b0b54602100da003014040c074082c01249a110344c0390002c1c2ea0f16641082d00b501a01103005881e14002a08503040034025840c2a410f11070030500e460300c02e0782182d410090440000304012002d6108581c1400350010081d8400f5000801d0400d0208101103941c1340c16008082d01d030581d0307030340308416501d100d4065440081000300400300013042c0101107021b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 632665206 1250 632663956 632663963
    0x14070c030605070806150a080402040b0613140f040911040213120326100b0a0207050d060506012015060a0914040b010506040b030a02030a1d0c011e1b 66
    0x2842035126903428050702c070215441c40c0002c1e000c0e010828a8a0480b44100e444404502c10515008800000030007103031700248040c0c003030f0b80ca813001400760340c503002c04440d07210065070b04c514000c40d2a4049020390382d82180c49140325046140140e42d841c80d2503c81c001e4440d0344900301400d85040c003028480650023000c201151a00c1907030002510b039031032070b040c2c41c007040c030950721071058600c1700d0521a10700c4d140e00701580c02c0c0029107082225038240e1001c0e03c8203881b078100c051b5407213200b1507004034a009145d4106c990030010709140c02c41042419000079018882c262030b8512110144296050310502034200701d1450780c05450110060b02d0034100d540e400600280071185880c1d1140f46003025107410021000000d82d8030700801003401802241103000d481c045440c10f18143c0b03003922178082d07804040c00380b41e01c040e030000100c0c2035552107a1149282c2c043c140c1c007500300051170210342c1c3c1d01d030908030000c54003240861000712002d0401086032800d002c4592555480001407a154220300040010110b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 632666456 1250 632665206 632665223
    0x6020a0b09030c060106020a0c0608060603150402090415090c0e1005070303180b07020d08090705040e100518060108241008011104050a050a08060103020d0f0f0602040501020d0c031407 81
    0x8401e840f00502103180071b4a0940c004010041151910608400040e485081080035040c180415aa180002c0300e4011502031480c1c03841c0308030900010004c0c42040d080c144d03c00d00d040b50801c000302820f0301c0e04d0b04440501e00c00700560520b003034007a0740c44804c95944aa11411a5644407102e80c09403014200550081c580080e030300c845e84481ca0000c102d078101c01c1d1041c078031311340800c41481d030304000d4801603039038510f0452294145150740b6a40d07071615000f0f1600c682c0d11000c820340c889808001d040f6003580030041c00d00441c10464507588010b0300c0000c150030903000f4100040390b1074600149031005031700c1c0c40b21000700400700320001d030300c2030790024090300182c1089040c00200c1070024055145034064155071035950380c0c0f4240070002e28000b00d500282c02000b002c1e5041240800c04100f41d030450390140c404076050402c0b0311b0700395401060308000030200406810715034184542c0794040c00680740280c00302c5003a01901d00e825240c011000303c0c0240016071201030040d40502d044040c2402600c6005031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 632667706 1250 632666456 632666467
    0xe011d061e041a0a091101020c06030117120a05040f0609051804020d21200604110d0602120106083603210609013809030d0306051906020a0b0903 64
    0x1800320940d0180e40d00c07103045440e50701740024041500c21228805d0b01c240001c0022083c0b103000b0410703a00051182e41c16406086003980d40049081c44000d10602003000510b0b52500c0030f42d030152454106005842c0d00c0304103003070007051a60252034814207031a40202030703200e60a2600300c5c401c0f0329080140b080f03070060b401100080c00121101c07611701d000810342510f40c0010042c00001070505034186014070071902c065030380c0d0b0301542000c207201e5045900015881d06c500984804030358400000341e0000e2400388000b0b6464403c0d803800c5d4450317040e12120fa55541d07a035120741020398448800000c20740c50752201d1021403d1584840741c0c041000c2507010088d681408080348841079805a1540c0e0104101da1780010404a498403050075409081070f0f900c4180418651188101001b0f20250104d440c01608002d411700c42a4444c196410220010304417100035000350802005428284200c43c0900c038a40400321034039001c04602c070700b0385819600070301c503841e05c58551411980000c0c000110381e0204106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 632668956 1250 632667706 632667743
    0x14010e030a0b1b071e0c03140d0305010b0702031e12040b0309100c121104050a09150506040506070201051e0f041d010f031112010e011d061e04 63
    0x2a50050740100500101e5142840104a0324400800004240c00e0708000c12400617403500d0307000104840c0d640000102080710f14011810b8a41500050701d4480320031400340c40344a00285058602a6941c0c0512550341d80b40e181071890b020305030b8002c0d80b5400030740031044d0910258000001c00b041640455802010f000da02c80842e50041e0040d02d000000001001202d120400bd80211003400c05003c05c100c1c45451001480300810b20207c40c04180c6815004401d0144842610094040200040c683c95910b00d641ca00800070510044410039000000045502d0980152412141c01500c0070b0b1030444280d0044075641c0c010407020700030f04000c00c5c0050060f071006014003802c94181001075a15070400004031010010300f40c4030f080c0000d90360014020340301044165800c0326400b20201854501c201d000a441c0c00e55080c1c191000c0d0711345081c07041c0d404c0054000c2d401c0411030030f18401c1d9141a4410050316031000301c0712001d25004030380c40a24200c1c5461501c07584607000300090b5014619001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 632670206 1250 632668956 632668963
    0x90218060406020a03140901050412030207030516081c120b010201020d0c050903190f11061623030c060c0a050c160e0a0b1305070504090908070b01080706080114010e03 74
    0x8002c0070040c0d110385101c50802d500820f0700c210f00b5485203403080c10301c410040000c1c803e1089008104107080010001e80c10540208210b1001e113501000351107000b1664a0020420801481220090320655505481c424080b0300f011440c1486551600b0b0b10340c08906216016040021500c4e04541d420000406c00c0000e61040d02058540756494554416104080500d0880a41444001150707258108000605030341e140048542e406084e2280b017101d040006240b41c02070002d14110352001c2c900c000304002520191403081182e100311410001d601c112416900c1c000e1032a0902180c3c000c1e00402ca00c00030703400203040c40c00721500e0300c94504030403031840d90300b40002c1a0724110305550304401440b03608040010680e0050300c81c681040803860141c00140c4c5a02ca00c003500c40495a10720110f1080340c840d03021a805011618401c0c400c0300c0c0b81e40b6080c4001d134007500058540030129070002c10301e403402080c068101c0d230080d5500310759a400d01038078840c0c010030043d030103052105003510360016840c1403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 632671456 1250 632670206 632670209
    0x903050604081201060503010b0418140a050a1a2b0c030b1614180a1a0306090f040c060e012001050a1a0a06030b0402071403031e01030b010902180604 66
    0x9003202919a81c40c00c156690070708040c0c0089040c05024030040c41160001000d0b1000c42e0bc01d9681c10709401c0140054800400b000703410007030b07402c03172110401030f180034281c0055000e42040740f010054803c1c2804a031840017a050b500d1580f111003842803e000202800541c20141a142e1400c54124020382d6103500c0e9600c660b004440c240c00c0350701001843d440e034103140010b016241c200820740c0c210030040b5154601c01d003648480010b5444048181c0c0c2d4542400302401760101501000000441109080c0240c004494452150a8034000035101c40071804100380181c0d407007240f01042c14185042a100c0140d4031000c41c1c100984014180204441d505500d14401e008400006050030880d04440580d03541401240c01031030200b81d00d0190707072540d0702c0c00c2c4202d440e9440c002803a5016100017802a101d480405861440803042e180b100c0721011000718010b25881c00c1010042491100c503048400003480058105c03010000108445205600203101c9504003c2d0400341c02481c9200055240d0048d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 632672706 1250 632671456 632671463
    0x20c011409070b0304080304032007120203060a06080c010c063902071a0a050d0509010b0111010603081206030f070303020319050405130c020f06150a12031e0903050604 74
    0x203909215001c41c0510003400600b1441c2d1590345145003d8031030b01c11074480031b00002c04125030982000d95100342c4c0c00b0140300710582c41d8195020301d907a4940e0000d00003180c403400e9109006202c0132401c543c00f10b1040400312100701014100c0d05001400640e00c01d5a624401d0f189252929107000e035869000340d0000b40b824607801c0036445064000c001510841d4040901800c0d9800b446050142007268182d220800040a80d000e54888210301d045070980214186884801d0500081c0f110410064000e02521203003a43d81c035214030f605c64480d600ba20440c0c0710103052442c041100f02d0450000c4510a98000d1024045825021144158514140d05a442075005030400716200982400300c140720b0540c4c1d0752a160007410282450b0005c0c6042081150000f0120307034a422645a0038000d000d098410091003068451600e0b107203544d0100d1041c4034410300e10a4401100101d4403066000c1c00c90760b45501036984a035102040c80d100000340802d604000309100b0906400000074034104072061042d8030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 632673956 1250 632672706 632672741
    0x60e160f0909181109040b0a1d030c0d0e0102150a0f0227010f0e0a0b070615060306080106061412100f0b0702030f070303020a0f0614150f06030622020c01 68
    0x303c6081c526842d000b0740004a100e654400203000200d91440502500319403607038400102e84000c2c0390030200301c8881c405004c90340c1c0800301d08281449000300e40e01000402a8461003846900e50004988881c2821403400d000c2d2000701c0410030070a03095010800c08a00d1200041c80c240d21541c00c2d82c0000002d56074100f8410314840e80100390350340040780058240050411245940c541d000041081c40603004284a440000c902d503014003000e60010000304141da00544200c41d243d40008002d0510b030b02865066600786400054418412540060392004601e821420001c80c100110051040a4090b0050310920540410b8404406070340000800036807200603030754044c0d0301c10b045c10000c007070400748842c1e048602c04201090300030801c61a21503000c40c100090740c0d500d2402c10002c0c031015907900940e00d4450100024024460545404c02200310b90700704001c80000108803041c40200c400540009010015540180c038008001c1145181e4039005410907000024490171524005004041001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 632675206 1250 632673956 632674001
    0x71a0703140606160204110a0c030f090e19140a061d09030a050c160f03060f1a130f0f1b02031207121d060a060e160f0909 54
    0x581511415400104030300c2070704694509180011042d000f4101c0a40030b031102001341000315502d40d0b11616085081e01102e40e121742e114130000341181b135107000c2140420340c0c540d81a003c0500030b458650844a0400480c256a03032411458610024002580e440a40d00c80501840140303420448920034410150001030440c80c006600319254804002c0c11340e88000c3d50140074031807030088100c84180916051551307459900c18807192800800c2401d80d1880080c0c5600842c101165010180c01c50740110000c0c048248800b205800321000760341d210b0300c0a8003150380344800d42010280b480d0785080081c4005010103040c841c8000703551540c9000301138640c1d40e0050030a000c80e040c8000c43c4c100b0a52000b0760901100c0780071141150300c054085402e020b5075500300e80100e01c0f180c1003802d51010740d0b43c58078428909800c6455468070b054680b9001c140c10040c0c00704511a400d014640310310790f0450032032224805074900b6503600440001040400c100064041100281801044050856500d0300d01c0c044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 632676456 1250 632675206 632675221
    0x31303020d050f1222031a061207060c03030c02030a2a05070f0312050c060a020d02040b07030c030201061a04181104030302070608010e150405090f0d02030d0506180c0d02071a 77
    0x5440705100c41045c200c1941c0510100c1d0711051084500d1035084803a000a840760390010300c1c810421245100e5074442d001000c0390a81e0f00640074980c03540b01c5d4405200f80310070a0001e0340c0304d02941414600003101900710000c4629a50400c1c1f0840c000086d0f980c60030301d0961501070911209800958440c1ca4000d070400400248810760624081c103072600c0350604803c11410340d240c60010700956100c94022480702c88031540c5e0b138120383c010002c80d4900d5607a20030303510b009045118a01020340155180c0200026400604036403050081d02200d00c051416081c800c016078810315020541c00a642e0325400c04e520784c01c03090010b1001d103010b0380051004030b24180e030003005442c050300720740303440c08500341400b0042801d00310b11900310f402114045500e0f521403c80903e440c6a0461104a074071911a64040403038001c4004c0150803210b0005016a986030b03028070107100c04000b80c00c448040a00c000600b402491000f90038248440d040c054074200140d01c0e03c07044001c110410001c2c4443c24014030580 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 632677706 1250 632676456 632676487
    0x31306320606070c120312021210050f0a05060d090b04030507050106060f200f0706031e0506030a03050a0212040e01060f030504150903090e01090506010908031303020d050f12 77
    0x3101080b24000d02d0302c03145554031040ca1000344a640140101c0c181610100b50203900d100c8503000c4100070441d12803170000300c8070402200aa030522503d8111240101e040d08040d80140d804140190a802103540307408240500c89c0d206400d9020032030b03074640900c00040d00d910980c2c0d00413030080c0d980d10744070001030820303e0071030340130350301080521800c0050884800d8010317644078421084d0346001e00d004407080414505002c06120f030304099000f4500c01003110354066104090f6524450f15805855446d94a854100c402c16128594558404208071001912035401028900000c0c419101d0705200d000011285400c15002085c015885e000140402c5500c1081030909207050b25080c40039091503144d401500c41e1001000f80565102c002000038076000301e50303000007052030005a00c0190381d2518064001d010594038140040c0c503c0380c1c001000c07070000040d183c100300075141545078107195608105038044080c90894a9008484410b0b0743c05000384513080e2495840c2158541d103103081110b2254 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 632678956 1250 632677706 632677711
    0xc0305010b0910062003071a09070608010812031008060a0f230f072706021204030c050d031205090d0f0f050d0c02011e0b1306080303130632 62
    0x1203c1c0072500e0200f001c1903000801440800c1d0302891141032415a40b200303425807280c90b901400440000440b4042c080f02c00e407050388513224100c1551542900c54400700c4064000703100780c03805640901c031210001824500215001401c4980c0010982e0340c1e150600c1c1480001c9031a101c440341e485003203894250860149050400300c01c9996116107100710401041c2c8280a0702054082c0c0240c00081c00040c05050415600e2004030011106041c0003c821003024aa0b0f004542c0140070303030f414031304011003000301356010b40394403080945840c0c1c1040d085c016590005803041d07041090740416484011020701c55503000d1848400580240303405018050906030002201a041104810449103181d9003d4192096001105404206104440f004a02402c502400700c40e4215100149a5000101d0f80c40aa4401001c0d101180401c65002c450411140c4a01c40d80e00660000c200040302210603204a8401d40d12904000901001c40c0f0545c4004940c800115002d10010f602918946213810ba14281e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 632680206 1250 632678956 632678971
    0xa0807080c09010e0f0403030f0213030c03141204060e220213050105033d320607060221010b0703030612020f15040312090618031713030c0305010b09 66
    0x7013800d1a11003400ca4000080019041503500d1400700c9c0c519000d03404550084050004442c00d084c0c884c20b240c0c02c0f203c618070048608000075000c413120004081040050141400052401c081c5458015900c161030074a00c1d80e80000b000380e40e0840b0040000c2010401b440c0305d100180c940c840000c240a1501c80354002c17505011013402080400500c2141030b0914030120600c1546001240c100640c034440c40d2190040c402c08280c1000c1003800e501c5084860a0104110301c800b0010a854102d468017800daa010783c100904000c0c10012412540041040b02c0c030110007000d01c1c807c000c40c80b49070450300b0b81082116220000301d100a15515000d850045d10f40401c04880702111303540003a10014028004074001d828907070014043d00d4803001514000c0d82c004154021041040340d000f031507100317070340034000204040701011060401d51140c1340040d01d5220050401c0000041c0004150b50003051185840002844010000a198500540081d031145002203407005900d010020030036002056007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 632681456 1250 632680206 632680229
    0x10020d063201030e01060305030406030e060f250e030a030e0310020310090c050409050c04030b09060601120b0604050a0e0109050c18010f0c08131404110906090a0807080c0901 77
    0xd0509a03141910400ca2001c2420005042246250b0a5000d01440d80c4007518901020900203100342e0150890032501860f041950582d07590344250340306550b01a42c0c201801001001c1942d0784050119401c01d1003441e50411030103050a01000070300e0402d421408500003104d903d405040c81c00e040009010411001c1025401d42c07601e60462000201140b240082c00c40e146e000f84000f1501810840d40909400d08091105240020790003209a105100c01c41d600c00341e190016102c500d02054160107410140d44819485c40041c0da0000075100b86000144c0c4180100400903165641000b04401044c4035480c040c0d41798908a08013007150001010314002c6841005480c030b2000d02c07407160715a00607007400c002d160700d050b9100444195980d507000401c1c1e5000080c1c1e5109000c07040c4254021a042d65030184103002d03c4005000c150303144540c280d641c145040c49881e096203490800390140820180c409011541d481140615011041d8085003550304418107500d1642005d01c9258090407032580175 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 632682706 1250 632681456 632681519
    0x10501060e12031e3106141e0405100309050c0105030c0d051f030515010b07050d050705190b0925032d1212060303050d020a030609020316120606021e10020d06 70
    0x104c100744500441711003144008c944050403480e4040589000e000d01400701c0003560301c3d145000e0000c2100c600f081c0c07858881c4009408541d840703141102d10540201d07510078200b882c242610001782601410115000c02d80c00c100741c490611004501000f0750142004000a487d401100b15601d8010303002030070b00d42d00030000400410400a41900c3c8190180f800070341d59203183c1070590805504001e09006402c091050300107005900159078058140b0b0b9013074a04410701613000c1161034007006500543c000300c0110130004242c801c10010540d810301c0540d0000c007542e004806080d0206500115500110b1980050b5250b6001511801e0490440400c10016041d03490141050141000a550a40e0000380111500d4440d420143c0204496032040d03403281072984065401c1038018228000040800e10b02c101a9096409908201c51158001d440c281d16048180070602d00303020360206003807103101e000701c144290382c1c4000c0c00c800403154400a030090a04a540c200d80d4110880d068801e5800e121 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 632683956 1250 632682706 632682737
    0xd02071e020607020603100f06050a0f0e1e03030f220e010605030a051f0f1401050310090902030307050706020a0b070c12050c0c040e010501060e12031e3106 69
    0x464424a404070389150b160b81d86c1514221929206400c1408c1c01003004c4400610590010042c01d400030103921200440240c00300d04842c19508590b00030b6002005480710b035151141ca500c400c102d140f016041d00d24007445000b01c1e006990041d00071440005400320002d14402c0b0880f0303a81d001c1c0682c21048080c1c0d5160010050003400050078030515265244c000c1007000d2402c40c0360350400c1198805014060365105089880e00381284a030611700955801b01c102c0c550f12400c00c4034804c507000d19200c2d0b522030900c907114004104102c41260944410011a40441d0042007a00c000b85a154000c0c1020315042c45c00c2d0380301040203480706003031001c803000000000341804503021414065150080d108c4101d28046403a0410340c0100b00d8000f13103440403810301d8580c19088a4140c0c1c8041d00d401e41c00d60744e503d0902200420403d46611260410300c640d5010920041700c030f0101c001107400041c00c10ba01d08800c01500d01040300010150710700610545000e81105054000501990412040c3c170300f600744 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 632685206 1250 632683956 632683969
    0x3060f0901080a0605150d0b0a05010f03081c02041a030406060501050307020c01081009150911090603011e0315020703030f0b18041b0e1816091a060d02071e02 70
    0x200130b00b0207480300c00203403180c01070782e046902260004182d00160191414007901c0035105540407154181008004101040e80002400490703600400300c52400707025107000340700350a00750f5050204a8003004000b40c8110703041030400d60845d40402c000d540e070925141040484015510030b50502c0000d20421103969004204048040d2081c2084100d0340d444001c02400404583c001c240064580a980318444600901c501d050701d529010401c40004804ae00ca5640d000341c0103c50f900400400041c0001c0d401455a016240d0f00d004611221036180ea81e148040341d090101c1031900c0b03501042d40c8060584c503000d1400744103a400000c0001c40902c0340850600c0301110783e87c610814441c804107040040e0300f0781c9104110b0144510401d81501c1c1c00001c1004142a034a2410303420055103200c4401b000410390740280c0d0946100c8110b0700349404034a0005d0300c04228610304030510b02d00d100607207858107402081d030340301c4400340141c0d00d950a14181d501000314508803300110714107240c100503116030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 632686456 1250 632685206 632685223
    0x60406061409031c0c03230304030528050c010f060b0f2802060f0705040e1612061509080303040506010e0c1b03041503020a08011809020303070803060f090108 70
    0x1181610b9035510407034003191a16152034209054507100c60031111220343c1c40b24648840a100f03946500d2840d1410030f1180b003030050010300341e1800000304003150002c0d01840080120030124441000741560581d510700c400b048106069012500004070400700110a1180411031005000108101e60a00001840381d0284204080d01160b000840d035081100f81c00c0804000741d17081e401d02c482c003208100000d4030751000b0f44000e8402d016140c08550844d0098040c0c8068031101055580940e88000c9002d162420300a00b5806014500381107502d1280c0d6405140e0141c81c56a10f41107568442100041220100340c1c009510342e00140140000a20086107136811216920a503196540b83c48489800a100d50843c4112504a05a4403001c230b040c04400781089900240003c1c0c044694080c1c01c0c0c00341d04c0703259540c20008000000601540000944601c0036040c4103c001610961903804030346168801c0e0020b9511600100801015140c1001d040c0031342d842c2900d1106040d40b61010480d41c1e4000b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 632687706 1250 632686456 632686487
    0x40c090302010e06130b120106140712050c0f070f06020a020f130e15010302032418031309020418060b0301030b0c0909040b06030607020607090e2203020f010506040606 74
    0x200c0001103c0f60351402d098640128180702c020300e100340e942640c000d09a2000039000526000b40c40001038181c01200b4135410118070700559490000c2c4c070350701c820740004607284260a05c4018480c040c20004208014000c61410f1390051888a041003055141805258440811075000c091494010703180d01c440d00782c00b024180c403003901d07040d1008141005009614980366040c8510008001c4860b404007280381284d000760155600da2920309240e01d0040202107007002943c4c1c00c81d0203d0b01e80381482a113015040650800d070b03400d02e9601501008080440c0d40b1540300c554001c0380a1005051910443c1a00e07403900d4000c00560b071504c04440380c503000c1480058101680d00d0001407442103c401100c140c4200144004594906460140d00900091b640780c0d000c1d00c20354000a854500004440f80181410b07202c88600620301605c2c0300a20708000c08a4200c1e560a188054801812008103410b4031320a401070100110344510041c02c5402c02000c0034800c5050030020400d040e0407054282103040d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 632688956 1250 632687706 632687717
    0x507080f0d18080d0801060305060409080306091b04080a0219030c051903080f0403060b0f06090d0609020d08090111010212010306022104110f040e06070305060a0f030302100b040c09030201 83
    0x48680c0207001882d5540e00c14409402822600a02c4076405a44a416100a81c13410482a121036003440100c0c0c014041c0204120b10400100b1041e01d800740d0321a500c54031310300301070358040407034140b40701d06030090b511148032680980058421442c22003d61900618500031000b601480e5896030820a160751040c28002d0087d03400782d01803850b010720000c0203550020009940c40b1a0700f0f501d074009500520040d201d16190649150325403910221013222194010105824400840300b008441d141001003281c6080e9109845401622601a1505502d000c2e00840c0d03215410700d0005001c504501e014440264410003024400c94500c080150560f5089900141c0790122181500b1945000b4004075038088004810481007103100c03403140f00d06e40020384a8482416001050000b81e03607419410f044950800400030b64168401c0e80501d0b0310600c0141004403840e520117071400034000940007600140c21508011402e0522030140d1320f00b01d50180d5040040c00c0700000f004108d0881c50100078100003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 632690206 1250 632688956 632688977
    0x30c03070b04021c05031c0b010906181701061d011505030402010c1b090b01050a1b0c120303020d051503060601120b041109040c0c171c05040303090507080f0d 70
    0x4850109541d11481144000d425900785420815525081040c7d9800405043e501e030340102441806602078680044c6c598041d11418900103a483c42403480c2c01c1091640f40390700c0000c409542141c00c00d0b05c000703c0000040c0c07045c108a100d8001104003490640d6001e0390000410001d503040303494981340701580c5099916a12603100485150f041041c001d05014602c02d5200009440d00c54890100c0700454030400c00d80c1070840041d1075902807082104041504038038501050400d15081500407846002225071003900d502c0755021650300c40e00240c000980c003092000100c55144240e9820603103841d9107540a8140c1301c0020340d1200d0081c500d904110903a0385c1160800200e400050710550010401d0103808211351036011641c00400c0100e1045040c80ba40342042c90056490b1310000e03802c00700700b04a1b00305040111301d241e07201c0c036202925088968030303240b520401e6105050041f40310355000700300764006061540c0b401c501d6400c5520541c10481c001c641414000440005c160420304014846d80b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 632691456 1250 632690206 632690209
    0x50903100c050f042303010e280503030c12060d020f1905100f020114070801120302100501030b040b241c0f120212070c090e0c0a0e09010b03030c03070b0402 69
    0x5008100741e10700407400110700172036010300d90300b101512200e26100c129003201100d4101030a072400e0704646041500b00c031120860700029082c55041c0c10308120705140c80b0312426980d0f2442c0d07034000c0323600e4400d1500c080f5095a00b0540194071580000b0203c03501030700240c0360380002d00404032018800344102034038005100e0300105041000d0003020001c0002c40070b8404a580a0840c09154400c7c0d0010b5103440c1c079002f410381c80700e0b081500501c207e6540c45a0303a800d20b048800080c286c00c03c01e40a41c401d948000080c5c0e07040c0c1c081e0034061842000008503d0501e46000306240328050055401031f24011a81d200044c1c1e0138605400746003046070b540082103010444070224038540c0001400a15080310300009000c6101c07601d08021070150708451644951140540260203441001404000e10f10350402c500d44142d00910315050188090382d40500c1c0701c0001440d1b0b03c096900c8600030086400030000024400c0c810744000020030343c051071401141c50032240c1c036407003200c6005164117100130204055 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 632692706 1250 632691456 632691467
    0x2030405100e130b1201230403020a060204080304030c05030c0f04020d23100e010f05010f0302041509061e080103060518061906060c02030a12030209030111040302090601050903100c 80
    0x119000f424600b400d401014142c0007510400c004180603101d02074032001a03050511031000d650b880f00c50b0290204100b03007142517084901a0080e01144104007601d4080741d00c2d8030080004150350001543d580e40b0314036119800c0d0460f6807000f0302c40d40000d0204125a1241d05101a5000c021a00169149085800b07072004060007552a501c8501d007000f1100c1c0820348210107800740d401d543c201942903607161030f400b028070001d01807544030071042003080003554003072040354510901500380503003450344520700000b109100d5200080000c481d00c00400429420074100c15820b00e5420703070300780400d0000d10090403031201880001c0007180d80d00001001c03851115440340796a01c0000a0b25070a040500068810729860a0301601007842c2c0000003405134025180c059589034090090302061407039444090a207551003108006041d000c01c80e602440e50207200c0c000942d0300e200000c1361942c0c194018080c91101c0101094180641004111240c0e540040c0305859070708c0858004c9942400b0070000c40d013 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 632693956 1250 632692706 632692727
    0x80a0b011b03020102071e0f171e0702040c0f1d04020d02040303081005010806090403030504170a051201050411071b0302150301050111010c09050d14150f0106050a0203040510 77
    0x2900d41d4500c1003841050b6041d001040500c0c054400c0400c036600c400d11090781013220724002003141800704100e200046141a00d00250041c202e0903a0038202e060b848510704a4948403020208500058240d04502d0144190700c0a0000b51402c445c981c40391290240000c1c40000900c1c0d5040c0d802c1c41e00c660341c2d0380c46070101c450040502c14190340340c0e581c0f450080c000c0340041e0f50308160b00084030000b00701540710302c800a1244000a106150030389507900c1c190000c210240c01940c0000e111640054010801d00043c54a521941c3d0f440340d507844010316101d45000c06802071031050b818210581590001101075481881d008080011020010303150301c50a1616940300940042d45000c1907060b0420030009941294001c3e22640469a100500e09080b41c2e440c80c0c00102103070341110148101d0400c504258121403080c0710020b65801d8043d8a54942010f0b4074902210103120310401c032119941c400304a00514540c2230003330070100d2100c006502d9000d1405440d000390220102403801c01e00c690040349 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 632695206 1250 632693956 632693987
    0x8090c0a060c080403060624020c060d09050c1018170307240510030b0106180b0a0201020417010506012601060e060d09050a050106140901030b07021204080a021906080a0b01 76
    0x1f08103642c4080000b80b02410506440c020b4050560781c0384010700226050401c040001d00c40da1906045440c128001d08186c00300340e400b84950182c0c0d0480c0c0d296100c0401441c0c901e900c4d8008030f81e00c01000180200d600e500030080f0003005a20040c00124000706490603190f1103000c1c14120404040c507160450303405041074410f18101001c1c0854002001c0c0e204003544c0c050900c2400c0c1d60b072511401c0e02c054034450445480b401b85107004000d03030f41405021305a1000700d480090f01c2d06d56034107502c81000c2803407200c000c0280d54903030502240c2c1d030b040100031420481800030000501c1d0354180f040002401489040203020000e140840c2d03980e52001104c0020782030701c0341048541c4042c1492550b5942c0d007401210380d98078008002c140d1035026034a201921100070301d821420381c04c3d99105001a0006415030003035101c0c030341c0020a0500311f6000340c0b01811400000313014005d52401000314030741c0c1d0b84040c40d406824a0034103024503541700c85103a0340115010404510074943d01c0c0100d81e03a000302e50915 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 632696456 1250 632695206 632695211
    0x3070b0307020d0e130f0615200d050d0203090a081207120b0d0303020705150112060605010c150b1201050106021506060a0207060c060b06070f0308090c0a060c08040306 74
    0x1062951500000d5400740000d81d0840b1001c800240e019144040001c0d003290f4821011801c000280b181608404c01c0740343c0c0903001090720366482403841741d2944805030241c00301d0041c1104a0b41400f843c8580e80d941c940320340085c01c03201171094020304180b08070900c2d0140160000000740c040c09003040030b01c10980d4003900e9203940f02c0a41c800c2c0c4103420020303260300000400501c9440000c4680e40100b03c031408000741041c0307815105640c15002580000f104031460b001c0d12020326034800d2541a00b5000f042d01107011400c4041600d4118101e074055005681030000504801002c40d2102c0c031840c05003801c50b00d00080c204500000121b0344210003401807883c1d0300f0f21001003a52035000c965603d0990720310f0a41c44494503404200411402115420401a4090082005140e1254511000a9004250007d040c030468404111309a00c42e41c0141c500420b048000340c01c25a010140d00c1e4403c4005001d0440c2c1c48030100010100886441390500704000320400d281400f000d6400c50b402140e000c13108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 632697706 1250 632696456 632696459
    0x10311090a021e09130e100c09081204051203040e011202030c0405040c080712052806091b050d0209040201050c01021c091e03020c0108070c0204020d0b120a1a0403020a020307 77
    0x1403e425610a5014901801c1d41d200803140c0c4150a0044241e4469018058030301d032812818100000c006011139030003006106500005e2550044c40000d041d1900700802d19902c0e81800d003401030544600c00c0407a441d40c001c210801006506201150640d01710f04001081e11a003400024680360042c50101d510500e44002d100820001c42c2c001e070125141d08040e2190565583c01c0c0e4503190785541c0300035016070444040180c819110040412040103042030194100066440314421107110080031640c03014401300c414aa2604000e00c08001d100c100c4140c60311404950108964080160000341440004141018144802c0d0155a010351040b62205800c1d00a4103181016180140c01602d080341c101d020f000701a51b031003480440654040c1c00030030090050400444038002d0080c02d40080040300d01e82200140d590303000502e00151040d0010074204400810003401121590344c6044540c0180030280004000d400d00f183d0308421112104002d5a0300c4c201030303041541909000f903060065200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 632698956 1250 632697706 632697757
    0x50d11030d0f060510030f0606050f16031103070f0501060b09010f0e040b18040b13050307030c03140703050c0f0f070306020f090402031003050c0a1d04020117090c0f09010311090a02 80
    0x1000d0040001f4000500010360b840d40700740c03198450790030b8181e504c102c100308101c50080c0d01c5500d0304d0200d1091170b0001240b40e58003042d5085400c0800103d5004021071658001e01c0024000c01d03000d858020001072034012004e0018000544204810051100180c091032080d034035980200c1402c50050550100307440c0c0e030890100700b440129800c41e0780b0910000402c8444480c09600e181c01a07014000350b1405d8460f44054600103080181201005207148080902403010750240151510a403035250b11003070500c100a003422403101860141e580034580040003000002046402ca82e00714a005954803503803408410540f24181403d41c0050000003400140c80418034041e0440b4099020b4860b64640c100401240c0300c114440d880380a5503c910400301c180707000302c03c1500644141864040d0024403c112404103e0031503524049401c40b000c600400e0410300c8604240c20b1003100c40c142158116034600464a2680406074081c040c0440043c2c200c83e282e03070441e605020b001c032041000340322046 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 632700206 1250 632698956 632698961
    0x70306170d020105130201080c0c0109050d17150105040b0f0d092904020906090a0209030604030e10052107020a0b0115120b0d031d040e060103050d11030d0f06051003 73
    0x3030384010f42c41c2000050b2680e1400c0c01080310f1660581d82e02c0f0b02c94a504101e07158076007003240d641ca00c9544c1c40c01c0d0f4000044042140b90780d994610b03110007148110500c062610707000010108043c2c41c4000345089260781c0e1040849003501c400101c034544945012240e507080e0300501c400000070a00e4540d201043c09a00f0304144606803030145414039900e002c00d0315403e0480c060f80c0007504140041f01061251038090000d50f40070751080740c01800e16035040c001071b14202041c2d4003075002c14820f078110449420308000c20101c140c09030501e545402c011004244280f5104a22060790b440444c0100c0c04042c0309209a080c6507810200d40704455031104070344025030610500e00c2c1c0c0419629a01e6007885421401a00d4803076000030500300c0e6500654800340d8040e04402880c40680c0f03011030850007507030b99502c54140c806008000412556045103002031030294078031449828462240d03048401d824002007142c14010504001280284503c200c1070082c010302d40140780d00c041e211a500c0b07032455040c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 632701456 1250 632700206 632700223
    0x2d0f03070c080c060720060f160c050312070609110919150e040f210e1c0b19060f0603090203070e06010c030e060c03041e14100807030617 61
    0xc2c0b00f5256406074440401100344185400100b0054142c003607400300b40380503030005188a40184c100c52920803101c00c98001a80f024000e61071616115160000340645840da100250009600600108003045a840140d000f203e40c0182000d80742c402c92410010001c644020f00c200103080301c811410200c500b2601c3c8080001c0a030003c62412111081c00805100403100721101c2c045901070585480c0c07101a004685605c00b507130714110107040c210780e048004440042b0100706a4600c800c2054140030481c1001b035410b14482001c0d009910040802c83c5c2940341c0350172072004c01d031441e800c11030144400c018214070342c084410001e000070f00050240e00341c0c110204c240d20840a4551094407061040d101803010f0350118005501100d1000002c3d00403641c4510f4182c0c000c05041c102001655441d24540c841d402c071b40b03101d1010305029400100f07582c002e0000783c442684c40c43ca0447c03450012501800d0305901c0f01c406c12000301d0125110320b0081c1e200300c01174182880f0512450a400c0f1119948540341e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 632702706 1250 632701456 632701469
    0xc140702210322050a03120e060a1205240918010c0309140d020318030a0f050703020a08010507080a0203070e19180b0a03020d0510022a2d0f03070c 65
    0x3280d00000807001820002c42130310b82c010030602e070240c2036440c4d2004000024400c4800d01c00101003601c030694904002c1d290200803551809a43e01c500c80304001a104064641104003003c1c83c42801c50f03624540072a2030090095485e4010390761134094804242e01e0384610040d855280a0162540325455007001131810b006110a0854440300001555100c031400c403060010b030000c0c00602c0000c0e0500c0b40450303204100900b01c0b003e4400d50f07100c414a4100d01c0d0b000302e40079841000f0400441c148030b84c031900100a4100200007a19188001a00c2800700502000b0b85689c004000780300c441c01075211000505014000301d045000320010310b41c00c03040c280945015558100c84401145040b40501a90101e020340b1070300700c16180d58280081c00c100f40e14110384c00d000700001ea50b0104400c1c40502090301c00c1c201d808030309588030310454400c080d24000300e0030aa0072040904030310341114420340440c0a01c4c0001418203003503c41c44c3c46d00300034081e184594103020006907041406803043c21481543d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 632703956 1250 632702706 632702737
    0x41116050102091e010206010501180302190e1806220807230304030203070e0717070225080607120209030d050c0c040603050a080307050f28030c1407022103 69
    0x400c4c80b6010110002520a580140e00500051106510440310402011200c44400c0101510707540007804018140300801da580c445c3d003800b003021040b0481004d8003ca4814003408007030b0800380301e803916440300a0000c0300200c41d58a107045010a48045050502e400c90079880d1620454500750f0b094078140c01e030700819001c2268011925140100c00c44003203d07030003001080f103140382140e22202007038018061400e11000c070041c0d12001d031084610700d216008950161400c882d00c0d045408603558002e002c02200542d2107020302000304001081358124a1500349500303420006407010020348180c840303598060164002490708250010302401220705940c0548161039201000d000448044d0720000d170241d448814440c0c00b040b410360045411500d81e00d00f007840e0030244e10011080e68400e84942c10041800e4945060a000407000c18092907440c1c0707802c0c060245500c000421b0b00d00002010b54403194005441e500f107559404131725001103440b421103031000c20b01d00701e0b55889402c9881300e02801003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 632705206 1250 632703956 632703979
    0x9150711090f061c05120a0f1209080315190803120606070302250503150610090e0114030a0f080927180a1a070e0409020a0504111605010209 62
    0x60350355058034400e10010340801d000102600c00d41c02c2c500f0880d0030030303500e9001d2050303500586e040c000000e0000040c1030700c411f0000462000700901e4040d030401810300c0705103064110f100058011080b01e8000c0740d91280c843d401811500003443c000700c100750540d40741e650030304000350000010001d0314480e060f000078032580f55140c01c00d0003c148a10400180180c00c07d140b0616261000900c504d0b00b44480d1215541158984010034903001000c20b81a0b005054a0100109464108041c0325481322615043d404d080c138241120511171410b0041440340c0c0700806030205d00d51010001151000d030841d90384402c4002e141808101988a05d1419004174140c440c0000000c41c40c911904a82103041d200c542e04e036480540c01c840e9002c1924401840740280150710303000c49d07841040c2e401c1203091040100140d08010202034001525000090300690501a004016a640d03003c010110350042c2c0d8040780203030000c0c0038504e441c89460040c1c2c024010540030641482815805828400d100765550000d09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 632706456 1250 632705206 632705221
    0x312010f090b03010612080a090b0a02030d1109010806010f021002160c080f03071e050a03020f071a030406020a02070e01032105030613090302120a0e0a0b0901090603020915071109 79
    0xc0e0175500900c41c010040303d40d038000007045c80c0020040700340546400400d0a48030103c0100640c80035480d880140c2c4041210b01800341c492080703240c81138a0104691602c0744079030021f02418001814581808044d0b0a644074042c0244028081c10041c0354046641d041d110320008403080201d9400c0d10910180301001c03903003031400219030b01d10b512510010341c10203c0c26510642100c913000010503000c2c840841c0d080c0013680c00c010030003480d4445e801404200302c54815045c0f600039198005070102900072060241450010222a0440e4219001507a503440592003130b49010300135800560350b691408000030610032010741043e01c01481c2801400414000c078000c40d028081580e0540c0d11450501c8104444100c550044421034403038019034800800d18000000581c004100c9a4003092880c40038036041c0c81d091403c80050441e4400141c01d004070000003e004055a0250030203159000401030700784d66035001350901060703070f006201390340308844d14110031038160300d040d01b42c001c580394404a00c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 632707706 1250 632706456 632706461
    0x1d0c040501180f0b0d03020a170a0c02061303051203190516110114011d010806010e04080313021f030c0305221b1202090a020a0f030b01020312010f090b0301 69
    0x4070344107820745450079042441c1d00c0d00101003d0812840582d41c805280026031118400d8019040c065005058003950318140001b00c0c0070f403000c188440e56020003491100700d070000b82041a86806031050b946480d480900d20b982c200c46504084c11911482182007a8885201c3c02580f050600020440401a00c80421801d41d10107503181020003114040541c442c0b446440c0d02c0030310700c135010004a005680181c0340c102d090030a030800d03000c8604440b511041080340c01c40c030500411210004240741d61409096081c0d590000c2e000400c09400000030030901c5010302c02a03080150020104c80451040001650a007110b0842d41c0010078107010049000501910030706118050b4103020f0702d0010040300c2206540e4002e44000c03501c3c040d10800c0c031004902000306500207007001c102d07503121000c614010451140c10040c5601282ca0040101680d4550b000300b80b0a003054150901140c0d540d2540b006138158059500040b81d10b0320100000140443c1000209044a061503010401064500140750a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 632708956 1250 632707706 632707709
    0xf27150e0d0c1e05031b03150906010906050105091003111b030306131401030206030c040803040323030f09040513020904030e10090e01030b101a03010f05330c011d0c040501 76
    0xd240d001082c9120035210311b080c41c020215030040a44411040c3d4425071400e406050341c5c01000741e0b1100c0e0040c01100c0b9a803203083c01604003401c26070300f002c081c40000344a50046000701c00c1059191648541403164100c02e8a5070488031034500c20100c0030542c50356070f032900102d070030070720a82c110b03110f200340c0105a101d00042003d8112015269030300b0340d0203209e010b90000d404000b075100e007000009031070201031010740003540c49443c0380035100d80e055801140c010b5511031084029001000782480c0491000700321030034030400b0781b4003095995a489511852003180403019400c00321400c1040105680a4156611040c0455150303071404248401160201028010f41c0c0700005040018804550441e2a00fa400140c0710a4000817a403500e041c170301d8000d080e68654a09a001100502ca03407040c05400c8005040c098480d0100c006040f59400c5603c0703400400400364081600d8508007403d0303000e080320302c1034503844024030002c3c80d02c410b012110304000400c807406000d060030510b403070314041c010f0343d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 632710206 1250 632708956 632708959
    0x8150f01120b0615130b21010503100b0307180e1b010e30061b1e030702010f0e032a1c0e09070f27150e0d0c1e05 50
    0x80c0d06039120018000c41401a00045108250a00030000d80900d540141d60181c00007a41c807c0d12003a0150340100c440702c55100104039200700e0070040c4555140001c40c950300005104010545800b07001c0841d00703148140d00120121030103845070f00711840007078110300ca883d0300e030808503400443c401100d9001031648440050002c0d8804a104070503140c49140308009041c1c00780e107074140300d0150b50705150340450360350040007581110003000005603150a428004c074400c1401c0a140c007000d44030074040c10720702900c40c504a560120202e0a254400d50203400c21004141003080780c000707031381d19081d9650003281900c2c29a411601c2d210440c001840e1002c03105501800080c80c0c1c00c0b21643e1180e600140d400310707801c20401a84622883c40e50780c40c032602d004aa07941c8402d040c110f00303020000d202c5d03000740202807200e201481c2008800c0d502c4414040c00c603074513204800c08642d120901200e4005139203251b81d50041c00e1590f083c0c14400310f41c0710714044903000040803840324107052043c9030295442c07217080d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 632711456 1250 632710206 632710223
    0x30402131a012303090609060f060a09090501020903011a030c011403060d1e03030c091508010303050901030e0106030803150111030904020f210118061406070c08150f0112 75
    0x410380d55001d0200b041621030001c2e40b03d80c500d00055010307081900125100030b2583c2c004070038007410180078009290810031140c1180138514142e40070031250b917014071030340008554881141007800400c0d4150f07420240010001d00940d0404296100d04440d43c000c0c95101c1c2c05141040d002644c050041c104040e150115647c0c21562044100820451101c409039852115440020000750803410005410303071103a10300142c1120340f584020460fa4071904011204446000242d908540140c8240d04403079042c81c0c0995200004001200548900303128035080e0360800d000442001610b201440c803c0d015100d483e000c9612420045910714402c01800ca100e4104001c2440181850303001801e001600000c51880d2a044591504800d1040840c21000d0f0541c00010700250034100081d550b02c4120450900080e824800050110916014060300c1003070005020020070490700c01c014000e11000066410320344000d50901045013003150f0440030b20310060004100d41d80030180e458081600300031072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 632712706 1250 632711456 632711501
    0xe060f0106030e2803030902090f01031703060d060c030e07030f06050c0403031e020a02210124140d05030c0303100f0e0f04020d06060f05040b18130819030203040213 73
    0x45132241d07601160030740c101603c41c0340703920150b10b8260755a030040c8008205072400d5031643c1400d5504020000e0400c8007c1e00400072b20015603150fa00c01050a600302c88001442c2c0890715060b0010300042c0712640f401e000e101d0380003051203d500044c0354114024007050007640c3e680d032821071051240d4000140411121103101da54008050030751501d00c9803600440314141110b80009007483c0e4060103003000c0307036601d010b4035003034004c21301802d110001c1d40020030441a4001c8000c0c2882d202a000f003924400c0741c0071042003255141880c204080d07800c142580d80e02c98901c41500c3d126030080b58582030740407a43d4400282c00c8407141c011012204400c0341841c15413114440d013847c40801038070a0341e1100c04142c0180100300c5c203104890042025a0750342c0034007887d000601c0240c135004084035214544d8020314014110445100303540c4194911903c1c296402c031845c040b11140102480c41072428002d1042c140001e825900443c0580d0084404006861586d400039054503d00f910203d01708855045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 632713956 1250 632712706 632712763
    0x50a2c0c040e1008060c0a020c040b010e0609030709020f03270a060f0207140f0d08040f020d03020f030a0e0a090519020f160809040605090f0106120e060f0106030e 72
    0x242c80c2d400500c1c10070301c501e505a40303400b00d07803038a00b00b030b00d40c600d250900182d50b40b00150100111041e10314203403401d11a14542900203000d0f081e019946601455000910040c1c0c0e65003806800d0152101580c00c544504003001d074554070350021118000d15410a010000c2c00008213041030881c0c180040090604e00465078481c4090f0584c160340d08020303a002c1c407040d40054500c421100d061220200200052020400d03203a10b8070810107a900d00b400601d1003400f0114400b0b8000200e0381e501521171180e8203103541f904034909401365960341018040850203412841c1c0c40884000d125108660980c4040d03120104201102ca06440040a1148181d0f944280e41410380190440034808400c0340d05010041c081c170b420003041e140044905040000d4104440d240070700c070b0300001c3c0105480e04140741c40c3c0155604000541030090009000b50440661181049074002c1c00440d80080140d401a041c11241d600b0020000c4c02000046070401c02d400480900c005140300489102c200d680038510101d08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 632715206 1250 632713956 632713979
    0xe0303041e0c03150f05070e0d2d050307022106060910050d0c0f1502070b03060a050406060e0306071d0607020406170a05070608070c080310050a2c0c04 67
    0x41c200c0d003444000d240003010031645904031242c48202800450740b801e0865405007100c4000304500144181d0360f0414009446481d82049803c0e40301e1881607900c962540540c1045503c0c90b203074908001254415001c0110210180c03902c00c1c030a450385c160444048034640a208480c0d9180080381d4020f0700080c01d64581008103540201c0c000608080041d203400115120030107000c03041c0c80e442c0758810304028a40700c40605c0c0008181451182000d55140480291690064844d039400c6520110120380c0c60b50b03400180d10002c00d0014802c00042c2c0e030b600001351051300d0b440100c41c031a0040e080011a1a03000300b28070701124081e2446c0140c00c9907001d0070000150815541643c00507510b1401080b0200162901480910050300800b501136140c40c03c0391501c803244d040340301002118014008001d421040c410004e69020038241d4490b91000c0603000d605e4455481168040c081c40400a100441d072280409602c80e81003806181040020b040200c070b0400391105102c3e400100002c010142c90207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 632716456 1250 632715206 632715263
    0xe010f180c0908190302070b07030504060f030f06030f05010f05010b09100e0405011403160602060c09220c0e03010504080a0c02030f010e031b0613021905180603010e030304 76
    0x5003040302d42d050700c0c0c24945243c0403050784042108030b1025004401d140c1c04029001c0102440d6079064a01801690010164003841c0b00300c00512250f00d920340103440c040e42040c182c000e800c0400300002a60390800645800c01e442060b2055480c0412405c0748000e03a014882c180c0321500d11461505011400340111f1070b071400b983ea4100009600780c0c50031995903000d12402007101c7e0f0b2012035100d00c02420036040c94554451050703186c10700daa041080300d80205200d540170800c070010a845040044c0030a500b82c00d648040c0d005031400481806440103aa031120040150740c1d40c1c0c0f4240c2d039020000381800c070740d400e84002d0a0544244007443ca460b2003442402c0700c00e4405025184a1503465001c2d5003510a6030700004200c0c0c0021030412040f42070b0780f05107000101604001c01003420310400301d5480e43c0c0a21400b034011081c0882c0300d0741c0d521a400e0554000d10001c0c042ea01320b1b440041d400000c01a0607222607219500b8007030750078400032000054038041c80d08091000002c0d66215050310180040c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 632717706 1250 632716456 632716481
    0x150c0209071b050309010e010c1119080f0f010513020d020f0f061303060507091211010504080f060114030a020a1206391805090421090e010f18 63
    0xc0b0a4524551a0705005074040c0c03520a00c0115201c0d5000d9001400e6400c524002d2410003e4111480000c40e07035013021148590400d40780c0c06034145050300c101407103142c80d80000b11740340b01e840a2040c1c140c00000b0340005841080e00204515180c6800350700d080c074850080a541312034424070640252405446041e00c2510080042c18220190400700c2e54030341060100d14412101c80900704144145030050640c070400a150080419040110104140352088000340540701403042c00d0095174000c004032005402490200c407c8012600500c50740d5150034062004041000c601202d41401c0018900040d00e90003404410164100402c2001c0b161491109446a5403911145410181055042c0707003070309145102594280d220800a0040000202d0b0450402c03020740c1d4901d11000301c204084e02600d4084418041b40c0d22581823481c0050322503190680313134581454070b0b12456900070218900301c03403071076180f146c884c0ea98070f070341c1201441684503502002098202c250300030582507004090a4a0303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 632718956 1250 632717706 632717717
    0x70303140106050a11030d09030215060117071209140f070b0a02070b03091c2f0d05091215090714091b0705120309010e06060f010c0201210f06150c020907 68
    0x260300187d6056800c620001d50140e00500700c0f80c840c3d035a14507226940240c080c06c05806082120800002000c00101414104030750a03401218811182d0000041560070101c810700410301c2c10030040e200e9000544100351071080e4000042c4820600054a100701e080703402900c4042d00d000f40510003a0f00003010400c0c54040d03032203505407141c5c82007111020000d450f958103a40400d420109090740b2413941c403003201600640c00f81940110005001501c1568525045840f10740340c00102e0100d64126460a4850140e004035441c100042200b40344120000001c42d00c0003956865200c46410400700c040c0d41000902d40050700a90501c6409513401040c404064a003410584486007440f207c4810320407900400814049065000d00624400300200c00203480a0700702000015900103041550034148030358019804156030240070001c440e4000541200c4910002c4840171000340280001001100e183c05804540105100b40501c45109661140319000c845071f000c2100340b031783c000d100b0410131a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 632720206 1250 632718956 632718967
    0xb03030405010f170406021201060e1e012f0633220e0d0201060f0924062a0b2a040b120a090c120606030611070303140106050a1103 58
    0x903801d0400034405ca01801e00180c642030000140820307150180e010350704000c0700f0f1a1901c44ca40d00d0103042600000b440800240b1030b800500180e518a002d07407000d840c603480001b5000c02500f141000d42104085100c1a00d900d40c1c2d881c2c50740000f04203007040e400c0042c0440154044503541544049018040c01800703203601e04250752144003c0300c00c0480101c0202d41b52140001c000504000e484200c400500003440181c0c20306100401c1149a40300b00ba038115111404030f50081c008013844855001c455802e50201078940d0b0028018a40602d0b125103403407110468012420071321a1025102603101a844606440d0410309905980710000000e180b000d03540d0b461040c10641c3e00c0180010010350024944a100d021500c805425000704010806818841030300d0000da003c3c03010300282c441c5588008075021107810404010411350300010a01131a003115103524100c980082c140d040d02c03a42d014000070100c0b090a4010403001c4c420080843c40c18404c03000210b004602e9100d10080714802c890130300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 632721456 1250 632720206 632720237
    0x613060b18041811031e0c0d0807080304030906090504050601080106080702070906120201030609061202060a030b060d0f050a1b030b0f0310090302120a09030f0203011805011b030b03030405010f 85
    0x1020050f000ca454400280110790141000d0140120f21241d4400b030f80f075005030041c60307070b5103844580501510078444500039500308122a4152031180e80c008135103648a01d45841c001c0c184a40e83d01030340b0701250b41100c0000c0d840c0340c14000c140c4140d01c182d40f62a41a4604113054a401002030011400e6006000011481d41414810b2000520b02129100e103403201030300024041701d4450b0401324655040800074841c1c400070708401441141d040d10200d5554901400860040001600302c55004500191030005404d140d00546400b0071315000c00c0001c0d8603001c90000c121100c4d01003400c0390718003019402d154140264406410345401602e560034548241e400242000809103010361881c1d40c0e4000f00c0c050590402500d044085041d03182d07807400520800c00f0f819249180300c010040381120135090215202134102d8010001031500c100c3c0100b049150007806004411030342d905d6101503070070b01e01d19a03200380a403414046c400740c00b07103280500f0030004444802c1c6505820040c03002c0d5203140003c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 632722706 1250 632721456 632721491
    0x3200301090302100c02010e070b0c0f100501060e03010203100b0c011508030d1b121e0c0c12090608061e0303030c041a040501021e010e030403030203030613060b1804 73
    0x49202e0780c0607000b42000712484d80c007269404070411045a00d4152945000000011440151b640c4000d8242c1c172540c0000c40d451030550001c240c13485501450f1000200d170340303440e0861810b03541a40c0300c01c1003650586050500300d000459400b80c0c1c4d0903031244c2c03c01400780d003080204101490100003040d1886040b0204410b501c81d6800340e07204d9400014080164800d034480c0c41c0e030300202d85c2074550282e031141c0740042c0383c40030103144415021b0350345050020700d42c1c121405007001c0800c450709012054914001822003c00d01e0070560b50340b9030714130b10128814414034000007502c0c0300703803503400460b202c240030b000492303100c95000b0600d071950410303841030340d9801c0002d544200e4401032080d42e203504212104141c5200e031020405494010300040c440c40e03030049507040c130b1000c043d624041107043c000901805440c8000444009000c00180481895404001944030b141d040d00d840c1c850141310170b5840102c0b0468400e084100c6c00601070340c140001a00d030030030b00c4a20001c1001c40ca0042d0000c40140c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 632723956 1250 632722706 632722721
    0x6040518040c05040605090f06030304090908070b0a1503030311071b03120302030606030705070c0e0a140105031b0d030e0415031406090c04180c031209150903200301 73
    0x31415144000c000c20064880c4586014000a0350f09002961600d0302103505494090400b26010f42d10000148694a041042d64002c280c81030701484065403900340040c1591010790203548000800000030304039001d500a5510740d03041d8101450215103035450450013450100c4035104a010200000c0300400d0601d25601400110340006200711031441c5000f0065102c031400c50030500d4014010440540ea400c02529130026003402c04550751041c0d45004100c80440c1e030024031b007900d41c070000c1c404484a03590005040701c80000c0d0f015900d98031101015a16080c0c618802c90b0607040750103407003c80c14840c107182c86051007410b10042840c03034400044c094070b21210138004c840c01c1000c8108140059035030300b440b0b402c0c080b03406014641008140661a2600d120402d0301a52300e0b152900e010500da0f0a1518040d40c01410110540e0b407640b420514010b401c060260000b0240030010600c140340a550000c01d80d00c50315a904258510307a9003440d803080d80310051400e4074800407600700a4800b07004000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 632725206 1250 632723956 632723989
    0x21b0310050a06060f1418030a0b04111c0804030f1406090d0e0103090b16050702061902010c0f020a03030506040204090e010c091403064515070815060405 68
    0x350a504142c00100172103d2040444200a00e03050428803114445044400304c400c00d44c414003e6000801c040ba1a001f0280801403094000c48100028030045907104e40d00c84601325900190b000b5604900b00106103030440c054401102001b0400000d48031805070503182d44030b17843e00f000004000381e0303942c10400b040b034a0098681040c1180d04480780c0c40744581c10904801d00f810404241b1b00d4545401640b8000c00c81e41d1050140c9804813900c41c0540c05899500e0341c01092541c0c1c1d69039548140c48421028141103015600b82000340719050b004461941c400f004590082c84a010385072030840192a01410130368000e64204070200707603040e080c044c1c011010605000441d0100341410300424815003944000400a105942824243d40100340340d60051032030032952400005aa110100304010310440c01108a580c2011a42000b15080303003108480c4140c0c2903441d14982d031454146034000c11100000004c080c0000140281500814a440660040d14042c00e00c0e0300d8038041111070401c0da032609c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 632726456 1250 632725206 632725211
    0x1209040b03061e0a110703110c04020d061a0304030503040b06190e1503031e0d0605060c072103050904150f0815060a050607080a0302090a0b0405130c021b0310050a 72
    0x414040203c8002c40d040440e1550800c00718081708003002050017040750040401640d2000a000364604002070300c16994002c00031075507840e402c00101d00410491046281d0155000c0b40a40c088110a095078441c1e07806031034a51541d5140c1d520715555110040040380c0c0080e10f401020000014030341080f0191600c0b002440143c00d040004800c194503140c0c1c080c2c440d6004014900c480b515400700110125801c015584d2983c004c0d20018002d0f1042c0d0304800c1e0400b401003002028520005209001c4070a07955030401a0b03100ba11001c90070160400b000b4010031010080e41580342440d0340841c00030748010101000d4030740c440d001120f1084466020151950000b65011403000c1c041d4001a0051000c0710b80d03050071850030020610317a0042c400041d01510010400d00c0c000b0340031fa0101c4250b2440140081d94a684911000ca1550002d00480340214100d44030080ba4681b6441848880e074425002000d0f254180c081401a14450703040d10394140c01492042e10140398030740a070720702500460300c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 632727706 1250 632726456 632726491
    0x7051c06090c0f081003050304060f030e010203070201090c06020106030b13030512070f021e15100f0909060b04051e0c070b01030b060117070f0c060615170c0c1209040b0306 76
    0x3424543c002c5c080da04403190204041001800010031101101d0351410030304000d48109a0550040c0181d07248801030394000001c209a007681036124500f500d2003403070745025581d120f0b2012800c03151140802400d944091003c110303ca4035610600340700350710134505149400300c0c0754100c50000006940e81d0300840c5001c00400711231501446800d482044501d4010070b014503019403943c0d108032600e030142c0b50004a6001c261a40302456401c0080e02c03542070b28000c00c139506c02c0c401005003c0b0700c10a484451030808194034515041c02400c0c020520014025642e40c0c010f111b18000c40800b07021500101010041d2100144030385d4000f41c021070144511320017501d0420005001c035000c2007480301c0c040c400c0d0b4003003001094129000345c40d220040d01e0b0902108290b85402d4000741350740d80100a02045040c1c2d0440340940c03040700d00d11054035001c0a0742e000c2c1c8a01c1c988011901800b001800c1640000a01c03002d01c0c864840a84801600103101041c0641c000010909051060f11400b1500703030300804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 632728956 1250 632727706 632727737
    0x110f03160509132102010e0703140d051801081f09090210030c0c0f0f0206071b061d01050d06050a030b04140309010e0105070c0305010f0207030e0907051c06090c 71
    0xb0035401040e5910b51a40d0000a81c0c1d50100e01c041901c07802c6019a1541e104410300b032003540901c80100c1c0420849840940b6800e0110b102d00500a11900307600c1107a40c0300f012140705406690801160010001c80e07060034000550f1007010081c25400c0102d005660070a508214504100040003260800240111240184180340fa03014a07403d040c50300341600a4000b81e4840388401255070448100c00345211585400c25051980340c801075400700c00030502c0411701507a880e0003410780b1500300041141559a5005440e000c50314640c00103111113501540e504c2d540603000034084100503030310000382d1544680014014440035042501c982c1a010100301c01c000c851b04542c0c0d11b4201d100015070419100304002000b1180281209040040216850f0304008180c0c2545000d594842c000340036030300720144808c00030740000754258002048240c01141504040c5602c0b4020b640b81e6641c0c0b85027184400c07020724440101c0c0440014260366210010f041503140c400d2103410142c5644200141c4030501c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 632730206 1250 632728956 632728969
    0x105010503030403260c010f02030106031a0105030a0e0703080a17010e101a070c030b070f170c0c03040f14040b100c020103111e12010f12110f031605 66
    0x2001107000e40e00c00c102c140042041039100c441200084105003400640c400b107083c1c9940150920214a5801c102142602c408960080d506031183d5035800c01451017a00c011007000314090710203034003007002080411215030081d0014542e08580c00e0849680a43da81c1d01c000c8142d00c04081880024519010410102032023403484d0300401102842c00300c1810a06109249034000c0d00c5a081d118036101c0900540c0724589040d502e4450300007134850007003941d07801e02c40b26044049a5001c0001c0e0030060350031445001310691829200d00038003444181c0e50704810415036900944101c0500d2005210001700c42d026071019201800e0210b14030020703074802c030041c441501c1106900034030441d1800c1c5070480140d80000c8090038039409282c046903031499503188404511461610030440741e0704025014980301420002c1c03106100603c100005a070b603c010010512016000d0010030b131000c01c0c01003010a95610009008150040c01510f02800c0400045d203007001c101b4003410904c3e00418100410b14100c2c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 632731456 1250 632730206 632730209
    0x411131d071505041a071a100e18030301050f0d020312040e0601030b030d0c0204061505040510050a020a08220e041205031b03090c0907270f03023f010501 68
    0x50800c20705003414000c5c20b54119561070b010312030040780401c54505020920044c3c14000c0e02104400030075003000100800c4050aa014406015503400c2c04165140750f0020030100004075080a1800d40c1d00303040402850f10315410705540e000144608000c0035907001d02c00e0302007242e280b001e03c603503441c9040b00075003070120010301031818185030451321110b5850100311480050340528051541c01c00b10310000340140826040780800c0e90300301002188030340c0c01000a00075a0003c07180e8480110039901e013103442c0c1c0304011500c0d005800800240c80098500c0c3c000e4450030241c2c800d840b40d01414a06046442d00c0310f075009841d851064001e00040c000d407a05001c06042c37a0f0310703126103503143c01320180c0d100c880c4000b1188800b400020004019080600c615506035600400816941c141102d000744041e040888007015007001c65581c0203d121414811710840d030700c44a50704201403440e020400a0182c5881c000800c2c004540c0f040070580b031144947c0e032030361078010029142c0b074011450f072421507405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 632732706 1250 632731456 632731499
    0x20f0c1c0813151508010e03040e0112080f070f0501090b06010f020703081b2a12010b0a030b06010e030a0308090d05043f030e1002060411131d07 64
    0x1000600342c0490010030303551001e203000103000709185a090340016800c0c071880d8021000d40d46428407180c00c16034003000420881d00d0380c401b00e9007182d88801d6111080401c070701c0000c0c03403004200701111200e0490ba0240007a035028400e41d4a001842c2e8640a00392894848102e40301700c40c010812141e5030700702c440004d80c04903a200405440313003190784844191181c40342741c0e643c800c0310641c4801d21001c1001640c040d45a40404500700c14418590400c4848803003040d01c0c49584003009105481805100d0600e10180003003441170384900e1500c81200215000d0102da0400c240e000e00d100a81e1420043c1081c064820380e00c0c81c402d80340002d00c040c20045000c0d4840304004081008200030b108a14000902e600340103005014245208940451664242d2401c2000781c0340b04002d10a254010f4403003c0c2840f420380700302c8800380d080c1500300c1c0c40300300032100204504c51812009000341030048100317411ba94214000982012441001005949070b0841d8460f1136001031400c0c815907c0107032003401303804070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 632733812 1106 632732706 632732731
    0x3b18131b1701050709061b0f0314070f0303110a08010314030415020c0112051311031f09120309080f0310050a0b0a0915050706020f0c1c08 61
    0x20200c54280102d00040e400044d10750052201001c041696028805503035450f03072300c403000070440810075000c00240e50000805442440002d00000780920820780d02d8140038600102078a00420403000340d004180b0041d81d099030070206c000e0650350b1004000000440c00c510300740c03a48c002e541c48600e00700c090742c1c0c000700841d8000c0b40401100e01c003a40c1b054a80c003200d0030008151402501e416900261055010700822035914842200d088000c003501c0c040400c0096004c0c14801407000605131035901ca04140c204040c4180c403104451181c20280941c00381600d54040900480000c5411000c001000030a030341003500425020703100052005030420b4554440700d4494020714802400704502c600040b035813500101540e40b00e00080d82d40c01d80f074800310703030707102c0c8065000001000311105017842007080c614400c1c0b0000762003c0c43d0f4240000303c503021a03001081d03054040d140c91003903031 = true := by decide +kernel

theorem cover : BRFrame.Cov 632553956 632733812 := by
  have h0 := BRFrame.cov_init 632553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 632553956 ≤ n) (h2 : n < 632733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
