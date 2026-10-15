-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4322
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:14:51.25657+00:00
-- url     : https://prove2.me/submissions/a9abc339-3af8-41de-a51c-ff98eb34e6b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 777158273 ≤ n < 777338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 777159523 1250 777158273 777158287
    0xc090c030a0b0a080328020c0d0204240902180d1a06130e012408061311060307030b010806121b060403120801030c060311160c050405010b071e08 64
    0x25070050211400058900c21440e0340b1a2801d45c2180c100e9207103c1c0840d449014503040000c3e00c01440c90b071280c0c0e24000b03006640801c102052920500d034001174025600c40441861380310b0142d6204945035252030702131003180e488142c0ba002130360140040385c40e1421907000100052510311510702d01198000d28510105540c0c000000303140500501880e41b154503a07002e0132060b112401401c283c0007000000140705240500b0b0000503c0b10308114041d42c0c4041c290600c043c01001481c25040408140705044424003850a410644644425950004000300500100f95010b030040e01b0844c500342c0310030350700b0b0f5526130500c1705a00b80040000e08e294080740012924070b181058030580554045c00c21031070301c1d4480d00d8804c044000005d84800080c40f010040041c84090f000400180120340340a000c134a079036208090250003041440c0302111200d040c02d400700040075984c04001d12001d0401d12040da0b46240d21a19600208015621081e0003000300c80e501d1900040e8000c2c0e1076000d11705500b020300d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 777160773 1250 777159523 777159541
    0x30b0303042301021507020a050f0f030a1b060606030b100e03030316020f0f152409070c0510020d060b0309120901170c03040c0915090c030f15080c090c03 68
    0x441c082d6415401003001c050a4404401c0c0e02501c07a000a400030a031300445464a14034080d07254091a03081d8010081d90b01427004040102c0c0d40c2c0c6c4005160081040f550b0140d016a103000c40c0340c00900103440d0541c00542c16415801070324501d602102c4c02c1881c2d00580b60143c1d25030508030b89881c2d06070810000248142c401849500c1e020001d403040750f40412010108074600258848402e501b9409840b00801483e03400040b1680000112020f807191000c03440800301140700461020b10950403100024041880340010000c00340d00901222540e000c0f52120f4002907020400d01c043c05801c0400c08034294502d141204c1c000d04d62080101815001c3c10034074900c40e0011010382d41006024040fa20030100041c0842d03000d090034a00c2c0c1541c03824a40342004c008004c540c80450401e0421210082d02c0029203400c904a426094000c1900f0459540031001051b8125140652500c0c0058a000c1c00c6500d0304d1100c1500c505808844886007002c08000c00354208650b84003000c1c1c0e0400010728045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 777162023 1250 777160773 777160829
    0x1c1b03090605030c04030c0e01030b0711030d05040212031c06050d0c090504080c03030f06011e0f110f07080609010b090108120903100501080c0103052503051f080d030b030304 77
    0x130410001003070030030f500ca683d8002810142d501403552101c1040051040c05000102d1503080303401800c00616a41c40010703020f442c0e000c1d442546080320365580024043d52170392042013461050020507607644501c004256010500075030b006001e060b107000d00104203810208008845144c00c24008002180b40c104100c0145c400104200c0320a00140002c104141007000514001e911036a82d0410b580341540004080080d200c1c454040c030b9100c2c50711801c00f40e0f0040720807503901006140c146007211003000c1040c83c1c0403030300400d030500d40300b001340002c0c1c49040801c0350350203031030350800900040303c89804200c200d05017800b4070380c45ea800001e0300c050081036040043c0480e100240c00c2d9062441c003e900c54086403001d81c40042c080d0008005c102d420369051103883e500c4070520700300d940c02c042d242d0f14926122140300d80c0e410030300d9a100042181344419000a1a0503950000303109501a11800c805441d282d07a20700080c00b0030b003000001011440c021064a00390380c1050701c3d50030480e0122020307401076 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 777163273 1250 777162023 777162031
    0x81b0901090b13081f0515130504030c050304140a090203070f0f1101020d020a110a11040f020c01051003260313080930070506120709081c1b0309060503 67
    0xf84245000015840000d01c12141c034200b25200b0b004203415003280320710903100018083c1d9601e020b00b00740c1c100e13030760341c2c2a01c0e40c40315051200d000125035580d0315095902e540500c07000790241c4030119002621010b000902506c60406527104481c2ca03541e40711980c02c2e800140c070401c000c69812400100e00a100300d0890281d034401d4544080c206001c005241c0c2207a0000c03444203000c40e00040c2c46c0026a4110300b26012000051000306086c80b45921030390f070700424411a991146803181d41c200e102c16031a405549100f44500000c2000d4201068100c8450f186032004591400000480355540400e02010b20080c603030003c10503240d5912035840c503107e00a034030340c00c8480043c144401c41642c0c842d100b14007400080c003180701d0310740c00540150b0420031013004034500d4942c1c4209020b008903150202901c00c0c00395290a0803070982ca03411400d030792031001f940204120f031046241d46109071071924400582d41105417158448442d1100c4030f5108030b015000c02501051164104115852080f0000d581c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 777164523 1250 777163273 777163297
    0x3090a0209190c23190e0d1403030f18060c030402010309060f0e0c10090513060b0d0b01080a0507170a0609060303020f0105060402090d08070c0b0a081b0901090b 71
    0x8011403031251400c9568441d2400c0006800101c41113485038040b440c00c034041c0030b91030804d0a110180c0904500304001c2c6030038004110b2040c410044540781c21031004c0c0342030780c020400300c0e00250382502c1c04da594104480842000340d5010100326003c046c24080d04100b41072502402c4c8554440318010040e038800742c000c0b0f042513603403c80080401c0c0203116400144040481c0400e50141066500b858140d141c034907a8490840c02803000c0d0100c0c0c0080c4e9002c115076041c1c4000076031104209146000300100da01c00385440200103078038260507103c0d500c604104e110907202c9120741d4590604000444800725100e50105015848081030701468190300340e40480041e201044840d01c401894007542c21552048002d81e01001481a01b0744080c058580d00c010103460440c1032400120008000445442015185c1c1c1d000149401c18405541480c60240900110300c5949035034603000102075400031220f02c2454080a07020f091050a000300302e890303000c0e050b0b50b04800a42400440c4656074805521085 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 777165773 1250 777164523 777164551
    0x60e0609161b052d0307141c02010b0f06030903120613021201061116030b04060e12040305150f162606030f0706080601030c210e0610030818010c02040f0614040203090a0209 76
    0x40748030756840123803110350190b0000c5004041c0005000400b4461035006124080620030041d08450010a5910b00e14040008825584465000c42c4250395141040e90000f030001409410b92191803420314100d91196490351851720301903801b1a107581c1809101c20798046105402c2011500050030303260018000c003800160240444d441515108100d4168400c200c0007107810414044107000c25160043d1051400d48070386404ca10641c85800028100301502d1204c0e42c409604030b11030f40c4046561425100e442c0d10040c1854101f135151710088072002c5c464801c8692010200c031000c41c400303007110030f9602c0700361841c4c64000054001d02a10719092040149895005203440fa80010003144401460800551040100411420282c6c0204441001c0e400381342e0810020322854100c4042c0b58407040000300c500310034401220300c0050607202079886801c5ca080c180d10400590f12200807100010042c8442c458240244416800308a41d000516048041c0103000340c1001341d1074a41c03100c0c01d510340304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 777167023 1250 777165773 777165793
    0x203060f040507030e0f06090607050a05041703070c050f01170a110301031101111623060c010c0206010807210311100c03060e0609161b052d030714 65
    0x9012908102c81000000e61103030880780b2001020300102003060703a54001f520701c51920441c03140d07a42002500c0442005070029200700da4034410415178001d07044668490b8050401d030f018059898110302416a1008040d003030014952501d1444d101400710182c50b2010f1342050030b401041900d00007000140801e44803082201140c1d0808001c60180d441400d0387e50081d4403105c0014400201102c920360150711160b404501100c4005004084503803114024071003c15406184a00b00403c901e5981c0041d004602e40c40751010640011230003280ca5401ca900c16a40e44e1100b43d504c410754450030901c00600040f88582512013158445214081d040050426107080d900c0340ca840c2c200050560b2107544c4a0740b851486030700d4003c000c0240407845900c1c0f2a81003a100003a241d69000d0402c2d0503262841d0140340c0c00034025006480c0c194027840080d01060114140306440d05051810700c07444444424011003005010030b08500040901401142404d50303d030764a01d80404da03c0024009849003400403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 777168273 1250 777167023 777167029
    0x1a0601050913050f06030d080a180b13021306050105071104140f161e050703020a050f030706060515041701020f280c02031b120601030803240a090203060f 68
    0x10080d03854480c02c000400f4944507000e42500400034010368440d802040b4480d1500d98400511900030007001000102030f1030f101002c82400c4910b03540208960281d00c1080751210039443c0b4078000307500070340301200854100c026601c100d0303415018990101e10244030400200c1c00001e102d0082c040c010704002401c00c003000000384084011101c18010f111042d00b040ba01050b1007800d813400102c03d0030f00c3c0d41469001d10342c480c1e4825090071440c080160200b0500c00340b42c8204030710000c00790050240d400c40301118080c1c41d01ca60100105840140c1004000603060400e4000307003003a5800081c0b0141802d043c116100b904032044401d090441d03400b4480f944190f0307440801410761120701c1c06030801c244e045503d03d102c0c0c0800200800c050214903a60750000d80c4001c160014045504035401503241031003c0081c078040b090000d8160300e41310301d000201c100415040154002c500c4020058510344200b0b1504540b030781a1040c0c20f030400e04a400403c540a8590042c5030801c10041440c41520020304c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 777169523 1250 777168273 777168289
    0x50603211b03090a08010615050c010b0a092c070b0318031603030c02010b0d0b06150304110103140106021b060c150f060616120519021510031a06010509 67
    0xc0401c15400000c0c0034865071501018040c000c0001800901c010b030321701080211031051540081017409000541d40010791800e5202d60000e500c000d085d0200a522a43c01c00010158510702002c142c0600c102515900c0d1405a41c00702c135640a002007442c6030a040d9000a42e41001e09100214074403201d48406124052001c1d0420b4246800ca0121000542c200181a1480d0b499280700b96498407403200126100c05100b03800480c0c001441c1c2c800d54403110f0102c1c03044514200c0e01a00c80b6004000c1c4000c00c007101003000d120070404d90713051148411780711110310008828401d0fa40541c0c8040e038110142d5050300321070044c06900030315817414080d164088504048001540c5074519114408003c54180c02010b619000113050701c0c1c59040a0340f03148030b2410414040c030302500261958880c0283c840c032540441e134900b00203001000b0b00c8500c1d124081c1d51620590540f2080c010401d000031000018180c0c81c20880750000e10400b101e250740310008261400107096241000402c1040403459115022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 777170773 1250 777169523 777169567
    0x330043b0103080324011b0c0906030b1b120f090a020603010324020f0d050603010906090b1801020723100606021b030712170d05040305040305010c020105060321 71
    0x1420b565914181c02e01a2540d205c4414018807000c2c480703444113260364001580c00003180e071100c401c1c0590299060a035569055607210405044c1400c002204220000c54010b010350220740104510341c0640110540304e00590382d10140f10001600000e040020103d202500101c0e03800c2a201031000580100d01554001d80060310341c603000525090081815420a0320002c856503011401e2219848400f002c0d84100c2c03d00701039464907074004c0381c116502984245a00c55009070704000914052400c0002c402040b180f00c1c1c01800c030b80089403c03900c818001c03a81901d5114112250010f00481e0408216480003803201203449554602044c6070f4040c0b04101c0600358540080036034903480b188084240000d0900726000760421a17081141d0703100b041300e5000c45940701e81010180c40c00c08048440034001c185064a035141404e00344424950007a00910075a0700400080c0105d15500e0400c0c1d003a118290b030351580543c030151940b00001c001000e02041a0701100d00c42e49800075400075540b00743c000c48 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 777172023 1250 777170773 777170783
    0x40902030601020c15090105250f15020a0c0f0501140702031801021504060e0a05010f381309051005090c01140a0c110330043b0103 58
    0x309002080d80c04010601d0007134411140b188611506000c1c91145010f055a40d50611401040c07100710080a0800351030700345440391500d65041c20301e0030306014411840c40259a03ea417480c0b845202100e0381d008440440302c00762118003c0c1840741d56003002d110500c000c103807829540c481040d00e51010f0700c001c0354011a1980c0c004d648410510205001022440c03200a0540d44481084500c05201d00829544640c001d10005848200303070408034141038842100910030b502c3d00504007400da5280d07008030174800b00496216850f000403c003110f1510b61a071001c40701240090b45c5141240b401031401c4984584010380450003020036558140740540d100c0c100910b480e100c00400c0a0044204400c08181c002440d01032155801107501e20102e00c0340000b0390f410084ea09030100188910251141c002d6100a01103a40322005c40e003800612039000c445c01c0005002c2e80c050111640d4013041501c0c2a41d03030303003030890795090070140307154111200b004c141d010308207079030282d22080c1031005c800700d4002c50081c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 777173273 1250 777172023 777172027
    0x50c0c0d110d03081006051602060a02010e0d122d0b010e06040e0414010c270b03070302090f010f0504091a0301050f220c0506030a0f0f091b0501080708040c050303040902 75
    0x517281d101203ea015080a03041100a2024030100250906021483e9405941541d0780c1c0303d1380c0c04220301601418108850342c0c411507102c100e20381c1e4044000c5692a80304a030402c400b003150340707810100418001580b50005200e0a0f1340140030150360207001c0e01304050501c4000c0d0030402020600d0f50b00503500c22072411000c0e80820080c001464a1143d182c10324000070088030403001c2001c0c00c10340300700a01c040a00e01c0d214003014070702003056444010740000a0129142d2602c0c0600402942c4a941518010046003080040341c0d40285d0009440e0703803054031800d0030300d400d050820f401000c0d2100d29210403040340b000d4000c1c50310288a981c1c02070565118001c114501055580d044522080b040382207032100030350b41d41c04200c200c8a0003060b51412242c1c2d580c0c0303072161040d880161114802d04513086d440c0c0125080d010b515680301d5160507220303036202d0040c0308441d110742c940301030244604c82c04201800c0000d001c0b45d108282d00c82d400b6204860070305040e40c81e10007080c910380054020054003680 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 777174523 1250 777173273 777173281
    0x204090e060112080c121602030c010f020601150c020d0b0714040509130609050624010815010e0a030606030501060e090a11040e0c0411070c06050c0c0d110d0308 71
    0x840c025040c48841550040145501d004181000e002070204050083c00001ca030700c4001420900c070101400859400c41c0d500ca919080c07180e8940c04038003208034420b00c911000c00c0f419500580005222090607005030240d6841c001c040d820600703000c0640000c1042d070380100c00c01a40c03036610800f0124001c4803c4441032400c1c0310003801000d024496485034041c20302c030030007140c1e440800b070f03e40c40305110100002012030751400c003000c2c041c4a44014070030b009020420901644100c2d6001c80c9840a00c03103c082c5160000065549990070744040005450504d41070600354058040c6901d240b2018141c1c05c007890307030f03074843d48101c801c2c94000b1103e59440b601c0c01c000c4490206582c640018010019040360718440d9201410030441d41d030740500594403200c0786540d400d400d000413161081c000c0e100b071011001421016005500c1504201d8090300c001d840072617007501c01c0050711020258131000b0954103a11501b00490b0715801403080f00c5020040c2c111414948034801002207540c03180d1506001810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 777175773 1250 777174523 777174539
    0x1110d050a0605060f091507140c030d0c0f02101b05030901080a020a08040b04080d14010806100609142d120c01051c020c061f0603051b0a11010608010204 68
    0x4100c1c3d00040c41228140a001030f40c0040344d04840401d041160b01c2c69184071204407080c00c1d0300a08c03174050309079a151031801a400101040000006c0402c41c10369412110a68040e00c001c0144807001d400303058220180303001418032000c001c20b816403504218448030051034829940c00c550f200211499000840c2e4400c0700d50300041c10982108000c1c109608280120b100240440002440035104240e0b00012405000445c0201c0d003421240e801706104070002c01c001c0c011081020312071540f1a20070040011400c1c0040c0e0700e00002d6910316540e602d619850031a5420052284590250b80a00b4400412000c0620300e414491580303110740c1c440b07905029080070080284050820780340d064102c0118844240c2e4084100c6031400d203007900b0b160821343c080d01214000e000c0e00713101c03255500c0b030001880041401ca02042c2c05061103548210905030319000104c05540b016207070b055282d0015080c0c0c0720018090005854203020929100c1940d141507182035007901c403031b640328000d107950020b01401140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 777177023 1250 777175773 777175781
    0x5010908030c0c070f060507060b010c150903230f0a1803030e090a0e071503060803030a06051c030206071b0b040318140d060903110706030b0406050f0f1201110d050a 73
    0x46005c00240500e1070701d14094024413681200400700c990302c55943c0c401d6030142c9098040503402a100c4400c0c0f035020f220071030040261002c20313000f0031a841c01c2070100d1491004003595022456000743d0030f0120705420201103402008101040c0007a134154603800003c0545000c005602a9882640342d6030008144012500043d1040e803a042c03c1021440d0744440c0050300c4001c8803840d014003030074904a03001c00c80c000c5c01140c10944a1380000814131440e0461a00080b06864040f0b403000c40b1b80020400141110705546401009a000381001407610f50046c00d610300b080c0f4030842242400c02d92680c1d40e00041408503411408130780030b41d5130203540e10300049445010749003075203110750001102e41c0024105000d0620080a07980c690140108149c0b00b214000c8500464204842c0e16640301d56008e00944130407aa074074091032401c0400640c920b4480d100641d9000d014004009008044043c400d0818820604000540d02e07200b51708000d990300c40c0103040c0c1c413180420004090400d261070400352 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 777178273 1250 777177023 777177029
    0x50a020301090f0b101103041a0309070b130e10120605040519030905210d0509040c080f071112070f060c020d08070c05120c151f05060705010908030c0c07 68
    0x14602e072101050aa440d12140c1011045d00c1d410040b0400b0041d91013030385944034903000b20491b52120314001c1d0b00c1c8424000510b000301d0b0242c003601c9030b0a483c4c001c03074940b501440806001d0070009107420803500183c083c10399040f02000b6141940c65885060303103140c16135000b400700c650275901c8041205025040c09141040c400300b001c4169483c0694600402820081c054a0b2049295248801c424003004810003060010034041d2040b180043c100541203800000c1802c0c0030701c1c28213011484403886200b68510685074030040d07112035259400121034119404048101038441d101d212401810b810300500781180c0700304508203001c9010b11342142556004200032040d90300c074000641980750032550465001c001f5280682691440e800c11616010000400511030500020289890b28001c90340901000616002e148183c5946c40740c104543d1780ea101654003044240800d02a51508034018820030b8080c070300100c0c0d058115122018664010382e00d04088070000a4440c074900d006101407402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 777179523 1250 777178273 777178301
    0x3091203010810330e0a140126030d060611121213020d031101050f0106020d050706020d020d09140f0c2107030b100806060d0f0312050a02030109 64
    0x11545048911581c0e82500e41107510290348881c04454005284080e495801d030498420307446919800f1a10300400c0c042d801140100501715001800b0400c0ba401068807030490a4281d80c8543e1801c6403103883c1883d907894820142e003609241da024400c007000580a002011400001c6a61408038040d126032000403c0c60400c1d0440c4058044e511b903000c0540781605e000002640e9190b5810000040444103401c0c003d61001151050300d0a26510a0f5000351815110000308041d0b00e130000c0b541072416003403003024016449846165240c40c45a40503180d480e1003844058148400482d5402c180c1c0c2024001c04a0581c1d1400d02400744101000c0d00750710341d842000a403002d4910725200a0300d5076903c0c003400d40120024008058100c0d4540300407000f4a40407429980c6c3e00b500d0749047c11041c1e00c180c500d880019403c090100e405103020a0300d13801010018401c07140d50900e81d0f02d007102240701c00d0056090002102c1c0045210141740101032207800510300069496040550b9442264507441810107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 777180773 1250 777179523 777179527
    0x7020c03100e16090c030c02070806040206070f120309200d1502070803161710050d080702030307060c1d0d0f060204080a0f02030d170f060a0504090809040c051603050f130803030912 80
    0x19003c0b0300740c0ccd00716406072003240d40da07042d9003400307061030140c9003008110880081181041580c076500a464082c0310f0242040340540101200f0f0301d0003a8101155400b88640b11840001101001543d0074100c0490000d800c00d0110703290408203030012900161031500d040b10413041d4550025540302204860311120205042170007040d0107102e840c0c001d8500491102c0c81c1e0314144010f010990740902d81c0201100e07031b1008a45005006066460060360104103501903101036400e00c902e0109040c04080d12a40f49018651541c2885840c04803013524890782c204008600c11200788144007480d400b840740a001101e2920501d0b140600c0001c1075402c00400c03c0f15080d0320f03080045042d4010500e100390802c903440e0080066410605130f449a903109240c0b140000401006c840035100714a012501001040b034504000d0311207101d1900742020410000101200090141c07000d0141c8180c0c8100650600d412400703090703800780d075680044421b40c6c00801000103400d02007009048203002c071544c0034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 777182023 1250 777180773 777180779
    0x1201091b0806010e130309090e03090f04020301120f0809030109120f0311040312120f0902040e010902010e1c020a0303050315030a170703260f07020c03100e16090c030c0207 76
    0x702c0d00384d6000c0c0010b494078400143d4641071501c2844160090400c23108100800c1400360a200e50301e5110401060156584401018561409109682c1211040015400e805c0306555071003c0010004104650005003402038042e00e0720300b403150340d0f1070510804d01d03401c2580011401901d4154070b6602c01041500300b14003044c2020307100d425202100e0b8071030f40c1111072100c1440d00740c54070403030815400002403030460b50b02584880c913040a101140203680420562200b50291400c0c2c600d840c00282c0851420950000d917401c020074002c0c8426201805110000c800354000b90207022980e00560004d9804820b2004e60101c2040b17586d98220214001c1101410781d43d1114002081001d140100c03000c0810801c0038140500079403018120420b401c41004104101402c0440c1000d40320200403448034000550514000600c40844940081c001e0105241e0408201c000c0d040c203403e6040c42c2d014002209403021a14000b900280c40d9150020840c180725103001000c40d00444c0c0c402c0c0455006603010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 777183273 1250 777182023 777182039
    0x2150402100e0103142509080d14070f05150609040c1a040801320f1302011106070905030d0e0d3c03020c01090518061201091b080601 59
    0x4000c03607190300702501d0b14401400181c0c0201400c829980c1c18414500410a103091a0211500b2400c4c4e01660200f40108003001140d45039611b0007401480e5011038184c002c114004c92a07908000031410156103019599038811140a0254a003152254003100c500036a803101544116880102611240d0052130561036140450000b40300d4041000030390780310204240001750031130b40a03156002c0280b000c00360302e00c004003007803040c5030f4180001100201c003c41640ca5694541d0b0042c034502d10381d820350b80c8900002080d01c60260400301d051105007140401100d4061058034842c00d91500c07215000c502d00004d2504200c2600340c000c041041401d201300080c0d0b03418803050085a00301200c0e1900c840780703052034142e01d481c0d242801d0015142c2109103c20006814800c14524407035400ea0783d107620340c2c20041d04c070ba40b100e003d070030b81c00052800400c42201110580c554480401802c0b0050360011401141c2100d10030182964140c600d590f170313909081c401d11a800001c2004000070140ca625128030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 777184523 1250 777183273 777183289
    0x20a0b07030f030c020f070e01170f0304270507030e0105090d02030a0309050c031c020c03031e031003080c101a01171008031206040c030908091011030f040602150402 73
    0x26841c18507030345030800d813202032080284495260f501c0c022a81516111001032001000900c20380841450b007144080300407001188210010442034000c604290906407598172036103410204071200d1111045a00700e070340050103407901400054400103104840300b0045400c3d110024001040c5a21100450b0380e103950001c1202c5150406140c001008251031074418208661001e6060b494803400c0c4800940509140200c60304403070680032110310000c140145501c034000c00803486103d040a80740d41c08259001d00085030300000b90382714424140d840c0d6480f024140c019003001c10081c4c0c0000313140d110b01110361144a042c904c501e2140e148448050300000d0074590812451158440840085025800203090200c06000c03440305276511020074403100c1241c024100c0307080c0c1c03195080140343c0b0703e054080e10444030195048100c6500e0451242d040c041c104032171105080800c2007040ca200310501e024000b40c41d008040072407403a92245000d50092404002c484808104551103050000581e00c1a503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 777185773 1250 777184523 777184547
    0x41404110f0c100c051b0105330405190b0901030b1b041203030f1a0d0b060d0204020409020304022b020f041103090703021212090d1b0b07020a0b0703 66
    0x101c0c26a8521080300003505203903c00e0700d02040c2c2404e110140505030f40207006851161060380900b500d10001c1c0500c6420b80d1030980d0100c4402905d461803200014080c9082005d80d080515254200000140440d040b00c10446081d409503e424035140d41c6031105001d140f044081c100e4400078030f541141c0760804461405000000310034070030264401c08160210a80b00144032110464003841e0850a029000d03140e00001203c80c80c3ca085c0740740300d90080c0840448102800500f41400c0020070b5500c06403c03081c0174000a078405011105500141e940340010406007121260140c0c8038203044c814443d950040c4807803901102503440c842050903c0110340300c000c044d01215007404200b00b20000c100100340d601030041140e640001000042c40c0300040c19021030784281d420b0541e1032000400345440d444105401c0044a40810440045180c07044038889451300481200d0403500e61000d510a9480241d4444854081c010502c1c105510381103410100403e802c00c02249404034656009010200d080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 777187023 1250 777185773 777185797
    0x90f01080f370510050108061023010201180c090b0f031209010e041a01020601080c060403060e3301080a0308240312120603010c0806090c120106030204140411 70
    0x2450300b0345480c14815107080159000002d6660b21102c0c441c1400150009010f002480d02c00c0340003081c41ca00062001030300322419001020440301c5840320b080c000929100d1814110341d01e99003c540001c51892100075014416081410410320300707034100081c7c4581e60344c4a40b04030380000d01c0c840b9588021801c90031921b002200140c5d21004e40005a590b41d1310f03002c106820625040485100b159007402109104a0036000c03980c80780c3c0d88102c465078956420146075081401444200000780e582c3d000284c4a199a00603692012070392070400700813050500c0c180c080c0030051300c07101c0810401d03116000d001d0104000580651a11030314043d160400c0507001e408003c81142c180740d42100b21000304044100c0042c00d0725810000c0b00f40c10045904445040c81d0721501d51404100750b03140500c2241c44080d09525241003035a04d40042100310400200390300740c1d02c2001c02441d0381d6042d40c12103140c060000c6440040c5c42c0c606001660f07000410032034281c3d0041c0c1c40c10101d000411917244c2903d128100310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 777188273 1250 777187023 777187093
    0xc1205011d040c090903090303083601020409110901200a140c04110301140105070210030c1106091f02070c1a070f05010b09091606030c050702090f01080f 68
    0x15183c45415503000d588100881403402c4a60000c00d40e1125461307003224082c3c0d80f061840c2d03d500441189204003800042d16004c0a146080341c11000b070554000900c0c240b4000500f80780d90762076800709951500038001d041c401c0002e034000c41503801c85002d50303042200c503500c0040c1280d5140c203181c1d10600d03c8005441d8900c40b103200604140200804815100050418802d00b0010920550290820b0044c656241c00300301d050360046d442a030a5030b00298000740580c96800780500c0c140c0c0201114100981000008030819000e0602000f0103809811b0410052184040e400104084c10b010402e4202c25540100120703000b0440000c10b140c192402d000c20240d000307000c00c00e1f100f07061080a10040901048900087c02d01c90194041780a040c0b058442943c07990701c08910355118810034240d03c0010749680018012640300c4e51202001c941c09092030740c500100d68002885c040d00490f002c0ca0b00c8410300ac01403054a0013841840d903108a0480108000781141004c0014203462100c8014041c03d6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 777189523 1250 777188273 777188281
    0xd0804020d121205010902070302210f0301140a05010e0d031116060806030706030608031602041e021b07060f052802060901140105060409180b09010c1205011d 70
    0x25401c9a1003009074000346012682c035108402a0001c41039928a058080c0b8100000a11b00600e000b2260810f80c19070203031000c4650026110f0b403840d062080750042c29414800103c000f80e0400003540030300b1600c00740d105810701000401404e4800d50b00680c1c108107891601c2001c3c0d4942c66201105581d1500313200329000d03042c1c22041c0c0783c101f583d01400104110038034002035064102c40207600842e0142d0a071003030703a600d5440131f5007550301b548114400350303004202d211003110340c0d149103482d024402807011500026245401070401c0c802c0200b960120fa000a40b41607140441c001d0701030301c2142c3c001800d141454a00003030000c46c80000640c040c80b5001400744c0311600c1c060b424021522000b200b40032a1500084000c0d40d524040342c481010750b1820f24611100010400c956048403002007526140c6803c1c2060032014000a182e02d400340300700032118400103102c90541c0362060080100000d14007a030362400410343e40b54502e400504d1842c00e40188413003000e0041c003280c408030040300e1908540b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 777190773 1250 777189523 777189529
    0x120103111513050109141008070e0d0b01050315090309040b19140109060507120c140a060f180f0605040c09111b0d020618070909060204030209090f0d080402 69
    0x480340007541c1a490000640506118000184805403107082c0c2e52110b550740c84e0b801581d0300a0040640990015410400e020800c1c407801700541e02c8007c41c0390440700242d4000101e00d80300881201260000da1440050003a4101040311b4480b1914403805070005007170400219482c0e101700701c1b90314040e54441c0403003122525180e840d001450642030078050b903103540340103041c0d10078a0108480c4c00240e4003040000c0d090301c140c05035031a0940008640b0403c51a61074162103103108000700702c405a10310041819150300a00c0801d0400f4000e0f503001c205001c80340120411030701e000458000f0f04014488003000300320381101c903205180d8003040c0041c45407110305003160a04001d03807101080d1810401001511180603000c0c01918441c040f403801a40d0004c0507003615900031115640060b448140041e443c407407011a60401207002e001035403103c0c3d840d1020078042c1c1c1c00244007a039a05400041c10001c42c20706190069010140c4d40c080c21708184200407044e1290100c1403540100001138001c201555 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 777192023 1250 777190773 777190789
    0xf23040b040b03043315090504110307060302070f08070303020408070308090114090d170c0304090e07081501030605060612070c0b09060603122d070b06040212010311 73
    0x1403940a515140e807510a031906a200325821200303c15070f9240340c0c4803525813440e090740c811082d4042625000e1941000f000525a110300312960540740e5000090800d02842458012402094201c20024a107410316140002e07640c070410415104000c0c04010904041202c43d16a5102e0354240d5229443d003004c60183c0959003140c1800d0144680010401440b400203010131602038aa42005583d0a034801700640598030603d90003004000c11000050349103602c010080441d80700f204d0916030015140f51850308281c0146612955546150b1403002041101c0d10040c00c00c04002d08030000301403400040c0311818031005021686070004180199a4007003514400c4031913860400017454155401410400b070004165200b8181c000482d454020202d400b030b1045001030000c28030111a051461840d62284c02ea0b4403103124400c055240003461a517078602e2042259041ea52a80d4103424118081000505078620407441007044440c079110807900c07103046030b400220305150000b4200201e8800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 777193273 1250 777192023 777192029
    0x140405030d09090513080405040509160f031b1a0f0d050c030717010f1701021204030206040c060813060209192c0c032a190f0f2304 58
    0x600a080042607034a034411544400c540d00c020003401076441d0030580186034680d103000501b00d03103810402030206051541119420034001c100b107600b00041c8012007400308056820003402e469801c0010010301480e020720080c455403000241e41064a443c0b059558086030030042143d188000c9800580021410155420340d5041c21050001d03151840b46000b49034421280c40000c07a05485815803091302d0030740018142c0e201c0f00c4407400d402c0c0c200b07615200c0f407403400b0381c2807030309590200610200c1910120070540203501c00c1d0020142400c0c50302e400c03201c000ea10380000003045884403c001c011010381c005074540c140c02a40c0169507900050100741803008640d003810700100c038002c001940c040030200c48551004809522200c240407420420440482030362491265502480840d00c7e09003a401e240c8410602d16401d074880d5820000281c205e80c10002c081004200c01c0900080381c2500287c6c0025100b100d85072500d40c4c074402c1000503048015040c80040c4801c90b01c44c04403030350f0012a00b02c03006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 777194523 1250 777193273 777193279
    0x9010f050606030103260c010c14090a1a072102060903190f050d1b020705010513300503070b07080603191b03151b090306050603031e070606060816140405 68
    0x9070f90001c11f00d45007c1c1041c43c046e03800140c0004000300d03001c1400341c240c0f100c2136070040c100030340203240140c60810070605070b0b882c0059501c20014000001c40d0344103440c1021032a003000c9420808501c10290621a00414001c00c9810030000403a06032404903914200b00d48078145000c100702d906070701315454000c04203240d801c28681203010b1803e80c00c0202404028209900300c500385a11000115420301540c8041152049102e1062080c480c43c10307100680f40004145a074102502c180410344a42c0552006680c55080000d0b0f48080c04a0301d012664002111309001311142400e5020a0760b800031180000004a05c0030441010080d10710494007801c00318a0320207036000e07240e0034140d41c10380340c102c1c01101e110700c0e00c1e12083c1000e0300c0340c1030244640f0071600d58140261940c3c903040c014000c01000c465040c00100011000310903051200011650b501001039100c1d0402d00e8000300301d038041d800820900514204100c401428010118070f150420b2a1251040451405d8010107014039041258 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 777195773 1250 777194523 777194527
    0x1226062e0f030b04090f02091f210503120a0e010204050f060304050c04150905010f080c0112020d0906060312020f06151503072601060c030c151409010f05060603010326 74
    0x1c140701210411006c220300880c0d1101041e15222a8210b4030082c8580d00c1c41e0807800340c0d608008006116085445412000400c00e0241161744d80316411944504a2440810300307100512500003003610900c108002d00000071480c0604200c0003c07005000304902c0c0d44102d01c00000078007042820301601d0b0f003040000c0d000b8460403580c1c031803681d4569003030f0080d20401864400005140b0303040100c0401265480382c040c0100781ca401c0300445803524410003175100281c08000c2c840c0ba00c000c0e07115006907180034000c0041ea03182107103030500102c20390081030030840d0f00440e075141d10000c005c1110b540009001c007148001043c0d01d8007280110f1001429104c43c2000442005004d40c1c004500325a803c451100488110b0b50100500d085403c0a01901000410303040440300000d0042e100c0000c201d001d41e044109038141c0200c90300688402c0084182680da5150a1020340070b400d001d009041401481c0500c09840c0030b41c0401c41a000512002e8094240381000c0c0f04041500010f1101101007150902c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 777197023 1250 777195773 777195791
    0x60509151201140115093b0f0105180727030204090b2e0306110d020307091401020d0c0f0807080f070b0c04030305071226062e0f030b04 60
    0xd440e0200344105c81ea0720101050705800340b0b2082100c10103980707038202c0d0064294420030b501020111011401c00349139554942010701406041e004034800d203070340000344003150b044c201844050148510340076440f00b4250144944c45402c6a2008100030059810b501c0a444995a000300004070380d00c069001860070803028103210b10108020310541d001c00000281c079041c10818050b800581c143c46c004807003081e0b41032000450381d400002105a05020a6040c031741014050400c0307034401e5605901192144070200326000801c41d2001d10f480d005d0002e0040c0c210350500291021580510040001d1910318580701048034071070584094503013019a543c1c407004400841a119800848103031403075000c41c8005456040b01904440950354950364035820710800b17580e004c0c0a01480d1209500713001c140051881080141100b040c510a03483c50311074134900300941800060741c4000301041400a00c01c0d080401203c10349840c1200079101d15110b12070070442841140109070000c0c000743d11a0030180d50b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 777198273 1250 777197023 777197051
    0x4020a1e031e051005040c0302120a0203011119050f0f070f150203060d06050402030109120c150204050303040501110c04140109141614070b0403051c060509151201 72
    0x126050764820011440301908004651203032800303650000b80641d00c20112a680b15045030400c6130414442c40e004044542c0f81d0f4001015240d804824200c164000216102549403d002d99484c185028010a1410a580340182140c2e030080e081407041c4000000c145465224840890300311070704240c02c980e121420b070301c3c1c4494080110321080e24980e0f0600001c1540480c0c0340300300c0b409418000c20040d904103040d9180e101038070008200381d901d556151903441c0451040111840c03d0f4429580c1c69411440600d03201c20103c41c2110383c440780520500c01401130303840000880b41510400d0901010801d034541003140b42580310344400d500a401e107006a03284c0112500400e0680760300e50703401d005101050001503600001182d490204561400041644d01d001c1d040b019584440c010b6014031745060340c0c54820f0215825282140050000a0081540100704100301d4500110038028000a8508800158070340350243c001801ca90381000c508070107a8400c07980f55400c10340b000003800b0440c964086 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 777199523 1250 777198273 777198329
    0x1501020f011a0111070b0909150307151b02310c12060501020d12050903041a070506092b0e030a050106230a0b1b0f07240206060904020a 60
    0x1180421365085041da000c080101d90f0384181e5030508145400c0400c583c0c200144038102800b440c1c0120381d80c044203000c5440c24460000607284000f51000c0424281070010003403c004001c058100c45050343c9140160340f0404070801848140300c0c070800000603065240d481075070602d0031038101072408000d010044c2d0420b00b4152034003041d680804c109591403006a032181d40c2d0a018100140340c2c0b8084401c4904a035000c95088010401140c0c1000d80b070340110140d1802c14201c1c0c001c0c2500104414041107005c200540e800003050000d0020820789840340c46801041000e1940c0c00038030000e0402d81644074102104451000030100d55460340d15003041c0d402007106001e100b02060481c00034212841c0941ca071841c1810b005400d8200035468054082d04c95000b030b6010110f14083c140c100440c80d4002c100c1217403d03240c00e0000e40500e07440d054030109001030203044140f44000001200700c0c05134001c100558000d10903241d0407d01d1f611480046d82c2c40d8059041052884042e015070061b05882c3c00f1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 777200773 1250 777199523 777199571
    0x6010e0918150708060d050f01021b071208070b09150103060507030e03030105150904060e160f0c151e0507031505030106050a15140313050d030b091501020f01 70
    0x203079080c1038003440da00201c00c40b0490b6658042150f0f080801c00d01c6c03c1c10780b9001900c6002d607056860700490004003070309a0707020040c0750701c209841154104292000384034a400910312042d4140c0c540d18560f03100c800c14005d82c90041e1600c510100000c1d074800c0b040c041c1d618028040140d2086542c0c4070b281c0f001c01001d055074524002403800c41c81c0390a01c1d20000c2142d0503500010533000b8a10081d20055015600030392085c0c1d006500d03900002140d004940c981400b031500e0401050200c070f09074034010030340c07000800c2d020100040085d850000c41e8100300541ca9004228201081034000e00c500e180504d00408009c2c0c9066140c27000300301540d07501d80c0c4101600309820100a91059440342054203840e030070301a40b9844022014208a400c00301410140f4003502e5081610040f00c00189005040c0c2080b940c10a02c9442c6003082810405e0501000c5c410b900181010004d020361080458400c21004117a080e890504c84140e6105a000304002c5940036080c400074002c800f146102a141524001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 777202023 1250 777200773 777200821
    0x150c11010c020601051c0809040203090c100504230301020c0f0309100504081e0a151506050309060402090a15120c2702090a150e2704060506010e09 65
    0x103444040381e44007141e814120740004015610741c11603c40e02407001807080c0b40c116024002003110408903240d0b80040d6100b5450341d0003800c042c100000510645039039801c4600c0030040100310a00154000c000400341c116200c1004802044000c0e000c00d009115141400c0b0042c41850301c00d949100001008164005054458240800c40b000c000d0303e860140d030140315081e03080036560185011021300c03040c1e40e08055030100c80c4030280c0b0303844400880c81404040140680c0740c00c85400c50700403647c66940184003e240440c6146440d1854035140c00c0e0192000348600781900108000300010f4009180e640440600030451555035030465444c241d0100040b0350011500d0000a0074001d5445089203500080107244108140ca48210001303520028480d40e0041549101040c551011440300460103515115001d80b048480208040344c1e900b0541c01d4a2440b1003110b40c2c03a0050b200c0462500158401000300c1c1c1900c0b298016121030345882c00c100d42105040782000440f00000c805140556200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 777203273 1250 777202023 777202031
    0x10212060301060f121103070e0403032f070b0619080114010801050601050415210e010e01150501050f0c0d051e09090609040c23040e1612150c1101 65
    0x158424140105441c070603840b040f80d08500c210081941034020501b80c0400600303907600e0310740b518000d0f9001001500e082e00041c0d620078800094451546085e407000099a90800e0300c0340502942c2c0c081031045c080c009141c40503d00c085403080d1105891400b0800d8101d05101e081c54880390710361700803d0110f607a1280541084e00010312990f0602c00d1a00400041e520b642c900f0342001014240707040d40c002d5100070403022112a0300070b222141201e20759000c020b400805c070f50040001040c00c1d1500d0035901a6107074504414070300d4101d500c0b080442100c20a080c01c54580311a1a1213680c1c50007801ea914003035000b01c201c80418542c0c072800508144001c00d40701100303507045e20314841d040d000d1040140e8100c014040482c2261800d5281942d000d445808080780316600e5800002e44164a403440051004003d0b0741260185030900504207110403c3c0000c0c0180454010240301e6009540b040c020510318501d4460300f0300482d0354015909001031031043c45144442d80000340b4060000d24002660b500e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 777204523 1250 777203273 777203279
    0xb120a0b0c0414060f09040207032705010815031f02130e13140a12031d46030503010f05180a1104080f0303040c0e010b03010317040801021206030106 66
    0x800400d89090342c0c800070f80300c0704641c2140c0c2440590351069007002540001800220215980d030700040c070740c8034429607544248084500400c20179010b112140305802440b0103041c070290f41e21250f0250b1140d020b0b0300c949425642c0f80b010900b4001d0381446045162000140c18049501c10b03001481020011019903c240e0380e103c101c0d0241c00707011390349140251a1607801d0f00124014180d441c166010110a07140d80e000c2564651013020300140c1840c001c81d846100c10351410200c0000c4103c42d40215024003000341451100030314034260b9140040d41c0200040074009000d10302e0500c1c058035009024001c1d005001402e015006410034401c07290b10302a10040440c1c41d0400841b001c0301c0085a81019030302d911241216009007500d031810391010582408002400000bc001d89580f2280354000340d5902d00301814009508400c5801600625019400402c000d0074040100d0f411aa041141e0340c4200c1c813139a0340050390344030741d5010900960010a2110b40c69141550090062508400070020159 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 777205773 1250 777204523 777204541
    0x5130f0332030412150203091005011a030105040c0c1a0f0c07081606020c030403060902100302040f170307151a0405090a02010c0204060509010b0a180b0a0c060b120a0b 74
    0x1440807061a98005100c00c1121411205800300103501c640990290040d055003488101e8000b00c0f0019150341c0f150800c19030b44440c40c8202030151a01d04142d82451070581103d081521040c420b26000315030fa030104402e41c0d840b89009c0d0070203507441030903100851130189085031070800c20703a203400c0081002c80203d0700f00f64030380c421203007995030000d481801c4c90f4401ea0b11a8116150782d40c00d4440540030440c10240200c00e100400146201d100300080b0b203120750040c0070704011134032000800d2500c100820300219000e46101c034221a9503080c607010210360110014214003076090001c0c1121040c85280c082c8840c19000b0740907001108000940400c2041d00700301c00d03a07030107481c1e140b41d40d0404a503040c0554030901c4508001d034000b500c082041e40d62071001c1407030f145c0c0991210303811440100304a100070b58400654443e442d446150a529941460384070112441103c5100050140e0074007001c04114913900aa08900001070507003000110700c03540107407200c0d49000215440105a0b00040040e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 777207023 1250 777205773 777205853
    0x506090604230703051e0c0603040507050d080c15061002011a0f0a0e010e071b0b010b0304030324060906140409020c0708060c0d050c03061005130f03 66
    0x282c20207600c2c0c01e910344010024254500a90826055000c0e465020010840c1000380b029644110080b2217642107001c0ca01ea030070110921407242c0300d40c20800c2030101003000012400d0584c0c000310744510081e141d500e040e440c240f00d104485401809405c0404401b114070700318039407056009451070402100e00140032405c1700d01d5203000d40010041c01541c0009400e055401038480b02d40504200360075074550703484a030014400d90000e0340740c0f1044800c108036540d04c810444505001d4807000c06140306541c0d98141e1038032050203141540400800043d0030301d44650003800c254501156158414540c0d61304d0350484010391b01070000815007140700015031350311454215610302e80700426181403906040c0300c2006540a03c175441c885c0d20a80380085412201405194015900c0d03440d69507039403c0410340c85082d100c00038044150032034240300300045501c981201000c1d04010340b9066507500c0d000e02c1010000380030707a00400115080044040100400403042c1c1e583c42d440c80f20100000101310354086861 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 777208273 1250 777207023 777207031
    0x4150528050402040513230c03010e06070f020304030c03060515100e122107020a0305100c0216030503030406090203100e1b0406081203041e080a0e0102070f0b1c02070f05060906 78
    0x315007101c080c1609545042058040107c80c00741c50460402c4c400007070070b41d25048002e80f803030740101d800d11902c55001341805007011541e001440c28031380396483d00045155244409000f40d0f441d43d000480e5044861501c02e400100142107003010ba680791401030240b007540e10858001d1085070503032041c551f00001c41c0807003103840300c403102e00084a0100e04940d540041c0422600001403200100000d88180440c540001403d03100040704242104003c0c03609000000039000320000d06010b001007903001c811240d102c4d402c500041350040c00c07440441e18051208850300d845501d0036003811050742002c1400d111080a41c003400d40005041c0c0c00b0801203c040340300300f0b0301c3d070f038800c400e4a00d41c0c10858020755030060041c0301001d5248028403031190480c072011000c9900840024104440c50341120b200b901e24071080c8010b00d50075061201c2107917600f41c2801840140180418480302c0500b0f03c2c85101c0d050105103400355182e40e5645069004110340040846050003014005204140001405485 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 777209523 1250 777208273 777208283
    0x60f030503180604050d060f020d09051506041e090311061603110f030f04050f06100302030607091a090d02190e01080f1b01020f0f0f01110304150528050402040513 72
    0x4a100300742d582d80010003401507207000607502030042c11780cac4c04613a100b104c508600440141c5070003251040340320221034006016621983c1703000d01203443c8071811500030301d03100c100c1c44000070341e001c103410300b990018541c804100281c4510000c000c60040780c01c420540e070318002c1d20184054144200c81301d40c603000e07400e170312440c0301024070005400425400ca25604940580140d5450030f41c0710404600b001c0c8111a81c0c4a02042a0001c0046050400003c2d600200d94a0000041070800301004601130800c5030b03441c003000d80454034003040d03a1908818101c40c0c4d401406028411a0b000f8050320040b424440e44a80c1c4406100000c3c1150005c03444003040489800074000018005800c0c400c01925015244e045116201d40d5040c0070004105c03032105001144010030010203c04e0003207094401200c51000e03140070500501c000903514803164100520080d0000c80c0035624411003508010340d02c115030050035440d080b2803042c068560302490195000341c80030b0000c0d54a480d0720304441180c01c8c0c0c00900d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 777210773 1250 777209523 777209539
    0x20f072d060306051207051509011418011b030c03120f14010911070c06120f090b1014030319031503030309060b0603010311040510051e0a1508010b030a060f03050318060405 76
    0x10101008d00400600005060039442e88000c44d100e0b4816030049010204c920f688102d403040c80d9a00018040304102c3ea11071300520500d00e66a00800c001000080241405001c0084d0725140d56146c20007200c1030021a07041158041c90015003451001c01c0c49001e1606141810414100b84203004588003240c01040500ba640c0c42c0c901c0450341c0c484202d003003480b9640d645400c2c0d0410303202d40c0100c01406004000c4500281440025000300700d50756400101e0801c00340c0410581070300d0120564201c6003c611424a031004040d04c02d0b8054102044032115001e03a0300e0000c0b0401d501340d4401044917000b100c08005407840c010901c1003e110030301018181e04d507004481d6000380b415800c0540c0c0401040380c42c0807120f6948002c0b40c6c500001e8245a800d4580c840b08400d10317400e0075405c040007041c9052601c41c491024820261030076a0601410192400020000d0b1000444d9080300c4000d004206944042554a040094480c4c005c05405204414031304920f408502e0b02d80c050303c0139958010250b01e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 777212023 1250 777210773 777210799
    0x322051f05072904060b10090603020903010e06191413080a44070507020d0c0b0d020406020d0908100903090906031101020607020f072d06030605120705 67
    0x14840c2d4004000441c3c0d5031406400656500501e00c20042003410200000342c62424545400415100160546401b4485083c0304035103003544030803480700320780d8142801030741c91020b00f0101e0302500302980800410710800080c4a40e04a8400c40c214100c59242400c01602c1021014905180b500340d0b2000120200200982e0110340801c0090100c04007901301a080701203e0120103140d240f00030442040010b21401e100c00b03c50a80d00c00413031041080c0c042d11124640418041e103107001ea0741c0040e0160102540b03400801c0200d10f9000051324004680740d444910100c540c0002e540030f4010300006003d00781310544010701030300b62201650f545a0241c110004410b003c00028902c180082d002c20510b0000006c0d000c0c850f2141c080954003070b40005000003401e0001a01c1d100b0081c3c120f50455001903070400c000140402d91030140d400c0d102081c108519041c0d0720600d480c0882e240307601624004440003841c990142d004004403001a6204c24038069141104c5442d20f05074411140c20400485140d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 777213273 1250 777212023 777212027
    0x118050114060d090b0c031902070218130b010b13080a0203120c07211e0c0e06040e010c08010f12170309010615090602010f0203090a230322051f 64
    0x290601106840c40021413a04a884a102d04801941c0d03130001c0300000001e114941854944d042c00152003041e09502d0070304258017007401d00380c401c1500703104034a80d0004608000000e180240901d6000f01c03011840d945c40c2c01c0400265804100701c04440c455030b04c3c00103050340c0049541030b0701c0754006000d080c2e400303c003e0418005500c1040b40c079120b800b42d0f0709c0205002301212003071424004682e401020034501c0385803501d002580900c0c05080013080b12070160009100b15030032019100024150285901d0f04000b141c064000214520460b500b80074082c032903580d01960150486010204000c00640d44801d202d80c4d42c80c501401420702070303030b0141c4400038a48090045400c05d14160000800a503100d0940b01990120401a000a1520002080410b509003c0d003100c1742c2e03c803107085141d400c00b98215690f031069800d00070302002c008003448080040010000d00a01e031070106903559908842001000517031000400d1209540c0b020012405041c40e40414107204801801c10844501c44882 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 777214523 1250 777213273 777213277
    0x90206070b1012050601090c0201020f04090b0315011e050109080309120a0c06050712050a121a06030109020a02060114010503131b170c010c08031306090f0b011805011406 75
    0x300b904406041c000020810510028081801d0007200500020350400d0304260903a02007200031400c583c0140008141c0c15202030407201160001c11000982c1ca0281d40424182145130720207640704201c510002030300c00056065043c400301400c0c2642212601c680064a442031540a403840e19403003840b0622030717810b041501c4034540c8030030400c60304000810360340c040424005410030030019002284110030844280c400c410b42c0502410b10600304810bd030001850b010600d41c110780400c1d254569600c09840920b0b41c0d01c14200081c105a03540d684030f1264401075480f0420400052244000018402c0074629800c0c1c0b0001050b95075502d1038942c10313108861408041000e54074008944280d40850324042c00841c010403d420f101c240308a225008107080844018072541404040c62603240080e085ca011280e2201500d0007202202c052818520002c25070080010107043d0464180000e22541e118285c2c104d03201034416503111100c00d4141426646d0078800c61907450514002014146001e0f00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 777215773 1250 777214523 777214531
    0xe07060e0f0d060923030f0a1824030501051c03050c15060414100314030f160209061f08040206210609130b0105270108060613090206070b 61
    0x78a0000c55010400154607812060b01141c80c0c6540c1c400507400c010a08a404041d1101200c207034102d840d201c03941985038031400d1103c2e041c600c0300007005440c0c18040c8584540c224050b080d8445466247d00d0061005c4202c409441c1c1810317000c0c1c1d003401002c2c1c0300e80a8030303060307640c042d0a8981d00c0c03010b20fa05290740c0300040800c900f4041d0512440000400030404050190800c404c00c0240d0b05200d814001100c5801a03000c40400c6013200b0000d9814141d145041100e40c05114481910920181c007411401041c0c07041c003c02070300003403600182c444029180c80f500d001726801030f5140c403101d003005081024a40c0740039a14940c4c1d110500070324044d00f5100e9006001910161503c00c0c900013612220344031000007040e0305064001c2c0121400d040090550040407d1850031300d51030b20703403503080164034144190340c480e441c422f03101c4e110004d4440c04d00e95a190110201d40c8556102d00c50b0a48a01c02160401e02030000549a0940a21640103040c05150050150340c80c0c80c490341c549003003000d4020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 777217023 1250 777215773 777215779
    0x9010204080a060f0e060c07110a0303020616092d060207080a03140f07060f0608011a040b03030702040e06010608150901060e0f09090a050f0a0c0e070c0b010b0901030b040e07060e 79
    0x146602e0400c103411b00016104481c40a203103603950324145001c2000504820001b8000d08000d60148002030300014041d80200d60900d0300480151022002c55582c405a040741d081c1c0004d01e11005104a010303520400c00d0404806501596a1112400c0366140100c0c881c5148590140200c0d0021034001c6110b950f0b4064140b1941d0f141007804030364880250301291044410503684c0c0900825500148923640107481254000d00440401e01c54002d034803400d40304228412a554040706869540070070444141d168068800c1c0031001009040d941ca49000b441440c010034224000901c503843c008000f40200c5034000e00a1a140e424600200c0344490508681c5402c14440d000c1c000c2c455a412045911907546c0c02e00908003000c20b0302d0014203054840035540056408160080002094000501d0075508400c0e800c1072644e545140484090564060207045a10102d0000c1409100f500080c0718605080c3c03014003410626100303110482d611145406000e0f0000c0c00d00780031203842000e6941720700b1801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 777218273 1250 777217023 777217031
    0xb2d040b0a09210210090b03060402090d060c0c02011b0b0403120e071e0603060e130827150a080a0c030906020309210a09031e0b0f040b09010204080a060f 68
    0x1a40910b80643d0100880440308072030690070002c504d81460060322400b00ca1400400c0c80340307080070881440c0806070082e8441c41e00070072022103548a80510290007504164240f140c40309011000e0641c0c0c1001105a000a0740301c47c044104401d40040c011440c3d900100c0111075070350301c1c1c078100c4011a40d042031600f0152200310722440400200310301005010411807090050003803000c031001010180d441041458201041000300d248941131050340003122075002d4480b100b1614000c00e0700d105000c800c408400303d800710542c50030311880c103242000e502520040700800b0b0408510341d190040020490009009400042d00c030038031500a40b480c03030041e040105008401303035180002c0e40c1007106c5d23205140d8800c4616481e820208000040c904040d09503080c40c040c80290700903c0c0d1009408050003408a40341600881070014040b618010703081883d01e02d450174511101c40722018160b600f540d03c0300d10030340800d031020f4041c8200c4003104e1030100206401c0c0302541d1004040d00030120318144c0550340f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 777219523 1250 777218273 777218279
    0x1060504121101113a1b0201050922182111030d050610050703020706030c090905070c02041a3001140a180c030f0c030206040b2d040b0a09 61
    0x80120100d070000c0400462900b0403c84005520300070318400e036801503c1840d03a00080310b50002c000400c01000810280e588400e6400189c496101d40d44035a40c000d501070388182c080103604072061a803240c6c41c2d6824403142100d8411420210419500078004503081e0a440942001d01c0d4804105040f80d030501a4812402c0c040072400c61b0800507090410f1500c41c400c0140d0380c54004034000d010145820032a08051154400075904e540e1030041500f455030315006000d050380a04800700080a00e0a000e11941c541072500030410000080124081e17400e0181542c201d450101e00c0b040d004c01c01801c0c681c2e900c10341c9a0703251918441e000c0c41b0303280c503c45006041007000c03081c0256940000c10071a0f0b00e83c0c500300710a8a0301190000c3c400300f5a00e00040611303070006503400407210100d94000400c1002da88071420090481c981c0340d03000a502c4003000400003040312540c0301800074001004020001c11400b03011089480102440c07528503160300700003c0c843c200400e80074041409051415016031a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 777220773 1250 777219523 777219557
    0x50909070e040c02100e0303010f0b030703020702031902100816120b04090b090609070308090409050309040603060518030f04050616050d02030d0f020901120c030e0604060608010501060504121101 86
    0x52408103d40058012400807a285040e0b03000e43d14a007a1700b0801545150324003855000515064090310359001070010114050500c2a0141d038041d540080550343c040c0402503042c1c8140405600880c052441014000c0003540594001449030346682450061025512803c903088030a800865004030359840208000c2c0d1968825144c1e81c82c4a1401c00ca42c60601d86507203860460001d10340c800c1c0d9408a50709000043c0307800c0540b81240e2081d41d01080a80d554a401130542c010303407c030302d900b081c5400c00010a014003a0001805410300000c404000440702e03044a8491107402e0000300e84500402040243e42800c200a10030411000d24a04078420315540f15810102c40840080c010307400440d8840003a48144034a2180303108c4550110301e410700070400a800c40010300c00c3c200b88160780e0124044201d0190308a07940320813500c0300342d40382481c091030444002c000f60b0061500341c1d8030300070000c200d5a000c2c000301c8095400613182c900700d0f100c090340c0308a11015154500350401c4507600110940784 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 777222023 1250 777220773 777220781
    0x20703060e0c04270f1e0b070807050909041b050a060e10030209030a020f0112020a0201021803010b0303040e0903160b190612140312011805011401050909070e04 71
    0xc4107900103400c102200d10104000d0f01c00c04000f0342034040441301525400107810601d010341c1c541c04804120000c040f81800d034840c0b0184038800d400c3e00c11039008441045111141c40703101d16115192040c094481510407544d03070160300403003030f00b1001810110700401c3ea4150445003031a000c20141818a032548040780c04100c10b40e005401160905040101307614180000c0f50000c644c6140450070281c1890020f0341e00c0300205800390041c00e0201c40414540d110710448403603959028010341d9982d420a9000307000754414030503c01d0411400001119924043c040c00140b40d60080003507081a060000140b07160703501420340700151004000e0240d000d0b9110082482c4240101c884907000d103000d81c00b0b01000807072000c00c4514107103400414040c09818034007500d022a006680010b000602c0ea854038610700ca1844d60b807166103020381c00026680c880c1400380f20046c42441c001d003c5030742d0311b80140c6801d1103412904c0c0d011900034070002007503060091441e0340c000c4c000d1a22030254041000418122 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 777223273 1250 777222023 777222041
    0x19060b03030c0d0807030b040207120e01121d0f12031b0c0a030906121104060e061e0a11030309030d1112010f1a160210200a03091415030702070306 65
    0x314407081c4c01c0040c5107030548502c0c08200d6054800b5440d200c0b0301d41d6686588061040c03158203224004090320603a900c83c200c220540b071041c0c0403c22844000c2400403203000c0c10600007400718841c811610441d4038001c94011150081a0300d440d040d83c982c8090482070000c1581c850940c10f038148011032003108100b1500d03030046d01940360a4032003414400c00038180242c1c460500700c214141034001095440b000c04407801c07150245051407000780c0a03000201d40b40b084c0d22420514413140d400901c0c00144034801004111215203807117208070792401019850b0f02007120280b038142c0051150f003401c1440c0d41c1200300b60400c105e1206103441050a000b5420f80741c00c3e00250801202c3c21014000d0007400b800204504c408500c1071420280f02e07085210030031402c12002409900e024100364041405103201c04494141120300500e04c10401507100d0341c803c14901e040d00002c4581a00080d0f020000b41c00e07549140000d85407190281440c10902d249a2002e482801144900500000401c9143c8114062 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 777224523 1250 777223273 777223277
    0x5040303050f090c03070506030709050a080c031509060f1b0307020a05071721280216060c02011d060d1b0f050d09051c08040b070219060b03030c0d 65
    0x41c50501080000109a00400e401507130341c81800c90081d40c1d6400101c2904407002110303071599990303030307a50101e60400c115880103030071282140000ca02c1748401314060124000079421141c1c1142c14203071002d0303a2142911220503030b8000a0228482400d401c41c0994041c00746203440c111000c88043d401c0d2140d00465103540160072101c1d14908000041c40544001d0480d00b0400c000c00d4100700302c41d500e940d0030748001625504003052800344102d582041e01c1e0311b810288c1ca01020302c3c0000f40d03035454040021441c4001800b80c010b1040d5121a64200f102c00d031140c0d65580040e51000303600559544004918a02d4184405001401e0303d035134000c001c00210112550116141068500104803000040b1031042030204404a4034022030307000c4103440e17452074502400300301e4100c141411424010aa5080e01e0355040d203120102c2c440f5040b00d440390043d88600e640b80f9556988000403030f00c0e0208103e01d45030b00300e442410079002c00e602d50064445550300500382c071320b440700d5172040e54581075042c203007080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 777225773 1250 777224523 777224531
    0x2090a02090616060e120315011b0204110a030513030e100e0a06020a21050f0d1806020903060601020a020609190b03090703150902010c0b040609020409051c2c010c0605040303 77
    0xf0a20b0f0060102240000b0654841401c505105800964000d460100d0300d04016080d000c0189050b80340032b048500d1038014000700b1007644440b0030350007990700c2182e601012034186004201141c0501c00e0401d00150141e0340d2030341500d00d2800304042c03840c030035001204000701560700c1b00c42c90303542258000c028403082c1c000348004680d40c42c06401c5400c0902400c411b0f4051020140302d200c0d00103080342d0028220011480c0d903458440090f00c010054441180f101c0740b51484d81000b0801d4a60090811000850855082c0d603601001240c2d26914500000d408c07003401d114a40e2181060101c3c0a41c407100c0ea030900100c2912a00d1903107054204807850301699010362403c105200041140c0403400d40106401d03c00c400d038940000e04154505840100b1148003c1c0000301444499846030300c0c1c10b40d00a00501000c00d0360b040c40b070b035100c40c02c16041d00945050403040e1340142c0110210842e081244070303520802c9000445c0b403280000c881c031049040c0070740c002d50180014014400c0a200f01d12a8074002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 777227023 1250 777225773 777225791
    0x20a0e031006060f020c03060112080d050901050720071e0803071203060815190e0d0e0301180b0c0d0e1002120c0408031206130614100c02090a0209061606 68
    0x902c100d444c00185004e64020541400f859140450483c1c15209142c82602c4003920383d15240d003a900c01e0382600a20203150200707101c3ca904064108500130700c12a91420140080302c241c2e8111f1030101a60321409030f03c8108100507081107010041042c10410341401c03200d6a652004c10309542c07000e102180d2000c0150b40b00348a864152203800054482d00d0010501113081101c04138150f00040c040841c60701e80114503d84d9003080c0d030040310300d010310701c80ae41d5603031401079a0142940004104480c0300e9401c02400381c2070805c800001c01c01540e0040c2900000391910500540e0b01d40c40301c030640c0903003502da0b00f076400300d004104011541c0c26080d040045c1c0e40e0412406840c8640006001c414048004005c01c011010001068507051004203094101039110f280c0010280180055421440c80c14a41d0028035030594050280c0054402d80b1400100d5001c0c180c102c41c0448030b610001d42c00514500490321207103242e1b003d4450020042c2589103000e014601668440a94000c00c541840d2110441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 777228273 1250 777227023 777227027
    0x300403050a020414091b06190f0f050c07030f05011103071d0418060c03090209090a1502090315041703010b0403120c210507140105011a070c030204020a0e03100606 72
    0xe2000c01c01881d0344041a09100f084552502d03540806d44000403400b541117003140d40c0da40110f80c2d41d88001101201e2815034608040c100c034200043c4a004112801e400c207403a1ba0082c0103c6904c8203158002e00460790955684c4a00d4a00c1c0354810b842540d42c4041b034207060300c022002940160301c2911002030905110f45100d24150209510900890600000303401645d03210003242c144681c0114003160903090140210010310302e440d0069803181100d8180100c801c0301103000351a06020f1030b060b14803603000d0208102684106110a40c0580c410580f01078880300c10307826190441d2086102c20300d000c3d02c010712071800d0b030000c1e0001001c4c2c8030001010400c001c807948000118918904025004d910305841d074600c1c0c81070701c04901000c10703000c60143c0f560318030440071140544d5100c080112042210245940288802d0241c000c5640d0401e00241c00e101001054a900b0741e80300c0d80c03805030642103130b09100282d00115281418403546941c1010b42d1380e42401096458030800344001001e51070b00c040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 777229523 1250 777228273 777228281
    0x20032d070f0503121303032607080601031404110105030705281106040c03061107050610061709120904020d020c0c03060a020c0c0603180706090f0603050702300403050a0204 76
    0x140c001d190003041100c0d034001440f400c00040f40c0c2c00d818117215101584810103230500c074100d814900101400e0400c071040e5080b803101405400c0a9800300444481c82140e08034492007030390040c1110201c20b450405031f41c030500080d60711003428900f0701d0070700d0a401c100100d05640509208120607452041100007030340584e94101c49800d2000500840c00e15407074107000031810380006090252600c0c0704041c500e2003d421105400da03c4001c8800c0ca252071154410910414000c4d18002180c02c0901d1001c0300300506214054046c01740545003029200c400420140d1000c905079070800c0d000c3c0400c40281c40544054180d000141d406020500315403c101828454024038100075203205125000c00460005040c10132200d00340d0b41c80da1303a03031203038142084450030f40f04056900348210200401c4c0940e102584100310b40390311078200005900d600096040d100200c62202c0140e2001089107202c3c2c9401041448842400000d00341421030400c4d1440076030700540040d0b40c25408600010114246441 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 777230773 1250 777229523 777229543
    0x40f0516030611040b03040f05120a051306030203090d08040c0308030f04030201061e06030e01020706180b0a0209101b0c2702090a06051c0c030920032d070f0503 71
    0x1c3c503a1328060034149848030383d000c05403003d0712281720301c0300150400104204c4148004081e071650380c0c8074440038900400030b03070010744660301000c40d50b0300002d2860b0107402130700e0194102d1005420481e441d8582103a04140040c0103550601c51090000082900c00c4011030042040407007142d42c2c0e15043c10042c1c2540d0a1f603014041e01e0f0609030406417000c0d4a203001000341c40c2035190100c0e10071000201540a40200354000d84500d00d0081d9102489042e000c00a03500b5104412400c080d40c1c03005881000ca00a0216040d080b11703103d19000b0b2400c0c481c541f407250204a0800c800c406c0615515418290407183e0004001d82600c56020850711404140120040721100029840e2030b42040119840407081c1c4590700c20b000c0d000c981d028109818090301c00442d1700c030b0b490820849a4003040100544120301c41518410403441c06524600f8a1f2002c900c2205030140c01000c50b1411410740c041d0070001150310140848400c0206c62092a003400000000c1400e060002d41c6035082904050900c51600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 777232023 1250 777230773 777230801
    0x62703122d1911071a070b1003030e040e030c070b09031b0603010b1b01112706120624070b0c130b0904020c01060f050109050603011a0304080702100804030306050f010c0605040f05160306 82
    0x1009c000007a400881540840c1c4c0584000c90428607a0030400d246016100c843c00c1c95008001d4040b07540d10003031010b4505600e00b2021580100d12500030386000e0b0f40c1e00440702d50003541c108014440c01840740003c0540c0d00c990050b1000040d0003003441c0342140d4904041c00c090400c0040d907251801c141c2c406050703c50503a20500fa010700c2510700081d00a106142060104444480020320545d440d840300641002c609107200c0820b0b030400c40806050390200004440400c00c0e1400304100c050583e00399110014a003603101c0c5c9007070501c4005600c0390410702d071880d4415002c100002411000b8010500101208801032107070b242044005050500305030840d5000303000620042006208103000c0c848176000c0140c00301d03980d0b142d03420300040b21f00c16110040d41104e45c0a004025180d440300203584550702a40c0c0c1089030548900400c004070741e0503a00140018041e61031003005c124aa485141c11030b100e44070103400c0210b9031f5100740c140700422218170079148540c0d408000f0b0184a00039452202202 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 777233273 1250 777232023 777232051
    0x8040303090311011536050702010b12010501030b250c050115090209181e1005180f0901020c030919051002100b062703122d1911071a070b 61
    0x1d4029089076002d6640b030011640711741c0408c0d044da000394480d141141010304054011203e103c4028040c1a00b03200c200c9a0700c1d008000100208004011282112908070b08240c80440c07032388046500c5880c0d004192159540c1d5407903000c1158102407941e00030701c081d41d409a116003840c030400403103860400030080f00044040800c03a900e03410003c07000400140c903030154171a0301c80941021020342c15410030b6412000d841c141c40740c8003406003030591080c0482c8400b00d1036962420446800d034010006050350740c0d8010f2200b905240f80c00b01c103898448440c0310903901f03025910f00001d91040300040c10301000d078201100044a1401071300811511070400c0da683d601d0f145601d80740b00c401652618600c1a20b01203080c050700541d8041c001d88805c444100b6401f9150100441d40035901e2540810b034400d90200d0301040500301311031106072059641101b190400a43e24000260381010b4007980703110103801148404900d4074800416001304c186220a241d441d26120310304071411041c040c007045010410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 777234523 1250 777233273 777233339
    0x21060c0a140f070b0f0103200a06050901030b150301081209060d0504050f1c09060305010b090103021c0609061715070e210c01021c080403030903110115 67
    0x1003159054001c0c4071038800340e582d410032202040103000b404401040c0b805014140700c02001d6401980d0706980c041c4902080b40c20702c5003503d03090b4581c94030312242c10010703c0302c1c1000712601460140120b1030341070402180001070100000d42402104910b4550040040010b1041d48400c00c24561520008000249404102d5000842a00030b091032030b40015101c4000400b045801d010102100c0c070305030b0071030303442c0d1264600002c0c034000010102c2c0c00180ca04900091380602c2806014101c621414616103000c00203130044001c0e5000c041c41103040c203400751040c01f1040c400e20986000703040c102c0c000070b02039040c03060400d004c0125000d4508141d000392441010401650906030708146603061403a1a50400008101d021042260440d02c000801030b0b070b00f60360b0f000841e0308030b4990b20903800e030b0b9034004900b8060010240a0045d07080042d10320400103001a00076800184102d02900301140c0b00e49290341c490b403e445a106542c40c000050410400400d100f0145041d50107070180000c0c04080c0c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 777235773 1250 777234523 777234527
    0xa1206051005120703022713050c0103140604050402060f0f0d050604090218041103010c110d0305040b070c05070e070315050603130f0f05060f150a030308010501030c0e21060c0a 78
    0x51300c1c00301910501100c403156501003504541040c46003121400c3d4011482c1000c4084000760315040140c5045c090314104402540c4284540302182650707800e40901c0d41c55440c03d03c002082c0080080384c10200400090b14000c080a01030402c0c13016024829584e210b01001e4a025504090202409641840c03040001a601e46a50075950000348406c04465500c030b04155620410003810303c0e03003551810080303031909584107401001910581c0c00f15899001d66101c11811140210343c0501450b0a40d4003203500e540c8503d100f401d40900070802c542c0c101c0d45400c0380e46003c00c403e9501d9030200b07903519000c02005000c914603100801c0c08882103070a501d04503102006000c2c1d148801040c00c41005584420482800d050408940e00700b0111407840c98080380300c81c101101918201e20140300c1c03841c401300034642007440400350703981643e41410b83d0b482d1000550140c209190702d00184103a0403280e1006844075400400100982c40b030343c01000750211403140c1080b2018148510400c030801c08581d400e9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 777237023 1250 777235773 777235783
    0x50906040902090a0b220f081e010b060a0c030e09040c180f02030114090907050604060e0102010912020c010f231c0501030606140621060a120605100512 67
    0x79240303100c0560b03181c824400055510495404c0841d07241c00110b0710380035074406c005070128030004011030007020584070395016801c10b8103031140e0011a4803179050014802c42c2000c4a141210700d882c000716189079110005042c58006101c50320015176200303240307410b140d800b000c52810150140c0314540359003429150601c0c0051107004180c80307003c0c0301c606982d0030b542e16442803469401d6000c0441d181c2d41c40e100d0181d01e03601c03050007040c8a03880203004101c030000082240001c55800030141468036103030040590381100252041c0b410741d5a1840c1c0c510100b807023614142401c500d6980901503401090300003400864000208404025000d003601c40d000349050700c0020020300244ea610f03111030340da6039203c40c41c00922a42c0514030381840000410808036402c004203945a440b0110800001082440060702800d0501854202041a40680700546030101600020054504110300e500c40307101803800748405504480096030341080120300c110103001ca0703014100854613060455071050502d695a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 777238273 1250 777237023 777237029
    0x408030a14040c1e0f14090105060a0f0c020f040f0f05090109020114090a0810020712140706110c0a03020f070f151d090108031e041208030a06080613060c05090604 72
    0x6008904d40706540482020921300080000c0130540c00441e03220600c12117550840759501780500181000428a40390500c2034514402c026918080881d002d450121010444400140c0c1c104c03060179111407080d140d41c02101a241070b04440461005805001c0d0022a50001d281480d40d03458040382900503a4850700484034601c01040c03a40d1100228000222809029805660988545d1505c10328150894001e05015030144900d66029490388400303580100c07400144860642042042000040c802e502160400325040c070b00a00349101e18041519051508105a01682c86418404c1402c07604002d4031000d802c0203040d440a841c5444003a500411030100c80c881032012068820090351241c180c011152803000348041c0455a640c4802c40c1c5039803020140c80060700d40c080c1c000041403209812101115004403004184038800e4444081c00d40020b8440d6804d641c032010001420302c0d08200c1280a2100380c01d8003103001c0382a1418904455004005200740201444918035980c0d82a06640131 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 777239523 1250 777238273 777238289
    0x5060417120307021e010c17071101111c09170309011404080903011b080a0b0607020307030812010f05030a0212150703020c010b06070c0302100c06050408030a14040c 73
    0x14030400c154609081044a862141d4220804020450015400a41e0110420503a40040c100401c0000450300b41c07480e00013101e003ca51045040c108106106400542c0003a4501d0f22091001c4101c4100d800e54010340c0842480c0c031008034412a4115048c0c0519284c108091001c20a0b105a5035854588005440004401c10000301c00100081820341018400301024002c2041920701071a1503446608407500c024040c0d8a400e0074030300400840d0105072030200c4103803602e268582e50410940090306a10440c40c5e0449030a00ca1400181c4003081120060751091b0b1029443d0b41c03007218070b82208503050344110480040441c04101070389010031003500702601514200d42604160849a1a01148003440c0f81e500380c42404024116a140d07019040c500f200744000c1c0082c84610701000540d0061150190450012980410041c680106078402d10307802403e1142c030b103294a85440040740c000b11010b0360312100000130400421004d00c035a5010441544541d41c1c1428075072250180b14045001d4049 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 777240773 1250 777239523 777239549
    0x81507030213030b01080d0f0201020c070b090102210d0b09011a0d0e1b0f0109141e0604080d080f1e0702120d060f0602060106021c0909140603100204050604 69
    0xc4000442d03070185000c0d40d084451080c180d43c2d1101000d603201c491220241c0081d18049a804c11742e07206008990805120800400c806402d11121a08a610400440d8158032400a0a514004c00c084010380d030b0b000b000c05101d80755403c10380c805051310b500f030803554810302c2d8000041c003034011030000f618111031180805036280d465511030b0200a003100700300300c6414032130300305502440008103186030000c140c1502c2ea844521549001501d19120a01071743e2900030030001c043e0b03c1418405040d13420021500d008085500403003001c5400e95006800c07500716a00401009070030103801400c1c0719001084000c1c0c21030030b03141015030104100e01c10420000c1079620030011400300c52003004160896100215807559070407180d80030314000c1031030f8440c66040d80c94280f00024168000b01d0358138101c0d082e0f900500040c0003008100c0c415503021060560911280c03c03804544404107224819a108042c401e0060504040040524050f2040c2c00300e810940104010f2200340c4540307003950304992270705400340c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 777242023 1250 777240773 777240787
    0x504120f0b0c09012c0402070c0f08161406090f040609020f0403060506120c010c060e12040303120b011e0306031406010501081f0314150a0608070815070302 69
    0x39141880c0c04405000c155a440a02c840201ca90300206180380003603c5403400c00091954004280d00c002034206104206003860701003d08194000303001140c440c20100c08065100d11103412000465008807440b0f034064401081e04104a040d81c00c042c104034010b2003414030141001403854401c41a0f07482c003c440b2101c80c0407141d29150410000b901981d08290340301c5681403102c0510740c100b40700c03c1d5201d90030480410043d003406c5c120321850362540c42c040c10b10100381600540d00556240800c450031580c5000300c0900040510420702030501090b08259182e00d1420002d2081c0d2068070041540d0b8582160312405a07082a140042c005c0804022481408886000e900030315081c1e1001d441c0e00d031154427a200c10040841e030203050728003d17255801c041e160424800e40020640c144001d4540101c0d03810700219620800d09170303a140f001f00884400c0381208004403180c2009a1740c840d0380c5034032844140501c00090007030b50040c0520b240205012802a44031800c02c5c0ca001d00781c0010b15900044603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 777243273 1250 777242023 777242033
    0x305120703200607120207050604080c1f09060e0f0d0f090e10030308090604081c020d0c08040605130302071809080f0a020d0e062a0f0a0b090a03050412 67
    0xb11038400144000d85062a251103580c588652049a0590014400e1785040450001078070070b4034156600f00c0c006044c00c1d691a0740710106607114982e4640703603114520300b103454200c800c1c840e80c101b0010554042824a042d00c0d010f000e441c0c0454959456822034216034400c488001524000001c040c038008020034070740d20058914410300d8018a6405408a0030811802c22b041c150408032807095071a03603500c1c2d640040c6270761a50020341c4c0041c0300c0704042260303000700d0211103002c01e80420750000052070320464001e0842144c00783c2642e0000704565030100814010244506079011440302d100c0054540c1c40c0d03070000c0d19101d89014015800c506594541818442d65109201540c0e1200c2e80076503607200c8054445403034001089500051280d80b048081040c0b142400180110000d8512418004055254048081c9034219034155410000003011401401c005c0110350380110006400884014100040e460b10020319110941d4403020200b80000e82c880c040b5000c0300c0140c049580042e10510341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 777244523 1250 777243273 777243287
    0x151005040527010e01151107050603070809060f060f0d0f0c031a060d020a030b040201020115120c14010e0d030e060a0815180712090c080618070305120703 68
    0x12581e005100d5000880d1041e4026081050410402007900610780c0d0302c05506180080034010020041d006c0451108124058000c9280300d0503030b44c050700c00c410389a01c081030745500b00329000d40c0000e07649001e0107500c00080c8806604101044905101d91900c5404a900070424801650041d800314100d04180440f151b040c4a05c40c1d40b0808494a03507560b8205100003460300540d5542466612001c26040e1810382440811b03141d016003402102480d6450f101c0020400130001d0381503540380c0c0030b502002e02440d5111005070405043c14181d0319442d0034a100300c00d40c143c000000c140140c034607802a980e080030054070180402c50340102c401819140c00c03280841c100344407030b0f040031010400c525015080300100380b0031042c1401002c10019003204020309240b640404407500d041400200d202c66105000c3c580ca40d190140d40820030381c1d0269903035803000301e050740300351242d0300b0840600c114240152501b040ca4048036004091617821611850b03182d240d80c10301c1005100d0001120b030100b500403a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 777245773 1250 777244523 777244529
    0x308060f04060b0a05070b181005190516230313080705060c04031707150f15120c05010507120c0624240519030902060a030f060b0315100504 62
    0x785944c1c5980400501405035040311070200c3c4c80040ba40001088006100c100031310310190b010003046804103401c0d0100050402801441c11a800b44014074402e00b141d014982c000e0b14030480324407200d19482c0c4010b000c00d0001110050032454040ca000c0850401d4094a03044404180034000d4402545408009441100340003010703406040100050042c440018104480c000d0080300c43c4050410040f503030034403883c040280740b1200251295181005a03001c08101d00d0440c03400581d90150142c40401c15481c2d9210a584e0340801c1440c404106641194000900003820040d051000d195100c0c503102002c3e907418020003805c407070b80c1e200b84000e5400c18144a11400e5800d0485840d90301c1c0d005107119640078051f03234820741240600c40c00d58680c41103000b018487c0d8816003055000715540d040c4400d26440e0350b04042c1c0b80d28454000d603035401c0062080c2d241caa01c001640056050440b0b040c1c94081d0301048404170b080c01048000c1903500c02ea10300080e01100c2c41141c00500c142c00755114000e0390 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 777247023 1250 777245773 777245789
    0x201510121e050718060902040b12220c03050f121806090d060203060906010e03070519090e031c06060e040906063609030f0818100b1306030308060f0406 67
    0x800250384840107124907083d01e40c441c0c4c28007807981c445007560168404c1e846008006103040200038a030071000e103220f54000100e80c0702081d0b500300303000310b82c2c6002c1e010704819910b42e103424104104000c020804909000d4600000c1c02c2510741324070f050072941c010400d01c070031440b05084243c0d21640d01c0c403084400b0694001c1c0070002011442c10000300a41040369098082c40c001f00120b40c640d80100c3e030003d0300404c000c0091240c24100010b01c000754840d428104052b0b03d86010200e0484103501035082202c400354005c42d1500c11ba15084128000110050a5a6450941c1c24801c0b070340d00a40c0c030510f2400658010513000e6861034080014aa1903021112003018101024030342c11081084181c0100140134078070029600e40d1791310007154141d10004001c07440034410341001602841c15a54041c4040d02c3c101e070074140c03080b00b480c18032282607100454655108244c2402d840c280307a00812007400100200005420b60f507014004000c090704282c4649403990852035180d50300d4000710060103181c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 777248273 1250 777247023 777247033
    0x10903170405060d090605070212030604020c100f020c281218080c0a090e07060f0c0503070f022d041d03040803090108010e070e10201510121e05 64
    0x544401d60050605c44001c44815081c000801e11030780c0300040c3c400b0314611200d8940c0c82c540b110130810000b50302ca00e110562602030f002c104c80d0079100921403400302268210016a441421606440c100006100c0b03460000c1c0c07141041c0f9006104020381c141006511200703005c440e0943d10740582c1d00d800f030b512a810a07007000081c089980341c4082040c000003001500c088c0032039510b524981c41030714040e046481e9160b000b06c1b0200800340c41020f000d8080a6203007171140c04002640c403400d041d40d0004809984400c2c80a0542086092410b655201d007014000c014140340344141c941807441500541d42803043c1d40740c1141026404c03641221041040307080003265911560743d042280c0b81d8208100480c04144047d0001407140c8241861030b2180c030199407a44148284241041030315014110f41c942040000c041001c404c07071403203100c0301d01070010f03c00034040c40d4407002d4442d12489000f86500b01c1ca44420307408214500031603045d400210b9004460701c514119103842d01650002e10722002e0001c0c814 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 777249523 1250 777248273 777248287
    0x13050613080f07240e1503071403040b0406090c080f0c03010f1b080c040509010e04050105061f1412190605010503070509010c050a05010204080f0c04090201090317040506 75
    0x351011021588107605881580c400c0031180c0d0b86482d003510407041200c0701c0c2c801003406251001481d00212080381040b4400e0203046000c616941e02080c48034001103400818000c695400102c80d4900b5041584a1480d40c5800e9446060012028100501d8540c403443e0440401080d03074003241c0030f0311100c01190503407141c0003503165640280410540c001d511300103031a0f0402060b8014a6005018610801051101803004aa01c46002040040d03070700e000b8880403c0b240d48000c400f0340249401c5d1801c906030304080c105a803c5510140905102d12013904500400ba03980003c000d07401c0d801c03070900e648141181010100b03540309034a0400302c0400710b030081001d0240d001100c00e000300311050f01042101d8982c401540d6501c015508c4038041101403010280035032007254440c00843c4607005803060a003042d910300e03007a40c003d038028078023070340240c5103024403c8000c02c03503103a102504840a02902c0483c0d000a07003a40c030b41e400050b01c540100c66806240c412001d080b40c7c014607000d401140e031040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 777250773 1250 777249523 777249547
    0xe030102030a0b0a0b09060708130b04060e03060a270f120f14180d060209090103080a030e01020f0a051308060106020309270106120b06121b03010812130506 69
    0x180e807103515100e4041c90001240b0014468207591441c040506808d1603e6042d4880d0301080c3c10440100d0301d02100e007503001c40c0811040f4041c000800c01038a40710340d41c501110801d0b00380040100810a607038500b55404807035680e802c1341a68500c1c0c03491502c41c4203040c03a0400308043e0b0413030b90b40503040580d5020505071807540100701c5c00b034034003440e66448400482c0407080400c501c1486051f0b4803584462a0120252a040c2040e00000340b09140c01841e128910780800d408140c01d07881607071075980c045401c5514603018083c201004807108000c619054082118403a540600c0084104016000c55045c07140c01911691002400b03001049070419a51140d0080d41c941c440540c1074040c030340c42282103034400e02040c008031410748003514200d1142c0c01c2200803039018035a01f0364801520b072101c00348a00d030344807a00184860000c10000701d00b145040328040000801c1c0501003c08400100010031001101103407000c11161a01d15080d950000c1003440441c41d5480d401603079100c0000540716903a10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 777252023 1250 777250773 777250781
    0x4110705060601050703050a081e040b0108160f1203140d090201021c1e2f01110c1005090106090c1206050102010507140d0204080313080c0307051806010e030102030a 73
    0x14032840480d521035544034011a03480c0294000103000c22801e04c00c0c1004030b03004508840d031080d013103080b111540e0f030814080c1d0b00615090b03070160751402102005020840b8144140c4c1c41c000113001ca01c8025610b880041412a1107521420350a020030851400c01c00d4440e000608000d03184004140e21001031400360801003240e441c0407409441902ca03d6001280180d0107540a5242c580303400d40c1003c002c841348a001d070010021401080240e04c4450b4001002d1015410801d480194182c00341d03107200006821107a18500c1c141c0703410024400820700c080c00142a00004035a108003280702e4607000449409040503401c016104c80c1018000100380d0313800610041800c0582e01c0a10225131790b000160301f04d88094440c00001840301d8858440c0c130081000030020f03d402903030014946562000200d00710381105494240c2c0d20240e203410400e5007010000c09910314030403005031030940d00c1c01001692116100c019415034041d0a000260350340c0c0076119403840f0081c007030025941c0b40b0704909031000034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 777253273 1250 777252023 777252037
    0x7030b011401090302090403080a0902030d0e030610030c12050106080d0512060f06030615070204090c03151422020307060905040f0b0d0204022203060501151b0618020411 75
    0x100800c900504402c0d0b210f01000411290050000c103980c0e1a00d46040b501c070400145a40c00003902c642d00f85005031810050700c02645015640c12440e81c4040c002c040c06c1440c05000642602a491003e00c040750381c9146034021101044004406101945806c0340540185d50105c001402541d00500005410000412403010b000c0301c2ca0442d550b0300b40401c00240d481e25030140e0402800c1c400076105045c40042c03480c03007040549000b81040b02d140c0c000703000d0707401d0150112901c8020030340400c01c11401c070031000c2080f0451f51040c070030002459144241414001d204028003907002032a155507000c0c240d15154100e801038127075202c464075001d000c0e000552603c5005d02451401d00c0c22090643c06108240304140300402c100c5141c10603800b00000b94211442440b21001d11074800002c5c80c0950100e1801188038040c013041c5585802211b42585400250f02024824841d01449070448941c40c000a00c0385d00046c00203080d054003000000400794000003d40042c0781c00000407140444202900030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 777254523 1250 777253273 777253289
    0x13020c010506120a0b070806010c02031606021504030c0f0c081c1e020c06072f0414010e042a0602031e04060c080f0d020a052215030b040e07030b01 65
    0x541d044500f29078444000c0400381c000342c1c00c80c0101d000d65218225035500660145448006070b035003900081d04040c8007032030b001460444441d0401495406101d144888080c5444d151154503060300c002e884c00603040c0000348154103002140d02044001d01d0441d000d0301d01e65088520001580a0540501c000608020042054031190015903403005840012002c0c0c994060801c041842c0140401a00152001c0703c0402c52500003240364080603d580015508640f0713804005101c9034103100840e0301d1151031122586c2008010b00c508000341c0d4180d5000359108100c0d908c0321080300003c03180000f502c107083c0c01a120000002820035400405801d00246443d484040048142c040780d50b01e00c02c078800c030700c0030540c1988a1400314091001420051031001c00e45854880000341d1300089a110441840c0811303400704070f80100d035000d8502e50580d0764040414a50a604001c039240c10705014104030000c2680f6012011055141c0d40c20042c0d80389003003c21207003520f407685000365140d0401d00070070341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 777255773 1250 777254523 777254539
    0x71209081b18090a031106010819021f090f090c050304110d05011a0102070e06030705100309240b010201060e1617180607020109171602090406020918150d0213020c010506 75
    0x206d10b40105d00a412180c2e4100100300c91500740300b60030146003561600340d03031000c0d1036813092100c080000da5281001445940f104609410000602d00e0140c41e41c1201843c0c0340340105a0f19501d400100301d9410941290490040e4101040040c0c41c1c40b82d0404014070341e500b00500d40440c500c2e100c1c44a19409030036001d0704c840e01d88482c2d9110f4002ea0480d03445505a00c0400308003c0790030440030945444130b50f49400f08040704103445140070308501c81075003c0030b0345210a01b50700c0203005101e4040b00c10070910003480f14620b0704182e83d407031400140941b00c440342c2141c03065888c1c0e8014100c442c10040003207848011882c0c1950442040406055401814010784000840c038030b2062207500d11481d8002e81031505110b01b28141d40480d00040102507043c1d40000b81000980e444460180c8918820b003c0544d80e28018018815980200b02100d2200d1043c01c085c00000e05038080710081420094030354500e14012800014150385100c18240300961002401040141064000310301c112425a1448 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 777257023 1250 777255773 777255797
    0xb0315040e06010b072105210402092413020309150c0403030c11130b031006050f130207022d01080f0a050702011b05071209081b18090a03 61
    0x80251091807034455a507030041001801056404c50151100c079006440c1e010858540e05103061441c506995100007290000c10081c12290b008000210307410103211122101742011350104440d0743e009005074050840c1d500d14064281380003c03545500000041180340703600c0d010240080290300640d40c078020303030003500400e805602000d80302502440c240c1c006d0900e40303459620700b101c00400c1500d044901c2410491840d465540b42d000b5064400001080000d1030086801018940001268042d80701403c000007082181d5460380e01400400094500d4a000118076201000070711a100c002988100d40d507089004c2e2110310425030284000300c10341c4926560700d0130010359511200b21070001d9020381040c006040586660011034100c0182c0c0008226024030702c1403400081411b20444d80021000700c1c200d414400107501e10200d408003410300b80316550422940725140c00d404160074210307a91499003100692281d0340c0c4070450580003000d404043c20504000e03500c4090760074040c3c0004489811300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 777258273 1250 777257023 777257029
    0x406030f0f0b0d08030901060e040b07021b0114180a0e04060f05040f0f0c1503020c06130c0339080f01110a0e060904050717100b0706051f0b0315 64
    0x2e50541c00c00200220200f141665881d1078551004025450f40d540f0b4050014601044100241c0103520664081c01d1601d850300d0020700d00f8040c00b407841c103114140c04150702c00d40d07000310000d40c0707110341c6024259407000241d403103400c60218402001c0e08049112000102031601c0711200c0e00481c40354109200e0f9802210b08082550400d82d40030b40030038091020070001840c3c2c081c1d2451107504c1010806031659462059500c0d69101005442c08070350009040310100b141403100b5a800391000e100c040700c580d0651900140701149000c0100f2010041c002c117000401c0b85000e030705607603c030920305440c00300203503001e03c01c2d80c01d05125603401e503c110070781401903a2041c003c549901e01c41419041c2409140841150061907120350640c010f18200b0040c541c540303850041900c01c10f40b580356412029005180e038030b9078400040c5070703010001c8107201c14004c01528804442142da0440e40108281d203903030780d1040c040004500340300e04082152100054480351140550304c1404c11220a0071044070450034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 777259523 1250 777258273 777258281
    0x3011505131128030506090f06120a12180e010b07050304080106081c2c04060503030d0e0601060206100603021b0115080c06120a020d0b09070c0c1203020c1011030406030f0f 76
    0x10301c42d44001094002a242c0d0f02310b0314600d0b0700002c018051050140b048000c6420004000d9068503941c003000c0c2c54000070741d00040d035840c1090b440c6403031030140d61400030b41c0c500101040c0109100d1020019519050050403c02d4602424080c4000c00c612a40c0d507003c141d48000380720016060600281003140c8880c0141c40100f1040303c16140e400460403882d102d41c890850b040b20351a44142c0e21080490591400c02c00b5100394510040001009403242a405107029016401071003158042e4082000000394201d0203c111031342c0d410050303242d030380001168070b154a0390800c2868640c80c003030075020b54a004c01c54580450303c80c2001c1c2c81d40d283c0c0714401e00c80c080c480d0800d220341c14000400899641840b40d401000403218285c0f0024940d11440001907104100f1f5035100d000038150042e5105003daa42c2200c2c00a000690800c0c2c0302c0001c5980181d190040c0208440c0704802017049032071658002c0840c80b0100ea2924103680e99103403948805030040503c008050106407404101c00c2d0070000713070700c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 777260773 1250 777259523 777259531
    0x180603011512140709090b06120f0a0305090d0b041b06050a1709191208071d0913050d0f090803040608040206160f0b0114030115051311280305 63
    0x100030072125a54031460400f0050282c0300000c0c0c40707900c80000c0c682005100c0d134118280302c0c1340f585d020750402008110318083c900034094145e811250001084620004004003034590500300350781c6600c009400100310600005014000e41440b00812081050102e140c0340150740c4900e5070400c1d0350721200200c41c58014110720401084024a201c08002840170346150f02c480300804543c10b81442102c00702c0c82c01d0115204a5040d03e090119100039600140204d52140443c43c100002040d034410362200e60078125000d5014400910116601180d030140443c1e443d50000100d031104452800010a12004242ca03031001500605010a100c000842240c2c00ca03070a0b5030342d4031080d460b1902080555031100d0041c00440c00300302c51030800201c0c55240c3d42001d6005644c4d0307411079850b000e1503509990780802c445100b44d250507094140038038040301c0b16050342d800340c516403d5030b170082c58200c2c000d2001100008040d000400c10900300040c0390301d076118511382d114241801034030321201682600d000395 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 777262023 1250 777260773 777260789
    0x41a011205011d071a0903190b2a090102031210060905010e03101107150b013509030706090f020f0105070305250f1a0606070506060409060b1806030115 67
    0x261304111001e2406114503d1030044081549801302d4540000c0c504840c45156600c210b58900c1000c05018001c2e00103907101e024882c0c0c500c0740c1c0c0461081074200810141c0001411400865a458a42d00c20005e842d045010300500c0011400c0c1a07007805e420408900c0340310000303140c40c2c0020400794821010030b6400360003c4d004100440000d00c050003d081101d90310b00d8400024041d5401094001d89041d10320032115200162202e0b020000405e4680040403d24010250052161450340d0001403214110440c00a1880380c1e02c0c0d01c201c0758154814a88050035107401c0c203994405000c480c2055101840c800c0341c1c903400c00a4044015107542c09201e5010b404100d0070710699250581840e40071000c610300c2c001c40240c0d4225544c0306400c80030600700940380000b03001044141813020b00101500200203c0c3c0c41d5080c642941e549070355803400100402d004035103408030401000060341005600d0b2074001d008202c00c14003102a014440c100f200d00511079800c01164141d8408a0744211040d20080c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 777263273 1250 777262023 777262033
    0x706020c0409030c0c1e0e060f0907091805010927110102030f121506040b1c110f0a1205060f0f12030a0c02010908010c05070b041a011205011d 63
    0x4004020081040950540601c1600b000300d44c0020200400400506a1a241c2182096040c0201c0301c001c4030540000008411403c18805251780d0401940c070070100031108a02c041d51040021030360345046a000141c00070001e0040c950318441da81200d4141e503521042007202800c0d8880b1809030000d0f5018119070590b502001c800803c080a8009016800600440c0c0c9450442400e80407154002914401c904411405208100001140072001c0320b004555070750409085c50907400c0c0606ca01d280c5004c0ca84a9100740070001d450340d402000000411030245600c917200710700200c941e680400ca4080001c2e4145c20400d40b0901c940c49424040c4c0d10107061148070040200c14091850014620190300400b544c10310340384000c08000034000c201c0f03182c1c3ea803203858500c0c1c400501011000c1d00721403c141d0401007060b000650010136908410f4000c58044400e8445040446040e04400c0d95041d041e034007880040b4402c180c25400c0b100c05881000200175010008042800c9080e9500b0001070304e03000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 777264523 1250 777263273 777263293
    0x1104030b041e02190e1305030f13090e01090b0703060b030402060a02010b0907180b21040f060203090c0a0b030f0403050c0705120d02010c09060210091502030708010512070602 77
    0x3040c050040c41e0300c15004030107488441030300014411000101c4c040300d140c0100405108011039594541e400151202c110b200030649540e4140e2240079140400c02d00d86c0001c1200d01c0c031180b2100c184001441030b4001003020710030301c031141c602a1038400401d84182d09070711301250045203e88140011144e000d9020750942e03d9030360800680e80c0c04a00028115921203003515015914611301a0094441e40c0741c407608c1c3f181808414030010029401400344810910108111446103101500200b20a44552009541d28508052450896000a44424408000c118546000054444000350122600141c0c41d540d40d004032550b110031a44855401150004103002901681c054003c090780801a5511507858001140380d1450804481189078003544541c1c10494081c0b04202c45034809182195101d13082c00c00c042e42e00c0fa0b007002140035940d82c03045c241043c05440880f20369a400c42000942d03407030802000042407100c003070245912503a05001e82c1000840f00160303400c121801900034044080e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 777265773 1250 777264523 777264533
    0x9010e0c1f0c0f080c06010e060316050405181c0315080a060b1c06020d050601091a16140109151514190e09150103150c12060f06031104030b04 63
    0x481d0032012900f40d0980c5608000080c041000750440b511880c004140740d41c0341c925446016080500514001c2d0004250440c10541c0032901105441003542c0128103500c42c07111014085445001181230360260075004881ca1a12114500c040d240f259018000c0d1703040c4414003640044203201d08600c0d98801f030480c4d0002070849c0c0049580e01070007060a900c0341594060710040241500703003100c41e940d0006005c40200428070540350814800c2c0780a41310103040800c140d510300103800366803a03000d20115051142c50021400c5026107030b03021420741a0070140c81100c501030701c1072940032100c2002d1843e40c024020034078807421751f00c0c208504154503201d1401c51460450b503004a40b0381e40110801400c001100c50040d0303004c0041108000c803070b80d01d20b070130402c041c100001d0340711103050200100010408513494000240240e5104900000d40409802040e15050070724100c2100241c100080007511500d5001c0e00c00455209440a1001401c0010000c00d02d2040b030000402d018001c03400b04000c80c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 777267023 1250 777265773 777265787
    0x70b0702010c080630071503060f0302060f03090c030d0e2d150408030f0301060801090b030a170d050f0907060905090117121206040f0212150301090b09010e0c1f 71
    0x4000041051604c001170f00d10a007003000907000320031084680003184220507858424040140b0700314801c3c034900343c103560016005100710028940c01c1030020000c03945943c0144402e140c840303402011218100341442001d007250800ca1011803060340c001a209040700c41000c042500c2d0950116240d901030500401c00510989140703941840401c14080030034400800c10040c1600c1f0388100302651250315205006020840c1604668076080c1080c0425101d9100051807080c002c1e40486060b051020a4079001824040d008800b000d003401c01083c041840000c500b017a00802138102940c03000f54448206070790104241c8a20741e00f01d041f2000401c001407804849074102d07010503080c0c1d5840a0000c4070b20009402c0400460010440703c0240700b020b10f424800d41d41504100380f03043d414070051a201045d103d000601e1040c003890441900c0b141036a0a60101d45025400b4039806001e0808481e0310b4000d080f104040c103401d105415100704545000322440d08948105007088061320340181c42100c0c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 777268273 1250 777267023 777267079
    0x1b02010f09030b0a0b040509030f040308071e060c03051f03080a050415050315120309010c050709020a11070f0e0112150204080d0206160e0d020d0602070b0702010c0806 74
    0x11850004000a031640441c03501130905400081070803103c2008020880b100504888000d6104000201c10107a40d2030a640c201c94120211548801150030b02940840c40e012480041c0c80100c207240d8100415688850340302c01c8242e404001640d2406038001259080c9140b5084180124030100b0015540c0c00c001c012003404d902d07255050956031070419880603a141c2c0c0382d80100304088108050741c04c1342080c14211007800c5801031589024510595140d129034802c8504100d107a803403200c244103040100170001e001c5054210360b600000c0c880144105c050202801c514000c40c2d00c00102c20508041c08400d075040584000b0322a460b0800403020520040000c8401c19000f001c01010082136101910061000401820301c0c00503881c0e0090034440010001203404102c61503000d0120b07401103820000750020781d10b0782c2c0102d005000040c201881d07840024800740c00011014100310f0610700c0c2c1c901070031640d0002c1c040c000710741c1c00c00c0c0ca40c801d00b200c041b50410344020f498051000d09141c8041c42e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 777269523 1250 777268273 777268277
    0x9020309031201080a1a0f010e0a0915150902030403090e09071d06030d21150801020d0e16030f0b04111002010e1005041109042d02101b02010f 63
    0x103044110b55800d400321100764050030751a00300d91002014400700c20384124000042601500b018907259000400710304040c01060b88039622400014004904c503400304000542042c54a090312074000c02000140c145c41c01c801d001e405462800041200c403e000f036070301550781615040c2c111030500040000c034100080600e000381c400c104000400c0408207054882c600050714100c0d1091514200341440c0580708072444003008040c0450350203000800b10440c601e407103200404111910600d0405600c0042c1d500900041d500c0001c0c146050349042e0300c0380807a080410b05441a1400018003075074025082e11001d084c0b03803000046000080c030b00c0e2003d264004d210300c18003d200103000c0003042d05a81c8404102c40503070341d42c5183d010652010171074081c80c9802c152003441145040e42d151004240c0d90a40d9500a600f2039000c2010011041d84080d58030100320800303140a080044400190360004105a024103140852202814800d1007100340d07582c08a40c014079030383d503075500460b03804204800d0901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 777270773 1250 777269523 777269527
    0x20904110d0602040b0304030806060a020c3303010312050a050a05030a110304030c031b21140309010c23180a18020c0c010806130e0106030204020c010507180b040902030903 76
    0xc00b24400f41025080b0301021540747d141519001e00000405414503101e84800e210444455a0020360341402c40c0d0b0948041100c0d01072810303400c1d4000c0340000c03d00c81040401d103004010000308400785040780c0c09901081c1901140c2030050702d140c4119040400002d008011340c05905014070021900308609050000f074880d040c50b400070558000365400c44c002035003411000c044c035174440135010044000c1d8200501044039540d4407030144c4000d04c803508183c90340c1100508103502030034007107424203181490320740e80c0d2800010090007040c3c80110400070409500e610b0345a640002c150104000d0350685240c80c0c109421040e08801c40c000c0d8503079a0182c401103001c80d0340001070070060580401c4c1480580c48501034110281050181c002c0c1504100301138080002c15a01c40000f01c0319545030380f5000520000c81c110490150030707207410103900540002400000414154080c0d441004907030b58604952005c0d02e1586580001849103084c22501480140b00305070b0664015500318000303c007264 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 777272023 1250 777270773 777270799
    0x1015030e07031a150a36090c08012403030507050705060f040f122301110f07030e04110904020a020307020a170601060c020109061409090c091c02090411 67
    0xd414615000c80841000f019071080c021030800194080501240840c1c201c280503003440203001d41001c10308205600c40881003100350000503107940852441d201094140b00010003414000328980d10303403003444010340c82e105580302c1e07062041c9584001c00130701164240744940b454604946540040300295080d014403000003550359240d000800d41000c065010548503440d140001c0440c2c0c1300d1f58841c0520605031501d1a0002d4001d4405007070110b030050b610701075961b0140140d4010850f125000300384000c0040c0c0d00700410309400103061600d100356500601e024103013083c44107803440c040507401d6440080c409001217191980280c1034a072144d104403802c00304581c000401c004900d60003500c4001030782c5124402c800c0c0c140103950240c05603040001403000d80d5800201846031a114000030004085803541010301131408444003000f000f0003542041c18010811411030f0310840c0d020f441407415000f480441c880e8100604222034005042c0807050b9144c4e10741ca1545c2c15100c3ca11035002c41100e01d20 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 777273273 1250 777272023 777272033
    0x10e01081e0f07090911031f0e01030312050601021c0f1403150a2c0c1606050708181509070503120d0605060405130c0201110705151015030e0703 64
    0x1140c40b40080340c00010042c2440c04003d0720094154100c0701c1c02d242031000e8020761030f20020403288c100c1c040b20b4680c00e042d440b00d10226211056034104200205c0e0180002007070580c000f20060424070f07250320410950320b481c001039903141d100942c0030550416501c0c658103028010000b10f8107418050420385840e860701003002100b0303802103c0040b41c1c1c0c403694440c03041c1810b010098001800181d42550003c03586076504040c86640c02450701c80680c43c100006c0c0314070b10410142d071845400101c01c4161f0070741c20301c0d02c28003078182113a0341307000174030f602c40091080000d001110820010b00b0015000b020907003042d190b501d00000781039602c030340700c0c1c13030030018242c0c038200440da00c0414030304511038a5007403104502e01034036525403103280f25000c00c1c0700c244031613920703441e0802c502c04881d0000201001c030018142d001d8607442d081a02d0020000c110700f420320401048807424001d100b0003c4406550780d000005490000d401111401e0a00c66000404580030f98461030800740c080086424441d565521 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 777274523 1250 777273273 777273331
    0x1509030708031207020d0212070201090510031b0e0f06030a110c03030411030c011b110a080d08060301020a0e0d08070b0c0a1e02210d06080a0302060f0402010e0108 72
    0x7200c4840d61000655181007003420303865a40240141c400740600d07001c800c4000799038040b030301d030320803800c220010f035503c2103a006200040c02448060540c50b0100e4070044090001d01c803014210320a100d01c5580401518491056509070900050002801451600500081b50401803c3e540580c0d41ea4148440c400100c20240043e0201c0000460307483c81c040c60039120fa201c2003e44c01c1e0282e400b0340142c0301e19a8011840100b043c0800304200c0c03840c4501d08120f1030030100c2d20f00040c0c03c0761a8981c013280080c008218085443c0c00c6842c3c080301500c8540c10700d801c03803040701c8000e40040c020800b10307140c5245c44110449068003c5070554100441d5443d04841084141d40760030703c0100c000b400d134000a401c95984152807a00c482c840308104205080a034881c40c10007031f207100004000c1014003208062406444621922000c204500d03a12484a9591050354481c00c0d400340c4104800244080d0410303860340d2143d64189d40d50103581d6181001540d2500c4d01600b030500c6240b40e20300b003c880001c8801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 777275773 1250 777274523 777274529
    0x60b06030901090515060f09040312112104170702030a051501060f05070b191e0509010623060306041103070c1b031a04020307080708010614060406080615090307 71
    0x40009829407543ca0100e00d81711020042c0c4441038004410400c240d5550581c400000d4401d5820394590394881c541129068003410100440c0341c540b0400a044601c548083d1901c0035455126107000100c80034040a900000c071402022f821300800704c155850520400f0744106071010782140d010034401da403a2414604905a00e2814403021001000b82c968411000900100141889132819106813203040c1a044010308003d00333510281021419004d055010301140b00c0303940c0742014030800341c51884c4060303c4107417a12949503090442c003040414403001104203100d4841001c8021580800a000a6401c000c09050340680e540c480440340c181210001c44c4203050790780c1d425107000507620b40070f240e122401c146950140c03124070301407000504d0141048150000d8901e403081d15600c3d840041d28040064001c06000c2c010008000f4010805401ca10240c815002c100113400131900c0600882d030180344a2003000030f0044002ca0110700f85280c0c2e540c0c0812030368160b00d16141c404000b0078a80391003a8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 777277023 1250 777275773 777275791
    0x15030f0c0705060411030c150403050105010e010b070b0903041814180a20030d110c0103021603030c030e0601120302010b030705010e0907020708010c030903020c19060c060b0603 78
    0x422811091912065911801640206080003900d03115242c0c0c0e040020401410038640c0255602c80f6541005403c44100e4010f00c1040a485502e0f0310b00032030341162004940035800c0200100720100d1407520f99059601c00f5070b515050402e55119500701140252160305c80b400304200100e8592492280303031202480c104008a40e02e03240725005034a1400040455103219603601d1a261071030400300d040072400e81c000d14940a000c1100300c4024400300500060380d0701d442680c00f85503042d070b000840000c4000a540540d8540801440154240e01c1290304a14101c0c0c41035409100080c040e07404a0780411080c90000303140400004050b103803c0c020f8108601d0060b030483c0420070181e09008a190440b03080e8050100f0b1450071001809020882162922035100d040018602074801c1020781d00502015002b2302c0782d40f0041b80c02400500407400700f540140951200707a451401d00380103000b941c126a041130080c00386001d400711028207a000c42140c4a540301c00b90805696960030145000703075820 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 777278273 1250 777277023 777277027
    0xf22060e1b0609060a030b060c250303021c030f09142401030f170d060614030702060106120f0608030405040510030b06010c0312090b0402010809031204061a15 70
    0x1214a003454003a0003864011420424001d040c255125a8282e89003001c0543d0f82c030303031250351018003513026141c0c1142d1260004004949107900c1b490001c3c0c80c880c03c1518110200c11028148000707006900e407404054007690104845004601685295000b04002da28000640042c88405102a600b9100c1c003501c0c9050324040c09104000d0900040e4124846030201c00903090202240d849420414440a01803005c3d250070141841001c400d000d43c6c5a0302c0450660340da840d820802c1c0c2c014510382c0205d01c0040c52501c04a2018040b90048034001d0f0400e80003801560305c2c00c4012200819040c00070403015440d071035145142102800f030720020382a058042e42d01c89007000180403c880c401800c0c501c0031356411100f040480c210392401a00020286444001c6c02401d003029a04868000c00d030140c2c4070729002140b02072101d50f01855000350702c01d0340da0101070784860f11080e6032070080400c011850344001001c10300051540d8801081058040c50141c0d18071380c40c2d00042e03032641e58198501001100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 777279523 1250 777278273 777278291
    0x3040308011a090a030b0a1104120303050c12060d0507050301060e011806030314130e0403051b0f150907031b081009030903020127090e1b01080f2206 66
    0x3110500c10310061038030102410020f83d540024095070b41d6110180100401740003052268585410910140804880280da42ca0341d80c4440302140d0750381c802c1540064640804a0010301c05081115113456084500498a0301d5030410020302a0915000b100d16106805000030203440c02c0c01000700500c055040c080039589840c0484101040d04401c1d00d040524240381400083c0c0c01100300003400243c0085607489044007001207420122540003c0c041d0b0302040100020954403000030000081c101800d001e41006a062182e034681d248414100c03107802491800803030031900c0f215540d205103541c04507035403d40e80741c4a800c8584000036105200e071150a07002e11403410100501310400d0390060b03007049222040d480c0100a00d109010081c100040c880d0400d001660280c0401845040c0041d510420395903801d4010040c10881144501c81c05a0728a2410801c02c4001107030542106031600210b507620a14a07003658000142011801078024400f103c0c450801401300d0451881500001491b00c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 777280773 1250 777279523 777279539
    0x50c2703150a1a0f030a14030d060f181a010c06090b07090317030c1c0207060c021014190c05120115140c070b0a171f0f081c030e030304030801 63
    0x1003c440070303015940007242c030480c540340042c11808150300b198140c01018070800050f03085129484011102d5410400080748404440c41c04500700c442c48156480e841d50521045007c0d640c80409160340b10308407071340411595002d0f500c0c0240051140100007501201e660725090045c0060300c030b00b030024107403540078801c000341c03d4107144540012032031803030843c41e06407218451071244103400d500b601c1c1001c555205481003601680c0a603548490107101003940c0c840000d50350a90035150103106802c203942040401590085136000700c05416020003450603603000b840c081d00710811001c1c20080e08000b1004d402e4a00014540689404a0b4906c807004280390020000c142d002521700351031004200d10380c02150300003480c2c4220f82001d01c415464425851040d180c00c2e132003075400340b9404c4403a03007041044440c16032036480c0000030300074240c403058407011142203220700c42c012018150712100012461961050040b5a0300c1780380d260118150180d44821411508180c0e0f0031008104903400601c0556 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 777282023 1250 777280773 777280811
    0x1030818010c0b0a1116110312040501080c090a0509010f0e07030e2d0d111005060a140f06040b030717090705040e03040b040612050c2703150a 63
    0x80424070b045000891603840e109016507000d40300034401a9030365600c00040d0f006000b52a5111035511000115154504150122010250b661403090082d0015070403401d1611050360240c82041e981c440b5255280d401003c229407084012950011141e0000903142c0c2d14076080b107019181800d001400c45103883c1c5a030246042c054641020715040c19044001407a00098812007800050507074034000380b00402180c000d00c19610344001c140280c0041440030368201782201c11288981d41141d07c5d111504042e0001c0f1081565550791204443d40c2c00c00450307004103031103282000024082152004030308001f8043d0350090f80300d40342e9801c0c0403080215164000c1074650f50640b20304001e140501c0c043c0a000d40f41c103198080c0c54840c0d5a9000d900151000400a0b02d01070f000412005640340d0300d4020150260203042c204107801401c100010f1a00303070800003659a4000d41482038900c0c50b510300ea2000b40f441c1000002034051241a2211052441743d030034a03409408801c000294103040540c1c402c401d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 777283273 1250 777282023 777282067
    0x20403200405040f020f01120606030b0f100e12030c0712020118061e11070608010e1b030612030910050c0c040e030a0305040c0b040306050106091e050913060203010308 74
    0x5514100801000ca5101382040c00460381c1102c5c0e1000c41c2d5030040c016281000d00303031000d1108500d0305402045103501a4040521100c0440b0f440c9400780c0a039003007000e590705844600e0000340302003c13040681c0c24810400c0500910180a5034140600741030303458640089944500308102d1818211b005650304542015000440c11011401d003d0914034040c00d40c035002e01080120303c0700f4403031440c01382d4407442080204001460a541d2180d03562030005024138002c1c060040c8001c11200450404003c1c0c81041c0040c80b202044d8508582c1e43c04100496850304402014040c0000c00105c1c12a42d42c0d91151760101c0c455480e9a40c4403903100c40603502d4002c014600714065854140404017040c000803d40b104107001e0315021035030b5506e0b46031890b56000c2e15440f20b690900040350103c1080b40c1e60700160306892980c4d4412629955402002d01c1e020324603c1210403221454000740a41d00745610210751124610340082c00e030301550344c0d590040364001da1095a902a012400c4684401d00c1454000e803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 777284523 1250 777283273 777283279
    0x1b0703080f1815071403040c15081501140c150a0b1203070f0c120503210f0403030908160807021e06040e100302060d0f0506090c181302040320 63
    0x207158480e541c0c069640600c41900f0300c80380c50460004502600c13404591154605048106840741840d140080b10032416018805076004500d941921040c840c100f4680f041d25844890303526000c0c41001510b01d0002400c220203040c100700401c1c0c03000a802c1142e00805068105804a01d151203d1107208845021310700c54800c1058040d03000e00e111000054031a12500064405010201031801c1e001080841d4040481c240140c0c510070700b4800040040c10301400c11080c03044441e904c015054003180006c50390b016100301c000b800f140c080b92081e48040307034980c4500b130494500381541c000c1091820700d1035000c0f5025100044e110085090510088045002d444804120174101e0307400031307200d409140144064944060b00040c48025842c8040b00210f03000b03001e9556900c07055100002400100710200003081c106400b10326281459000184641c5050300c2090a00304202c050000c00e295450f00258000c164904118914410b403000b000258481d044005031101c1500e5002c40d9503a16890a0344 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 777285773 1250 777284523 777284551
    0x90a0212011a010509040213030c0608060411180a090e070503010f0b060702010f020c130203241507050c03030a050703090819080a03021e130503010911091b0703080f 73
    0x4990741c0b211103407031100001d081070394448030004041002070040c1c0075200b1140c510b030640001400100c00800050340c0c802c0d136610352aaaa55028401984c070400208110b140f030801c10103141c900600c00d008416071005181c440790350390740c11030407060b200e4203a83c81310660809075080000b46024400c28820754602c1c201840640c41c1c510020f80140100340003e410302c8080d4200460542c402d0102c18181d4030010021a203026403109000000d4100300c41580780005c42c401415082e281140226104c000d006118450b16440c3d040c1c041c0d42500247c1c012100c0388503912502840d03507014809006901c0646e81c80c0380d01c400042c10020083c4407039603c2441c80c2c1c2c106005031101e610040c10702c40d40301e039000600d5560f680d443c207030704070024410340f482d408645410109401032040071600805204099880c0581d0080e281e004150807076440300401014030b41620400501e90610103a2640c0c011014424401c1031401c001c18007880303a02608007100000d8498080140200021146c0c41e04400401c80e130340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 777287023 1250 777285773 777285791
    0xf03192c1002011802010c0311030a08160509130b0f030109120207120c3005070501080105040c05071502070807030509011e0c110a090905060f0c0702060d0f0f05090a021201 76
    0x11307414a20b554041c1c10022074080e514185130040d4000c00310811000d0850ba586c0c4c1c51084018201881500c0544049041700155544140b0880a039148100000d107040c810200c8060804000c01681c24150703005134109107a095103980a104003060503004d03183c0d000b501c4e00b15120007428020590803c50342c00500554807400701d016007202105541100c20f00c8039081d031809002e041c101c6400fa03032040c64001a02281c0c800c00102140020132903c3c203172240384850762660b080105a4043c1211540002e00506c450750200d142101051176505980c41c005192122984450101e580444800ea001c990002800143ea50f88a00d4521441d2100141900c01603041c00c80148042070000005d4090700c00314800080541c2c5003a1028024070348601e0070810040ca62808a0701c8800c11a28240f0300100750000a40b00c02403002156074450f80200881d1500b01c0760300500b0000e14082c0305031041e25a50321104038005c0344910482c0e015412450040094aa07188100905008100300762000d50341040055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 777288273 1250 777287023 777287051
    0x1a04060602100c0302090904050d1101020307120f060f0b031b1608070615080a05070e060609010f0201061e050301230a0c020f060403090807080f03192c100201 70
    0x242040c00c03003018001c074141d03c981004401034010500c156600c0a041d03424801000000185030383e11000a480f2946000384650703115080303010481e00100800d040c1d241c0c1c150745842d070750310102051281000000d00b4503200c03034022031030303104c00d400a04505000000f40b092400d103490240440c2c46480581c0e901c0c00c072301c800708080c558a038036400819081c004140300040089540102404114481d40004c03599620880c8540d280c010401c01c1d11a4000e031500800d0300c40d5806541441054080c1000c2d140005040046920260f880072450465588045c0400c4850b00740c15040c00d0380030041140050541808100745c00c46503080c060303803010703206401c1d85181402c074003900545c890400703d0f0000e004c000000c010785c182400c04003070500500400f000c1004054010f060401238600c503504449000351660000da41e52100701c0148819940148051010156501004094180c2178a040c400000c0c4440e031180c00f002c00e00d881c080c400083c003c00345941c0d00f00780c0c0f45514000e065100a05c00d02c0304940d05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 777289523 1250 777288273 777288283
    0x415090201050f03090114071206080c030604260a030b0a0608071e0504050904050601031b0f090f021902011b030908030c0a1404060e0f0109081b0a0503101a04060602 73
    0x803c45941c07404400240c16040a520060b11000c407140045914035200000408440e40017003c101c400d4034054020402c468001030070000d50030060000c000319100d0b5200e04c0c000808031800c0a521502d148000c0410141031805824a0741d036a4502040c4140c02c1c00804c18800c802c0e81004040002010030040700c41e40c01201526101c03080700c03200c1c140301402c040440305403241703401031500406003c0c10f0208101300080c0c4a4101c5c2c0c06140403000080d45045d15600781e48861048010718602c1d64418005159039900c100c503a2011103400515054000840b055050700a003a1400540d54508400704403203005c3c21081300918080c60200003915055030790034164040500340e0795000c3d10203e021004107000d0440400c20b00d0343c0650a540319650781d14000c010300c41180100c0e01402000c1503440c684d500428189082d5003488019115a10200400c0c4411f092030b40700c907507400140c0c844005080c3d1418019254003019017580882c0c050260b80e030b9282d90000c200081401589408000c20113254082380e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 777290773 1250 777289523 777289537
    0x1050c0909070c0809030304140a0503060603061f0e04080a02100b010504090911040e062e03020d020d080408030a03050912120c07021e04180c17030c06010e041509020105 75
    0x42003035a0760f59905040c1c00501841c0801900f5100005010551090880c4240b10004007110082e42260b01c500526444172020380f100c0c0c0e05a44800c0200b440c4000318920030000403506018000115039078402031400721020350381a03841d07440c0042c2541440e0360602080310181084c543c140507480700080002d00501c5244607441844e61f84800d03600400c0011544c000c5041e00041003400b00d00f45c161000c0b6243c40317040e038001c150250709081000c0b1280100030400c0361160300b5500841a80d203941c080c4034070100392800882e4007410550407a030000d0341d540060406405003500031a01c80d000444050300b01c5202401441c40c1b0f40c8061480f43ea004c0121044541c51144802030900c1c2e611010b111030114001d00d00001d60103485040100740542000002801c94030b41100c0500030200904070280c1003102c00b60000d8803841c0003032000d2104800180c142c0e02144548801c40340342900010300b90b41889000c0c0c0020380502c0a80007400203011404402c0480c401503c00d04000c41034160740040d109106d202 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 777292023 1250 777290773 777290777
    0x20d080105060703230a17270a0212060105030111030108280f20010e0f04020a020a0c1d0c13050f0a05060703030c030f0b031015050a0b0c01050c090907 67
    0x103201c104043c0b25000c40c400848620708a66417114188130803640783d8000140c51000540b503102250450202400074034014035291500c0000f603094414000700c3c400c00f4240e58116440345000c45401030b102d00e0707440000414440c0207409554108001c150a50704000003505844105200602c40b440b40494405e44000c11100c1d10a0510702d4002d403510792501c0c00f1800b400e15071200e0341035028407803194080d00208545040c42e0141c01c3c03041d801510112072014205412401c00011b4012508040c2d000f807140350001e00484078488844c3e0744000b4521110f8118004888090200c1290040381411f0380b0b81010011a03094100410385088210640030340c8034031031103128440402c0b5500d4546480c618050800540031a41e03d48150a016015003015020400002c1c80e11b8854072000d1403038460180c640700014046c0007400d80090030030307000e010300c001c0040c50480f0200001a29035261800a002000a082c0d2681c454421400903030840c0c9000308060442c07030341003001000c0707179861004c840e612034444c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 777293273 1250 777292023 777292027
    0x5100507020c09010609180203070c14010b0a14270a0506150a050a090f0501050f0d0f0c1e03091208040f080c010b030f01090302033406051501020d08010506 69
    0x3950101d16201184950700d41000000c80082030850340403407442c0035119681e0100c0e1000c2200c2c14008100e00c421101c0600003502d00d4170140004000e02c1c10462840948000420414441c40015a0010781d95100710f5081c403502d904d219940c02c2607800094548284100c4407840d408a540c0011484001001100c10755681c0c0300042480d690090b01d103012210380080d140d00c8810f03186015100380e101050300804580000400552000b1402c211020b86038180c2d281400c0c04c400034102c1c00260010300310407c182d0380398070031100c126245204034440701710a5540c100034400c00c0c110004a14030144c0703180703003010308060100300032030a40d20440415824500e4103110a94450030151200345081e2802080100005206501c10005400c4410002c00850651700300b003040300132013400c03122003400040142c1c10034440d2500840c0310341c005510140714441511003044860550401004524000f2503009540301c05001c40c2e210113040315100b4000a00060000c0092148054008541403180034807807800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 777294523 1250 777293273 777293281
    0x10b0418022b030c21050a1812030c0b01090b0a051002030702030106091b030e07060806060c01050702210a1e03090c03080717031302130e160906080a051005 69
    0x145680d0800380000028000c02144440c1c94024416000102c4c00e540c0c404070120003458500300d100814250000640702c1d149810740384001074500000701100c0076150070000000103103900c0341e0042070355007074402d0307880152001451521000350801038125403442440c04294000a85a10b403240060310000ca4800700c2c4a000400c04034a107204600c00250103500305180010f400e0240c0e0401250380001000c0c502010b00600000c500701c9003031400002c92503011580400900d8050003400d500301c4000303230506107410204c1c1d0b842d0f825900290384000c01030740448020180c220b1031060a8101070b1000e6180d44c504403c05a00030310341200d000c102e00c0418051080b0f0b28051b03000360310030703a005640028484481351790380c204151a50443d81c2c065491001c6105500600840355049a1190f80110094041000a90240019080110605810180d845103004489002007009001d801e1506035900001424a511082601c1c1030794030a0241c1d60015810b1030016602044480e040f511104000075640d403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 777295773 1250 777294523 777294559
    0x7050a05181c050c0612010e04020d05060906190e0303062e0903020312030f0c0703030f1a010e010302041802090d0b0f0403080709030305034302010b041802 69
    0x81c08100382d201c031004608502080c80c1260003040c060088059644080340302083c4481485010b05c200d002040c0c2000500c08c80c02c5c0d07822140d402c18000f912010514440c0c0d44c0d0240741c6003081d40d40410a510140400019288290840d2144403062006200d01d24074850300650b00d000c0035002d548110804582d4041c82da0b100002d0410750060300d52844061045641e0240c20b40381c042c00141d001c0d0040303440c86081e81030200100c034019110517080504c0317a034850040d071a1603088502c04a08040d107030a50b621104259001c1e10241612480c0c00e1480340b801c4800142111000702456414035005101c00c20003802000b07160748038050701203030140e1760350108000030310f14003240311006004901801c11b000d58404001c4100d8840c612a8039a0006030312000300587d144511343c40020001502000052245009640c01c020f007010507004262500f0b820088920f8407440c088804840800c1910403449901c0d030900414000c03030410384040060b4000380d0000c0f40b400d40c58500c060f009074040003401580303030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 777297023 1250 777295773 777295807
    0x20c190b010f0b120a1e020703080f0906070f0e0a1511060403080a0e0313060302030609010b16030e010c05060114100e0f061c05070305010302100e010c02100c0b040b0a110307050a05 80
    0x78443c1038800904010546e12000070340040748142d0000301d11600043c1c10346490070310359005501d11402004a965050740c22100d0000100c038910800a58903880c98103034981c0e81101002d00400c0220941d810f00400005120140c400ca03104c03801c0e44408240b10100e40c00c0442d254010040d24008038400c0803000940e8507603c608a10303520400142e01000421aa05038082c40c000c0a00b16040c490070707607903144411618002c08620b0101794100c0345144000034040c2c0a12001e103801814400c9020b00240c40b19400c14109a01005840d08864441a681c1c9005e10000035040000e04240c144000e031040494502c00e18415854040c1400040a0320300c803030070000c4c14020034000c1100340410701d840031004010301b500307200890141e03020502015040d401615105080c8006a403404414000c503000c000740d49a40b074180c0000d004030f010032500440c82c0301880c18030581c0101d4007503070700b0300380070380c21780100c2d074154070558012a8207000f0701c05025800021100c1ca0600c0d413400726207446001c11012005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 777298273 1250 777297023 777297041
    0xb03060f011520010b01030c0c05060105090a0902120f0c01170c0304141f061a09151e030415091502030c040b04080d020601060206100315020c190b010f0b120a 70
    0x1540f403108040c8858405400c5080e8200b400e0360203001002d180c4005460a0341000e4008006070084170040c0554100540001c0e031000071042d0210381e802031900407804001324405000300e2034010324680c0355140380820117070821001c203190034240c2086000d90f41420120143c040300c001c410010200d03061003100c40d0804070001c08041995603400c1301004502c07900240c643c0d2a1002c50500c0070004000d118403440b2080c040c0c04201c0c66151061039000c0001500d030413001d140c20003800740300a4100c504841e1a032100c0c3c042c000c44a942d241070504002c92903541c03480350300c40028209991a030004481c40401d0f062030310340300d00c0540c176a29100d003113654074080c64111038030702c035004100004c0c2868001540456040c0b55000d546840e41c840e0350803030315140c00f1078041d2144010300038100001260641c90f04100c980c8a2001400c0c00c445105081c20100c0c0a80c5a030305586203400c40300d05028004090900400c0b80b00804403140d840c1c40304000c01d9008205240c004446103900192881005400c64000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 777299523 1250 777298273 777298307
    0x31006031806020a0f02070605190509030f0102030c1c05040c0e0403090519170105060f1003110a0918060302090a05180a24050606160320100b03060f0115 68
    0x4034120f400d0f00a10317096188070000014031400000084540c0101c08aa007182200110b406a00c007808009407131076400904820f03050300c103000307840b00001401c0c8040c500407003001241583d42c000300c28201030841004081c01300d0381d9103003106020001c0c85001006045071311410b007002007560382d4182602c110400c0c0d840943c10100d030380b00d00c00542410001440540e80f002040c4011110048012800c8882c12100300750070a283c1e103448052890040d003280402c0c212440c000c610301c030502401c006580c10507402100411a0524103015160704c102400c15104d550b00c0301041003d145400140d5000409030420140b1503450003c40c007035078442c035443c4901e024581c00b111428100c526081c0c1c91086004101e5400950320b01d0a00c2081d4003502034103000300c400618160511060010814100d00301d044101c0c01d1100380c0081042610801010120040003040507200103002c41030404241c600c030f001c0091080d0008801c02040300f50a040c058190f551954084000d00403140303041c0c58812154814542c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 777300773 1250 777299523 777299527
    0x1020307032a0c15020d0e1b03060702060112020a080a110906040b01090b030c040e0103140d0905010c12110a08130609060203070605130c0602010515010503100603180602 75
    0x351140c00d908010702d032100b0002026003406014a140c0302806140600d840000d500c007a0700000b180308003d152048581e07910005140052581c4070404882c072003400c0342d2040d0401c03000c00d03501400c54041d2801050060700070700b81070326002c50025140c200c14064031200341006000032042d51609100c800180c12418115001901142450170050700f840c861a07224490620016a050501d40074131200c520043e160044418200848101d190304020220f0401e0601071100040105220740118006c6000c0d441303900300f0b0722206450604060401155206010852008100d02c0e68800c065000054201604000549030400300b22407101d0840c2c465201846107030105814441e00000821702d42c4a149914003415a9692081c2c80d51400740c881c61003d41c0080c000f11011a02c203410446d8800344080c2c2c281500c0c0d10a0b90b544040007099081100141e54074801c1149207030314810541440c41090805504500e44800c0d400d0502e1514000c90381095100c004040d18542002010b22030aa40310000755 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 777302023 1250 777300773 777300781
    0x1090e1c140d0207060f0605010e04050c190507260d0207050708030d02130503010b060307110109080712030f05040c1205010b0901030b1b0309150c1b10061430010203 73
    0x1002c2e4022803c01d0360b05c10f182c00c26400e04240d85104580031154186c4400ca0041c0c90001000002d003002010314280074420005000142d003c180f035404e180199444c0c403600c841490409840b1000c02001511861034040d0414101d204048203503801c9a0380c000026980314024a0194105000ea500c80802840040340c0b02030315090396000340c1045585492603603d80c83e0b4a4080509880d00c1c0c0044c0398001c901003010403030881c403808420f80b0b000040000804c1d541d0860360360311003d9020182c141c46480038000b103485081d9060044030324116803e082844241015141c00b40305000e14403401504003490041e04c410414290042b5040e000d005015010f10340e0b5074203144502010031940b010724040101c8425817030340c00180640740120364800c01000100c080846054a00c0d402421000c4003940901940341c103200000b51340020490000054920a056828800150380041d0080758002e12180345201c1e82d5110b00c4801c041030b90103060300c412811107800401e1101d014010101903554000403c01c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 777303273 1250 777302023 777302047
    0xc111203070206161403331003060b0301050d021f030b10030c020d08072c0102060108030715021b0105130201090f08120a090f0308030103031202090607120509032401090e1c14 77
    0xf41447d0308090b50300d240c0c1e40c20f14000071412203140380209040548240300500c418200082d40302c0200d88040c181d13a040c20440e00744510401501081200080e407114a900018103000640854032076845c2020b0041c040013500103501c548100389403104001060740001c07103c500c00c00c0c0c030a500030000713502d800e400424001031184500e0300c2000781d4054410440002600300700042200ca03569000701415440d80101240031019501002d020349440041075440ea500d82c40c00e2050300d01a40401c3c41901d110a07803031001402d0109030364000642c49000c8441041280703c04228031300000c0d4403003c0650f46028800e000d48510b0010b4200c0803500d12441c0b004001c000c2e07400f000b5410303240030703071104040400380f0403200c07040c0d1041c8a020381c0c005900384580c000060006904541074009400c0160501c04403002003490586106065542010396070320600181011000c030380d0242400b510240400c0d100405000d543c1c078920048409400c100c500074500c818400c0d0080100d4a644e41041d42d40c81c00000701c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 777304523 1250 777303273 777303361
    0x2130b040e0108070e190b060a08190606120e0f0f0607270b07050717010914061006181208041e0f0501030c111203070206161403 57
    0xa032603554403074800007003551240013030700707008507820301ca0400f0440d60340d00d1690398021841d8802160181c1c458084c42066a25480a82141445580c075420640703041840c40202c5600003068601a07850998107002259010042c84459039422502080040d0742c0518140f6203010310b20074151500074038802120203140803510900034011030369210ba8030031a44116184151019450985090503200704000111421005d44102c60156042d1135081c2e46d241503804140b00041c11901c4180d55501d407600401241c4042074040a482c20004d200d03524000032004009001030041b001808126015444e144400041c5440039000217003c030441900b141c502100260410b0007180c0100e020354404034003c00b004039850048410100100c8a003e25200c0154010b120035030b11401000407403ca4003203200b0080180034410b4440081c0a941d0f4541620001d0a20b980507007020000901250039200c007640c803c5511813054907d0504d03a42d2134903821136818082000e00d17501802041c0c0501000034040101c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 777305773 1250 777304523 777304529
    0x7050f011b0207051309150501090c090e01030b060f030307080d06031a0423030c01060b040e0606040e0f0703021903150815010e0a0b130504030e0f130c0302130b04 72
    0x2032404078210418000340d0301c50300140a040d0f0032000016418440070015004481218081e0048800901424444c582641d8098100345922503c40d5041405554010b4100f001446850340307a40341941907664001068401805240c0309441c011700c180d2145d5024822100382541c0903446569031001006c8038005040d4510003038461140310707005421101d0700c506030f05106640c410301c0405c0407460340b04291215503125980200b0b9210501210307103200790910803070000c2c204c2100c1450300c0781e1030322103540c620080041100d400b840341440104040c1d0286c02007141c0202e0000400100c40e41c030b07444220000c4c01049420b0b420b000d01a0100240145c06601690104900b444000302640d114113801c1d90310a4044000b601c43c402078401081521022601c41d50880040040400c003200100005003d6001c0c2c142c1c0e80300030599510078401095080403451074010003e8030f08401209a110010f0031120030f02141e02500b80e2a80f042906152096044a201c0c00307400521030f1241d03032109048542900180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 777307023 1250 777305773 777305801
    0x6080601060e090402010305100503160f0504020c0d08070507080304060e0105090c01020d0c0c090203011e0828060b030708010b150304050718020d02040e0402030c0103060308091507050f01 83
    0x900200300c1e94800e02012165600140c928055a01e96030300441c010507006005803503111b5001000b168541d0207000184460003280d089001890802416a04207440b55009511480c81000008074006012034002c000102d60f0030205800e503170b01e41081c2da1902c00c2c440700400e800c0b0004104402c115155010410460418008000c503076030303170300003607984001080861f8090382c001c50a10707000c10302c1594000003c2d44240e5400341280e540d42104d5041c4d0300280c000ca182c640c024181300d070041c0d055250010003400c100c4000c21514440345800d10182138400049080a00f0700b42e160230078803642d42c00412400e24007808035000640e03207650643c0203003011105144280f20342c104036502005080306403800b49401070054641c3d10300e000814400d081c245040808055024031403510462420b1020748014841c51452005034030b0544105401c1c01242140726040c145024014000716810030151451903800b51020038503011000d0b02c440031f074050500300070010310810001040031581034100c0c503183c82e281 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 777308273 1250 777307023 777307033
    0x5150709180501060e130b1c02010f08060904060f091502030912040f0b03041506030b1006030203191802130b010806090112020607150c0206060a0f051e0103020c0d030608 75
    0x1054208003520780a1141000240c065140c030136443c684003e81c0d440329003110340d000503511110070100d81c8e42c622200c1c0400060b01e03110002000d40d600310b6400c80c0e00034128545044149052000070b020b1401c041e00141440f0758134500c101190030654010740389241c000220040031364010440c0b00c0a03500444600259002d40120550007412007000d45d42a254844e00d00c0074058140172600358183c000900a4038000712009200c031a040c01c9204d40c801860040d010b2200c02c0c03401c41582030000d107065020100301031040040202c40c07841240402820740c5119400b2440b10040d04188a40780b020f03d4000c0d50289000c0c02c40030f45c0780003660100e910064203882d4551180d0302c080170807501745400d2141100c43c0ca120b91001c8010300d441c2e80105582da106203200c010200301d01d40301e141120f10605000c00583c0c44030043c450303286094040381c1c00502c0501000740e4541d0401e4042001611851f50000f041025040040026800ba40644100c40e04d4a8101c464140417060000d000d00030610800c4070071700038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 777309523 1250 777308273 777308309
    0x500f070312020d050708090a0e01030f1e0b13050c131409010b030a0f0f0f060504030315051e03030408011b110c09040b09010912020c0306160906080405150709 70
    0x807801680301a0a503c40a041c002d681d1646115541f00341c00b0a0303801144c850700070441c110b5442002c1c2c0650b0107101e43d80c04521091811506500102201c5100e102055110000140400348115441226455440800c9001c1d1800c28170b4010040c4009a02c48210901205d003c04c8651111222924005c018985520380c0705c20103003224000c0014680582120b41000007040d41800055280c5128008280c5070110503200c00c20001c40b80c94044480b9034444c0705000c103155050042880c4060031081c41c403421840d08002a20200c0400d14103142c4a44020724a00300c1d62b028030a450040441070700901021250100c1316048048210001c0c002c9101185645a11800011558000100903100804c15180c0d40c890641700d1038003c010710b82540d200d0140c1d1000486603e04800341001603002404090420020182040300c020700078901c50b0640002900407a0f070000c0448116081c9060030420b07920b40341407540c01c2041c84003ca07002d6407003200612070107075804209582219074a100c0460a01c0c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 777310773 1250 777309523 777309527
    0x20d0c2301021e030f2206030501050906040b0a120204020c0a06051614030a0f092a080a0503040b0a110f0618011a061606050f04500f070312 62
    0x8038489110307005500c02e00ca420b41000494005105680c812400300e070034050486c2c801a04441c0541042002a4403000104401d0078a4520560030000469040c0a840140d1010580d09912446298a0102181e812005548031581100c3e032062941d03069811401c00c0b41000d0001e4907040d82c0c5015500f105103d40c0c0a110b100d0301c0c4459504036a0b541e00c82c61620b52010341d201034640c03004a4600f4507a00c201d00000102602c01d0507016a06000301c0300d02d40b00b40c4424612080100f54000c0301c050308a010703900005400402180c040d10101240035442e24150202150090440d1740707025603a01c03600c600c3c59400840090701510a4110b4001e10701c600003080c140c5800c0c1c0ba01d40e441c9d080c00c6e8001d000e4008041ca441c80c050070b403020000713049205001da617031038a0060703c4c01583d42440707001050f0305010502103c0142440e440d0104d00a50405460000b180a03003095541281480d0366504012100e8070b4000d83c001c41210004030701128000c9411106540c0c941c0c1c5503120488940003000302c0210464 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 777312023 1250 777310773 777310813
    0x9030809031c09240f0b06070c0510030b0613081b010e0f0423011406030408040b030a0f1e05011715090f0a200406030f020d0c230102 59
    0x2c110341c2c0c003452482a9941004040d04600c1c00444503034211400741200042c120070014600c09028401142c008078110403807007280d0740710020501800e010400c800203d038590940b17104495064070084031005000100728014440d2034040303603004d00c000580d409035080c3c00341090140d90b811070a503444581d05166410b88840403a2425002c00e081e0718910f1014900154a40384403a00a48041003945d81c814441c010300c070401185000800c50701c0c0c018070400410f6903800100c02c0d419500c180c035505003616484090701640c410001d04c4400003001070460708464011038841038600100b0300400c01e00a8080c2d0b4102c0e49501881c0d2907034a040b000290700840c4820300e001402000010300b2440040032200241e5900040c043e207101e1149400e000c107a40b1081041c114040e019942110682d00c0e0042d0340c00c0c003010400c1e0301912843c2001824404034156200d0712800c1681101e0805244503a49040060050079030310441400410b04205c04009041082850000100742c1c00d68420f250003419441d240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 777313273 1250 777312023 777312037
    0xd0201060e011521060617060904050c060d1401030807020429010e0f09010609240e01030e190308100f032118030f0c140310020f0405130903080903 65
    0x18031103802002c003c0e4000c0949014544404050804000c2c2c0d0140b448142d03940c9900c518001000d281c40c410842030110f5099800030f5003201e88640d203051035115266581190007007248075007800224095440d031251700010b5100048513020100c0d60f543e041c0200c89400c1004168015801c100804288546a5049400014000408030388000c3d50000441d415110f400810342c01043c0861501142d503103204a06000f0b2105503521500c043c2030180c220300390a05d0340410b0469042290386502c056400c60004030b4104400e103000141d400c0c000c0100352502084442850002903842e0f9104181940700c00356502c903c1104034920103840e5a0f24440c0036101d103921001d0300d07280c4112100c0384c03401841c50032401c04202d1450403108075020304207600750070b81300741d4021103442c082c000e540020070400b44600b00003460b201807041c0c62460310102183d00d032f112a40341c01c5081540010000911701c2008140d44c06051f0141180c425480300d965104014440c00b401540850152000180703000b00000445480d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 777314523 1250 777313273 777313289
    0x109080a1b02130b0a0b070f05010c1b03050f0f0d0501030212120d0504080f030f0405010609060e1305030408010f200f1903060b0a02010b09090d1713020604080d0201060e01 76
    0x150980c02004000184040280c0a502c621849400a861141607015001c7e050007480340c4055500710340342136401c6070100100402400320480c0d01250601d03620010050294040c2015540c4000f50380c0189224400c204030064502e50119803070212029550005059a2003034a00418084103030711100e542c0c000c00d071190104040c0401c140b0710544050b17080b9a40080c820003007641094100684000c040d00115008104951901c08000500c003003405110000c1607080420007000d400d04c2901014408001c3c0595110a840d00103002040400c0003120b00070112031008002c014410f001e46c0c405032641203d85c50030300c8040442030021100c64021038030203c0c005441c1e2071030300040701d10108100e01c903111450b0506560b00d40c001503010500000300000307080c0f98000201c9151010800900b444061f01c03100c03a9520005090400c641c008a5207c204400b02d044100980e668000c038107040700c0c401e20b009400c1680403e0021726800c0c0016468181d41080c1c0003801104e89490894441000912404070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 777315773 1250 777314523 777314539
    0x203210706020c0f0f071a0714030403030c0606140901060e18070507170f0a260f0109050f07020606061b03040b0a110a15090219230909070e07110109080a1b02 70
    0x49060b2600c0300400201d4452704182c00112030303440700182941c1082c1d0061b004036400581110421055115000151200321511804017040c070f008501e4420050054106018502c02c049407150768100d07450ba0403090329a03225030355241016000340503400400c0111040700c0c0c07083c1c85c10502030703441c01520356114101c000c1c64201003c0c0d0000301c0700105c03c5002c03200d0841c03802e01c1c80c0ca075034510510043c0c40f40b0046031282c611549040d025200b16040280441240300d650014858402d60226909400c108101e0380340e500c0318034046101d00c07484480208160f4510000900241c0303040440051b201c4400c1130b0321402c1019a022410039194040900c001707161010b103207a4840c15000c0380d80184801030001c1c0c6503054484400c0c404030004803031508003014411011441055810b10601080304841c410350704a42c042c01c00c05141c41d0750318150b024442c0b038810342030000341840348503100c0140c4010b030110083c01b44016a080c22240da90046e99010300180310818007921490074002005412580542184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 777317023 1250 777315773 777315809
    0x40c0302090f21060702010615020105090c0105130803031302030724140405130f060503010c1d01050c151509040203031c0209031501050405130203210706020c0f0f07 73
    0x124070f41c5034020902c0080410307207080d030084000400c22144a0b8140303800000700b10b81440c0c0090804009402e0607001c5a05180c104801842e0100d9186184c520a00781251036031083c201209540a00350424030f114031000c000c0200e4000c506c060303980110300035030030741d120580c0b24a80c100c1555070603c03224207035007e01300d403660102d4800c05140600e8410074240b00c1c245510740c3c00040308540401c1400c0380307242d00c94886030710000d00f612500c030040104400800800c50b914401410861204104103c008200491002c06074060030880e254100d4080035102104034102c01c03c0320b402025a00003110861208000c0c4481c02c10300300d0640100d40040c011801d0284511b209107181c03140120b10101c0d1602440207841a031420001d00d00c05907000c180d41402507061109020441d140200660102c1440d2440c0f2805620045408582d00020b1007203160303420b0550300042264401c401c40100004c0c80020301c4034000d0004200d105980700c3c55016a02081c00b0345200955410341c50043c0361603104506000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 777318273 1250 777317023 777317029
    0x1e01050c031302061603050904050c091003090602070c030803190b40020a081f15020a151406040e0607180306060807081213030b06220b040c0302090f 66
    0x5140c020b03c01000c0d1490807006012554008020442c02c5010600104003013400349001d00807103600007803000b440341c14000c0000000300700c00d6189010b082855070f01d030400002e103c1150100c840703254100071684092650b03807408078100e82c8121140b614810503034103249034808203401104c074407010060a824000114030074211411031034401e40c1c00558203d008001c0d641e881005611820065403c005840702a001030281410800401310b003110001602d010000d15200e0080b9010b90316054000380c125649603406a150802158025080348008940400c2d0380e401d81e002286821040100406151517260501060362480060500550403403800540c0c0c0f50f100b4034400d0910340d00d80b03440c2d4140a43c6c0fa203402c0200d0700b8513000310100360402c00051107101001c0007002c0041d207540d4452407418200c168001c0c000c29250000810790070204010440941d1030b00c01b04103004541e2102031000b1440748034180000e00589002c0d80c003603414516080a4680680300b555004000a401e40c00d080e4030302010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 777319523 1250 777318273 777318301
    0x30f0a05190903050c0c04271a012304021e090102010915050106030506030303091b041b0f14070515060105130f03030e04050118090c080f1e01050c03 66
    0x104003050110704840e03184421460103909000b60003601c8496840d40c141c24121b0800500c040e0550042d800c0c13803007449902aa00058203070f020f405400340141400c15107002c800300041e0a1840c24542c20380740000c150344210030080a401c0b244a030a04070f214055000780010782c0608080340003285c0d0402c920a800d9044080182425881440001364201c002e40d5903265030b105041c46480029a00c0f4014054990144035480d00050124010350440c900400c0c21640c90000d541c0054448540320551405502e45410901c1d0800704070140c1450402c004100614200e0424041c02c0040c2000198104400142d030450301c0c1c054100000d0090307914881806507064001a1007141008030800c24204000605240b8802410403201109803c5180d814000c164801da0b928151144d85000c004100580006080f034920704071042c80030580c07030010b00b40318001c003219501a03001401a0962034440c0c440100314001320039141840a07a0b029040d824140c200c07481200c02550304041040442d07085960280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 777320773 1250 777319523 777319531
    0xf1406010f02100f0e21070813180f150b2d0f031501050f0703210f0b0112090c050613051c03022401051002070b22060203030f0a05 58
    0x1101c2d074806080b0643c000311100701249214182e6141003a503c400024040d4548900003200e50054442920b0b025580364400c0c0c400c001c00030040000d00140c4945081902c4006122a40d0360041c0300308802e81c005c010b0036a50700c11000151130201c0450004000c03480716425581c1301d0741c800c0c2c285144001d550300034245002082c041003110340301d0718a042c050340e0000c01c100c000080d08c0c0f83d268200076403640600c503c2c074a07549042c480c0c01d018840e90420144107950715103405140c8002c2c8d04154107820780d00c1003003c10746405440c1c01c00c00820000c0c0a6900110070201d001e9072031850802e52156600300302c40c0c8080c001004141e01d41800c00651504002610f10a054107000300b8826585400060200d9100621044041c4c0b00b540500c1c01c1c16014490108034004102c00180b0790303190019161171050050181710703c40d00b1580704e6030302014800c2000202a0405000303040d41c43c5100c004142014a660040460301c00c803140c1d01080c002e2003c816a030060555000214458480c95901004be00000f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 777322023 1250 777320773 777320777
    0x150c090501180f12030f02070e0606070f0f05030a020c1906230a030506090c19081906090603050717030a0e0f060d1e02130b0c0a170c010f1406010f 65
    0xc41c0c041140000d1216590042030341080000c51030b002c0f445c1c081c1080b02425040020b5402c504001c001d00c2029102095021004807945541d401a518220301880898030700603005003075585e0a80308101001008025115254003210000f02102042101080c034200e90741d102c60520341010070209004e001c412020400c0021107203014601d0180c1c0d02e0749504a01450302c0060b8480c0203014a508000041e2034202c00c80245503440e100d00503170750710b14510590b454802041a0000061031600c4510400b0540c5552600c1c1400419030340e603032401c0903188074003054440b800b80c40000104440c82040b03901108410502560a00044c02c0080c0d8a4000311311240b170308074103080d01034001a80d0b008010071500000c00c0707002442c80003982284120f5000d03214402c501038810002d81c849100403001040c00c0750000a0320558400c800280c0c141000c00800700100181001860844070425070400313400303003040c1031000304184600040320000f41c41809076001004024007010868652107401d40c034503070071200c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 777323273 1250 777322023 777322067
    0x2040b120307080a031401050f0d080d0e0c0f040e1507090b03160e1c080f070605070504090b0910030305091503070c02030c1806060711040504030309150c090501 71
    0x40c021003401e642c81250101d90155001071510402c6400d40700e0245403110105401c20706604040c0032512961048002c3e511581c01d015001e810480d420088500703070251040c041c400e80c8030060100e59295210410148074510f001804d0400c0c5c203291003075044003074248000300711114000055140c80400030b402c5000b00440f030600418258036410046009900083e841a000f0010010040045e6031202c0b11034840c2524078001e1440000c0c440710b62032200d0b0082ca4040e40ea84545041c404648180b510003011a4100340420a40b01d4102e00030344119079101006004480048041102403001250b00351002d2000f11400e1002c82e1250022b0f2144000c040e140d6001c8100321168859150011220000092100c0c4028011030406100c041c0350180f055904200101221100d4502e003036006048902030040424207105100d0511680780154202920801450400c0d0074010058035540c2010740b4141104200700900b81080d1092080c006019502d803801ca500784001143e8805100c00d0301803104181c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 777324523 1250 777323273 777323299
    0xa020d02030f010608090604120f0908010e1c1103071101051c050714071203050403020a0b190614100e06040906080c0a0f08030901030b01030e0102031906090b0d02040b 74
    0x115200440c007a203502c2c00d07610700710741c50414000e0200300010003003007880c0c04c403100b0b000000d044118002e1803840c403810180400c80303100000700c03104251a4040c50007982800607520708401d0100e91440c04580240c007010301000902e8090b14460000030100425030b000300241408207405402550510b40141340917407400d0381480503803090200240225640c00e03903450600078135035009006d1040d2312075001c1a4034200115070311480710b801c031408032301001c0c5034558000074101882840362064180c1c1c0b01880d02090b0910b0804810312100d10030241c0321b12841c02d88041480c0b058200d80f0181c003a0b0003429108010000ca1007103520742c42010030b981d0000e10078003010401a042d8051080680013240090a018414000700700d010f2307905500c145241c0e80c10040a103c5100040100c501160f02070901207020041040101d0051000003104641035101006100540e40c034089510854405000e040c080183c039030f078801e0308071406180e486900201d800b110600500b482e400000e190341000303050040e40b984c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 777325773 1250 777324523 777324547
    0x10090201032306010201060909030c020f06070f031e0306030b1b130b070b0f0f181606022a01021005100e010e07020d0801030809041a13060302030c0f060702090a02 72
    0xc4102e1040d8000e10104104040d64240721300c50082500c0350043c0000b5129460141102d041d03040060b01458030130000c5606911204100c90489500060a04030341c0c0f000e0400401300040700c10040800900b01003c40c0440d07209006000079a608072000459a44a00d02c1710860b100c0d01c41c500d4a078100044c4194202020255901002060f48030030440e40c1720f0740c916141003449030090551060206140c14412044900011607520007000704220031110305a0b4241c0d85480610071400b01000c0749510082842c1d540440c100440c601322030300e007241072004003004000001c501c0401c5401a40885440d0001008a800542d0401520021580c14689440507458036440903000350503402450024000710941c1000b111002c1c0c2103520302801c0d5075045d5a9018403910070745103d00d1180c0e481c1c4c2d1143d602150510801414448024404840c000c0214903c0015208070702c8140e10900404a0400700790400840c080840d5400401580c60120f4950801c841114040c00c556070b110360034099100110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 777327023 1250 777325773 777325811
    0x200d060608070603050609091504061b0c0b1003150207020a1505040f140a090902030c030703031e110a170c0703150507020f0d202505121009020103 65
    0x304141d000b404039981001c40107000d98030003411681c0100e00e440100407601002081840341e8054200030032100b41c82c0d5003050300141030b141a031100d4445003d480b62860a4000807a0040305101d43e2044a899440e886043c150f005181300144c1041101c0d0000035440d061a03008040703551009000460054480c1140740000b50a042d0780740110300b0000d014044028441ca5500040045014402007006a00c0104090444503c030f600f101984074105c04085550501c4003c800800c0a012915002c0c1d0300d050040140e00a05050b441d030041d0035905043c0c00e8424140d601d854507034030004001c0d643d0706a0f14000c07001c4e550b0450040040090000c403001a40502125004500950b0001aa240c8070303d00c40c4211480540000c080d5407054500031040c2c00080743e501c04050150410348042c4105e030680312045986280e07001e409010b211711280d059140701403440600c6101d022085444d54542040c044071050341e600e04602507106d9800b9400004241e0484600b0520604d07020540405200c1d03122101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 777328273 1250 777327023 777327029
    0x90803130504060b0a02070b090a0308211008060402062b0507020c09011202040f0b10021f0c0503160201182f010e12072c07020703200d0606 62
    0x1a10903510200500c1c6410b000701d00203005480003013850912800d001039507500035440388104a510100b840503696860700507580095402c144d40c0380c0d5036880340b04c2d14620300c40840d020704690031148010401040540483c2019180c050009068548440d001c203c01c940002240c20305151060805407000540306c84c0499a8004800c8086254108400080c0c10210300c041c0f464020251100104001d00c17802c0d005180b40c81e0107440c0000c28040b444061000707003c0f07485940c1d401200c201b0b074400100da40041c905a64545484071071141102805141e800c0d0b81908641d140020000c0c0003185001001900ca40000003140c000010381d030040347c24440200b032800340155070a0100f41504041c0405516222940d43c024100002141843c1070000e050400460b00706c90242c8040742503417020032000c21402c0b02808401c1c01420044004901d00c0381082d0340354188060f45000000400c00389400020101300b07403580610b040710f000c0c020301180c1d075000340c8260300c1030382c010342c29848031011410911510010f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 777329523 1250 777328273 777328297
    0x501150f0e06031b0d1104020414241b0109020a14040c03140a02070f0203100203040203120f0a0c1a010905270a02010e150c03071406090d080601090803 67
    0x365103072052a030301116006150034020b4200070880101c0383d5070114090740e100030841c3c4002d009201e5080505d8120a681c070300940080c40041c0200308000c0c0303180c0c1000c0f00b410458483d61300500c4510809600c1c010042200c03a01841800715804415170b4104500c0070302144c000000744d8070203940000e40e2140060780034800030b40c0301003c203440e58240350186003084032060409111107450512a00640c600050210801e00d0340460154200802a40b900c0c52140e002000c0300d0b00c040c0c030000d00800030341c41520304a10238440c0c103c104030000d40820075140707115061214103090245404040c0d400004200c01220710103003c50501404140e03072421540601001480010f540c54421150962480380c51004051134510410844071240c0000e00c1115256080c80e001010002c07010104008489110051480060124010325810741c00000f4209060055403c443d212000c50ba02c60b44400d004e070358250107a04900002d012841c0500381164000c1b5061400d2803015a40f00300c1d05095400c04105020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 777330773 1250 777329523 777329549
    0x906011427090a02070c03170403050610080f1902041a10030b03010b04090c031b0b2b06180c020c03030c06040b010b0f12281b080c0405010507050115 66
    0x2080d04000c6580c9610914009007149042d91725116100001c0b064400203001e5001252031854904219003528000c540c494100c0316103051230388200e000c2c4181c07400f452585105000020031190300000e400c01030303071480f408003140d4111540c00703100103460403050b0350382900400e07006402e098580c00d0040c07406006035500020380008000415084d81c1807100c0c403030303c00ca09125084012966030041c1d0f8045030303404001c50b42102c2000c81a81d04100281d801011907141c04108501620fa45003844065181d0410211006c07400d40607101b808c641203401150b910384041d1800009241d029440f042d14243c00e030040342c0030031801600080c0b039544600200880f036003010050004011821405d180540382c150543c5045c442079601c40f03002c0c3e004800b0841300a030030a02c045a18500301d02a0400c041802c4042d603d28404c8000305040a4480000d10100c400d400103d000d14003840360144502413011071043c0d9141520b00b80044945810420042d68507540e43c000008940309261000e0000304554403d02d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 777332023 1250 777330773 777330847
    0x90b0906041416050f040b040c09090c180b0a030609051f240c0f020603040f030e0a080304090b060d15031205030402031018060e100f090209060114 65
    0x81d00480402d1000030954002e0100102c1000b040b6801015200c003075400380600c141c440c00040192825081240d000391824600707002c1c080c0c0c86040c0c0c0301582c45004041c062707407009100c21a8010399103d684c815181807008203101c1d448904c0c00070058146203203804a8500e40740c860ba4801c8410559500c0100da10b114891556900c000e22543c0042554007000400031a5628250090076401e03840030081225050b0141c0c10005200e080110386600a0821600e034a01403803c10152049108190085139002c40421a03510f0109001c81c1a56200d1001c0c0d801d140c680041c90010b0580c10180d9a8481d0060111400540d010312031000c0350062408102001891401c1c455504812500c000040200800400002d03803000a00d24082d401440300004401c2554020344c541e01e2442c8c1c1c0c008214906181c04040280e20006440041291607001017292120520550048a24284001790803070303100c40002d0249e600450030861803c1002e41c01e240340030501141318038084034148105800481780d0001c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 777333273 1250 777332023 777332033
    0xf0209040c02060103020f150c010903030c0e100f0534021203130b030414030a3f110910020318010903080912030f1803060c04030309060503060103090b090604 70
    0x48903600714070b400500150350454005c6a00000511500390040b17001201c1e13a5a11007400707046a6001303100030b000b04080b80c06480c000303019000c0c0d11500000910052080d83c070310720700220244c1d0484401c0e1210071424091100070303500c0d5008800d440001c441c0c1d0902c10a005000000c40d0529202c03400c8003100f4400040c0b0400222100c6c026001c00c26600600071100001d06801000c13090711100208561259107501e0203442e0640e9401082c1458000405c40c0c3c40301030303084072406250b500b8140d100c19020016024a650359081c0001c2d6008110b4600300ea1080000700e0381c4010015448800740514003c90400890003000700c201e00300005074000181c0e552480540825420581c000b460509941451a00c800340c680c003403403030300d5445003a402c46141d0682e1010000c07140c2d40d201c6482c88070b0f115005d2051000b441d405c80c002c290700030f004060005421190f1a4125400d49502d51a020402401e103d03003210180c10042c41181815500c1c040c900200d1261006503208071031180040400c3e103071038945 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 777334523 1250 777333273 777333281
    0x150e161218060e030f030a0e03040b12040c0501080903091e0a0e0106030c090f060f090317070507050d0b0112050708060c09040b011e051e0310150804020d0f0203030d0f020904 77
    0x3d401e40d0010f02600e02841c0110080740d0304000f40380720208070600c0545505040d84510f500c026010400000c0006030307600701e002010310444c050404400701c0c964490064801c91300031900068a60400c0101c0c590078902204072000d900100c3e06010300c60a0041d000c40c19004c4603403c1066500c6c402c0b401040300f1039040c0144440c03d0010b103000340751300e0304d42000f10a00745050300170001841004421381d05028410070000000f950480240200711409005200c2c0b03070740c000c10095034140210b840115240c01d24850702031420350302900c18040b40c2c0ca0200307440101111031344200c8883c020b492000410a1080041c00c0c015416a06640c0c0e84850302d00820081b070710002034130b6050080301120f801140a00c00040d43c061800d13810200d655012003240d152541251002c05007000b1804000c5c040115900900041603401740c151807021800300c1d45041d1000030086900940c0009142d200400080c0ca1440110300c841c40541140d003000c121001e0802034801319890f01844581c0403400245920341070007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 777335773 1250 777334523 777334541
    0xc0a0609051c090b07060f1e1b02060c040b07051e0c09151e030a0c03080405012307120c0f1101020c0a03030225050907030b04150e16121806 62
    0x40c004031042ca0044c0c444914012120058100380d0b0341d049907400140e440d004101403000da1000076069050100ba040001c045082c02c03424001e01140c060092180006200750242051200c42814145800d0340f144440d030050808a070f060241040410014030700d00d40f600101c000150252010041c858280004668004c26801031146078506044150b03d60690107a411140003016240d40c07000c090200c0c0c038081401c0c10040803080d41c00e0000050121a2001d402139401c01d80c0e884064040421000010124105402805502c200b040c2e00029686540d0903440ac40307182400403040041d91100d243c203c038803410585407214880d50f40a80e541c4d05110314410340504441d0707900c001d420760714029903e9505d410141079940e070711444400b04019a40c603c4004141c0205a2011803034803c0c8018042c0a5120788540a43e00300000c80a076400384080780400e4444144a6504940d40c580505c0031251198248000340a03603081d00415145040c01601c8005802c480f000c0f000014900d414012661001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 777337023 1250 777335773 777335777
    0x31203020304021c1106070305120601020703021819050c07020406061d01080603030d020703050a12180b0a0e160815040f08031f0906080118080409020c0a0609051c 72
    0x4100801a0781d80c807136122502d074050440b03548106951130611006441d440042d0b0740460003040c0901095840b100801a50000081c1101c041d04c03600010b90f503500b220b003c003d41c0508000400d03807040840c9000103600a40164242d8200100350010000701c800551700d8003206000001c003241542000c1c0580c0f0000c104601d4075a0140b03034102d00c000c10b241e081500d51410800c0300c0c408120f155508000b034400128001004640d80c84141c54081c040d175000040050100300314041032041c440e0248510008054001e1449110700103d03921a008102c0042c140e030300c81d641c3d801a1460400040200114404000211062490400c880d80d0301e0886d41000c110001c1c041c3c00204400107800000842c2e1312503102001a407030f9281d061440300b1a1800076020039505034103c20001d40342d11541c024004489400008101500e000c003085d000c0d080c0c0e060300291180000300403c02c054001c0e640240080e080311700c152030b02c40515070368000955800304002c0d01c00c0d07441900a903083c600d01001c141c0401d030300c40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 777338129 1106 777337023 777337027
    0x112080c15011d040201020d0e01031d07060e06070507060c030521190203152115010608010e0103110103020f0c0a1b0b04051e0103020906031003120302 67
    0x901c242d007510b03d0444030200c003407003601d000140607640682c064180c1c10800310050303d03d0100721700b4081c105a92844000410710041098508580c0d008000e8101031349026401003000104100c0b00e84680030400c0004002500001d440045410a0504203c60089400c058841d0f0040016052a48581c00701e0621581c0400c060644100f0f41ba445410b2200f0100d0200c0d022400304850390140e005440c03141d801d00b0b2420700004645c50300b050100a5094640705411428a4840401054803070b030150014400583c008102c2400760950b4040180d1940c55900d4889002480d00d2006040c1540000c0b584a5445c12100311100803c00030100c0700318010170301c0c01400c02100c2e60041450902d85003000702c1e1a558586c01c440c02c8400042501d55550300004030030510703000c1d0035031081c1416402c01c00d0352040d03110940618807403590884402c6440b8a141000d80301e4071882613041c0e08041c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 777158273 777338129 := by
  have h0 := BRFrame.cov_init 777158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 777158273 ≤ n) (h2 : n < 777338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
