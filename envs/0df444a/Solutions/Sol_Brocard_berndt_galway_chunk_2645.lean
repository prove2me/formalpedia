-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2645
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:19:30.5407+00:00
-- url     : https://prove2.me/submissions/70f5e924-f154-44b3-be52-6debdbd34dc2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 475539568 ≤ n < 475719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 475540818 1250 475539568 475539583
    0x80d0501060e0108040c050f010e13020c0d020613060c140c1b0103150902030703090c080a11060a0c11030715020105041a0601020a03050304060902091503010c030c020a03050309070e0108 82
    0x5a00d0348611045240c0c0152051441200c0140c00c403d100d1b6800c00603400d14003940c0741c6000c2c0c1417625280300003100b800034a6490388003010314045540071980050200040009210702c001c01c0c0000c10750751a240000203203400408000402107a102c800140069008820100f080d005024403240c841d590382940300e0784e03100843c0204a00c00703541c15501d5a20750007446a00000400f14080d599011b05211200d406507002410840c201603641030076401050102c81004054520715000e00303000000ca0070843d502d0704580002c140300382810842c603054590025003c9800c6a4061480228170b4200350000b030601e040c2d54000c0c022000042c8603000600d506502032407040e88030320044410248800340c2d003c24240201c5507140941d21001a1f100403030300440107035034000e205e8400030620038010f50100700c0e0700b5010349250442024406100100c5e14081c0078500301d01d000707440e0400201142c0c8000035a5880d03009805420b2050001c042a2214410301100c0050404034010a9481d6903e9910903038a094 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 475542068 1250 475540818 475540829
    0x80f16060c020319140f090a1703041509050913110307080f060a02210a0b0607030309031b0b19020403050d0f020d0201021e0f120c0d0e060c07060513080d0501 70
    0x1200c02201004d40c080c4103805c610030103d0b285103040112805480c2d9080e440980b455601000c072540c0000c4407c201c5948200740000e51018545503407401100304440c07401c12055605004121400b0702182c2c941c1e007140b660041560140e401c07600a2820410b485a20b003004440c5c150240795000301c2d9040002503c03030f03200a215004c5030720a5903a29504400c030700400d0040c0015429141e0800601d0841010080d0415000600041c8044071000016405d80c800ca004801181c3c5410140741410b07008416104501c4524120f44c6030302002c2d607134481440c5030081c040a80c244522002030024625031317050703402641c4c0c807004680c50400ca182000e00702180c20514100148030701d04d100c0c401d10344180243e41105200d0654007c01903a000c440740041c0e000305002007403580703052068451503d107021042d4040e80c003810080e5600c481c0e100703000050310041a83c00b401c1e90b006406000407103102c8800c80e00b550340c00617400200d0313031102d039100c002c409440c000292000c5004140c41c040f414659014034120350 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 475543318 1250 475542068 475542097
    0x7020d03210204210f060e0f06010906140619140c0106080f0606101b2409060e010908040509130b09010209011b0807030c05070f030f060501080307080f16060c0203 72
    0x314001c03a00e24102502c00802018485d05800000c0011100d410815450b0a070b0800d880d8141d180308000380c600482640400f51460300e4880405c540c0340e0150001144030401e03980d0514007d848449003200100031400e0104000d0a038060505400d4000169242200ea1000078040140c0d10f200300c9603250400701c14580d5900174580410007602c0c2202c4203141280880e1036429960445101c40c18058a0b080d1041e80d03a0b1f8050026500d500382110300c0d89201c81448440041e13540300e41d00709902140c580120720749141e80340c1071201c808143c00d582610101c0e1421103e91241340c0d508030040c000001c01c0c11009016004c0b50042c0050444190080d103048002a81c440c49100c040c010548074044214402414501d410080341c00441d100e00b104134100c50007502101e981c40d03942d01545482d00300039030050b50868880d40090080180c02d00886006201d804021030401d00c0540b160100da00c1590224441c9410001e03100a1140c4c00ba1030754060f10380c1040c010400e9804841c0007170344940c4180c40d41290304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 475544568 1250 475543318 475543349
    0x5030d0605090610030b010c0f05061b0c031b0307060c0210050c040b220312051e0c1906060e070509090711100b031510060f020d0507020d03210204 65
    0x2c2c28000b02c16072040c4001040042c400c1800d190507801071040d02c1e8582c0c104140440d15034003003800c800d4075901a40c8200024002803400c5001d4080321050341400c405150810000314200c05400000d640030b151040720080811800c0e110014034502c03400d40020045030400c00c02103505138001c02c48a62140800a082c080d955945110384814404c1d400b4814400000f408401c18043c1903000c4c040e52840344d020380991440d1241c031003010b00400301c02e003200001d00019240c034815001c407085d25403800c0011052401d111168403001e4440f0030481e541070100001405410905c02560070050042c100008ae10000c0d00700400014910703445001464020060403010404840c4070310300c4045c04507141c0025220405600c0c2e034800140041100d0954180b241801d504450801c5001c02801110b8030b84048540c540341000c0900a504550241d07000d5401c4084040c034040e0708281110500b0b5030445104481300d60341e140983e03032049503602c210341360540800510208611340d030041c815100c5510744c04074503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 475545818 1250 475544568 475544579
    0x507080f0114190213230a080a1122150b09031218030f0303060108010609140108040c0905090d0e0301090f0803060a0b130614040b220503010905030d06 67
    0x26101811460020642c102000510901c0d1500710b0b4000410802000b41c94001c0204400b18400e4007a00401c090070340c1005480350514110200c1840c521054843d000c581e86050a02070721141052805400b403c06080d03440c1c3d40c0da9840e54900d22034144d03070083c80d0041107a030b80740000808040d41607100200000c1d6010400400c48802d80d48210710040081880180340b002440d096000801038945984110b40203006550b01481800510303841c5200454407450103000052241606900420502028a0082c03180703401d0458940c2c0416400c1c2441125a166444c0c481000180c2d0b51080110a180c002444038140340480c01d180111200c1e035070a498500d0f0802054202c600e5030600a0569011004500002359024043c1d070740030000174102410740d80eaa4080030b465506c140852510f204920409105003070300b04076a4034004c0360a000180c18a400d0071925000c510034028450100203001c04d041c0d290161b0071400001504002d0000d002244007441d0690381da80051410808060400c1c00c045003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 475547068 1250 475545818 475545821
    0x9030308130803070e01090506040308090f0f150c10110c0f0c030c0f12030301030f1b03150504050705030304080304180903021e0c091602011404030504060e030c0d0507080f01 77
    0x20a160004841c910f07640303884034240e40c5c00c4051540c942c1030140405d4001856500e180203803008502822485517208020000c21048003c2c010142e4410085244028040e8a54200c00d000b01c40c3c0c4058420350300d50391400714501e40030000382b41e40e131414100250740d00f030b0002940182095a0110f002c494007041c4043d03402e42c036011300542a5406a2010030442840d01c4d000b41c1ca072880003000781c0b200e480d0105014196080da07100740c209540020b5502c085800308004060003011400104805001c014116681c0381c40200300800001c1d011a190703000302d400d101003445020f00a00e0020f00312a500c0d0340d514503154590300280b0415400081054452458107200d0142d80541903042d40038100c000c008030702c0600000315558900e031702c512941a1420090b01d82c2c521550240c101c0c84c8840b443c4004015000b829500d40f01082c042a00d10034052100180d040819103040d43c000342004402c0c02d0205e0042403038a46034602541d84504c041502201307000340840c80b81d00303031402c2c1d40507a00030703030301c0d1030449070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 475548318 1250 475547068 475547101
    0x62604030221120907031a04050c120c090405100b0a0503060412110313090f1503021c05060408040303090501021203010308030604090203031306030b12120702010315030309030308 79
    0x2009600700b0460030022090108152407422400c030301c039a09110b1140398000e0050340455058005901085d000e01c00c0c0442141180b90b01c1c0b561031908003032854160b80b03441d11f65206480c910302030803d088103031b810360200b840a60240034014040700d44500e060706000c6d5540004641683c100c2d8503008603000c842c00c3c00c00704901556400707002806142c503640c4c1c503600040300d0780001c00100681810701a000710824030080c0307100c2c8500e140c40855541850701c94000c81e4487c043c030804040c41c1006c1d600909200004001c1103130b40480d6105498141c45610f001d504c04030240080050051f1010001007180c640c0180c0152030190341d03040042a114401640c3d20001504d020108140c02c0c8010000030354030b540115800103010f0008544840d00d0fa011030716640140303d8100e1031114004085c048603601d44504080a60125004104a034001e403a5544840c03510610300d100709400a220b030203590080c8c0054440030f18071000d05002d10390380d041c01442c0c8042800304800007541080464005541f803000301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 475549568 1250 475548318 475548323
    0xc03030e06040303020624090103030905040507091212021f0207050c0117040807050106051c05010b1c030c02061e131a1603110d1d0409032f0304062604 67
    0x9040f0742e124001f010302c20340c480b21500030013200c05000d0703001207840d6240e4103030086200f03880b0301840c1d030305080c10031043d520018030300d07010004581c00c10010404408190110207400c048550f0310b102108034200d05008461281000f040800d0001085c4140ca5500418140d0700460981d0411032210b001103c1010341850304586289400c1c01140c00b143e828001010707801d00c02d0000040d1640d0395004541e0314030b007181c5c0b5900300314240710504042c048207001c1d041d50f414088607112044140f070b00c1102e060725400300c2d001d0700f001340380c004100031900c50008480d40b00e07c10001203800e0454684202c03520350301041042000d100a01d00001d0075400f9401884800843c111016080880c000103080d044001c005054041000500210950560a01c1000030080c0d00d6070350044d000d091a20440c2003581d8040d2640d000b13030b25142045d008640e04c120010240005e001c080000f585580ca101c64490580700c03090a59804000340000d051600903814902111800001c01c465100460a6211040044401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 475550818 1250 475549568 475549573
    0x15090605090c07031409030618010b040509030d020f0f041215060303140706290a05010509030d03020a0c06060e040b130c1701090503071a0112050d05071a040c03030e0604030302 78
    0x80c1d80002d0080e010103010103030800c405d90411900784006031030700350103592110088944800d4004076040c2030180310381914050f28148040d003001d400c80c5582e4401c61304080c001a5003c96915035103c00141218114460b0159070703615aa21002c03200148560b040c030880d00b200c40c081c00000d041f15140103803022030744c050b129032a40c480781074003c1c4142d03406508201c2e00d03165240740100d184117201e04484140b2850032026000c80200005201203e1500d07086517060007018807400300709550000d00340302c00e80200c0c980580c4800c151081901d0300318040300010583c03828000041b0f080c002d046012845075016034140c042c1929401d01c401d03075048281c4400381080000d10800d11034000302c40c0018100070790040000450702c9a90322041c0c1542c104000c11100c0c014000000c1c0d8117103c2c104401e40c00340081d849a0710995038650384055072000d10600810074040041044000e0140340d02151000342c0419110040b1480c0600d4901c1c4c40c94440d0008038045100c010445001d41040020748003640c0d4507400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 475552068 1250 475550818 475550827
    0x150d051012080a0504030f0b0103060f201303120503100504050103030e01031e0e0a0b01170601090b030a0218100902091305060604080102072d020904030c02120115090605090c 77
    0x1030321005030707100c0300403d018031408020001c0080c5840400d00c1045001d400852400d50440c5000020340716010310148100307007131031300140b000f0154100e0b100c211222a80100e9990440c1030344400d81090b19030000e001c508e800c400d00001039800000031403080c8000c0842c25035181d01e034420001204d00a010150010303e588080700c00c954003a510200d5803224810880c80501480140072090724210510f80d005500300030121406c01c08840640c07800341018006035660707210011612580d6070014850610466120254441c85480034071041480c260090001601591000000703410a4000d644c548003071a05000b0000d5009154401d03100600307001449c22000030081940c2c00c0103010054070903503100002704000580300e0000d20081084d90702c1140d14095440c800d41101c03001124441042500c190100741200040c1e90f81c2031050f5000c5d0f418104101d080c005400864080c02c522141d0b9452503103010546202c007442d1074404c1c2c040310010b28060040c2a16070003805482d480641d148000c0b00020f01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 475553318 1250 475552068 475552073
    0x111040e100e0c090d0507050319030315050d30050a08090a03210609180210090806010b070809030f06090c01141206060d020712141e0c010902150d051012 68
    0x3001710500ba03014004481c1951344880001f801e06940440c1d40d02100070145035401055018081d00840c0e40c05101c00e203070f5403850b00d00441c0b500e200c1c038000144001003090320250404071044000c003142c203644140240581c580d03e406840760784041c50040c0032030f1003000000c46084000030748055240c3d059440000017140c00c1c041140b40c071001c28052400a403501008180c9402601c0b5801503210040c0c4c0c0b000d401744880c0188a4404449080107040084030801444909400240281100c82d04a0b55554403030782810601c80e00d0055074141030b03150040403070340b40c041003000030418007407017414041e0b52a1920000055590032000d402a840b0702c4402e100c40494210418003069100e030010f00124501001c08000340c0499010020803180350410400151019501c20110341200f00250b50f41840c003da0981403044200700c0c0d0111218078080040c0341ca106040a4010355400c950182210007a101c08001d000d00ba6080020600e099501c0c0600003200d8617404000441102c1c100c4640b0554101030f074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 475554568 1250 475553318 475553329
    0x1104020d0e0a080706110a020312060103140a060503010501080309010801050f010c0c0303050d15140f010302040906060e090705030708010e040203120a050703020c06030c090f030111040e100e0c09 86
    0x6031044544903911404241806400c0c8100850948100d54080c1d980b0340e03529102003200c04001040084100030700c60314610f25000411610420620f008440f45a40c8243c01200a000700c030000c0690400d10400b0b0040ca46901c5d003040003500e80c114020b005603070300e9000255684c01900240c5002461600040049050040c0c201044038810f00d80304444071034940310300030f1124840e80118005000082c4001c4107400780d10500c03560054486442e25944e1030095100b0850107032441c81d0b8400d440b20b10000c411a03010f6411a80105103052041c80081d507601805005003c0401d01d05005480303d50000d212a0f20035000c80784104030f1525046c856900b0300c0952700c001d660040c001ca805104608142c0d000d040c2080251400040b940d44490b40d410461030002d0406013000c82c000e010300800d00500000c0c030301d00010348181c91425114800c0c001030990000703001d0100100159680d000000f03002c900140742001880c41419140100c00080350b66a414420906048074000300d02ca0b4140450300c19480c20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 475555818 1250 475554568 475554577
    0x10608160c05160b13290c0a06021209061e0103060c1806090305070506070215031b040e0105211015090603060501050909060105010203040b1803120a120e19021f030213080a110402 79
    0x190211828403508da500c8104980c0610740c2d2203604030900c1d00f00204d040003000070f581d1020302c86a0340580400d104a216541c08010b00000344907a488080310090b49101d00070020004d200301c030f0034083c002ea0700d900241658141d0b000a940c0c45c040d6078400302c0c0d6130500404442a0590140c04040d1000c107015a9141320707000600700090030301d0f5501e0f982c11503172b507000090300c00ba1141491045a40d49000c0811000c881110000c001d40020407050100192000c54a40403072010741a010500180c18100f0300d56002d9590000b20b070b41882c280b00030090240650050b8180c2d0010f80380b5004681711400b0740e5aa545c403d218140c010391007040309101e01c00b105405024007404000e41e100c100426900000d007849010085607500d82c901050300c1220b10b034442e0700c1502012080c0d50400c011203804840b2a11030f1039010b929010014080160310441d15140e1210100048450680c5507145030b010300200a035101c2404410040607030070340428131080108000301465400050520110030100c05d1102a420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 475557068 1250 475555818 475555837
    0x10b0a0503100f0b0301060806180a051005040f02030106020c12070506090f060d0b03011104080703080a02070e16020c010305060d0201030e0f0f0312010608160c05160b1329 76
    0x418400607046111180f02000391001c4841c243d100d6040040052618000810452080d2a105071a0901a0103810340d40c0e0045402c0201046507a20b92421941180e00360b1700c016003080c5072140c00041300c0400d90195058132144d500392480f100d00101040b080d00e4400082d406d0681103000c081201e441c0110007416410f00223404800e44491481c0011040c0d0462084460195160101c0034058542031003001e01c0340075000368443c00c1c28149880c6a9499842e800020904940007440c06101e9000b0030400c4001e01540c0341c1303060300d45401100030b441c2a8800121001610440c02d1050980d802070203030520480c0c010340110000c0751541c0046000e0220b040240400c1e026810542c0e030000e40600c1000c4880c00f915004540e150001c074454502510143e20072010460800140811144a038502007211003482c545440b54104c0703810300d582000003040404488544d01038000800400c48806000200b400600c1e0035903581d6a08803600f5081c5c0701621a906000801f000b207600c907040c41024040f0801c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 475558318 1250 475557068 475557091
    0xf170d180902070b04020a06140405010809151f0603050c1c060e0703090c090903080106051b0105100302040e070f3c031704030b04030302032802040602100203010b0a0503 75
    0x203540c1d1400c401240d100b20401d4a41e80e014400b00000d500b0724260520051005142034a03200103000b02c42079003405180503090403c880080490480c0c50100110400d403100d440c1b02c250786e0300382210001a0302c2401e060007603044404400000340c181c042d204903031248500c0c6c0d080a240020380b038103400540400c0e9a0200e181c075510301c400705041c00304c0c505580c0f040c0e10f15100081e00e00c109040003181d80b00c15030701080215041000c200c00195100c00918110b6140d03080c0f81d034446603610102d8074a41d5544042214035840e200401904507a15400074045074005d0f00c003000000110080c03d5102c00144c011803080310281402003240102c25003007190044403d40320100400e41240009866004401c099682caa900750030920900002c1c10a03090591041c01180b0700d01440d684d54081c82044c014809020f040d40800010fa10001d1010310a40414140c0040d03501032445860190003034205003d4800148540e0440c00400d5965101b102e06031500c0c0c4c01007500740180351104a42076840107205000e0316 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 475559568 1250 475558318 475558367
    0x9071409010501030e0a1b17010e0c0d14030d0506100f080f0606040e0c0c071e0603021303080c0a0b01080c150c01020903030d020703080c071e0c080d03060f170d 71
    0x30f00c0c42210121805102031f03030080a624008001210345c200b03410a00d10b50745060000203c0074800500694201cbc8107840d003e1066545003800f03003640312145403465244c040010144101e000380e034400740c8104400c680c2110001c0d0312003011513145869030005800315580502041c0c451100000165101800038070551402d80c89852a1001a5090350810b06520f004200c10075080c03000c0c4403090207010b29a20080e134000e92141000121000351142c2024180e00040704410003030380c0c03c0034601641d00700000680c1e80e0000c0c12040c0d50780900310f02c02d031381c0e485107000042044d031700c0840c000740b203218020304525180c0f00503207040280f98000c00d0f00b20410366081020603420b850034000740509201c1203000503107a50741424080c00304080106455460b6408000c4000043d100906000320641c100000d0307249a5003a01c0c2c642c0e0301c0c81d05600030081521030141c241042ca94150804c40c1510030012000c5011966100c04e0f140172403a014044d08070303800003041d1611451280e13803a2072203038034500c2d010030b2903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 475560818 1250 475559568 475559573
    0x103020904060b030123040c080a1a060303070614040c050a181a040912030f020a050a050d0b0418060e030702031f15061d010906090501050a141209071409010501030e0a 74
    0x1295907600207080c040000c50204801c0c0141a080c500050481102412b8042d5030b6a451034140401300d41e2100903440d140d03012030b0442d02c00700309666840d0751242d010000740e9070444103510000000c0720119180b00000601184a041a0030b005c0210b4418080044090f444088200c0150500c03c0d0041c00c44d900300740c162803441d135541c058003155a001d1a041d0b5404d01d80b0b814000c0660758450507900c40240100809140640d100007101c2c0c201e282c1d494941e444440511081c0080c00c1c501d1441580b1030305100c40131601007101c00740c030819070784149070400c04d40e20240200d0380c40e401190400b0703500d600410078020403a040241000b5008041d400000b03009410f803000e94042010b1904900d0000f0085d01003c88203003040da07240000000b003428502042413901000a1101c0303124001c6904005010810000d018000e2210700da10343c0e2150002d03501d880e110180752000840480700d458151140440018516507649c2d6204c62807200030300380c0b03a100c0e8241001034000e00b0360070910318102e02c87c0901c02400f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 475562068 1250 475560818 475560851
    0xb01020c0f060c010f090512160b070c05100b0316120b090f030406050706050946050c010906080c0706230a0902033315130605010906080103020904060b0301 69
    0x1143c9850010003d0046d845041007450300034050035100c481002080818042240e002a001140d5032100d0711280d5642d5100045030f40c450380c108001c219105001009900d8a00d076000010f01100c150101d80040d0546820b07031035030084911400c2c18912442a0030300102d001301424a0740032000310100d0b0915540101002d145500c540c0c0841d00144c004140b2104020310390003066007040d060001400144d0f81290303001e20301283c80d030a03e900c5000008240044002845011100e02c2044421818500c1941041c1e5152415203c11600249049401180b81401903050078068039200a0503400c041e21552100024860003411101c0126005000d406007621a942c0d00d12540c0c002c080407038804690b205161a01402c0f00303071400b1400044c0301041c4c002851b02801d921089440421038101c3c1c03140000b100100c039101c4c40003a0011113403120061034400c15040502181d5080c0c1e9405c0000e41d50394012907a0031002c0c080203600c1059200403030b001c500140c20006007032100034000220000daa150102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 475563318 1250 475562068 475562081
    0x20d030206010e0a0b0108070e0a08150108010c020f0714180411130506060708070c050303131401020303150603040c24080a182006030109051602010b01020c0f060c01 73
    0x240141d101c1d4005012101031807402d43e070031900c00402071041800c40300010317200820040034041005a205000f00d626503610700110014200c480907035980c040c580c10720130a200d0090060410660806001c14909440041c0d01041d04060300003034109203080584d10030310306966684841d4001c403001c142c2c0b002408030908c1c180c0542e1064041d0a5128410707010310800000c840f00c4a45024500390800c40301e0340b605000c84210540c040c7c111591001d181c68000b04202e0713140c219681520001ca1080c0d0107071440403040007034400d00d0109100140c0500300480c1d80744811941ca0150420294044209081c0f60001d0350304203218030207100845403950001405426a0301345103160102102a42c1d00300386c0c200030000e400940440091154000c105202d005560500000030720744402496201c160345071404c03ca25401c07200030040c41d5656500c01400c1c003d0700056135000203812003440c01e110681e00500c105c2c281c080040c1c003d03003941c400d440200310100001a43c210740041040003501424a4203220382e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 475564568 1250 475563318 475563323
    0x3050d061a0702030d1e050d0e030c010b28090e1f060f06021b1c050f060a0e1f020c010b1215071107030809040219080105280b070807020d 61
    0x15600c90030a03004041c509002a1201401d06c41c808900c404c810714601070315036072140c10b818101c0c4e413828074143d540010326100508502c07601022818260fa16011340000b2a0080c045035a1407030a0381900132042e00220b048600b20242410100c02c0200c20300035004009802e601209030344060998060301071000c190030b07002d5600725131340700024000e5418049044000c2d14462000f41000c1c81030b003148001c0c0031102c0040d80d00c201840580e501c4416152060114420f81c04006c0e150b007042584111a950380e02600d14a503ca070501c803ca940003440041d04032050608088a82541c8034540c1c40c16009502c1005c03a00d40c95525030702410450303102c0d01140100e590501004100500c0e052036176445600001d0200410044101c0c88140044c00016400302600d0304002c40341c1d629640140060001e1140c01401030400003a40c440b44100c50f003204120b4129282900c100200072204440d4003442c0201c9820310000520f5035000303100c0c0d11821f81c00340906c54401c04c0103d140a02d00e0300024074844800c0ca04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 475565818 1250 475564568 475564619
    0x3008071d0301180308070906050304060b0604080304090204030c0603020903031803010e0d2001020319050a060e01030602090306061f030e030c1e0d020a0209070c0204110313020103051602070303050d06 88
    0xa03d0708159001341c1c4c81368030001c6880c0c0410014100341c40180f4900c0007030000f414207030b140c07501046580d807614201d030000d200d044101ea42d01ca0f550007801010350014841581c40744054080081d0080c064000c0300c05242008002e0b5181032081c00744460040340300c50b00c43c1e80641d0b8171030282e8604c3c1c00411004004003002c1c1c607042e1112608400b0421403140c41d40c0000a1a40140103002034203c0e415101240c00c040d924022486944001e1400024050f6a0106088409082c000414415658010450000240c0655400d0f5603480180065101844205e9003880c50195402140912079032081d0300b144080f005680c980284008454a0300c01e1582c00e520340701d181c0000302d502d00c181c1004a038196040705d001500d0006103940014502c5c03130303000f813032001400b8982650310210b40c0d90350b014004551942089540341d05240015400c26407000204902080c0341ca404600320a10f00c600309c0491100d00d9000700300c01400c607a0103c03002d412250302c01b04045e444100c0441c0e00400400c40c1120180503100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 475567068 1250 475565818 475565861
    0x40f1b030212090f060106050a02030f041d061504140a05030a1a071419110a030206090d08040f02040c1701090c09050d0308010b0c0c0a033008071d0301 67
    0x10441c04000b00a030041d1001c0d80700701041061000c000c2481411580d00e400c1803034461a5542069040d03200c0d0216500070a03c0001c1d004c03c88030030251020106203520041c25400303070307104002d0010b02d95401510399900c00c1c06001c1040000d181418500300100c000c0c05903881035a03a6004685000c42e1101c08450701c20700141c00c181e52204601681c0d501041c54600459000300baa100a0f4061180500190b1072041c84560600c84c24082d81105201c01c03000d6003200c602c0034040c14004c1d1a5442594181e10314011401000081441114854025908540d019050108543c03c100080001282180c28492a106085602c030201e0743c0c517900a103103058000c0362101d600c4000500d03140c01504010710482075680c04002080e4041906070640b08032100d6660703100c0055142525229a07142c00c00c4d40311240350700c0841000000701d4890a02c90b4040500403008010b020082c1107851414080800500d494000508551240340c40c60024003540406d02001079081c400f0a00350b90764030b0107405501c0110761 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 475568318 1250 475567068 475567087
    0x2f01090614040203010e030a050f070c0b1b06070f090918021809010f05070c0b07020705040213080606040908121e040b090d050c070b0c070f0f210f02040f1b0302 71
    0x2c0d00081c114100090362519403103501c00740207401541000042e102b40401c02e40d0821094407504000f40a081200b10f0f01c901d840141e01c00c0866402404500c6401181c01189801d0300901d0081c03140603030b6455215059080182520007060064146a0050460711503040940c60f00c02c1e110115520000c004040b07460289412400c0d40e10180e018003c0341d1410301000300859000f224090f00d41e40c8050780490740c1d01e55080880c94401682c0249611031b02c00a2249001543d10210808480c020000d0b00d2440d0381f5542000704540b00041d029140450030040b200000115076040340c0d0101710012001021040607804030141a0111021a44014860240f00308002c0422040c0100041c501c0c01031300d004201421a0b485410610643c600900c0204907001c40c01e00a04c145406070a02d01d0041c11350b1035446130802400e8049109003202c065030011500c00e20680340080b0407480c2d42085030442c3c2a490340e400d200003040304402454205a603521604e40b078240d125a482c14021070742d6405070702c40c00043c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 475569568 1250 475568318 475568321
    0xa03080106080112060b011106091b06040510050a0207080d03020d051f1a07080a08190e190302100905160504021908041e0c0e072f0109061404020301 66
    0x180c001005000901c0b0040055180c2809000681c41d40000c2c0450058100801a54603241803100501240641c074200494000005460300301480981c07200b10354400400c00b804400c1c401c1d4000c2e140c201111000b0f008910340288002d0650180501c1102c10702c03981c8014031070900c90640450320020380c0000c0c1c40030400c12203000340d03074103c04400c00c07040305072101c1d203169800e20050344601c490681d034100a885c3c40e02000800d440700c0031b4015500320340c1e40d4402d80000b451440308560609091081445420070b41c2c40741c1c480c850310407035004010100c10301d090000207044d034070f400320031030443c4540c1d01d203141c9030032050140c1d6001501c42c20051641d032681aa580002941503004240200e2041c019608012002681100000f603a03092000302c548840c180000141040c0341c3c0150036610500d0402c04000510414400320348034442804525140c10f4801c03100c3c030b116021041c007500ea0400e1701140d01c0280f0a103280107104400e000054600d4141e80c5c20b401d035103940306d0041d42a04894200820750800703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 475570818 1250 475569568 475569571
    0x1e0105010e06030102090d060b03120c070602071502060105010c15020d0f110702011704020109050312030142110106060503090c0a0f090b0d060e030a020709050702120d060f080a0308 80
    0x46000b5424081070401040284d00f004031f01030021500d600390300405440034060004081c1c036030404030380e990100321221030341d03031545109450051107140d100241c04810303244040a40d00003940a0f0015902c0c1200440b05803000e440140d4411b845882c85c1880c00449100410032104602e20104071a11485035890848a0301b03000a110040701b04001c40040c0e80c84000b031944500d02101c80c203000c0d01c45000484801d219030308402c2d00b600c6440d041081407501003001c1d5040311b01c1648200d000d640310000034108800c0c04000e80741c2d4452100309041c802c1091000e1030360904114034000052031181c825983c00e56406a110301e012410000034400d00400c01d000c1240d440307a040c0d5401d02c110f0307d00404d00c825070300140300c0da580c001c0c0d590540c58030982da4608d20001641d0040d40901000c428001d0080d120360040700c4000152003607800001e2282d01900500d4490784d8260040c09811804070031b12909640b00c3e01201d92181e03501d850101d04511281095005849010000c181e41441c03850f018281c402c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 475572068 1250 475570818 475570831
    0x111204060c0806150f040807060c050c0103110414011101020a03140c030403020606120f01060f06120501180f020d090323120402040902130f050603120322051e0105010e 74
    0x400400c2001c80d441308154941d09600800740160b50740102926082103000d1078000170120b0240782c030002860b543c422500e0003900d0050090b1007440003644010f40440d0b60703441610729010740c24817040008080c41c048244505006042202050140360710441c22640300d40d01e5100485e40d609211000600341c100000c2d400f22108085a186040988000e0755075400204800d11034800c40128041c2c1b61410300c030045455100500030b2004648406a98458240c14042c080c00070746e4980940c648040c040c01894122005908140d1020120300903880c00342000f4001414015020041e46a84044a00c11032400c54080e554009800001c0080203150040000d80e07007503085802d06c2101c907048070500f40c2c42d800550490303000130110350901c01b01e1000003d0104840501d40340451806500c02d20b41c101501c02c10044041e1821850140b0043e0001d02041da00e69100c0f440207122111000030010760800103d00510440d82d000307008803000701181e09000b03200802079458000420107100d032500b40980007903 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 475573318 1250 475572068 475572077
    0x101701110405090903040308070b06010e1e06030a0b06040f060f0c05060601260a1d0d02210c0a1a0f0610120216050a021302090a0909020103111204060c 67
    0x44280340d0214540a180141485550040c021890701e540420450b00195441444152501c2150a0a1400078412507205010130100700d451074941ca002c000c2180240c1d64056910811100b400a1010355000100030f084030740e40d114071003c0300da035541004e07200811941d02e041c01840d05154008140f00d0b4010000000e010344408810006900801c0e510740c0b0a4081c60080150040740e225001d42080b42140a0212080d8001b80003620355550481e03850615064852034041c02c501d900103076204094070088006030044203003020b4a10074a40400c181546a04102c0d01301341c1d10242e500d04200c200001101c401e44c407004242440052000ca0680c00b0f001042980c0451070180301054400c0c0030b40d8000c0e410040070340d004004c8290143d069074a00055001d030410025034500d0403a66440084109a20542c0d400e030700d0803d9990340e402101c4a50001520344150300d46882420f101403c09442e040b4141a25030101400e0085040f0240004c142d0398051130085040038104002142c0f490780301c010402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 475574568 1250 475573318 475573331
    0x51003090b1306020f0c0c121b01140c0111070c0f181d0601060e0315010b0f0a1e0e090f040203120d090b0106020d081f030609030314101701 62
    0x31212448194400e89003502c281d00b40480b4907207640240714a0000d06031014001c240c040c10444000b42291440100390307001610360a020b1002556000b0780e071254000450101c6500c02d46511549040e255540800851810850f580030510b096984580941d0345108000c94070344184207030101d1810003013070030203000f1140c1d41c03c2c514654100e0300030071000b000440d00c54100c80204150419440402486070055502c2540c441c4c0c0c1c000d00004850001d14440d01c502410300c001c54031801c0d41c1604940d1507041041c9800c0258551115a42080c5021001c1c40050211181c8000c00c00f400d40ea55800d013030fa9904112407219007080551000544007010002e00728003004010780b4006032011202046003d6140c07a850200d00360800307001c0503c170007082d602988000007526500043c5000c035408040d106c0500d41c0d9168004480015021225154010707490b82040010410700d03030246c03d00d1800384ca40410348404425a0341045801034410301300c0400f0101041110107101140081109007040090251 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 475575818 1250 475574568 475574573
    0x60f050304060c1b060507140310050114120f2e171006080c010305060d030e0103050c0c0109110307050301021e0a0c02030a06090302070509040807111c080405100309 73
    0x8a00000700300901d0183da401c0311250143c0110030f4038003813400c840d02c0f480072003010f8541030300500307011f44030071740402d880e40140000c5040400649100e1141340000b110014585801103510003042d079050740615204101010090442c01100e0384200d039803800402240c00d08429410000e001006000c0f00000e060b801c400301c10011540c064210761802c04c103902040006030f401418020b2401c0244a003038689040043c032600049075000448400b41c9040066030f68090521100014079a130050001e9000301e402c14841d030203988001c0e080144010741d2420b01d52007910f0350b403c4504c500c2c015101c40a04000e280181c1c40c08010b2503002d040b058000b54148410480400c1e000e240c5200004400324020864015840c820707450081d05030303001400c8451407201401c04400426555030240c0050099110201e5503090184080d401164041d0f0700342c0c644221602c620740e0303900b0454022940101c406801111140001000000990040400710350baa480d1004005140a028104800741400d01990001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 475577068 1250 475575818 475575827
    0xb01080711101e020a03050105040e07061205070309020a0b090405070212070f170f070c1a0a050d060b04080106140d080702090a0609020d05010905090a0803010515070215090109060f 80
    0x2850b400003440402e11600c1c403050181c001110040c8000c40a2000c501d410015a154100034120b07002a501080a00c0751003120545a65013800380c2e001180e1042001950704a55502050344500b16160004858410f6070005a401e10b056015031500d0801160b40c20040c6030521070725810054a0006105000401460924500135110050030b0380c2601508502440b00744007900d20700d18142c0c060aa617504855203e2500d41e041040140d544001c0081e020610105042e21510005034001510742000030340503045071075038000e10601c108580c032454001568507060b0081d0011745210800820b6a90411561080031403800d011680706803004516000401c1109040b50903254050319980300c640d0740c0c0084503001d010540e00c804505440022811032100c0a640f0050507078030004000c0c003942e1030f01c40c1125624801345001810010040004201174074081c04507581c0451000c070824209916500003e40c0421701d0750f401a41c001001510300da0306e41e0b003c81e954002c0c0800d414102a2440315000c02007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 475578318 1250 475577068 475577083
    0x3050609150106051c110406020d1706060f090405010305010507030b0f1302030c04330305041121011a04180c0e0703020903100b0901140d0209130206030a0b01080711 73
    0x5007030160005411203080b001e03000e6038041c4d4002c181c083c00f031b10640c2c1d0544986903003e0320400300180244000301c2d010762f1250041e038407510b11051040e1100e490b0a020489580d02000032100d840c0c80c100105000ca031154020a4029030284000194526245102409544400d81d0b0030f8891541400d003881c040e036401000c0310104260350303001601c0c1d99401010040314442c0390407050084d80d03240b07a4010740140364051603500340c4a224000b203018014000c15000d40d4029100107004108031400420366003001100020315481032045504000d07c65099130342107400d10280349a04501c044015a0710741814020034516840401800402c00d5540c3c541400c010480c1c01415032900981c008101514401d8042d5980c2500040c250ba912403a83c21188009002c0001b41a00819829000064001c0501c0380a103c01c1c1d8003410b011914582a42000040e00c0000c10384901c031313550340c1e0159025031580c40165201c0c3c024035400068400c800f10001d0003144004102800b00300003040b20003080407001c107404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 475579568 1250 475578318 475578329
    0x30303111c05091504320a1502040506070c0e2503090c1a0d0b0405101e0b0412050c0303090a23030f0102090f0312030c0d0605060d06030506091501 65
    0x240b5622910b40d9141440c0103100c0799070070b44030f800d401c0c0300034803841c100205410404140301d02100000340c841d8000c18200c042e02400c1e140c00c02c00c61003001c00d040c17a03500b8680941c0644018039250b1201c00180042d080003000f42c80d11003030b1b02030510001d0410395690380c1210070030f4600c000300c505040c030701e41c00803200b0b0b00850205911100440f04110303040c00da03400500f503c0100e4500c0790300505444c6001c0e811481003404d045050081485a0742440d10a9500409080f0606a2600c2c20a14210007420038241034076a0403041880000c0c201d0b80c440098400b0b4415601404556092414018607110030412228072a800c200a614256512103050104407192003a10384d11060a10000c01c0440030054500c80d014010710400e2035800b00194002c00100d40119004998070754a281410707601d48040501e4031102000704081381c030480d840b00c06051700c910a40d101142e6240c4907000b0611a0b04a11480d100c1c55880701410b008001c0d0074400c90750701074000d000420340320705d42c580085482c51040c80748 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 475580818 1250 475579568 475579571
    0x2180118030b06131503060902010f030525110304030804180b012001020714101a2407051002070b070806030705010509120106290408060a1503140601030303111c 71
    0x4044010300344d50041062003000c8039000d40056a241005000361a174944c0c22400101440004034070680a88906406018113604504540018407585a5200030002d41d04082c400590500ca01c108010002840694442c1c050583c4942c078000c103240c0e0049a0050003580340f810040d420420b0f136886203010400f15581c6190311700c3c448011117031900912a051002c2c04081243c400c0f80101140010f8008140c40007080c200210071020301610309030303425911346c2903006007000f60b111500851350003c1d02000030110039407450032240d035548907d0074100f0048665000d4012601d4400e1000741061503901520b1800d110085181c0400002d0b01c8201c14000c20341401804145c1c0724a5413500d0041d55690013058000300522921044c980c9c1c0190804d50300740011102c1c840c0850182d60302e070340c2520b00b2640040001c2c4060b1303c51100401c00760011019012618100503000004113001082c103030301044218021748036950441c28000c041e00e41c0002a02d0f0f1070b080402c480e000100c140e031480002c0d05a4505c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 475582068 1250 475580818 475580839
    0x1707151209062a0c0803040209040c0503060f0f0709050303120c0f070507081e06010611240f060109080c010320360d08090a0902180118030b06 63
    0x8000c401028541c41c050102481c203881d03003020b000d002203049803209103011100c48444034098100d81d07034568848020440c000c1800842c00500340b83c0b1851790000c0c481c0c3c140c4600140c440010920304a4102d460003001c00c0d1500900540c403c480294a42040443c50091126801c3c400402c1d524400d2407503c02c0d040d10750300c0016510241600948201c2068452080d03900c3c2e1035400c01564600c0c05021799070960080005c1202416480514004000c6413074000d400603078605031094419940c0c800c071045960054040e001c0d10072130380c0307282c1d00402854109100c0190600310741400c00144004d00103070610400c0c4c18103000c0f005000440000c801c1e0300b442c011402c400149000500414900b50325054140007280c0340074188500c200c90b1508240302c840c41400302d0a00161080418510559241c0100841c02c2c50404500060014851000301500302c0c110145d50340c0e1b41d2400c81e07102c400c10740038444201c0c0c03804ca41d569001110310701505c4100c861842d494116100e8807490f500c01751019214118081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 475583318 1250 475582068 475582097
    0x12091409090c1201061706060918210406030b0f03120a09050a08061911031504140a061a280921021503040506010303050a050c16170715 60
    0x7007019005a03000d007400b01e211100c03031903860103004d640c014030310546c400c41480610041c0000c0d4145c450600140701c128140c450800c8445070620012500c00580500c00121040b850f0406000020107a00050260b445240403801000c483e058010740d445040c0e000f02d407488650b000602120700c9114404400d580d030703004440c1a100010750340c0c0b01c184c2220f640300000030b81c403a012944078030034120364407030100c074000500400f000c8030f40d121951080c14005001290407001c84130340102c505800a000003030242100ca5000030210350854492a805840b03100c144900c4400f00406a110842910281c1c10008801d58a45d10310358020300e120f0982070702c03076840c0344802d1040d03100c0802040f01c4a9820803417000600c0070f1a007515502000d9000e16680c1561207291002202100d20407030708100036001a90860f5001c858681c031552080b020880700703006071242d510040c42220f160600d40f080b01c114240c54070b421143d042e82003000d03a50b1280c104002c1080080c0b1140c4201c40180e01c06e280c6102000b2421 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 475584568 1250 475583318 475583323
    0x5011211131509150e0103050a0b070c0f0b04020102010b2d0a0308040b0d11120f070302041d0105040e060f0403050702031212070e0f0102030a1404030602030f041209140909 76
    0x103030322101104a8038100140c8003d40340d00180b2000d0400810f0040c09486000001c84d42e070082c0320041c0342c2d6100b031620300b01142824503020340224491401251a10aa880c1c186400c2c041060940705189001c007400704540c0c09210385905208190b44015040021100d0590144040000d0034031020000d80300c80c18640e079a8450b44c0c040c55220106540302d5031607e4080c000d90304407072200b051040c5006403003540071514005880d030080e40c0040c0e008260355000004042080c0c090004c0c0300340b5030240b00c040394002032121450389215030004071055039850a820442a5541903d103582545c00c841c00313002d0384024008880368043d4160502941d82d070304134030110b0301e00b246141082d0720059010401c000e03401302a105140c09120703203990714100c2081d8501086110008100c155026900030020708450303502945040150720880030301c49080558070344a034010381c3d1040301d2050900b846c1c041080200301065014020395410f51400001c02030401c0039040003800200f2a80d8401c400d168005020038108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 475585818 1250 475584568 475584581
    0xa0216050a03080d0f020c0a0b0c120a18120302070203010f02070c05100507020901030321140105040e010b060301120201090909020a0b090607060c0917011a0f0a0b030f04060501121113 81
    0x34078038210351b1140d47d0204192210141d0070111000c002d02d1021030004e8814000340d51a84000388103580706511640c494100030861000001c8c12000d14820319030108880c02100111060a61000350342c4905510406003100d014546508620744188000000701c1c131444c5d049010b0b21426074503c50101103a16084c0d42c1381c051740c03200a603c20740b8080040201a8010702e1240207100038180b0b4005800c0c0e240514007510360501a81c241c18484000400c164030b0076400942c01d1070358007070000030007014200c04074030603a100b600000000d02082c080c0c0c0c000c41d60312030300756001007440d10020041100750f5400507015504900c04c10301c40c058003150702c009956980088540540d40002c08100c0003501c0580541520f40911843e0004c141c000042410803a044c00703500c0000c4041014400c0b400685000c2100c0c031030728903e5841c1c100581e4940800c98241d040011400b620b01280c0784a040d00d86840c0030b40513143d05802024100c41a9101c9034005161800030340f0040f0003c480040f01010600080d5004240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 475587068 1250 475585818 475585841
    0x30f0409060609050d03020615180a05060909030f0f0a0509030a05151812030414100f18050c040902040209060d05180d020d0503070e090c0a0216050a03080d 69
    0x140008015800d6444181120003076143d40b1102e560720001c104482a90030000b40150300300f07500080400c68255003100308114020a070701e204010303841070580041011901120b00540e11010312510b450308002c04c1c0c6c2d0018810340158075088580c0c1d000f200b24001d0125515900101281d1010340600443c150b84206801404990384c2d0405402c08a40e00e024041500c08140c0001000c01c924034054940031118026280c007e090418080002d10055840140113a9204011078040d03640c0c2901032101c1c2540c5460b000011403411089101101280c040c14195104400040c0d1100d0000c2c02c003084149440100316400a04e100903030022a002c1e205114207203610550006440d40b03800e01c50f51001307010341c80c003402616001c280c8000e015618041c0200400140c1e10120624852901c00c41c011544181545001d900d4010507502041c41503005031092a400b50000c039412882036810040b00d0703a1003401030f0401ca520b6152270082007001d50a400040c0c500c1e440003418005014207604000710022 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 475588318 1250 475587068 475587097
    0x2031c0c08092704020405060f060403022407030f091d0f04060905061617070e060a110a080306031605090a090f0c0605041701020906031611150a0b030109050d0507030203 75
    0x110b4444a0192091013100c040303105602c0d00c3d0115040d0300f0b10713410701000d18502a003800c1c5401c1c02c0d43c0800103d0717015480003100c04802540780c0d1903003070a02c0000d400e8091285c0c49118142c00f91080181c202c107125002081c2c0c21141014045901d000c424200d6003041c082207032040d40d40c580d0704002002c0c064146001c0c109100d1141070110017000502c034940c9600507a601d0007244a05442c1040c823100d0203a80840008200c802c4460803850300c0381c01021100e40324180070a800c00142d84440c1480038200303040c0c1e1002400700c20841c041c1000e200704c0c0390403003010f0260740c0e0050405001035589200a480c4000c21070740e5822101c1040201000c08106a800400d0701d00f03015944e8100401aa10502840c0400181100d0221660703105000341e892490300100010700319501d0407400d07441002071000342c4003000310f10a58041c01c154140503a0342c44101a03c0d0062151901040c030805803501030081e540641c0c980001040400c1c40030403182d00078101484c040d03070340e031034541000c038a1800b4400e002c81806 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 475589568 1250 475588318 475588369
    0x21e0c03120a02071215050c12010308040501110c09070503090717061e0c220918030f0c05102a0306080c01050f0714032502031c0c0809 60
    0x411000001e41100c0b407850b4200c0300c1e0a612503404500d8952943c10007042190034401c81c03041210160030440e403040084c3d010078102204011600f801c1002a48107480c2100d00282c00d1081e0b5901402d090f1008921070000d00409030034001150307103140000e01e41801c011001c404a448000c0922000000340071650447c1000c640c0c25400a440c4e41065505181000c0b00d00c2c410040d41d80610207031441180c4d46900c9500b070003e9110700000c001612080010780c01000702003c61100d540b4801c141e0585190104c0380c2d48020b0b42d1601901c0300301507040c86014420382d060018000b50300094407102c100c00c04200842c009082e058500810710350000761500480d410002d01e8500755055010008490001e800c03181c140384640010b44981c8070790090309990b180c041045101007030410b88119a000101011a4074005070b079204440200c442ea0344401c41d2000c000b01a8040d447d08100c0a1800aa15881916100725140001c4d145105c204402011200c01048141159440141003a007440d0140c510b603000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 475590818 1250 475589568 475589593
    0x30c010920030114130219081e0631020306090f010510050906040b011116030c051002031213051c0f030917071502040306060e090d021e0c03 62
    0x4034624082920302604014400310020716050164072413482d09441e0340d120750b44801040034030380441c50030f0aa0300f1141d015220700c812003100610400030254a00503100c1d001d00d802500c0790034108400c00e16025803080c0140401c52100c201c04109160744010220072411164203440a18080340e80c004e5458042d020070403985040200f690702d4420b0400c00200800da4551031101150780c41c9001746a0071190200c001f40403803c0ca40c0c13000d0320b000d40504007021a0030110700024078140c0ba103c1c02072900008039400700b0802101c002542c0180004607511261456142c4001390340e400391043c0350b0007069a18012814070060380141001054201d001c2d2010320840c5824103014001c00c1024600044c0060364840f0034034440e110f00503205902c83d400002d4041c00004842c40e60700034503030542e20b244e500d11100600100c20310040c802540b0404020900c2c520307020107202c4908005000d05015007040000001240c1c0c04511121040e561100d015511540040218074000d40e4007050394042c80b40a007c09038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 475592068 1250 475590818 475590833
    0x30c0b04080f0a17070f05070f141c03081015081e1612060e01080a03090e0103080906031510081501211d0a03230c060a05040302030c0109 61
    0x54a00c040100c40c0070358950300c800d03550f0f90107554014013100b96000c0412048040ea4004001705070049000c0300da59003064451030300307042003913001c40118208070b102002510541c0000d4004a40101d6100d80d24000c16517140b9824281c00c0030042c204502c4a0000f11a00780d00e02425029107000900510b1881080c04081c2c010341d01520030798442c2082c5140514a0004078041c0d40c4204007148880c40d400152900c183c92000e40c02101040c0c542d12502c000c140c240c81300f40c12130300070081c0100078400040c05043c05403844a171500800031110000c001880402c2c800e03c210340161100307591455684c0d440014600030f140c0c1d011803040d071003031071044017011182c1c4c000f0b01c00c0d0192041f10f00c000580542d41d4015601d121404c090800c070703c80c640c041c041c00c118140d0310a4001070410091001c80c882c0c095102d1b030624064182c12000300300b00d0554035601040b4800809200b1001e803400d1840c00404c40c2c151582e0f60b400401d0f585100380c80380c0000381018030900640b1240100b0400a00020310f09140054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 475593318 1250 475592068 475592077
    0xf18040602030a0f0e0c0d03030b120a0b0c04051c0f020604061107080712060509070312020604060f05010303140309070f08010f0b030102090d0b0c0f04090515030a05100b0109030c0b 80
    0xc41040c18401000004c2040e03100304485180030000030205da030100d4080c41000c0d104104294141950740c0010130081d101e10303050780002c0c01d400c4042c06040000745418032003050098192010460300740b1081c001600c0c5c091240088500b140c4011030305906601c1c1a90881500b9040250001030201d000144584c00c0101c101d00c14550a086e00c0d0600c1d12a0b51155484929104a0300b01004100000d800315000d64891a0014110300030342c3c0606d03440e0744442551082f080400380040c0d22070b600300420301c00148500c8032080403911090149500d5a2402000c0e650368001d01c003900b11000020400001007048030f44024440503907010407650382c40350094001d1015102c480c6007141490700003230b000d203018802c49030101f6004240c920f04580ba83c44044c0c2000c1c009001e2000c0841c00c03c4071101d01c0da03103240904014a0006000b144c035241c66080c540b90000c2c104600303401b075030000340e042002078408250103a00c0c00c48000c00041d00700c558801251804038661025200c40d484d000d02203100c1d42c0d03480040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 475594568 1250 475593318 475593331
    0x50f1e09120d1d0a0f0e071d0604090e1e011e06051c02010909051303030c1b060c1404030501230907031709030f15060d110f1804060203 60
    0x15140003008001080c2c564031101540390010f640c1000b0150441d03c0c40b41003880a80010b082c0300409038941280c800c100c0f00e61380200d400c4250000800202660110010441415002d070000b0010504400306900b0b00076401803c142c2900c0350308a41000e402003109229502900c001070351403c00c0740001500801007080c0c03420400700300300e54003800d5003070500078a4203c83d40500088280300e481c1030380f801d03901ca0302001203040004100c400901303180c09018441c0500440141c4920340d0b81e6070700d00501214140203081e41449160130020308401c828104450512760000c0c808074220a82003401c440141820100341c10441c004507001c024440b05601481c13044007506101c0410700c406864400d090f100031522003216600504017400044c0203020110480003004564500705000700000a007800c21140500c0d0055101803110504090356851103500300030141d91085040c00d00d80c980540990131040f0346401202e0082c0403400030385600354800c8000301141b000c90880c2c00d0030701d05580603500a507401c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 475595818 1250 475594568 475594579
    0x105010f0306180c0903050303040b06030607080408070f0618050601031205090303071502130308030a060e070c0201110f0d050a02161d060d0b1611031801050f1e09 72
    0x3050280c007911550b400e03202e460a0b9110b8215000212a0281c80103049110030000401c0e000130016030b081010f107005c1c41c0f0070b0300c0c1004180b620006141c50410014000810010300c4000c0c0400709504908032500e40e0b4004c00c1c0c0b030484000314109200603188d1400143d501c98039020044c0c042c80710100f0110b0689203c1c2130032004950010104807580c1c01664006036040d0020000d18000600e0f0081d480714242d640d40002d418100310f10001a581070303084d40143c404d100008104080c0408034172a81003d802900403c2c00182000c040c01820907400102c000e0610198070540031513550104400b4020503030440032100b1f00803108500400c140c001140c200094840c200c030100c242e0001075555819100320124402d1040080082c85203140006080c5039080755407508610082503014030f255200f80d407080400e610b060580300009040703009550444150f6003090107000504c0e50307006000807185c4824a0001e8075a9191b8081c1406032240c10464400000c541901c4642c5105010140601c54001c03181c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 475597068 1250 475595818 475595837
    0xe0316020a0e09030f0705210705010b0d1104020903101b09061704030e040e010c0503010f0e1b03091002070302011e0e07050103050907090608030706110403050a030311120f010501 79
    0x4039266110646040d03200c1d800902480d000250188040c0c4852401603045801689540b0548c0c000da11031040e0395615410005080b00512500340141420f8960503101e00e22903070a103844010440307070303600030707061007035800166483d001c0c0c2c0d08001103400d011030308004002c001c42010348411045521846140480e05204000807074500948005a8410710203035400b100d0b40c0d45580444440d2038003da43355001d40d903459510500c0e0001d00c9440812462520f03802d640f1350508401c01e8210301d495000d840482102800c02c01c42c03e01c2407248462400c80200407030b850361039410b410b9040808515001800502c085240418075038150405401004100144203a4140d190340000c140c1d00b110192040d5584451000c2009512960240d40c0c4600320405a0700019115402c0c1b10503a552640000020390010850ba0103020321031242c2070151555a00e40c0d89801c0c6141e0301c1a4541d80c1c0910060141555100080a4000d200c3d08a0313041c491f00120342021403503c0d10104816600078002c007400039140c0c48 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 475598318 1250 475597068 475597079
    0x30203011d0715050901181d04030320190201090b0a02070b0a11090d0206040803040603060e06010509100c11120318010201151205010905030a0c1103010615030f0e0316020a 76
    0x40490303c509599514149024841001903503084540d42000c0c0c41d10100300b40000e08519124990301e42c0e00750b0300c40c12907002e041c00d040040c02e442c0c1707600c2000781502c604079942401e0940c100444a04112541e0608220798a51005030300501c010344000d40a002d581c010420b0412a60b401480740d507101d140d00d2a0b1a40721440210201d80200c40300c1852210b00700000040c1c0e03d07101c0e040081c10b03840203285514281d100d0b14100c0c1103400940c0700f2030200f926a60306000c0c0072400303500e10368010000e1801c1800c0a0010b80044c903166004041c9806100510006800784020412448070200300580440e00c1151030b400c215503039500c04141d40c180c01c140144915050f61060003059142100d4801c000c01d0542401e990001c89903400c2000c0790359641e00e01c2104001079061001d0171000700c6a40390720102c2101401d0802104c039205405601c030340d142c514240701d0210b0200182c5c48114841c6400160010300503c2c2c10000c0802407440b02c1c1d288404608443d5580b40d42041c40341c0f06100b41c90390791000e039480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 475599568 1250 475598318 475598339
    0x1207050703170a0f020a09081b0102061602160608090d09030b0c0a0318060b100311160311010603060f0f02030c04171501120204050c0a0801090f06030203011d07 71
    0xd400c01000900040c0361600101d8003005203a07040f440203940003448440b443d02c1d480480e40034400e400e020809a020402480c10140101405401c0c0c140040b1700d00c1000b038000030f4a0b42002010941741510030100002c2c0c1e45d1081143d441d010303100000700c04400d40c503024040c1c002c0c60308880040c0207125140610802c944034000310000c59601c01e0030300003e80c0700c0480c02c010f2030b0045030710981050399494200780021811a54160018010000010b15160758000d001d8042e08012049080c90b0030400320980302441c02003200c0e5200d481c40f0b081a20300c68603103400c54511550315001284e560130300c41d0100910801c0c0d031201d100294007210030090f0340c8592074464240e000c11111505c07000d100744010003189a0110402c20880b220070269002110a900d11032001e44003a0807039000151551814021800c00380300360b58002044c1c0701c8950030020302c5440102680b405016541c640750700c80200014007c459004100950350041c001d204030f104404078118130000172070a400c510703c0380b4a000545080b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 475600818 1250 475599568 475599577
    0xb0603040b10083a170703090f060e0f160509070e030303150901080a02010c06110f0406020f0115031101140c010f050a1104030812060d02181905101e050d0305120705 73
    0xa0382c1341c171880b8644e02500ea00b49420000d0031070341815100c500d14000145005500840144100d10005900140c4003d10385019041d2000c4161503010340c403007000038041c914030703202190802c40300606030b5613851004480e056081e981d55a09031101005001012568651a6484050549840c0301c00ea07601d1040c1d0f50780c6c8080042c0640031600d002022004103145400c40400380c40c210600c80d03d892031108035001c4c16030159000e40010b03042120f40d43d82c9080e0a004e4030400c8448000d03e25081420764680b814082455450b60303043c084d91810501c040302440041d02c2011249d10002c20840c180c044545020308411144441003e103048020340b45280400240c50560381c200d22061700b00200d804a00101d0340d405050554010303803615484005a40d0407060803070030954003a40c400c050521122016480c0c0721200310700800c3d4140300401915140d031200000468802646a000c00c00d07200304680d4201ca503540146800581901d404814140c10800502c00794400211400043d90b51140031900c5004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 475602068 1250 475600818 475600933
    0x3040303050606040b1e07230106050108040b0f041a01080705010212040b0313080d0203010b0904050f010e160e09070804030801060207080a12051c0b0301060602010b0603040b1008 79
    0x802e1000d1500d0b50005d00c1e0030740c4401880390070140741010588541c0108c12030001e4174003486012200306490700e0400e004001c0202028202500503081c141c1d6500c804510040c50000155400000542844010b101e2485007100940d01d1502c556110004142c0303415450040502511440c030b664102c100500b0112402c440c06401d11781e0540d00c1c0c0c89c2c82ca1b88485d00d41e2109440c081c100f441460030341c03103980c4000d6000340303246402d240e40c0d800584240016a4001440f042131001c1010041203466030801c542c1e513010010040482c0b8059038601c1c107481c40d900b00301c5055080407282080002094108191a0190b4040d0301e444160781c0c2c2c0c03a14100d03501d04282c09052801e4004075003920024814070310146080111b401c00324241000400c00000151700d022020340d00a8403442503a074107040038070900c0c000d04810720013030201071a01c80c0495028072020300020040401c05000a04000090036038101800b21b0406a8100a010844040c258104c0000030400d010f020a440600003081d4940c0040030301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 475603318 1250 475602068 475602089
    0x40504110313060908041802030a05060d03080c130f0e151f05090121050106110c010e0d140a140c125109010203040308040b090718020304030305060604 67
    0xe207070354605018080780581200c03910028400810352071f04201c849105036109441c0140c5034601410140250b42004d02800c2c050601410001c01003640a201282c0c032898405281e642d60003848040b0002c0d07845544082c1503441a20800f03c0c800400e80c0c6e0850045180c0781c056424103510b601004080701e180c0380002203402c09500c40c450362a000350060110900c5c14100360345081d10300410342c402030300d041c4d0103d8036041d95280144441074000b2500c1c075104850380020310340c24940b0000a07001640d28101c01c0d01c40c1c0156000c0004100e2000c00031194015000b0944800e0700c094074021040342d48072452400b0328000d03120036281d2410310070407180c501c28040d0018842c0c141c50f80f80e521406410518503041034400701c81c12034150454a40c0144415190984428500304140d15400780d51401074214800e0340d004006100200e50b102c105039400c190032042d4140d4a40700c0c543c02a2a0210a50140004800003140c4180507000d6a016504c9640a62014003441c1d8905040103614440da0207440c0c050f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 475604568 1250 475603318 475603351
    0x50f1e1303050d050108010e0609070b18030c0a0329070c080a030e06010b0c06090303060a1e05030a0303091101020d0f050714030d09052b0c020102210405041103 71
    0x300c901108500d034160003800d01500d003020340c43c80e200031344030240c00402d5641c0d122582e221042408201e41c550108426024005080c1006881c040910a444041c1e440c00800840407815581c113100100014600034900740c0c10503568984200c05080059003101700313180d028109003507203204060382403203064261781c1d0340d0440115950f81c00c0f558200400348810569600d1560500354820006203001c1e15240e41001c3d00e80d103aa00030f003403074820300803c0119076070000c0c818411913886407902d03030003582c050602c000e600304540c0c1501603811344250301c004e0f45442142c0c403100c241a0150302002a032401b40d45410340715581c3c14016603030f820708181c0510002e40483c2e00080828899009850030a1181c4d0161021001c040800c0d451030300080c085a00c100d6903154010200b1104001038411703680c06140c845d800340b20b030941410320300800b000c40c481030002403000c0710210380c402e000ea2981400c0b4400d03460054402481c0c0c40003e900a40581030266140c000c1c9080350450500540744580103070000c0d40b254 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 475605818 1250 475604568 475604581
    0x90f25090b0304030c06090803180a0c0506090607050105190b06030405060708090f03030f071107081c0509220c050427060302061902070609030b04240f050f1e 70
    0x1c0da0004106074104003549074000c00241c02409101803050213418035070b80741d0500e210034070302c4040160441403159100901c85000507040d2160002200c0048450586a001000100d40f543c46440030080c91540303443d04124106132014884d914100182d00100202103040061001c2031000340d0740581765500c600c0000740ea2620400c5210791050f128015a80144d040403e038615540065441c50055201741080000c4135a110f0400025103540000900d155450541c0390394a0703100709001142031241614290203aa40103000f16a0a82d00180080740c02e117043c140e02c5103503280b20074076884505040000510103140325000796011344451131042008038045080262503641c20113901102036403212000000b69644202412020507055415200d803120003000070b0a00c080c5811103414415600001c2c40441c20b003000c107962103640110300060151400c49405180c42c01800c2521407642895002d00089506400c2030f80560091815813507583c940b1002003814901c7c1d412109103203c480d1002810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 475607068 1250 475605818 475605839
    0xc0e0307170a02211e10060e1302040f0212040b0f04030801030b1e07020a0b0f070207060302070203150f040507150c02011b0821090604210306030b0406320a09030905090f2509 77
    0x2609e520041001917116411060a4240e80110a0711807601010104010a0007110180143d20002c001e91300355180c5010350307001c0c0c103903041070001030a100075950000f101d88100c000c1c81c5c06040c0711000d00b12103914100300005d5a590060108640e404690000b01c0c04d130f900001e100500401c00398014224007414400110700a4105440681c1c0c10321403a2860011aa1442d080318050307100c10969140034905810b08038a001c4040d885041040f090316002180151f2002c0440a046c0d0b09181030303810301d0200540c03556928014030001e4000c4400007000d140c00c801406c941c00c2150244900e585095494013080c0b6107400f400c440150868086000300f900c16030583c0c40300001c2c410702e1309000407050b4a80d00c0e0207055400840707040350b4540e0f942403880400c214401c100301002159000c1841040d509025182d071821016012060305501c611385102018000c1045002170070019101054600c0d00421140c00904241c0710400703a040302c030000d41c141144881a000c1800402d4641d42e90851400d083c400b03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 475608318 1250 475607068 475607101
    0x91b03110f01050d0509070501020f0304140409230f07050108010b0a110f0318010e03030a1706040b0301180204060b03100e0c0c010c0e0307170a02211e10060e 70
    0x50403c0320401c03000820a85505c0303000c2c00f80c4e0781e0400038070b003840c2414000381c50143d070710b601036045510604c41008180400005580400820742e00810110318602d8400403419180096a110013500203191400303d00009440501d00c01100071294100d13903490040d140c40e1002e00541402c150308100d480d02050040350304540040c0b10100302d0b800c0e54112140e080c00c0d81c10083c0c01503002c10007407221241c0307903900000800d04410300300c01131884d00780c1c028000360080c2c440451054484007a000014415034460f482142ca4400240c02845036242060b6801d1741e4800101c4200d2180b031a14202046220744102500d2080e001f132800c01480c01d0501c4a45c400c04a030023030000c1d2401400700000c2d02603000070f008207040503249450302c3c00b042e070340d0000b01400c00550f82c100d69082d80e810341e1105000c030400294a49480c0c1c0555851107410100c50750000540200701203006c691280c0720410050b1046080100d05144024041c0c41640b1a40001d0500b0341e0300da8800d80604854810101d661601010f01d00d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 475609568 1250 475608318 475608349
    0x3080a110909100f060807020c13150902120106020304050102060c16080403050a14210d06090e0714010e0f040b0d0204050c0a0810030b0423010f091b0311 68
    0x59003000680c80000b59a40c2088400d482c030000b9609042003401c0c00d115500300908a2410314032054540b00341e00a59803001040240e12400c240680b075020606950b105035902d041d03100344490305503220007141d4080e600440010341c01406950001a485e8404801e48054550584c050074841d02d41c400c1141c01d0707400081d07580c15081c0c0c5071400d540c00503032210010703c01940b080c0007a1002d5441400d01581c410f034400c1b084261504801c10b5803001e00b540449120042c00d4a4000540310740804111000900d1180c00101c406440e0884a500510000844404a400182505c0d101401090044406e043c0c0701101c0e80d0440c61040b4180c450b441c01c0c0e00003c0100001404464050380399030002400c0e02c03030546030f141040c04002440350080c1d5005402c5a880011400c140203e1391941d50b80d944c1d10003008102420f850b401d0100c80c4480c00e0200c4040e411945031100911149141d075402000030700c52541c00316201d809400c41400e100362040c0c90740302100e41150400701e0414108081c801a04101c1401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 475610818 1250 475609568 475609601
    0xc1713140f09072001020301092a050a121b02030909090d0e04091401050403081608010e0408031902211518070203070c090c0e09040c06050a0c0816020f0a0303080a 72
    0x50540c03401309102841c020007010801082d0005881d1100c49204088070031050b04a20030015034907001d41060071907180380094941844a0100d0785000c81c000c3c0b036284042403d007a01800c02841d2241d00001400c20404115105012601c80403034150741e5414114445010070031aa507009401d02d030542c000840c050041104154001c1d031170f20300908480c400c407021804507214000b804070200229214201000d8a41070442c9594103000c01c019183c80010002005c081d40000000c0e8080216034941541c076448010641d250425401402c2c4550880b0202d126251207038000140010302d421040f80c803d0101030680640e00c000d2039808031500500600ba403080d41f004004507000a1003206603000100b0151000007980c413440c1100600c64900c10074100e10855010081c07001080460214608545c541d0410580c0c500c0718400581c1c1c070140d2108048d01003003000c1a00c12a13810000802c412091084800d40c01800c195030800600c8120b40c0405400140c0301c20001d00743e01c0b0a03500c401c5691081c030301d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 475612068 1250 475610818 475610867
    0xf0c05010305072a08090907080108011116060c030b090901051b091327060603120809191a01060e0906060f070803061302071a070c02100c1713140f0907 67
    0x12400e081d00952369000014403030700c01080400d500b84142d03c2040550f920203450010100c0366031210b00490000507241555170518009454040da010314103445000c0c05604840c0b9001e0074482c000c003000c40759151240c0d5003092500340c0e10b4141003211102d030070044c0a201e500c2c11040000c2c000f40a03d400c2c503000722501240c074000011542d8080c0c003083c1c5c401d00c030114586045181000b12185030410440911100400b804031410010800c01c0c00302240c0042c00d8840c0c0710342d040580e04031150070240c65426403100c0000ca1000c0d4000d1200700510800c0d6068403550300c4100511603e4810307244c03243c40d040f400f03003d0503000a915200440d0800001000d14881005c01d0100104070303448040c00722100900220240000e5001c001940d60000301401c2880c0c0320200c540218104900c6020705070700700104801c1c1c60042003a6451a16150303080703020490340341c1860705c1e540a00045203020302080006049140010f0b494440c5001ca0740ca040940b100c2003a85406038113891196a07102640f5142d2004607 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 475613318 1250 475612068 475612087
    0x3030815040e01091505060a0302100e1003050916030203120d0605040f0522110d062306150309030f030c0c03030411040f05090d0e0a030f0c05010305072a08 69
    0x15440c000081030000092007419485c28080320f8416802c5070000c98280f00030400580c1e900400c81c0c080765019a585c600c812500f5200321001c0c0e6041041c0c0350b200d0400000111920342c0b40d8840791091643c070307044aa41c1c04800740c400710b070a602884005d40c50b50100d0300000c480358000014052030070001c100822040d4a0740001403d4440c12000081181e6a0310208103102c442d1000200702c1d550101801b125140e010b440300030710551200300c298007070001d00642c0030404c21540c1c00071a002000d50002540440706142c04001400c0544107244218108600340845d0140d4a0480e8018003401005507d00b02071a0790a0015410045c030781da680c11400c1c0050014910184000c511991107003070185c2c01818002e00308800c6a0954145050340d614103010003924000014500041e0780c2e243c1402200c8051580c0091a54800d9400c0104264003805106080051540100301a0790302601d0500040e51800c00c211004241802010040d8500459080c0d410040a600c5102d0714082c0d00740f1803a1400c581d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 475614568 1250 475613318 475613321
    0x170c07050a02280b0706242106020c010905010e12030f09030f04030c090501090e150c090a090e0d020105040309060c0f0c0b190905151332030105100303081504 70
    0x3540100104c80b0005a0f0b0000c100d090b1050089071219501680c0c140100074614000410a40c00740d05601410102d8a031a1481a0791000032425130140055543e56140041e0b1806801071080498581d8202a180c145550004c104200c5040c49101c041d815a509d0408440100c44041c100441500003007104544003030b6035800500c0038501591142410900d0482000126003050348401c209500d04200320164200100d00c01c0c12603030180c0c01c10070071134442900204039486104405a4445010640015035074425040b4403003400101099034022821810f06078241c40c4200c400030001403808605112141c016408140824020780c0182c0c0742c400c842e42d80c4040000a030300603222194002c50742d20800c0082824900c041c0050f460b10130321842c940f02c00f00e50841c41d070384607e8010031008550048d810b40102d52000040015025034140c901c034621425010b441031302e10114030501c46a42c0400e0500301401494040e084000543d080d240c51a00c0c1224000030203864640b5280b02041d10380110340d40ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 475615818 1250 475614568 475614649
    0x60d0206030c03041406010605030c0a02120c07140f0f15070818100201060e0a020703020109050318090108030c0a060b01030b1809010e1603030507020109090c170c07050a02 76
    0x2440d1082e6030f9051504000c00c00d5950030081c82c01541c4031100600c00c960384502a203402040e070001c0b0b1603c0c3e0302c1400b426406e28480c0114030b25403100102e050210f85100007a40011200701c420300551540f1400c05029070011b44a00180e04043e87c102c46540c07a0800c071060242d00880c65507514106202a41d904807640c0c00b20300c07000c00c03145100e25a41040d01d40071062141411080c0002c1188520b0314203440440c910040c041071180c0da001c529103007418000c1d00f00c100301c0c07a4003200b03aa998001540040d49021001000d05015064401c00802c050303c000080b541009191001441d400246a848030080d00003044410f04242e1100d500505585601c440440600542424003205143c8007914a0071600785049688a99000030740d0480c14001d80c01040b015203406141c42c0d03540b10014001a2041c01d10b66000c9000c030b600d0110403008550b4408042074144540c0281c100c0c1c0da880d80e00c040c0019014482000d002504551007a0f80185000f51707a0030012020340c051a8202d0a085490400e003090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 475617068 1250 475615818 475615831
    0x12051204080403111801090506061c0f05100b0913061e151b0803041403040b030901140106050d0b150a0c11150f0309160303020a030f0e011205060d020603 68
    0x102150901c01c10003130b001400c04503241a01c0180b0480003041008a20b000180b06403012a5079560208140307840d02022036182049814140a480b0446c02d020310040c0140320b00654079518100c04202e031108a20125000c403070814448500304510ba40412480b860420a01d4801555400001854145006a6902600d01c1e00100036482e4031300038114090003800c0c0302c05020440f030011404141007510880000031034200401c15202d41e100d140c0060313000d021140c108164030000c0b80006410103c03000a5200d04a0308000744200c1551304001003000d2020f01a88002c02d1040c4070740759946400792b01c414950ba0004200d8695022507040d60352441c6c0c04050000e000484411444080c4000c0d0f041e07800107072009440750408250018541c1e80c16000d45040d860f42c440000010401e6014100490311260b00c00c9420142c078036a4a250280d074078040c0b1602103010842951080c4a0780380170300c44584a60906854000d540e0341c03003104807030041c4070080c2400c1d8031100e005101400347e1500c03400b95210b02d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 475618318 1250 475617068 475617083
    0x2120d0902040614040c0503100303050d110c0d0e0d170a020a021201020d051003210203070204151e06091205030706230a0608150a090b040c090606140712051204 71
    0x4c0c6000740001e507003202c10858240502082403140701241802e0000407640c062502c6078880300c444841c0b00180c5100074400720244004504501414008102d4078442d2a454a4644c094800c60b000e1102d1205007843c0a042400d01c01d0345030215241ca500108511051031050324100c84003580052040280c0c0620180240e42c085488040001d561191070f402400040c042c403581861680c071030b8800c4113460400d8004050001d520001140200144d400d01035009000f440020b03400d84806500c1441c03440b55440082030340881014507101e105420060354036981c3c83c440c40754288580c0f41c2d00d0324030a0204076800d200400080011840328030403222500010b02404410715800204a07a0700e5074082c03c0e441c0c4051a0a0f402c2042040004030010055030009060141d60b403584c00b6030005145842c8040d2000038820308000800c20301c0b041e02c1c8192060b0301c008001c465125841215542e00c1c0002c5012929400c02c1010042090034142891095a9180440c58401c0d4003140070440d02c0180c50071543c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 475619568 1250 475618318 475618349
    0x405070203030a0b12060402060912030c03030f1e220c09062c01050108060411070605100618030f05030f0c0102070302010b04050609182a0901120302120d09020406 72
    0x2070303d14014000f808900300c4010340d207504585600f80d210341c03001d44002d10a10001482900a407105014001440310f600e042c2c0c0d480310b404d00c0e511601c0340d10460385240d6906090001503104402809100007045014424482c5981d85039a5281818076000054212082c01c5000c4e00016200004002c05044c140e000071801c5850300c03010100360452101208000021a0564008d84448052260448009203802c54007070f1a4000440d00901d065a5040358294000440c2d0382070160b2508010b0040841c00020301110740e50703070800c8441005407441e070560842025000c1002c40c10200842e004203014005591800c00c1000c2380a445038022000c0d00160b03500415041d083c0b607028400c2c4601e1003001d50702406146440e40c00a0199200100200c04c0c0f2004030300441070800f020400a1007172124403500c60408003c01c500030080c800410041c41c4a10715180000c50b140403c81d8440e0721095068004086805803120340c3d0301c540d04525600700030550780341d207403801595990203054010181146100c804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 475620818 1250 475619568 475619581
    0x10c0203120c070f050d0503180103150602011409010e1506031e070f090b010c1511030a0e011a060a081b1204201309020a09090b091e100c020c040507020303 69
    0x20f500c0d545d400144030b1100c008500780411408011200000c0b10000504000300a000041c1e004118075804905030302401a0003044594055020801c0846901c1c5190500d07610380d401c041c00d81d0f804001c03002441d00f00c007000d580943c4102110580001c00201510100c072004004c6008000b001b2103007981d1a41310090401030840d82109901c0544550b44050068400300d900280120528443c01000340000745000d9002c025140d100c0c1700094240b0358815039030b04201c2c28138400340c202810204501e520b0402c051040180b00d9500303045600015180900b070040d0100281c0c0c0b00c0c50700604030000d4070a022410039003058160001d0181380180600d030b60704c0d801c1c01e040c21810012040100c18401249825141c0707150380f014064614040d250701c0209401c0400d20101e41e040310550320802c081c9061401103c10442e4070610107103d4040751003202e802116640c1104041000214074108a4105000031000f03940c0c590044c01d01890a4011180019241d0001c01c0c1114001c031101c0e00141c0000c01440702 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 475622068 1250 475620818 475620839
    0xb0d06140a0e0d05030c12070e010e01180b1308070801050f06010809060103062d06030605160e0f060c0a030c0c060c0308011e03050f030406080f040f02010c0203120c07 74
    0xc10044040003001841403a0854a5451210400b110140320b000700000d0b03010050b5030201c95041d00140f110f180c7d02e0400a1001d0700010b080000705020036108082d00030154030823100d407150001c070f02180303c00040c54002c15070300b20b0380040f00c0540312000321580420811001c00807100107080c1c440000645140c44030513401c07040c2c00a40814100901c034410711041a00014a06044d02d0b00103200080204600400b11000d02e00704910f0302a41e1407510700000d00786001d40c46401168080e80c010301540d50b80003822550094001c0f40900030680b040103040301400c01a120202c4200050303d400e24001c0442166031904200303078030840009030515101000c00040084140041000307042000300100c1c03c1c0d0b03010f090014140507048068110b242901e40040b85000004000d580002c103a650600e008075281b52654090f02950000c50060b13404a00400800c0340d4240c8201c2e08130700d003200070409603401150141d48018007640c2c5071040c01021011000860010300c9160b001d41f008040c29483c0484014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 475623318 1250 475622068 475622071
    0x160506063f0c10090e0108070806040f020d060612020438030a170c011413020d0c09150602010b090c1603090801060303030c030f0608120d0b0d0614 65
    0x4040629107402000c42125041c81000c0215182061150440719490300ca2070200742a40d402e40c80038100c44200107103900090701c0020b1326040035144074182e032220b0046130707030f0381c59071040b03c5255020000003408a1103180421603120301c004d10300c00c240000350301e481c4240c0d03802d50031020511303155803038401c110b140611603181e001044043e0450000302c0d4032400348205402c0c801080c480700c5511304e9580195014403001c1d5040c0d5004002c5151164155040051600140c01d108015841d1050610b0030b0b0b8a00841c00c0e10807110181141e1240f0100e6003400034280c820f6000700c032000164000410841075600410a403840c80e42a04040380349481d40c0282550944142c42d8010740b03504c81407101413002e601c00c0b5202c00d40d4800098003049100e00c1c04480c124200d6200d41c4140d40780034030100400d90304d0b410420b80f08549a6042c0504000110b400e0110390580c410f541c1558441d0009000c680c001002918003080003500000c0c020b0300c11008a0345420403540c04650540d5144600394402e40590002c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 475624568 1250 475623318 475623349
    0xb190c020a050c190e070201020702030d020a02152a010c17010e01170a0b0c2106030607110c0d060606140c0a021e0310090c091406060f16050606 64
    0x30000c007202902d400c2e80f1401a41052400f590f10307034485958258000c464131000340780c640c030703030503490f03c2c0c000b200030700030341146108078402d0159810301202c140c4000380e496520b5400402d0307810f11021540b14864241c0c0411200046070765400c2ea8143c000046c0c0d01c5c906040160000007040044028a00800400c11a00316218003c00c01d001481101c11603901141540c4504121018406038a00b00a00e08008100000c00d50a01a0108640c0c0c080280c007402c0003554134030b0000d80071a1403074012030300c0c20340440e8a550541e100200050110348980000c0359000c092a05131640c408050001c9120010886019038405458020810000d40e00c1604107001c1458514070604284400354000c0d00c42c0c0f60783d500030b845404020f00300e8054035141c400075010044020b0403103186617110544040580000203041e90515520000028160044d0064903540780800c13404401c00e0b611042000b0303aa40102c441000340c1e0f0f00c05d200b0445400311400d10408041c0c01000240b40300e1500500304000c0e0442003125 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 475625818 1250 475624568 475624573
    0x42304050a050f19060903020304180b1503060906040b0f0d0c0e0603010501050a09091e11090601050c0a0b15030303010e0f0603070f06030216060204090608100606020a030f05070b190c02 82
    0x20780e050790460144105550705c0840810340c0710203800c08034514081c0340c00c29613070442c1102c4a040c150201d503011509090055402c1c203000d040480d284030060004461030b40c0c100003890000340883c50244d11100e0030f000014101c5040c40c0300c000109501d811101030864180d042a03005020740d40c6404002a0300c604200c00030703c0b0f03541c10140480d402c500c5901c160b4400b50b896402130783c2005034407492008850900800035040010600b007100301201969209405203080c507011a045511483c21298402c5510005003108001c50791003941c0190010440c10802e0400b080030240e541d0b0610044d802070080c000242c0c441e00740001c0380b01e1a1600500564801c1d0705c40c40e010004101d04804600c11681c46040040e16040c800c4010000030004000c0142407900c0001d003c41c04030282d9006c4000da0b543c00e4101c800052452200c5011518503003c7c41d0701607404607201c038000903c2404202c1c5901c0072860701505001032039a8403940c0e1001940c0c10201c1d020240452000686648140749003542d8a100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 475627068 1250 475625818 475625833
    0x61d0c03070806130f0309050904110f040501050a1a040803030702071703030403021b19031b0501140322050304080d0f0f120507030914030909010b1305042304050a050f 74
    0x1071015943c8220010320001d401a135410605000300211801412301a141d4142850a494403038440384000004074480e004040850369541460302c40c650607200d014120102ea00d0030b10b44c03405000e100d1220719030b6a8a5041001046103241440614080d40d443d4004084050411007036003040ca940d80d40c4801d590748140208004213900141c512030030500b00c1c45242801c0e8503000495510040007010354200d074052400001000b400d800d00c289440940381c14481801e0300c500045035000315110840e00800403d10200e225500f42220b408910321113041c140e107041d0704d07980d5540d0554100381e00420040c4c12900e00700d060307150009040f031401002e500e00300f42c0d41c407030303075207007d0012a68132000c0c800003951400042d11090082e030045000b1038111041c0c218040032181455039940c4043c5520340251440b80002070072800120643d03051010701b00d0200c110724102001d0100410000d41031260149218500140e100317910606170740035600603405003a81d4007150400c103181010480b214060365203c0c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 475628318 1250 475627068 475627081
    0x70f060e0c01080714030717040c06030e070b040311030c09100608070c03050a081008030d0510050301060f091a150309122d04030b0f01150305150d061d0c03070806 72
    0x4405c1c49540040640c50b80e125203490320210b9112803090381c400c0040840300c0510050146440448088032519075041c09840d0208260340d0702e8503214410718560604c00c0c4010700015a25002808201a015007201c80c503046910000c0c540c80001d6503842c0e40006406810700c103c0394845201c0780d01948a0070580380a40540d90300074643e10519684400b0011000045a10f444032000480020001c3c201120707120100c590041c0000d003829140074a080e903408000146504040c011281103560440c1c040041c1c9260980074005091000b000c05512001c40040100d1903a41084008404440c401800d480780340c48000c107481e0100300c40744c0212042c810301c98000c4880b04181940c00c08103500c07841c0005e07030007a100da40724140100d400c0201040c0414041001000c00710010038100c811307024081500c007080d09400c0d021100141c03070300e0036548540d084c0e11100703092006444114510542000034200801c642302103410424403850b42d125000004a180145030801011000e808850080d001e64140311 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 475629568 1250 475628318 475628327
    0x1112b0203040c17010b040e0d020f07300f110906010e0310020c0c0904063e0304050c03070b0904062c250903140114041106070f060e0c010807 63
    0x14401c0c1010940c9030a41e41402e02c4e001e400c407450b554000342040c002c1c0071510301940c0c1c0302e802001c0b0140045c0706940148450680000d1030104944403445034100c508826424110080c0d00c600005004281840c4e014000030911a44030200b540920150b11008031250200090408058030a40c10000031000040315a500800e031066080a80e01c401643d5a034060b01846c1000301920b420340d4464250f00c100010701c03a09030080100360521280700030307060446c030440180707154003594241d401201400c86945064290801150440c0c01503040783e0b0a0301e80c4500082c41c05a60b5042000c5110740841c008686080c280141e8024224061489601443d02e080851078031910b034203002d00d0100702c44040703456140390034030541403070680c3c51200d0360076401102c000c3d16040052008556803428032400e0801c1030f1061040c41c018202c81c14001c03400391150317222070b62407542004000d035201d0020400540081c07600401204414880d0350080b9100780c0000146d410110483d40e02070521002c542005034842c0d12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 475630818 1250 475629568 475629593
    0x50a0912051806070609020405060603070e040b06090306161101090809040908070c0303050304030216080a031404092903070b031b12130507050121090501112b020304 73
    0x240e01d841da0715040d110b003420310b54110041030306800500019220050114940201d4000c9000380d0f020312035503c82c042400100e02c001c80d4040001903a40407040002e16040e0040c1c0380c138000003894141042c903d82d00007402c10405075084034102e010381d030840f845144c0101300b01640300e108400030002d0008545548106100341c8030302c0792213107590318203540410036031200b0f5401490301705142e41d40d6940c4924014009500990b41079015124450f944603200c017001400d80e041d07903061006040c416104ac0d800303a600c0345291814030f403110300501000c01e8204032885129200306058200e808010403440f180c02d4898101505140260002c1b02c090010540f003004980d0400f81410b03040d00c13110100f0601c0741c03203401122440c40c00000070781c040c0980848401c50221069018400303560003195141c00540760180e100a4060b60101003452020b40e104250740040316041c025800480c2e81c1100c2076100e0700c154002c0c51800841ca00e01100340d9080f80c6801c607848003160584104524500300350300c1c0e0b10400d140703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 475632068 1250 475630818 475630853
    0x6010201091a070e0303040b0706180c030c0602120f04061d040c03060611010c080c030907053a023a0b010e1f170c0a030305030a0f021905070203070806010b0a03050a09 74
    0x2150980580381110030848200b441c0d800c14332951956031a454074a1000b911441600c005200c2e000700300c629194000220745440c800c21480618040c0703000340c117032100301004994411008084101e000c2c241c2750790003001408a030f107550003d192030400d180035185200c00092000c4c10784c903003402c0c0c01405400c503451a4100c03900a0380b9680b02e50f00c0315511440e1901c1e6800c03030358100490034118911240d40e201c20318060b2107520403024100140c40300800e8062510407010351701180c4800c1c2c0510b0445a50b411103170621043d070044041100490b0201080b940125003103580c0c0203041c00420012450304000754010700403140d42e180d0700101040c034000c900c8941c040d00c0b0f400c08440704aa10108010031240e003070070300064101d060095903802e010700b098108039900ca4495060143c0001c04021340e10840300c2101005c40c6500e05811a4141200d6070307000101700b02e800d441140d9000c1144c080410a950003841c81c80641680c0f4804420300806442001d0a048481d070b0401c20050b0004010100e0301441c0350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 475633318 1250 475632068 475632071
    0x9120718180f0203210d2901051605070b070b0f0f151f08040309050f010c0b090111030a0c02010605041109011d10030902090114010c060506010201091a070e0303040b0706 75
    0x19400002d04010706043c080e403000c1c407501d01071050b00810070081d003001c05120b01e0801205404007446d400308047c601024280c880360104070b1240d90b005501034017402d070381c0c9560050300450b2aa904c07454400c188d0814104001c0101e452001c00c03e419a181d68006207440c08282903003802050040043e01c080c2c40c2c103030b00c10000340c020741d12503e4410f09260103030f481c00e40d6402800c20300c00020380000000e441c1940042d841844c0030a003070806d00500c41c201d486c181d4419104201c0c0f6181d00c90038500180c031684665403911014119405450040e50140c00b11400000b0404107000000e42180d1843d80010701640c100700050000840c0c08003951400c001c01c0c01c048646c411601c088001c881d2031280c5c040ea10902400142d448154141c1c072115506100780d072182040c2c1d072500001e0040b000b0441c0c0050000b031803d805c0c000040e0003600b20581107070060002040352070180e510a452507080c0c0c90081c2c200541e03075081210a0b540b104041141c1070046d0050342c5840c0c00c2c405a42d20b98840c185000d018107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 475634568 1250 475633318 475633343
    0x503011404020c10201b0f030a022e0e03030a180c0e1008060c0405010207090b03071707080d050904050a0b090c0702120a0503070309090e0304050111030912071818 72
    0x2103280341311704190004211001ea03a80941c403d100300f450751420401d19581c0300300410900c102a001085821101098000b032408640d41e05001c1018181000101402c4110300d4880640c1142c45c0910604041024080d51300c030b281400004040355800d00149154184040403100841c3d100d0540c2001e0390083d191284a03540e030f04842d180b01390321903400801d99200b12010001c51a0301e003000380c000d450b000d80c203446c441540c1d03421042c1603410741011513505030481103003040706111140340c2020394803100301034800c400e44e14a01c1d142080040c880550228400042102c000e00c0d19225030350303024182100410000203c50081181000000d28441e0301420001e0464150f540e001b01d0100c8142c0340c8003c80c8c00308400c51800301c1d160380041c441200442c403982004160900325015501901201000960820b4a8880112000c094075080b080341e034001040300c201e140d1a20701c038200c5421800c01c01003001034544400302820448540daa1a120b91500e0f400303e6014141d050314200480c0c016241d082007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 475635818 1250 475634568 475634591
    0x70f0507110f0d0b0a0f1401050a0e070c060c1e0507050604022101110a030b010801060507021504180c020c040c0804020603091f0b0f0108040302030d2a0503011404020c10 75
    0x1616480c0f00502000d9001c4d04200c00c0344526003100400d030300710340c50038440d071412860007007500c113020f02825900041c500000e01031211205a25940301d4441c0c5010213441c03076943c680c0c00484165501c03e4000070040d03a5400320307070b21038a540c0d0b042c410700910b40140b80c20300759146c140c2c440c4006440207110b124000046605d080d41c0f0079425003030540190080105e00c1c17005010103026400650b41d28082403c1800a000c550b0203450034504030350003515520b243c80c26650800c2454001000b44102c15003051102144076902d060080b0b4803c48a4100090020b01c403810281c034102c07100825620490a000d500184654488032440c0c02c1981951203d41700e84541c215a170402c1c80d412004410008134841c8014101e4454000741101e1001f500c3c004100c12010f0011940b10038120ba000e4051390080120317008480c0b041c0d021456843d41d5404e1841078101062203601918002c2860100146d00803005200c0381010480d43e04048404a404501e05041c1003582034039010b0380891148042d5403103112910 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 475637068 1250 475635818 475635829
    0x2603010e0a0f0b03030d021201050303030402031009050102071707060e0f0d030b0f09252607030605220e0c011403090307020a150e012115090e06070f0507110f 70
    0x9004070028152922900846c070750308000e400c0000c504281b00301d0b850000405080100c101c034091038018004d4401440d00710005000f401d00011700321810f642c204210004148100d41c50400400301003851941d0f020907051000c2a100360040c103102c0745d04680000504000c00180c1c00341d49902c00d080105500d001c040004403800308403c0b00ea03402c01042400c01120400305080040c0651100c0143c42d00c8201140d0102c2d0311141c0d184e00c02000c0344800e108032280c0203445505035031080c0707a480d0200d082d035240d80200d0300c491041c01c0d0384001107002c40d00705803500791940649441c1804280041480c06d201c00d000812500154111048600c00000800c0601c4018001c440103150081d280302c0000e940c601c04080c003003040001c807000080304008030b03405562048608445019221244082408a2000290040c80c44a5591280c40341c00c071b2000400c1401409842c0030317a00498044c18007882c12041c043e06800010321442c0800c9410410703480000e6070703400b0f000c5d140c64041e01d44da00124007400100702e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 475638318 1250 475637068 475637081
    0x405061e120f0106150306050603150f1f02010608120307050a0908070308090a060c031409010302071704050f06070c06121d070f210b060303162603010e0a0f 69
    0x2001e8000d0034040024850150001030803204885000d08080800f800c04808440792030217599403110081004c11403100c01030450b10f99110004080010100c0032302e001036081d4040425134245010354450071641c0030340a214680040c5240070213000c0c1105032250040c541c0c4002040c0c1000d01c400070985480d01e0344503194500142104400702e480d080d8490600e88466080a01c1d144d101d941c0386030000c11018440c45607400d18583c1030f00c4010b25601403c0b401865500000f00c110b042641c08e0110302c0100348070030f1a40900d1280c80940c0c5990ba411f100034482c4030740e200c403045070054030100031510000b840d451048080301c40a1030807950824000e0031079000382089c1280c410030400781c5828003c10395400b00d01d00d03003114504114019042c3d6030f4403480c03100d030307050350076203082000049240e4011400300c04801c2e174025402025a40703407400c00c034845026650340d150169003007000e0030420b40740c81070000d90b250720130859070b04034a00319072505816190074140141040c0895840d6822500d16580680048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 475639568 1250 475638318 475638349
    0x41502040812032a030f22060b03010e0a080304050610050d11150403031805100e01031e051806090303040807060e0a020a08010c08160f050f130306050403020c0405061e 74
    0x5034808191078950403102d80003a00c921021b101640c001c034107605807584120070414124106061440c9442d00d5090051201c03d0039140c05540320460320340a150300f848110400780c0304140c1750b601c0b41002d003011407812380c00a202203050052940c2c01d004942d955003681050700d500600d00700c490001c0340d01003440340d0002e00c2c1c1e8000e102808900401011f400011006010b20540c1c00b01102958803000c01c1400030548200c00c01052003045443e8942d403207500a40715881024401c000340c0760f00d0001d500f0460b41c045602d500b0078440480c030003a07648014000140c02c03500d240300550031420b081d1034000c46403042c550001c12032941d40249076500c4405010904450303030020240c43d44507507220b0003a070107064449850300001b0041c90002e032050641c6015251051000d07a50100071041c0000162101c0e0b010050300e80d085003003888200c0b113081080a0742c2000d944a030034003003414101890060714081085c02c1c20380c803d031304142c00c004103526060b240000128403540403007d0000e154001c2001ca030010850f2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 475640818 1250 475639568 475639621
    0x618070b03010902030414010903050f071b0f080d0305100e04051903020303011a03010b04090b01110703050a120806031b010507050a0b0103030906020303090309041e05070804150204081203 83
    0x4103c440c9501840c810742c000d100562500c5018405903088403030440c1d00501160040c4464034040346030201501d0030a00c1030301d07034043d040c2a03458141c401da85150302001046005400a1243c7d46090200d0b6003507401c01e060078052410b11940e4a00344204500030740e60594031510010382071203010841a40b40d10041c1001d07801c1560340d810000e4403036100b40100b1301c0e0761113410b006034028045001103070b04803241c4402042c142420040c6010103811072003003190401402c2c103d4480251024008440210722801c01081c03145010324090b10050942c142d40700501c00190208550f640300440c100e8550501031100910b00c40b81040103940740d0044100141c4540306502d10801000f019411203416240070b40c403640b0003556598000c036130300d200480700d0070115002400300f169641400d41201c404a4080d0983c2101c1d540090150030489004850080004038404144002d0100a01c10400045074001c0150300c1d00d0b0500c00484e41d0307a81000040071040c040000041c01c1203400101d5600f0b0942c49801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 475642068 1250 475640818 475640821
    0x120304020613031e1101020a08030a020a021e060f1b16060f060b1201120515040c050d0602130911070b040f020402161707020a0b070501060b0c0f070b03090618070b03 73
    0x406a00c1c10701882c04a0321110b9004585d407a640c00001c4c0f0007842540201c00c545107903500d007a0840a13400c515410320640c414410824442403011074660004804840289010720b0316044500009802603c0150500344101c541d040d0100707004100c0349564506010644030180610b40040102141c0056440240c9081c0c40416820302c9200103103035201d255128103281340d0f211600c0080544001d100104198003540a040404112244580d0300500a580100c0074595600100310f80c000800d904488080e8002100300030710324a04000d4010303284004e810400801d407040070f58424414414007804d8440d21b0b00000d4100905070902e4000554007500940d114031f0255080b4101d80c000d483d003220311a03503c0f22102c069403480c02c01c4e6150190010842d003001440d00c500108154440346050317803079540b9400c1c0404d02241d040300400181c09560000c00d41e0400c460601406c009441c0c120782d507510020002d00080610000700c0e540c00445507800100408c8155814a262041340d03880000d51003030200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 475643318 1250 475642068 475642103
    0x1c020a0509030f0316020d0c1e080d0c03020607030b060705070b0918190b06090a2702030103050715170705030708090102030609010b09060d090c08010e12030402061303 74
    0xc000c1e1620314015400c50310400340b07220700c0f02e8a90055800c0d103048180450324810240c0380c29007507140c3c0c0c64028100086615291360002d803040b04000500f0102c4202d0020801c4641c104220a100c0b041039450050031402151740c0081d00c0700c00142207101056101d02408165586840899000b035500004035254142d076074080d0350040c0c02c0301003414030131a03a803005419011810025203208146403a020a00c0c850316101004c010b1640c0c0415541050091001161a448541c58200541000411300d030042c17104125100ca05000746402107095801803004000107840010800706035000014421042c540c1e819040790400c1d402000304400044c1c48080c85241c9420800071401034145980c1d1010596580f4801820307440f06590705501b00301d482004102c13107092000501881c1c180100f2061608008614001c16580c000505a8140c1450003003005030b12024032680703503444203900c0603200510f8107900b00c60190100604c080d0085000050703040d1070000d00701381a0051580459007004000100c2c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 475644568 1250 475643318 475643327
    0x15031e0118050601020d020a030c03030f090507030b0703020732100606020105160e041512051c091d0415060909020f0a050a14030106030f03020f0601120c06051c020a 73
    0x800481d4403501d010081002c07540f0200b604181014190018801c1081659040740c49105255043d03081503640d0440c07d48506072801031859190040d07008100c11810350901031410701018100405041c410407081d800514440340900d041c0e01c480508210b0038004481c41152160464050181400346101c0d003005100c19501c40b80a983c1e0303d500070401039071900320303050240da103050b00c44000c00d046c008800101c0c0740c15005241040070141d03a20024603900c4813100842c0100600803035a50b000802444003c0c51041c03800d00c0880c02d00d24200b85c40a14001c2c203490040320781100070040040c041d00107000c2c0050210010b008500f038180411441da541c803654001004c0301c0400b28070600119400c200e05140c075040303140654200915001445150009a280712604510b2003501035480c0c61000002c1581d05d064090110b000341c000e0403c0440c0c03000310b80c0c20124143c00c1211070003a01ea440801003018040040251492401d0007941d0f088840c5150f036941c95000c00c445402400007440307048103a0b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 475645818 1250 475644568 475644599
    0x10303082a070611042d0914090c0609130b3006150d15021201060306080610060e0409030c08040b030601090b1e030a090b0910060e09060402040c051c05012315031e01 73
    0xa00299180898032b602040840d21170700c2e441503071000915034030b40300070302095110040d17100c0003c02c0b21241c890f0320500484140600b69281e01440e004619490609400744030301603020704590300311000b1000540c00210740300071800010b0701d2050f191480307200204056044400c2284050b541854541e901c0d07100070701824141c01403000d240240404103080300040b4035074805890325504c81000c2e625020342488001c2605080035810041d4119500010808503401030010380081801d5656925218001500310310855014040c03c0c6020003101c0f00340c00150080c6094001d1588215640b5294030481038090031881c2c0e07001d0007a0030000148203034000d00046032400f81401c0c103401c0c0202079540076448180c0c0e41c1100e5007182a005200040d0040c03800343e0100c0c803221414200b050402010240000e2100003100c009403e06654a0042c400ca6880c400e83c1d8145210140305881c000114801180310298100400307000a40c000c0301195070360030707009220f101c9480b840501038080c0d03a540740c140c03c070402c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 475647068 1250 475645818 475645831
    0x31e0714011e0504050618120f0307030506060703090e0403121805010b120a081b071401030f0b220f020f09040e0106030b010303082a070611042d0914 66
    0x300d410011034410780a4070b48103e030454050000369031040c0c004041f188680c40a0b61b1180200341903001690a00d102a10701c900b08885039a84034034000e10040d00315100604000d00c1800d05000030400aa40111080191350100f00f02008680b02c43c41d0583e480300304441d20608480c2442401d01d42130f4070410007182054082e000910a40740000140801d03803410310410055600128068404100d50100822801074200d17015848440320800250a0660940000040442c80d240d8200c0560385801004855861860104810400d0100140e00394160711415510b01a06103982d850312130f41030744440150b20705010250360b0340d40c1c0402c6400032640101410b41c89039260012600c00114144a05001e07030354484844441c40c0d0940e1010741e61450300800303247c81c400041c0c00380390001c101134241030310060404e41142e450300d80c80c0c900741050f1284a02010002e10050004102c04400c4064217151085074170000c151485041c10250300441039900041680750811482024525110906510407030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 475648318 1250 475647068 475647101
    0x21003050a1d030901050c030702100f0210060e1305151e01080303060d02010c26040303230318010b0d0804052b0b071b05030a020d11031e071401 64
    0x400a14914603008040114508964000d00c11800294000d100a0883c000c847e0112400c04250f40d00103501c494880d50300900160700b24290141042d0100b2070313966070982c115800c0c0155030411440000443d0000c081050840320300c4030b90b0061080611520f5104422a0135011840c6000b00005000000206c6500b5509460a00015040c4400b000b07407806030200602080e019010384e001140ca140181d001541c500b80e90484422409151a80003030709902d40c90882a2220300d941005031111038000c0040043c01c90082207c003240e000a000c032039100c5881b400743c5940210b00ba19440c014032030140000c2d00704c00490044414046990040c000301c4c3c01c200d8040099060070100c0308180215105088113489450010300005072400e0003061f4840f400c0d1400306103000c030f4445090340e5403c0d252000d54058100040000ca00d541c1030024541c00902400e2040c540121526040d580b0300c12104034030980300c0d04070105031401905004a1308540d400003c1002064083e5521a009007041c800014000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 475649568 1250 475648318 475648331
    0x120e0901030308011a0c0c190b0711270414010f3308030d0f02070209150321041a190207090501090501052d060a020303060328110d021003050a 63
    0xf080d4a4121803002c0c1082028020a500c1f442c00e0092030b50f00d02c2c204003d010b200c0100410b040c410300c40508a624099403102010f04403040c24041d0601068071407105915230705220f2404051601c0c40540c0241d0300c074480c0c041d101c913449003840c01007914003901000c00b42807940c481b10f03040c03080440500410600300080c00420280d200b03458dc2540303520462402d43c00a000364202031290340e001c00713a904450240903240550f80d50001d86050310868a200170004a002c80301840d04080000c011519280d2001030040130f074402d500d1500713000c3c501c549040c00703a2100146808a18007020340e56000b0f100c0d8520210217401040103504c45002e80208005580b81c1000040d8489482c0280d40c101c401c0034000703006048440c514180700e0000350102000a95902409c00c602b07440d00030007019108410340c06940c030303030402608040c200140001408506500306810384038035101d243c800b030a8540c0c0b20a156004d107080c400450340c0200300b2071029501442d84540c02d010190150400c1c2d03c2845046010840c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 475650818 1250 475649568 475649609
    0xd1a0903040e070305060105090612181f090204060503070303080f09010b0109060c0201030608030d0f0e2409011e0608101505040b0607060f090308090307030507120e090103030801 79
    0x490099102d204803448001d00411041c0340650b2040780c1291040c903001d850004c80f6404034016501409220b018010f022003017000690480364102e10641044029051a0b1034240b030403c0005840e000c09819255204c00c41400c5640759401a0014840a0103070307104140c0c3c07410701a0900ca01110b0074410480da51000400d6020184200c006041d4161280c1c502103050000441d589141c080c0100e0505544001c007050040381013010b80684c042c03600340896400803a4207004242c400340c20010441d03070f110251b850504070700400040c3c011000c80d1014442d03a42c03205441809000c00030b44165000508601180c110961500b0001c00e460a0900721051144d41444800445000700304502040860380360030301442c42d00e60403141140c80020642c03401c2a01c15158601240c0f42d84084000d2541ea5903030382c40070982c00c140035641c0862840c010390b00340403040e100504140305a407001008004070200b01d80070140501100100b00788050407681a0303607100c0c90013500d29203082c040d02000c8090403e001c881d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 475652068 1250 475650818 475650823
    0x91f20060405070b03060d0b010b1308072d0f0b03070906021507050a200c040c0507030801140604150f030b120714030a050a120807111e03090d1a09 65
    0x502e40c0310b4010b09034240307043c406190907000504103d521617100000b51021809081c0120301070702a5a04941d0740302140d4400f034080c5201c641c8002c0050704182c3c800c118880d0300680d2a8921030207201d0044011a0585411400007129041002401c001c1c00e408500052071401a42c804c40381038589128141e1148000e07030b501c00c980010a60b4002d20980000d0a15100750041c0c20407074200c0c00c0401c415070401e440320b071a12000a80ca2403496125440c5059545414020072070001814140a1700e85a2583c0700100061014045d0002a40d11000c0c051004d850b25002c980007007079454100e980702032106100500525900607044002410024942c2d85480c1140544544540c480010b007241c0d031038941c943e60741c01c40019401c2da00d4003c1c03c4107100440c2040c0030704060b2611542c0d00110301001ca2401403c0e48801801c3c0318100440b0000884c0407510002d40f14140301801c24506040702c0503001c8192451140700c114640000248400c0303010403d6070752035500403940e60880555140d80b100405036 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 475653318 1250 475652068 475652071
    0x3190e07061d060c031902031603051c020f0a050708070c0306090501150b070605100806071e140702010302071502181c08070f03050906120121080a05091f2006 70
    0x5190410440c06d00310780e170310b1502d100d076051090060324200030304409145206030201c24241d0204000141000380e0718600030098903110a00c103130441c01c04000c040c00031090301480c0c081c03d05010b070004100d002d1003698029101450342c0001d0044906440e0700c0c2500c05090b040008840c10740c281805201c0e44484030700701c01d0a440071000701c1410520552116005088081c006d82d8005500d00e1010450300010b0003401d01c222955201d04d800007105600d154a14846100524208188407403142aa2032048003110700e40c40d02440c0160b1a81040d081c204c01c0b1040d0140c850402c02c5c800607994005040c0c0303070300d400c5080310100c0e2103002e020014400d10081030095240200b030001d0070400e10000580700c175840102103002e8500141003102c03100218000e036004003040c81d0703034460040041000311080c41c8100301040f503901010001d41c10550b5440360601841250764203201011801d02c003c2d0702c80d051104a1b00309034182da9402d400700090301503d40c640145402781c04001c150202c254203040002e600e07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 475654568 1250 475653318 475653337
    0x330e030f06010b030a1e020301030302010c020709050603030a0c030329030706020a0b04060e0a06090606030b0c0a1e2102070308100f05060d02090306040507050906040c0503190e07061d06 82
    0x621390b55604030004002d04915440d136130060041c1d055100b190609202450103144650000101000790b400087c1c138085039075115952441c10306d02088251740b004002e075440111039090840210517949410707409005200000398100079401810340580c40c0c109100c80702502d0a4094480c544d40701c00e412615030002ca81d015110045d1039002c03c00107129a440200f444100340c0980785000855a03aa605888145105031b503080e48a00c0203000b441803444441c2d40081b24042d0082c50310b144110f015150000c3c14800e004485030003074130300da0300601903101d80786540200800c4807501440b4405a00003034105960540c0060f051500296050500072110016620365a0a000d10136143ca42007041c10350080002e800640e80030301204030305840c100710417400350740300b0030181c4440c034101703014481036039401440c8910850501d16020241a080801c50350050400c02c2401183c48511103010050601c3c0d0344651150702c5030510010700d4a9025075450392400366015032014a12820040104500450800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 475655818 1250 475654568 475654589
    0x1407110d1d010e060409020702040b0a0e0a0b150a09090b04050403050f0a0c1a040204050f22140304030c090b04061404021315030207060b040510330e030f0601 70
    0x280c161490180d140701d040300310305140c00001c040c0d070500460102d801c241c3c8660207264020400c6000c40c50701e13014021a03070f90180c9111036090300d13201001c003030711002174160705019a80b11410840c07626500810324440d42c10300c510701d80e250046880141010719074440c0000141c0b800d68802c0380e900e401d00942d400303a60103540f0b160070290601500c1d48c140d0b0000301c40d84140b09040420200140f0003551407040c0841060208116244c41c1c018071064030750051082d0070300c9540038100300a4030b0b648128514058122914204400f8040c98500c000801c075281505051102050000c10041404507400640718010001d01c000042103041c00180c481d13034020180603440d500c111280a08050b03000e010621202100124600d40e0795018140c4d21f4401c1c500da00000750001448000c0c088180031300300c40c8010581e020001e902d03004180345000000360085620381c0f802c40d492841c0c01c4a1715032020103045047c910142900d110080080c0c80d040d0700d24290780c001e0080b10340e800c100b4140410301c24100c481c181d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 475657068 1250 475655818 475655837
    0x2a210e0901121b0503100c12140c0a0203041d1f0302210a0c0e09121206060318070f030c170c010e010912060902091008030904020901050702041407110d 67
    0x60360050510320f0098000320b0b07880e10100041e00c2e902001420301c1c0307500030300b00001c0c00341000000800351281400307482e0a017424298200c0442035010f45283d480340309030304902d132642481d000890541c810317503001404828000351044807018114542c030780109021000800c100c0242800240d14515038800a5400720141005c0c480e00c003800010b50354540c030031000351a9100e010360303a518480442c64210743c3d5142e1901007080380f07003041000b10a01448402c1e0030b0344c1c2001d070b4075599082c9044000340031034043c9002002040c0d0b90b02d2229050804009248140e0313140507103618400c4507a06d050300c0b00307641001840000042202030030f540c00044c0c0c0f08260141c004001c2c40d03001540c1d24680b0380341e02410045c20a0f00043c02146200110000728820440410b8400f030a004000d0395020282030901300c00d0660400704006c410000c201c030341c8140c0070b560268032a882c001c0141c44601488002a402c1400c040510044000c036188180c807940e900d40302c0100307407103005200a5850f868080010041048400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 475658318 1250 475657068 475657073
    0x1205060402041a031c080907030f080d0207140d02060106140313030e1e040b0609010503010306090312060e07021b030a0201052d07050d0f2a210e090112 67
    0x4021141081c80c500c5607007010300e000f030080b034078100d110102d2191148080d0021703698160f1204016411140712030080908605540303d007103510003501001403014000180e1001645951b40680303e40135085503020180c00300c08010030b515280d1200130780c2d00602410001041150061403190030f5860340081050842d0f480c10502c0343d0140d10301d40140c0510113080c044030792542c1c1300c0030413981e860f26084403100c2d55180380d01070006a41144030705910030403081c000d010315030360720030b05403070440350480c001186d000e445007419103800005902d800c070403e00b040c80100b40175241d4144180562010740c220b840706d1186001e5058041c03c0100481d0785500030f528a1005517204402401108446000002014422040003280b2180c981c2d00b2000081c408603255080c484188800c5c0000076107800c1c10111307d2034200f0000d00f000c00d6082c44008101d030700c0500c2c0940c5104500c1c40300b203d560040880c0d59250000b02e80261024040741000700242443c04424201e003415610710f4101c0700e00c410443d0013184036a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 475659568 1250 475658318 475658321
    0xc0a06050429300711011104030302030a3504120306030803010b07080c070338010527010b271003020702060705011b0327020f0307050603010e10120506040204 70
    0x619103d080144084185034040c40c1000c10b0074014151074840c5514400c82d1548607095400307084440040c03180c140001c00c0841e4010048610b8541c580c0303009480808809454103a80c084070f80703400000007502d4403040518440c0c1c1c0c02103000b240030b008020715484d281c0070100c0507640f8074000104244802e0004001d442c4669010307011881c8a0315440d400c0c01802203030f05142c5403442c1c4c41601c840d402e0070342c40346003191001c0000c2d1141c1c510001041240f8a04206980e4880042c0300700c80c000d03800740703286c2801e041443d03050320ba86030000300b000843e80d60f541e2015002600040d07540781841d03011168000c4854040d0020030359800300501080426003001034182d00030742050400b81c3c0c20550030844803000540130710a4044040c0e0079114054143d00186008040350000f12075014641040c948141ca000081d10801341008c1e8115503c8091544e10b2000c40d0808400c1d510517500024084000b1034a82d60708100c06115100100c2e03480005d50313486644002c8401407100240182e04081c0102d40541003d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 475660818 1250 475659568 475659607
    0xa11061e0319020c07050f030a0305070f021f02010b0102012711060912011b050a0c380402040c0e0109141c0818010801080c01030e0c0a06050429 64
    0x840803442e04a6000e500c1d6841640d01c14082190380e034204500920261402402d25041024241d0040207207141640e400780c00e9205910015041103141c02d50201150307240707840b0684401c2d40a046c0d00c1c0450924030064041d212000401b405542003d03589000f086000010036804a4102071040d807200741c80d183c0040010222011a810801c204203054150320784145407070006c0b8400c4000648030700e001c086038059070442401c074002c01104100c00070700c00d50b11a110380b0890350840408880311202c1c51042038060151031450f0840103001c00041c101e410580000d51150340255400e2202c0303684143c2c2110344013854100640825060b00051200140c1e40c6015281540d02408403403400d140b030b4540d0000400c410808440402c400202401c200c0004540066261002e0030504103950501c0111070312030301c200d00d85c5810035555100841a41108200d140c4660300b001d06064011911a40010b0a580c068080c03c0704207054a4522143d4048589050301503806200c4010309005940c1c0b1940e001902 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 475662068 1250 475660818 475660831
    0x70b0c0a0204021b01180b0f070e031902010219120c0807080310050f10050a03020d1407020705150c060105040b01110106140f0301090f02010503040318080a11061e03 73
    0x1012040401621184020040300202c160f134040c42000d101e50315800c0d00c1c1c50b103811854501c0c1404565000440419855400c802c641c9544020b60b540d00d0012a4100701100030a40d00d40f148118480e0300c2d045045103044128001c0e0b0030303078480508120b2507071f0500c108d00070b001b4500c044010080781c02c2441400e034012400e1051642c50302e81800c5880d940c4058006950341c1c9900255030b5800c01c174601c0d00b50400307001e0200640341042c0038030071410040c0c0301d402917400000600d9000909904190030300d51080502107115100c800050130b000800958500d050701505000e10303650070598024021180981d856074004c07000401d039076030900041c84050803820140782e0621031580d0814200d02000c0c007501c0c024080709455010b4103680c030300401480e01d0f4051040c6002ea4541041c00c5c01140c1c5008150841580a080c03c580c1e035240c0d4038048031350a1040441900c141541c00c0081400303480460b0540e8071030700550000203081c0502c010040988600b804015070009422030880002c0c0024015541c03120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 475663318 1250 475662068 475662073
    0x1818070c0f060c1206140a05060d020c03070b0f0709120f031101140709060c02030730030c02011205191104080708150c0901080a050a0f1103160e03070b0c 68
    0xd0703a42d0798203000d03142050209000320b80142840c00078440300d840340000501d0040b2154032080e08813804602d1900320b90299500520000450b0030b80151a038044a03104640c407030413203a030b03200a4140308040c040c090356455040c0c0c90038004a003000c1d220341c41030015611302d4901d806034641705950707140203a21098401c40600030724120307c41c078001082c441c5d14501580591105100d00e41100014548446900b100c41031000e0f80c1c202d4000b603100020440b0690741411000115640b0b601d045101000c3d840840343c500c03a04c80e00036102010f0b8801c09402c121807013a20b55480703418040a01d0400d6900c120f03052105541d141c2100c0010030450f03046489140e15014000f4139045e11150810f0034841c040e044460907a0103140041c1841c04d5000c4000d50000945d1052400d01740b040700001c140000251a58140300d03180c2001c1a0390082650010358414612a404c110b00716104100b004640c00407a5440d288501380c101d0658207078010032940700c0040b802009849050705005104a99030000380c0102680c0c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 475664568 1250 475663318 475663343
    0x504020301140a0504020306060a0614030901020c07031a060a030f0204050a061517090d020d0c08090405040f110919021602060703090f0602010b01020a0b130b0c1818070c 75
    0x70500d002c607802410030400204031454240181450000007515580c0a60203444003001400d0740320b545448a103045c110100d035640c03038007400341d40a4001c4031852100c901a202002041003101e00c00c02402c0344140b00c100d01d095a81c5e0b000c104400c0385c984800780001008a400f80c00501c1c3c1607000320751100782640700080350341d11038002c800f4241140790700b01c01003200d01071203c0700300d2500c0c0c0c08541c0c0081e101d4000c00700600b481c44001d460340000810002405220075604041007182c1341900e011040141c02040b181c0703400e003019503040d10b4180f000d4505800d6910b40000c0e41c00d242d0701407403140d03442072100c1401070703042d04031400254481700c07480074038044c0400c5030030060b9560030060640e41e019030307942a0402c2c18924800d410b10b265034003600c00e40e031501000908036600443c40100098010080c004c3d140d40782c030414813884a0780d40000b02020100c0d020000e4a10494010b400c2d102d020360f07005030507034480d00706201440c0c100300298030b51454070100040c207291180c041c500c00a80b0401012054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 475665818 1250 475664568 475664591
    0x3300604020a2c040f1503020f06120c03180a02011d040b09041101030c3b04021903050108010b18100b07120f05030c03150303130f0e0f0105130504020301 68
    0x50f40a400603d011040d00b650301100c40ca058082c078407403034a081208016408050025050088003884000e00803070b0a10b20f03100f040e5403210117aa06496143e0284203845c64107070103126195100b1103415001d44444000161103580000c1c1031500c1e5a41a162210340b0146000c8818070001409080c036803058441510a64513140c454207035000b241703d00c00301040c07201054005426150f07170b41d141c4803c00c000d285002c0c0f05002201103264400800e0008080b88841031a2203181e030000311130303e03a5003081c00011840b0611002c80d07808140403080740c3d401c00c4030342d8030b400106e42a0380311616496444410488070083c4078011810441c0c0040d68100d0305680d099540032a04076540010405552031411a40c2c0c510246e038100c40313243d12102c4180b51042c40c614054400d00450701005c0c2c007000034040b12903c1d40b40d00f0380303080040b00c0280029010340c104c4140e4449234504401ca07640244041d80980c0c4022612034041511118141c44009140281c40003071951484007e0070000e000781c0e070564840c04035014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 475667068 1250 475665818 475665857
    0xd0c060e100903082a1b090108010c140703030204120308040501050c0f0a050c030d0c08010f090b06030c07060e100f0e06040807020d1502070c030515160c1b0803300604020a 76
    0x81303406070041d1b00b4412035110b46c02c00080c40c3d4140d2000c81d969040c000000e000320342c171186440b00c40c2021240280c88081b14101140240182d400c1340d0f91055440c4d41130018141c1100c1c0d2076104c2c5110364003d104540d81e403440032669009110880036100414480002c107140a0070140c0356101802c000c4034180043c410300b80c4183c03031004640c60045500341c001407001700180d0400d1009042c000714140003c207002e101092a40c400100a5012601c01082034000c1003801d802040b81940300000312a0140c0e00141ca40300100b10340a80c04140d549001d1003d03840c0074010905520894101286034140080c030b800740008030301c80c0e203011140301c030107090b03800f0402075544050407129001310344807200d041c1140b40c514600480c046140c623a031903090042142980180c00c201020640f41e291803418040540381c4102c1e890300211300c03403407881c214403800708116030b0020150000c802c80c190241402603120ba0341074102411048100d0282800b500040e4060405400030072440c4040c0c502180c81800e07800f8142c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 475668318 1250 475667068 475667083
    0x110325020310050103020303040504020d2306210c041d0307030306030b0603060609011502280524040615090e010608060c04080c040b0d0c060e100903082a 68
    0x1018105000101019420200180c200040300680100065411500013a569003d1446182e03c030369000111003048601c15003004100a00001c0c814100c02c051241400c0e00b143c049500c3e40c058510b50340740c900c000d120131480d0b030703480d0138900040e060b001101028000a048030340c440c0d01c1503c941116407d48440d00f04000c01d80c650003a540010020b0940c034145d40c800030098500d51007680080113000590740c90703035507460455400c151a210740ca01c5a00c0281d040c40351000d00c0032103000e02404012500b4100c0c41200304a24414000c0c3c5070b2582c03c01030241c207a400300b0808426031003c00d0300080c000941c1c0b6440502d2002e03817441203451300c590347c81401d070544010003c00b90490351681c02c10402e003d03003000080d07000f007a160034050070325081980e069525494071105500c01ca403104040b0050740c03210142c044202e5080200c8a80c2e0545628001c0c0214680b501482c1c000e1902c9442083d05603c1604018103032640000c1851820309000584103268948503011700000c0520103607291280c10401851 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 475669568 1250 475668318 475668367
    0x209090405030a090614031302040f060b1206030a210e100f03050a020301080307021c1e0c0515031f05040e2a010807180e152e1103 58
    0x1180d0782c85060030002c1250310301317a0285003481001d500b00d4006611800550b0b51000704c40b8101c26190010f800010041c0500110000d1050324000000c2960007600c0000e05403c40c0840042c601e50300c1e003605040d41d522076404003602c3d60500a070004014045030210309001c7d03c241c548450841d041100042c90788012010400125a00e071054019041d018000c144e8001e40d10a011425503140448050301c070710030700d00001d104141c400f03075074172130b2513041c8207036100781500645c0491f85d600c0740341e440a128140c03c0406a454603120200042c161a144501c00f852201030b200780d030700310748802110200102c2000c1c0c000c122005511004201c075102c6224218031548588002c0410035209507400c181c80d0099640462840540014100203074ac012658640004441c6000400f0301210620500f00c40001d070025080d031b83d1680c0a01415403041d2001c40b00c154400c90f0101c40920286002050340100e440800402803a440100912140031b50b905204500d030480540e03140c000707860440c003200c60059902 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 475670818 1250 475669568 475669573
    0x4060509041a03030a11070905090c1804030504300813060e0d08032a03160c02150a021009050a0c080d0509060d0b03011b0e0406030b0a0c02010209090405 68
    0x240e03940d441c1c60700804480740c901051030030004414502198072840790011580c10700c00e120041c0c2108410410441c40140b0051070104014103082c20482c0d102c10840c00310902c00c0070b502d640c19420185d400d6031140140e5050f240c252500c1d00d0b0003003d45118003402d4081d10055080e1160700c489041000707101c422544940581c1f81e840d056141c1c18080501543c00003020414000052100d0f503e0310090724070140d81004032661255511540d4092500710060800c2140d07000405c11400c000d404000f0310300942c40568800c00c0c4213076100301100d454070043c4020b54401303054507502501c01e221400a01c070f01005031041e12080c002c0341c08818282e800e203203001c5450b40c0c0503641c07500500c011000914080d10142c00a000c01a0103888010414000c644041d80310381701c00105a0b0404015501a4a001704041c00031320410301d50740c03413049100316808800c6c40800c0440815402c1403505104503070a595001d2445000354403070ba200c8200604103420b00130150b42d400c03c80c0c17032a9a40c1e80c0d0300b068400c5108500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 475672068 1250 475670818 475670827
    0x1a0403020d11120a0206030a090c05060a260606070b0601051605100b010f02070e070c1a1b0a050f0702060c120406110303011d060a03060c020106061409010804080304050a08040605 79
    0x80c8512005100400d81c40f541007064210010380c0c5150441e9044103e40d1804a0074048030f003840d2050310000e070b0249500c2500000c0080c0c1160708801c3c2d14941305009039480403505c940c40803001004508890090380110108412000a100d0000442d000803040c0740003401e00300f0104050010441c0c0c1501582d0644c0040400c208501042c020592414002e280020844985050180d980c0314140100112807a00c034001958240c0305d1803141000d1038000c0000e28803100c2c0007203420359a21003a19480815030420780c4048459821800310303000007900b03a452904c1c140c030900038800305400644040381d000800304019080003034104104054113405ca5051545d8030302d0441c020340410800114041c16400502c010000c600c2184101101040342d45a456400d54403080062140c1a0640000f4059890902d07008401d40d0305610490030340d9100d82701d181d065040480031000d1703400b50450300782c000b40301030707001074005520007000d950042e1080040300c0241035075548001d020741180e089040013400108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 475673318 1250 475672068 475672103
    0x30c09021c0519061208090d05010221010302040b01080108250305160f0f150309020409140d090e090c010311040306020d0519050f060f010210091505100602071a0403020d 75
    0x440c00000b045015072030f0031805c00341e80e991000350041028082c460130602e02c240e010711000f0340444d0004a00e080c041c800c0d0400030a01d24034016000e00040c2d01951401c980d0140650140d004107058403948001403145450381440c902d0b076541c0074100d0074815150490000002901001025041c0f0001c0d8450452242800d5000d0140030042d1321130004c1c1c950742e1004000c41c1ea11140c21410b40c0131246004500302c00d590000c90060040800000d004a03800403548424900102c0c006c0c0e9003454543d50b0b101120340d610038000d1504400d89800303c40b0340110070050501d6021391b0140100302803200010b82001c1d03580d12070303004070f8020b068643d040c20b4961080001c0004002c29404401c0b207071950400644c1400018070b001803000034105030296210303150208d003e030b0080120a400c140f01070001d000038080d5103070010301705c003900c84440c40103810080803608040d8a440c214050712a44e600030402103283c03506800c1c0c0d46414140480c0e1035082003001001584a020120740018050300780c034104a03548030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 475674568 1250 475673318 475673321
    0xd1d031f0906110a120b0f0d0f0203010b040c020c040b0a030c03121b05030a08060a090e03091903030807050304030315061e1b030e0f03031204031107030c09021c0519 73
    0x9051201e54000f040141ca0340141e0424580c9401404a12001400400f00070100343d80e0548240700c42c1d0b000c50006003410401c142c40d511003451520990080c81006509800d00c400c1c1c030020300803200541c000d030f241d091250800b03a20540742000c2c0149101c3c0d001d035030b035228144117403415001918494082d810303001c0340c0d80c1c01280e40c007245804240140d0804500c1d8882c139869009003800002008803000c01f040709503560202400192541d0401000840020509150742e075110204441c0103c451001d40c5034007018403400d0f1002c0300d4140e182e49540d0366410a0481c0c8a510044c4201c062550340d10b00032910307442991880c40038000030f4486007501c040070b0300ca40c000380b11008122005c01500c2c4540b81c00041000115119156060a00c40742c01c601480c00212207074410500c0300e40512003c6890714030b07582044170043c00356000f610380d01c5000e00b00c03910160312410343e400080c1c01c41d06038480400a000d8554020040e1841200c100d9400e5210001c0440c282c0740d064803005550901c03840c1d004080c0700d85 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 475675818 1250 475674568 475674581
    0x203060f04110724060b03070c0602030a0603050d0c0302010f050f0408160f030323010f050f151614061b03040809030109050f011401050a050121020412140d1d031f0906 74
    0x6e00300b5003410340c030384990001c0c050340204100400c103a0700400401c10b014444e400c84009194041d040d2000f480c0e01d080014140f10108106400544c213084204e1640005480791500441001006981596598480b0350316940290444041d0621240103800422040443c055440e44079540100790382c0c144075800e40689500211a2642e50a1400100252060f48070094119141503524462403c40000042c07458013504c400c1e42d00301440003402054180ba034810a013141407040c44d00480341d0708030640055846500302e600140c04a07850341005003d074040f00c051030b030062140c2c007090b1030017011101080c00e4403082801140c03182c2c080c0011141800e4280107620b8060b20060b00b0032210341c90200082c54100f0a4412981803080c4441c07422404108100c0001c050b0000700810340d511035803000400c00004030302001b92030718076080300da442081c840480c60450841e125034500a2070003041107007100f0620480c1d0610b40c544110280e40520707403944031100ca214070904c0000142d12201d810300205031080d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 475677068 1250 475675818 475675829
    0xb09040b01030b010c2009100602010c020a0c060513080f0604120c03020c06070c0b030c03270c01140d0c0201140916060807120516020c0102010203060f0411072406 72
    0x8014078144a40d17800740f1780380405034001400001c3c10300c400f0310b0004552014006540c11200c18810000260340d4408207104403625a8000c20140c200e0f00000ca850b0105240000d0045144a50800946200f1740c040c100610b440c260310040c165460114a02d48003d140c920344458109000b080180004140400741c100240e00701204100e0095030000d48510031030507000d102e207a0100da080184119120600040e108072a01c043d568245500b0f0800140c01c2290500440d015000000581c40313200720a050603040c007040180b61f0000a40015a09558100d400304041d010500107803940e10524021429085c00680001480d52100e81c642c0c1c2c0d1601c1d00900a0100313520145800102e00d52420509003142da207464511203503200e44030100c0700b2600000d250000581044244030000101e151016042e080580850b0710440c41e0360300681c203038003003213500316440700b50b85a119280d410b040c2c000d04080000003a90b14030304802e980e650003000600c5000e010000b401c010039054a004244609400b401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 475678318 1250 475677068 475677071
    0x102030f280311070305181804050f1203010506160b0109090209130201080115030906111c0b060405040b011205070305040506070c0203100b0d050a03030e0111040531060b09040b0103 80
    0xa00f84030f03200d0300e00c4c814041c0c000c04000e000540c68400551a030300034114048020521000380c1c6148110449821013030341c0649840c090040e00440022000800f4a6002815140e10382142c0c640f00400425821500e940300d0011064002c500000303c05042c1035000e80070326800040c800d52140184494060010981001c2c402c404082c40007503030f00000f9150460ba50300301207074040380000004401038006028001c0031581050072036803180240342e000d804d162145130500d9a52103034100e1407900307582a441d05d07160481001c01c018800c42c00d1070342110715405030606105550340650350700c0404458081b1038500002e0713619400e11040000512032560070034403d142510400d9003e0300000e8641d81111100f10b40d565079828407552640702c00081492454012050300e800b0385246c28041c020f0881380e00f40c8002d5500e80b000c4559145442d4081d81c0c2500c8000c1c14200da1090420308000403042d0900eaa4103610788607165045c002c40c402c1c091000074102c80580151188144414402591620300340d0303a0605 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 475679568 1250 475678318 475678331
    0x5010f05010f090b09151c050c04050a0c080c031e090703050706050a050436050a1b12050405070b0307090515070f120e0d0302160f0302090a0b0102030f2803 69
    0x42d585e51413010303040748048500552600c45480080e05500c11b038801c412084001c40d842505104012503083c080072000d80d8180100c0d034680720958111540f001010f00030501c404081501120864041c2d40d000b0b85e030f00461744071890455190041c1c0c010481d20200158400340d000e008002d42070211500600480c208141001401003000c1c01074020f90054000f5640c502d03a0392140d010118005991102c01d0400060400c40300c1a0b01a001e0320f000c54004001c141800344051404540c0a803a242001803a0b903140020018010301d480036140191068805204070310300461022143c0c0c1c01540981919120b1007149480c2000740111241c01d0301c41044115818002400840c00441003400c040c1c0c0e1044000c00001002c042c26030b41440107014a0340c1208442c00e6a00800d500010300c1c900f030800c0841c1903080d842d40c030b44180307034580d01030700009400c24009000700d07400310244d40140030b880308140103503800c0c2040f0003c4001c0640200c072180d4030904c00c48000201c500e030710001c90015105146000e1140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 475680818 1250 475679568 475679591
    0x60203040b040b2b020306120f15100e010b0c0d021225050313030506100501051902070b07062301050102031c020f1210120b0105040509030705010f05010f09 69
    0x1c0d0103684149a440302002410003115584a44001d018004103002c103c0500b10b0105900020b400841d80709001e03a01c40389500841d060005554000b20011000410207526075155240c0c90710000340c02520036000e52000031920b130302121078460103130401c460b501e512404038069071483c0400d40d004010a5400c00d403401c040f1042e0302c4040300e600c02c1103142140c2004108030a01c0e08800c81106000d4554040420700048040558603501e044a01070b2040380c0c110780710000e100641180b18811140852410045041c5020300313500810100040e50050712a550f0b901c04189080d1350040c103045031084d1351344000e01b110401d081d4649801013407401545a6a44c10403002139900d20412010b04e1308501050140c001030113441e011186a0740442100c1c640f1032a480b16010b51481003500d0040a80c00d1a00e400714031840280c0c078540c001d54211660304401d91801003030200070302028089116a0004003c100082202401041400c030b0145d60001415803401c8040d014082c0c00d90021102c2d14140f0004e8a130 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 475682068 1250 475680818 475680839
    0x140607020f12070c14060d0608011a12070909020604031205030402010f08060a0605030a180503040807061d2e020c0a05010c02130e010915150f0b0d110c070906050a06020304 76
    0x58840505e0408038000c030400001d0714500602c0700811419051540124200750190808070212505800112449541e4810031007a600d58100440c282d610814007008424080d800504503540080e04161030b1030384031303102d94020159184000c1d02181d0000180003c43d680080c00c4046024140350602c900c3c2080e000082080e00d880c450b21007048404000b0039003030825548011a1b600121007080c400c0c0c9400d01d0580d03165009031045010342e000e54100090001d001d122000220420031071100444070b8400200103076070340e0120308042c4a0400b0390220500b0600003050b40c00a030500d4004000030740d2650704200424940c0d810082c1004907600344440161505519000c291109040210381e10840385016801455810400f4081540b1400c11004031520381d80001005503800d0f461220300c60707c03414503d05801c8144141c002071141004003002c41c01043d800f038408154501c15403032131f0100c03840340319150000c10f80110b01c01554072041000145400c0301c1c0d020007440a4000741d4101403a0180030390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 475683318 1250 475682068 475682093
    0x80606030601020316020418050a0b07020f06011205070f0b0d0509070515070f08130801050105030c280f09020a031a03032208030f030f1e0c07140607020f1207 70
    0x5000e41070361700a20456803036801100c07450390910174501c0607180505200c4e50355012181c0585413007a4001c04101e0705072002c0f603040700c160f1500c001001036901c0d080c081001d0b25010003060b40c982c0075180300454401c80400ca040010171382038941d00d8131801243c601724220f40010300012141d41c86070401b00926101c0307414a500c41640401926124585402c02c004010315042000f0401c44001850321100880032814000b941e80340b4008018a0b1b0300d441c1419551660305504591004d036881d02c9502c8180b00100c640d00c1c2d40307400e40c400401103a44040744900d0b105030b41c10402d40c96402152121f40c0e190706203e110846036030318200000f1b1080400120751a4811408440d6003120741b00403020001c0301560081c0e0003000c80e64110f279910844540c6580380c0d81c0040ea803280f1100120f60100700c512001c4180004418818001c001c0c15407103500c0d4411b00ba5110310422205400880358000c0420401e0050503c9140550050007010303000110f5542042419076510380345000c18041d103004100c1c81724440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 475684568 1250 475683318 475683337
    0x1b05031009030f210207050d02071e05060304051515040b030318061b060406050a0c0503040321060302040908070302010b0604030b0403031802040905010b01111b0d0c0503150103030806060306010203 87
    0x10311303880c070524041c03060300410401c101c00c0d01c0c1d000156900404c00c0010b240c050074600343e401e80e0388890715148d0b8100700e44440400a800c800e080b00040c0440d00e0480c0045070080d10690481c0c40c00030440c90070004040e03040b10b0344802401a040020120306090165258148044000d94505543c000540071025070080c1d0180c0941c1c03001c10400c80510064142803605070614040764610f180500d0108050841200c1200d00327103041c81040340c88103001d04140d9004951644032001c2c104400141a0081200191040480c945900c40040503031124800ca40c640e501400250796070f98814180030b070a4170403201c9664041c01d01040104089088450a141c0182c0e06150200703244451406e031801d01c4c0035000000e94410300e02041030080040560082000b08000e0f250000d408148032119900d840c0015045114040b581034510b5140c5016140882d1aa100d02004c003159038585012034580300150315111504001200180241900412919070102c400c0b10701030301d186841d0f07000070340700c0c003402400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 475685818 1250 475684568 475684577
    0x90706120b0111100902041803050304030c110a090212010602030c03120c040f080f0d08070203121e01060203030106080109061d070c1401021206030606030a021c1b05031009030f 78
    0x15080160710614440300c0b521403440440f444d01500641001c02400d48400807445245811480115920002c054400e03068141e04c41c5400d542d43c5480c02e43d081601000d0031600001d0030180d02c42d6a1b9100704900c009030000990040c3c664000c62408241120185c20010943d031003880365102c2c101c80001100c4994880420808054803408a41e0b46130340180e07080000d41500c81c140101c1d02c490006980c40c2c81505042c2140c000c0c0356007840a8a42c5035050740c247c00103030020010110344264078159550043c07039800e00f108000001d602004880c0d4403c4c1c00c4080103800000040180c036600605160241031200300c00c0260301c0c84c2140c0350481c03081441c41c501c008256500058006801083c901103140d802c012038115a0f00300c1001c0710300030b43c000219100d000901802080b03160030005002c42c400c400c00f50040c05035208903020002810b0700e00c40400d4511036104890340001d089291004203507040c10340c4c40d411883c109002c04d1300380b5002203910078620b45001c0d02080440c1e48600c050340d0380015400c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 475687068 1250 475685818 475685831
    0x1903150b0a0b0a17060906040e0c0303030c0a090b09030d20010c0e240313080f0a080103020a06020d080a0b0d0203010203010e01050a1a070201050a0905041805010509070612 76
    0x5058019091118a440e4044015100020450b2646004100312000f555403002d4941e00450070300c034442002d48005410405c81400030764075081c81d40c00f10401c2040141111250566040081d165078011184e003550794001050b00b261050b08401321001402c0c000000714204980d0340042075954520046070300811414110384049080848950500d5610000080c000c482c1820350190540011040d458000c03000c48013043d501c480c204d446018400381c00c80350145940c88260240d00070500901050301d10b00d5003008800602c8050600420f920740c810385440010758514010450b40b6010340c1d1240c2d05640101c0c1384c188020791700000070765001d820040006650455070010a0000c070070440029019031000001061201810302c1d40b90403508103d03520481d860b240e00c555070211049241000d000322081c03250360015030003203010340605015440c0400d04039070b0b51750010f400d03150305500d44454020540480418040c00f070207981e500c4080240100320f840e2408200501803c1940720402049903102d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 475688318 1250 475687068 475687103
    0x80705030f06120312090c0d050714030c090a060510031406012a050609010b01090b030a09081c3e0d0f021b150c1c0f0204140901051903 60
    0x2424072076404074101100d1300c841e01c6001d02d4800d6001511b4203c06445a400480142e00e40401c0c51291203078001c003e4101c0c5440d00c003c000c1001c0c41d5004c581d91501034403c17449001d49421042034424080c0702c0b00032541c11b10300703c14004002d006202080405040c00203a00709a10668010380c0c0144081c41c0582050782d03d1454508044264050114101c4426400070113110700001c4017400340580c80000c10003491011b005540d107411501c81d051100e14140000340c2682500e50204405e00c3c0114091860b000340d003501303c180c1c40d102c6a0700c1144a9500d4241d02480c448184c5050348070308800800d01012100e85010070030302c0d02c5001504040c0000050740914000d01e035080000c0408944000b55103400655000180c0c00b003010205205510842400704c0805120f80140c5000301c0040c050186407200014008007a118120300f40d541090b19a840304400700c030a031000b0401004c842c03003480005c0b0181401c2190b07030a010392190744111341410422401440c00e1841c20f0480703510511427076800c1d054030b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 475689568 1250 475688318 475688329
    0x1b0105101e05100e03070f0f0e09030f130602160b09040c0507050a0501060608100f05010f02030c060c030123030c0111070f12060c020d020a081e0d0b0a0501080705030f06 75
    0x707030000c070b42000c00c2c4807442c41c0d00f5401c141928400725040307040d200c0594031410941d00c4180c103407082c009101203400c0f04012a1049851140e0440900b906892500e8080031041c9060b030b01140c0d40558600e080c21042142d141e041c4001060b240c004c40100b0030417460240079000d903002d06201d4511079555400d21a28190082003210310385944141030303402f01c90803820068003c040620134003001c0741201c0001414030051100e5042034528240e2131000150400004642805600c18250198072080150350403048040000610a00040c0030072552581031584d00c034a031044002c0380d00b252408800310300c140b695012401c0c0035114028070386035038003c4481c850b02d4941140c0741c0c0705140b6810000e401180c50801c031040c0450041c01ba401c180703e000000741c7d00303e03030311100d0201071001600808441e81c00a003001c40103205100b4a90780e1042c0c440741c030036005919603108030441c0e440656901074001150900307491600c0180004d08060700319140455001d0b0a07840b0080145078517461000016060b5900d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 475690818 1250 475689568 475689629
    0x207021513030b0406020d0606050307020a120c020301020c010606030b0f030303011202040204120b01030203060f040f0210090f06120c0503060a0909050a08070b040c27050a0b10051b010510 83
    0x703c0d490b00d140c00c0c1404d02000940c04640b160452604021005c1182c0740100b04032130003844254020091030075607446040c40030950f0444501044001041c00016079401d0000d0310310900c0340e1b40005151854480e025044070759046001c0d01448440ca1890b40f0b594011041e41d044581c2403400c0020b40940e480080c2c020b11454102d14070b0080c030341c8010300510050410030341c182e91090f4103c500c103843e070400800140000b21001021031118250748001820181c070280300d500100d0914a02d010b40324201034030111804e421420020301010800c000f403070f8840c0202d2914a210b81001c503d5070920101003040f4803181d008401148e0f03100d5040808004003009400010b0750800e82e00b50711501c2a1a00340c5031000c007510140e42c010b40741c2c0401702e4465484c0181d0038924042d0900c5c0c141101503120f080c0040c0c00010481560b02e41c0e9804822560303100e030402404041303065a1a00d03510740c02541820001e000c44c015400301a8035000401281c400c0450402c81905c1400909415100d050310140c00d01e0b550 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 475692068 1250 475690818 475690823
    0x30305061c0b15041103070c020118120b06060705070b0a05091e01031d0303070e011205070804031403060a030f080706060f05030106050d0b0f090a120f080a020702151303 75
    0x5007005594288841c1000d5075010b088140031840402c024802040f060b10065545500301c1da0040000c030b441e00c0d000724124840c013441030401303c0540c4000040f03e200444164003820507241c0000459082040c110312860780210200c3d80d0905020701522001d9035058a409414040301e03002500644c0c450041d41600c0602c0c000810300c00d0104041520b00901000b6803440e90b0101c0e04003070803413882076140715031180c080100000030350450303440c01d000b1240c840b0f0400d8a03505120301058902e85540b0503000381482a003030380c3c4030071085003081d01e0000c01418601034402400740c41070092080030341d507100303031102200d802039030400f00c1c60010b0034402d119128903078006052614088000840e1640d4661560460320120001c0110594138003d04c03042e0501150300034808456480001d0b403000c1009e6400350840740d22000c8540c4020790f5510000090090424800440c136450940e00342c0a40c8881c1041d0300c2048a20154100b1220f80d02080d2083c1c4100800c0210072404280780c0e19a07080f000c100b41c021034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 475693318 1250 475692068 475692109
    0x1203150f0d080d02090a0506191d04020705030918010e070c141c02071e030f060b0a0b030a051605120916060903050d0311070f0c0306090302030904050601020c0d03030506 75
    0x3c901880b80e0003035000100e0f860080100c03110005080c034009050340c20322812100011001d601106040b0344240c407060008901030385a0950a031503032118800380003154443c400555454459108200078100400111460750001d00010310120703451181d07458005926003051174800780e00b860f0915450000400e49160f52240b4040e180407894200141d01c80c0d1300f81170b001d407040c0c1e6441d01c00500d1400b41d0100c40c03c03840384103c031007000020864081042c0c02405804002041d24170f5800045540e000d940c02003000400200502c900c07040c4a01c40e031500002e08004046a000c1c100c28064040c1c000d940c10f18022610100004100981c1440701c081b0030101c0014030b21420f03890310005002d5003a01d000560356449601605107041e4028070541d240520040a181d0601c0c807030340d0315140d01c811510b0044803103c80c0304400000041c8180601c80700c0c3c80c402e402464840a100c0c0500c02100c0d0020110390465100c1001c2d2a502d455401109441681519000c1031541e41e01002c10b0101c03104040307810880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 475694568 1250 475693318 475693327
    0x3031b15090a0251041e05091b0d06081c1101140613200403260307050901020109171b010c0f03020306030a0b09010b01021203150f0d08 60
    0x1d42000c100b040e502c40c8202d5141c1c0500c10b10480d40070251103400b13950301440400d001203036544007401c070303005860100c03411041e40461990840b900382a0090381c482d807800c1c1e411107180810b03000291086000307020b050390182942c6c9041c1848035403108002400d00c0e40010000b0f80d0700141201600f00030003414403a8116414000b05402d445141e0428826820004020014144825006000b811405110752841c1c201e03035114001000703680c404254414000c0d030340d030f1680b59003900c40358000039038401d102842c080d80f59461400c107040c02c041e45035510b0401e090b444516040e206000300680307070000c40c40d00c0c080da10754880c0710050f4010000b5840c00b8001032602071750b07880d0ba00c020300d008140303d4210201c1f09010b10000c1c4002ca0980f60040d0b07189010401240709080300303d120b5070107141d005100504030f8100303001e1911004095201550590b850b65140d103080c03040e40d60100043c80d20701828003940fa2441c6000b04403e01d000c46000c140e94403a00200749003200a990b005818680d85030002a407950301d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 475695818 1250 475694568 475694581
    0x70b01060207060f020c03060610120f020403030e030118080d0609020f220602030306040507090e160809030a1d0102121216080105030a060c110d09090f060503031b15 73
    0x1550b51600c02c603c0014036142084800b40d102003205001d00307001500800c1e542c1c60b0358040080d0540c0c90362201e010040710007181d6180f000c603400b9030114080c00c0e12006030b95604508004120701d03401d200c1c0c240282c0c105504043c079966004604515183c100000076241d18900d845003020f808164807901009001081c01c418004c004002032100010b13282120407290580c038105080700c072541c401d12000d030300b0900001e6224100317500310540c42501d03450030694450b2102c6840d0001c100a03903110550302450815011882d81040d5002d40250840000394103204420070b0003043c1c01008042100c2c90020541e101005074000c001500c01c40d100b19405545681e14510302c40da401c4002c40381c01040c0c241e07060b1003c09960042d070788107046c0e0380050068070800d5215141c10707010385031071940741c400c10a070070340e601e14149018000c2c01c0803c0001e584580e42d003441c0541c0c0c40c06942a20300400b00b05450304a042050365000000c94a4620760001411302901d8401800c5081040c103203a180b10845608003007042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 475697068 1250 475695818 475695823
    0x15030507052b0506031603030f02011b05030412020c0f13060503010c081006080105010e060c120309010f0b190e07020102040b12161d190f0303110f0f060a020906070b010602 76
    0x101003002c8841001265100700c10103079202e0a41302ca5400c8514006030500100c0e22480001c0d0050601d07000100342c03009458000c031141040d100700c5100050010090000b049090f01e20f01c180c1500d64801400e260b00401c0000e0550030007141c01a00c034000081d8201c5150720190050303001010300030020800340100c0709029240520480f000c18515001e110040340140c09444800c1c103950701030750303a80054100a0144001a0b20455204009100710100c58041020314402103110300340c07405c00850715008941d6450192040300440345e201e480506142c06910322102c010108031040c01c04404169181c1200503030080c82075810800101000081e91404250b441c1c917018060700490628640450b038000089501b8000e0745c84081940c400d4110b4400b0a1038480c43c003031503007061a03100d2090503541303450b514081802d590080b03010410900c001e5a1070a03081c0009c9501c40d5600002d001c1101c5010b411a8440b0303c000c00015001e580403c1d403d82c50744903081914001035000c55040307583e58403100040d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 475698318 1250 475697068 475697137
    0x5070306030c08060708130f050a03020c0310090809090430080a0c21020909160e10081b07060c21020c060c030604110304030e0109050a1503050705 65
    0x2a14480e40c07001c005003c0800051441c4207550542e40c150300c68a40100003140815484401e59401429002c0318020420034031144030301c2d51083d0000c00020340000181800c0095010215140030728000b42100071400002c1211401c1c40110b411008950b91450041c0051910341c03200b0f01482c0b041d48201c0d00c103904c0141c000038440302c2034a801995545041d003c20a4411014104001070643d8442d4024440c640c0220141610700620150900c100400801c41c031110454038445100600c0017000e0030f990300407003400c102d0f10302603400400d00d4100141c0581075603805041080348004084114410613000420740365010b51140c000c3c803034032200c1503004040c1c4c0c070080b440403008001900d04180e10103a82c800c44042d581e0070030140c00d66981b400007201c5190001000380c0d07000b81d01c42c601c141e641d02ea080002c0d44511b02c0791300d6004014096000041004569400c03241c040c41480030b0901081c001141e00d24030b007140310702c0c4c08102079070f81d4102110140036840042034400311725150100e4032400d82440300c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 475699568 1250 475698318 475698323
    0x80c150412021b0d020f030106090f0930230a020a0c06080105240d0221010b07020d1202100204090609051b040e041b180b10081302130507030603 64
    0x943d00b00c220359812484100000180d20781c010342c0210f80c03000500b0f14041c031a080c144000d00026003180d40b603000101f174400c2c402e071011440c3e43e200304420810880c140643c0e6140303c2e100b01428448611184240a1113100082405004904902032000540c44106040020a402d441c0380c80f84d400440295541c0e44c02038045445070360303040300826540d10600703404e412503000a00d51424440d4004980144400102034105e141c0c8007006802e000c181c0600080c03198a41c50795100c10b5100900c140e4034407401060b0848887e0380810002a00503030b40c0c0c48135a920450700300f203030f03844540700c01031003680780c1150401d401e07003518000f0900240400d41944448100ca202c410140102d81e98245124107400c20301d4140d0705040d5060000b40540107170b55081c154814414009100c0c50b0030080385103550401e143d8440c407000c080c2029008006089401046c2c43c0c654240c1e0200000c602070f00e80500480f02c000e02c20b00c0491101b4110606543c3e80c00c2c00c030400e1010550040200341800030000f0040d1680e030106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 475700818 1250 475699568 475699573
    0x27061803151e0b03031611120d020706030b0105030a0e0a12030e0c03030c0307121101020c03030105180411060a0c0204090b0702120a0e0603040c0b0a080a1503030507080c15041202 79
    0x6002c80b0168000c802c1e03803c0c0e0090281d450140c0303e02000a035540c8200c030556040002c100381010b562101e4500c08030782036040300104030107400400024030300745040d0002000c2604004101400781d8000302501d820400403140400d007401841042c030702e4010f6030003014103554403403100010886e816a02000c1c44007080d2085d14845d0f04014207142e80c91003644c024084c01d500c10403901c00404d21000c1124004c030640d107800c0b55200c0c0310310b0a80342680c101c240c90b40f1680d00000f00400140c80c00d9100400c20450f1002c49260614050f200c041c000c40840486600078200081e04102a51040c0705500c0400c1e0300030030030070030081c95080c13552541400b00c2e0882c02521a0740100003100c00c08070141c60031401c0e03541c1d40320a5031180206220b160340000c5c00032103d00c2291100400d11050b004080c040042d0260703100c040034585140c5013426103090711696080d02d080c80c2d500340301180c0d003c8220750025030885000d075922000c00904914140c000f40b030300b20f8003c014405000030026000c601241800c000c0c0d08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 475702068 1250 475700818 475700861
    0x301050a0519020711040b0a12080309070f06020d080403050d090803040506060d021e0604030602030103050d0806010306080a02010302160507080703060c020105071b050f01020307020309012706180315 88
    0xb1030402c901c0741141c0500104541d6401c4c15007468180c00000c1495400340800484541e580311360481c40030b500c10101c44000c00481001084c600400660008002070841c020341c0c1c0c0c0c64003001a4071091090000c104101d11000064241402041281c8268550250030041d07113216051039a4550029201264a4001d040100318070b031074080d840c0c0c618160020550702c20351032512583e00d0060311003144150019030900c000004100d080c03001d14020341c0120050f0801005000d0010000c3d00c005003002d06040c1391250038000d001000403070200e1030381d084c00c00580d50054040b40c100340e42030031301c401002d5104003000484c00800114140c402c5074880e140c248107402c0284d1040c0e00b41d80c01221190002030b1252250301310703c0c20320141006803600480503a495164191140d40c02c0e6401100e815001da0b1000039049801d50303110140403941d0480450302e00d8805550440c2c008003620030b1040707504004e45402c200300a4486448803100a55100c0c024091005080c48040c018000108204100c03130005a07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 475703318 1250 475702068 475702111
    0xa12290c13181a040507171305010903050a170405071e090906021c0b030a02060a050c0a060501050a1e060e03070b0304050a022b080c010e0105100e09031206100e0301050a05 76
    0x170203000c3c90040d10b8000d9030710350290f0f0184484500a20101c60b900741d96021101040d800e00c80e020000c6d004e5501c02d07944010140006d00b004040d4120400181c0002080202291010600c002a1030840400d5007200081e102c1e10340800c0308507001040c0d024039010241c003c0041650080100002c83c403403071180c4400c6c3d0941101120600c034100c58054004000080062a0000007090050b19505101c1e04010005440310325056024200b19011541c540040c000f61402105600040030104c600e40101200e214544d140c02115102c1c003c00c2c020a51281d146507501409a80c015109680c0c28588920b000d06041d540c50140540a9000e084843d07030070030000c84202d01c5400d40c5400b1581d00c5082c80d02540d00c00d503c0d5440130000e40c280d9540c1e142e0035106441e0038040e20313000315003a00c14081035504080d14070082c542c015102c060320381c2c030410441c0040f052024165910010840714840c4208920390706503000d5209641d00d0380d02d5442d100c200501d050203688041d001d200e051007006130390500b07031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 475704568 1250 475703318 475703321
    0xf0f180c09270304060833010909050412080108161403190b1b0a020d0f030b191d0103020a0e060301110d1d0c030a0f050102090a12290c13181a04 64
    0x310354100740e003002000c4007000b04072003e00003901e02d41f046c076240318421b5444070010101e50040d20129042c46030f8480c4000c506900510245c090031800b0050140ca402d11819101d030f08080b8070074508016241907202c5d400c0d0ba01840f0000400c01d4607154444103209505e4054000002102c29021190a003c0d03041814140402615030a8a0580013081d0b1075607c81c0c400d4a0504c004401d18040644a02d12506291100b80c001800b0544221103c0150343c14825014030999044aa4041c0d18404400420140e641c5094200841d0450211183c503612048003003809020b0320b9a04411078200024880704a0304213601030304594141300e01c141e0f90401d40820032502d07050203290560b41507202050788008101000144000340380324030300051500c030b061404280e5406159010084180c0c64030350f91000e1107540000f000b000c1681d440340036180011082101080c16010b051002d408002152420f225070480203080c000e46a003080c0f40b0703c488034405912016055400d202e401c100c60400c50b02c030441c1080d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 475705818 1250 475704568 475704601
    0x6030c0309011b1d12070602010b010206010504050c07021509060a0903020f040e0d120209122b0c060b0102030d06030510110909040201030c0212030f0f180c092703040608 75
    0x259603240380380c0c0703681c04c0240d020142e002c039440d4000d20541d00c141155404114900050805400204198030a4800682041016882140128140420408020804800c49000c41e504841c80c55a5a1422200d0a40c9020b03004480360007510010790031309844d40260200c41100e108903156200c41082c0420300080e12402001a1a2940800007941175540a05000005040f84040040c14011032900203070315200d038a041c0b1051a0450018010120070744a0030781c030b0b074021038403820f20300c11107170350000b004480742c0300000e001c0c0c40c1c0c1c0d640a840260b1081c401c64103440210141800090f4603410180d03141c2d912030500025451924406062a880400903100324540c014880d05251303541c1d400643c007400031f1a81c0d10045014501c1d00c014950040300103076000b8255034510340007501d03000700c08a103003200c05040d41024503c1c035582c4070300d803d10001c0c0b14030100c3c90a8848800c542c44840e00b0028070154064074100c2d000040da018004c2900c0000508100c40311503076240c0ba90b4a8050070a250070b4078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 475707068 1250 475705818 475705871
    0x702040f0b010e090606090303070c050f0a0e0c090d0609060e1e070e0c04030b0a0e1e0c012d1107060305070c0602130b070f02150a0909050604060506030c030901 71
    0x4856082e000340d04d403103081c060748001c0140c00a441d00c20380340c0020b41180d018032000c94002c40c03030a806004038100b21110802d42c00080d1040084e6500740b100d10713140b440000700303d019011000508100340740c855008500361075620880c1840040603a2801078040c10721112400002d1107100454041c00c4050f402140c2481d1861018105031810b1500c0e04a0000d030050201d850440100170000014030300082c2d0703a104a41c8036400280c140c054808003410041038150031600c90400a410380341a502c046590b14841c6001d00380001a5600c07141d0b450008100e9000c01720108000602d249113154001c55a100103441c00c10a455a580d05c072030059084800954000002682d00c1c0341c2c42001030410340c024060f004000210b009016560f003103040d980d520003581180c6911040c00c1c07100440c1802c60840500d0318410481505003c003070a00100b40c00800d00c21514507907168000702c1c0c1561200d80c0481d000e0f090181c94a9541d1600714128005540309444040166103060310a04045e0043c01c0355006058 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 475708318 1250 475707068 475707077
    0xc080c16110409020315040b01060203071709010207030203060702100f201b0601060c141f090303020c0a0c030203160b090d320c010c170307050d050c0702040f0b01 72
    0x40c0c054076414040c0000d5481c00ea0841d964000c0440507980400c400101118402c440b000a0304d098075000b00e5038501a40074409541c400e100403000a602c1c144c1107034903081c01c41191500c41c181c00004038a060911b030700113500b500414003402146540800c403404d41d4034480b903040c060700c0c010340384542c2101c80744040e4802c2c00c1502e900c00040040c1a00003401d02c4080702007a0691004280899400d201c2c081c3d0250740864002da104c48100801800c01036244064440548903425903a80200c080840801c071400803d41d48880a10415000741c0c10745074001c4d000303401c485100c00586811000b10001d03000613407083c403a0140040000c166850301009484401542c5820081c543d4140248000c0034030045800d250104009049180421260b4a41d160022282001d00d104081c0c46814400407880307041c100f040c0002c51303402203a00f0100341d41108030b1900c10b00b0303540e54a4030400c940038001d00008040140c2864240302e1180c4404010f40001070089804114480b8600c0301c0404849144c500f00d80803c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 475709568 1250 475708318 475708357
    0x516152708071a010b030f0901050907060806150301090b0f0303031e060d0f0f020a09060636080708010f2a0e1302030a0606090b030a020c01060302040c030c080c 71
    0xd4550320290101d80c0c400c140d44402c40e035511021010003c400d0b00407040000c0048204542c03000401c02d02508001640300070000c50030884091520384039640103682c280001030303010440b2503c840581100030002280059225611110b1410280c640a40520b00c2184402b909460500d004000c0300c0c091030f0a01700c425524580d00e40c0d03512038150020100e0390702001208408012480c0700000c007a442d8410030500380070b075185204005202c0c2198100307120b85032900c1014011f039508401214031082e8140801d0000d18452090307040800f03080740e4008284074501200081480d00046c0c041c0507902500000c1c844551200d00002c00c0f80c82c141c11009030541c02d07000e0031400e9408104080360405903464242c00c441d40358400f10b4403030601c591480781c076198000f0070040c00e07000c03a12a520144c0301c946400c0c00180c0c075108c10708140b40005003d8203151580014901c801d4102507001078003c66014000744400303180c070301020f4020100c800fa10f001107800c81d000900000700c1d500c12682c0c50480f85801281c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 475710818 1250 475709568 475709573
    0x70f03050405100f0207021201020f18190305070801061a0d02180a0f0302120d0e011b12090e13120e010201110c010c0f02010e07050405040305161527 66
    0x140c10050400e0b1214010b050907035107100458020011021006000036907581c00705d1043c41450724400161940036403040c4100c01300400c1d403400700c4100456010021510204040c0000c095112011480c180020000000000c000340420f00c44203e801030300080180594407000540c0d10300c2c068500019000781000700c0da014074066809840f08894003030507107201c241c101010036801c5800d60040d41e8002004041001145000d040d091201e580030300c043d04190b44621005002d0850b078241b100e041c00036070782840c01c10014107003401e0384803600040e240780b401902000244c0740c2c200c680103022080182c0000501e0f074400c5010307108402035101042d410a81c0002c502280ca004030017040e94115501d07200c444160900500141004400f45400001c58103c601805458404540b02150559040000c0e00b504801c010440fa03007100d1080d140072481e640c0303615089902e842005800c1c0f9556400c0c0c1c1c0050300703202c10407243c41005203080d2010032542c801c0300341050815000411030300f18051300074040b200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 475712068 1250 475710818 475710821
    0x150702011e120f0501090b032d0307150c1d090f07090503030403150b090f010e040f0f110907140304060c0311041203120204030809040c1e020f0c0603070f03 69
    0x1c15640d14201000ca0110168a410f4808043c40250015126001400110080e1046d165212001c600134800c01c08085028412882c0d11145071108040c03424280807041e00c103204403a8407a80c000046c0f107a0101c456035030401000301c0c0c0c600e81f0009414940d0000c81c2041d0414283c00741d140100700b40c2e1143c5e1500d240c03906400380100000d04201a080f000500c0340c4040001d4406035102d6072442000000500c040401c0b50030640c2040d22131680305041c4260050000915410b403040d031400c441c40c0f6616401c02d48050071203650300030040f030b61140d500404d0000b01100222010f00450700450729890301a0215100d803204840d14451070000c00c00702d00000c19641c080d45010000c0e04012071140b490f0240586070b0f410030f51203141c407468031029460815070f00404203203448070b10070300840c14541142c032518a28011031b1207050045645401103078603a40150304038a40a02c0c02c4100350600744081c100203442d10307201150101e01c0d12074680041200d00d05070301a64070801060f501e0310f600105440d003c50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 475713318 1250 475712068 475712117
    0xa0b04061808040503061f140d0b04260426011104080d170124030f020d0204050102190503090114160828140f0f0705060615070201 58
    0x240e4595032001c854240040d96501040c00034020070842c0d40ba80d1a28043c9030030181d00030200880302081a0303400c411801014800c01c02d0701c20b0380c1540707800f5515072800b240718000780c001d010301020707030f0b0f07000704010002c05802c4c942284c0740001d41c50310410041c0492054078002c03800340308801d040500c042230029501c1c00480341003141100003c030722192440a44c01060707015810003003540d00000d200c0c03003405410108006c01d002618a002c1e4444d80b4100701c102ca4a000107a00540d0307401059500c0d01014800e4025040240340d000003155100c0303c4070003000c020340c4248240c60250181900e0b8101c0010a0039843c01c0558100000d0340c03800d0489801101c4000c020350f81c8d03408500090004004c41040ea240000006101c0c440c4240e0741c41c0101c01c022707141ca80c0d4205414000d40290452500d00e540200340642d01c116442901e0b0320b03002c40110880c5240524003599890400120300c502c18010001002c80c007030402070300e564000a0703090907944041c0c03040350006404121704900d00c2940f00c2c49075800b034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 475714568 1250 475713318 475713323
    0x14091c030603061e0b0901030213111201090b010813030807050d0e010509010225020603010b16050d03021e07030f030b03030c0109060504110d0b010b1c1b0212181c050609071410020a0b04 82
    0x5417425117133340550454620280c0010039040e5403042e2580055800c00032864100500e14101d456420841d039009000c511300038804400c008000c610044038003d960400d25519803880c0c0240708514103002603e00030b4111140403048600f640a01d4000f4803e00b500a189030382d009484c952640c0e0810507a0b5074070f5030125000e0005401011080c0c07020030000c0c000384440c0c282c1d0740d5002d0380e1640e10540800c1c4c2d144000b0700c0860002810010480002d07004992203001c025903060110307a41d000d002c0060b0640c0181d851152465003484c400004101c2e06512452250344901801034164403030303400380460312484400c020204c0520900600c940e001041c09440a1076444141140307503000c1031100300a075001c0d0342d2005a41c440c42c03c07000d158a0b8040c00380c038492800d407090710303400c000104104c11710000400411320b00618507a10b640c01480e4201410b040e210f50003404503212801c00b04603c6940720442d1003505011280910600018944100c1c9821640f0132940140a90340c0161221440c615010300304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 475715818 1250 475714568 475714601
    0x50901052a06040f0c05060306030c0f0f060c01020714071206050a0f0f020903120c07051c170c01060503031201151e030c0314091c030603061e0b0901030213 69
    0x100190207a0401030284100d1044460000c0c00300b00c2d2508a03c8400d045e0043c03407190318140200400d903240007401d000c05030380443c1c81c00c40304182a008030340141c0c0c184100035040080011030303980d0068150010702c00740d84500f000c0980040b5446807181c840449016804104040705914004554160041500103c0766a00001c410742402c0c0c1a4080b070700b11540881c070064021a050b040c1d8901401500460000c26a42600d807444905106440364180d01407035114004010301d031407070791000789181100c5c0303540a924101da40300c0084090a454100400740c8a036036080c10310109080c20f010050b0b0300e4408121114291603401d0000042c2d0f0310b140803800c0c0c020081100400c414888030f0040f003085007030060300c0000d254010408000c2c1a00c14031440c01c0c82003a801c10511034106400180c5140010340c0c0c0100c4814034050100880107003041d40d1001e054517040041a041003c22007140c00d01c3c0c0440120b0422940c014501800201d203000d201c040d41c00360311404149990f007156004029140408040b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 475717068 1250 475715818 475715887
    0x50319020c07090c080709030309090e0c3a0b0103030e01020a02190504140405030a21020414090612061f0807230d0503040510030b040e1c05090105 65
    0x41c0a140c19003650058045588401440710826080158190400741510b44002e61a0854034090540c144520070700c8200d5076101000e1152610034011401c0130007000740f028a002c0d01048101126030740c0c91040396440e10801d10114000713003500154140055000c00e021169030f28580782034a42c00e00e1041d0303541c10340c0100c040c164010780d00c42590022152904990a41060401052004032940691000d103003603104010f2001064000050ba42c44120390b01d8200840c2c085d018070928031003218127a080d409400801d0205134107000c04402003c42c04182e0b40a0325542e01c98081204102540e981e40e4183d4002030041903101c6648440400401655880080002d5550400500c0c10406500180a18424150301807004d01d03005d9400400d120102e4480402c0d01c1c0a44416489200c0d03442158410610315070a400d000d40a50007107201007200400800c104d000c0703039242585074000e13803095520381506001c401c03400d68040e809a0300c0d12041a52254101811000717041c00303225100300202000d004401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 475718318 1250 475717068 475717087
    0x3240a08030304240209010e0d022209050d1707030509030f0711090109021c052203020309010e0429060c010645021806040b1b01060605031902 63
    0x2540504c0c4a5031890305444101c0d0304000b541d00d000401804110300400410707a50383e9002c00804210207048540b054801420300c0040d1071845050ba621840700c20320300e05040200180d60100c0d680c6401201600c0300200e44100407611008002034084070240daa00103c1c001d40d02c40e90140d6840318814080328034103050741f40a4103068010090440f202d1440d50006802c0b030800030b02c44e038014401441e0560804075940a807501c50354039202c46184142d034500c001140c0c9840e540e44c480807204102078061440c241414000e40302d61140d40110f02042074240c0420442c1054404c0060020682100c500404103054074000880d603d554155441902880300d01021070085c0300300f10080007000c190488203400351002d9007004044020001d4051076401c0e810342e078840b00102d01c0d10b20038070403107006a960400c1054012207129803804560460000b08010507844020002008a0340301583c080c02c21805200c0f42c142070319003034060303c0000307a001d01c041485125202e4500c00c07244020400581400c003282c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 475719424 1106 475718318 475718323
    0xa02101b0e120d0f030609020d020a031a03030a030c2a0c09050c0417031c1d03030103050d0c080d230f0601081b0c03030f0103020405010b03240a08 65
    0x85101413001c030710a5110802403d611038045444084c40500d1200a4020064003804071b450440c00da080711074000690200580001d00840c80e2007131440044025240b00c403040d00c1400044014900c2e100301502c030f400c00c840e54034840d408080d44d175810040d03418800b03944441015841c01c824030028041d0041124182e5a4142401d408040e070360450500c0c41c0b244001d46400401c0d402002d1350010110341004690054007182000c00c8481d40fa0041d0301d91000b0b00c0020020342c001c0200f003030894013410032403d5a9000328903ca0a100d8243c02e620150360091601c5207040c021070607040020700c0e40048040d00305900401c01300b980c0c503088001034800f01001d031481c58010240d510b1620284014001c440000303a0003800d5176103d00f48150000701042c000e0204030301c950b00b000c002044500416007541c7c441c90f0300c011803c05004056000087c419801284980c010500f40c40204025104 = true := by decide +kernel

theorem cover : BRFrame.Cov 475539568 475719424 := by
  have h0 := BRFrame.cov_init 475539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 475539568 ≤ n) (h2 : n < 475719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
