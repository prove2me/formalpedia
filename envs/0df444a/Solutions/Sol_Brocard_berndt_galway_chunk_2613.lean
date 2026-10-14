-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2613
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:13:28.645763+00:00
-- url     : https://prove2.me/submissions/85b74d57-744b-48cf-8248-c926a22b688a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 469784172 ≤ n < 469964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 469785422 1250 469784172 469784201
    0x510062109061d0721331a0120120a030c0327020d0c0302030105010b0307081003050705010507060b0d050c0306160e040504051f0f06080601290f07060b0907050310030303 75
    0x81c0c4000c41002131200007441c1c0c1002100400c08076072061018112181ca0b207003100074003c1045140303956030300060400844002515905c0003600502e071802d0800c20718604002c404ad802158501c0c4c8a90503400ca440b200026643c01c1000c910452248804524182440341045035a00c41305c0016051024520241074090103a0710040d55880d80880c1c00c543c0264404900b01e40d011041c05021540050515005010107044400f01402d640710191242c407071f0b102d22030510000103008410002590054582c0c0500200711b0445203009050240d20344041c00c080a109028200001d2503404150860041c401d103c1d61b6074442c080c0c0c410003030000504021344140c44c04e104481c1941d060301c002c0c50000706807180d001400320305004016054010b0348c1554000142c07a4210200600c0750203c41c503114400050280d00b146d545a041e0030060b000d47c0f048662008005000060000901040d9080540882d40c01d4131058901d03901d0702e00840d00c901040c3e42c1940701400f4088100302281c0b10360080d042020444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 469786672 1250 469785422 469785443
    0x60b1009140f150a02030a0e090615090a05030a081b030408030d0c090e1504060605070213090201180e10090911040c020106260d030510062109061d0721 67
    0x42003201041c0c1c004c05148001a4400101c62441710303030000050003052003d941001031401c101d03002030f00e2441600024012070307202140c007034074503a0f6010400000b00400740c29240c001031141041703444d0790b00c203410000300900070710000c3d03512070303000812682242c2c1408040c508120f00e101206020300702c458050420000d00d40004581001c44820340740c001c0ea4660345800301c40d00000188400e42d0200c1e80401c0c10300105111110160703c50906603940740d5031075400007506d01500c0c0300503150b5070034a01d5070384041141c65078041380c05010f03900303840e010700010352005483c903564034060000d03220b1110008001d4480000b00440508082e0007140701c80f00340b4000483c60a1f00c130141d004101c905e01c00008540411b5243c504000c01e41070052052500c00751030180308500e4480c1e42021303c454544102d00803c940d0110142c00340550590320310000c0803000c400c2c0300040031070508034007401c40059001900004c1c03400d40e1111000000d0740c03600720760141d042444400042c0440e2981e08846440c10707180002030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 469787922 1250 469786672 469786699
    0x5010b190e090102371b0f05030403050a0302280f03121b0e0108100b09190b0304080912070e07140702061605060f0c07110d020d060b1009140f 63
    0x110204d0000382c1c045401c03042c8180f03040700210405500c0345942c5900b17000c00c02d061b901c601d0f1180c20302c20781c605402c1280035004600700e00d0200d144d446544d00142480c06902e030880300301940850340200c02490300006280030040140020105002c016004101040382060304000900480a0f09038041089000040440303030001300301c0c0e800a0458044001940740e10340120302e9a007000c42d0f960001f4a440c005810141042c080d8020780c41804041d902c1110403075107841080c00072820b54800740c03a03000b00391500e9090074039100081d9005407640340d00c110300c6048100c001500014a020840d03030100f00081041c5c03243e003003e484244501200d251184410440c03e80580c45140c010b14144401382602441a00d0074241075090a03c09080b01c1c0c00913032440184510b8496020507544801d030809503c4000d225000001000340405c0714000b034200d00668482414000940c2c400c10902c2026282c560891480e03480c21501000d441c00780c402c9141403820044071600300b0541c045084500034090302e00d00c2e0003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 469789172 1250 469787922 469787947
    0x3050d1407090b1606020708040b040906150e0306040b09070807080a051e030406050a03060302091510020d0c120e060409020301241704210c05010b190e090102 70
    0x300c1948015010644018800030552164044000b4100b0741440741c201455460401400003418202600c1030b82c010940405201d00003048500420080407d0b6580340e60f100000006861031f440750320703084428005600c0c4180c2c0500f540ca2a0444006d003c0c0507140d445c0e07580d9030f100d1100079240340c40702d20030000003003102e03e0104030741c80140c0138a0000300580e14003072a010b45005103c3c8080e002801b5411400b074489940081540c00380d54240c10a80d8440d52041000c400900742c41c0e0003c2e41c4000c03000203100001103a00e9030910b10503010b89500c4a0190a11400c1e80e40d406c202100c400064400048500480e08901c00503a07110740d20b10700441405101c400056068001d0f0f0400d044081d400001007244081c061550640b202e0074691110703011a4800001e03002407041001094818070030300002d4108040340e08040c04110181e42c051540080e003020080c50b0701d8a5080803900d070341c80e040003281c3c645000604864003001094140206509040e0b02640d000d0f07002c1c01841d4a0741d000d001a286110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 469790422 1250 469789172 469789181
    0x30e03091003020c0f0705060318100c0c060501090204050a09051306020c07081b150c0a06021801020105010f08120f0f0304061a01080108190201020c09090703031806051603050d 78
    0x1072541d030b0150300c0d41003800300c05041448140f42005c10354443c0c48200b01d59100d40e000d495025603519850707003401c0927145406084c0715103c0898016140f424080220040c0c00c1404140064001e102c1000725a03202c581c3c2c80c1c200d12940c0941c1da07200210400c10440320b001900300f1a07005039204003a0400c0a610b0303036008203070703004020403c9454120803c01c0c00001d90401000007120959045442d1105092020071001480c54160f8030640740c0015442805071030801403d052560300c010300f1540d400325201590401c051100185006500b8030000155042003621410151a038000c0608030004120106580b1640040100054181c091001c3e064503280f06020b18800c502520700820003144000700d100303c09640810307940c103100c221001802209800250f401c801d54400c1300c1060071014900040c1d00d003400418496034848424000c0288940c00454450f085a100b91244d81c4a8003080f0703250700c1555100d014030f00003d0803c0c040c0c00d000c03c01c0c041030300311554080c0c01d18505d040e41d04007016069a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 469791672 1250 469790422 469790449
    0x90b0711061b0c0a08030a020c100209100309060b3106081902190306060317070b061c06090c0806010b04120803061f03060e060d110f013606140a030e0309 68
    0x5640840d402d80580c09c2402070520f80030541c00c0440c42c10305c10400040070005819860b204140e0b4482c00c1800304101a030050310013047c001e040c0c11600102468120580403209060400415140d600b500f050f1a14020f107000c0c1c0c1c2c148000b520007030643da9001609503040038000c2e40d10a0641805440d04501e810442d00a11700600700454102c1c00c500b440c44000c410500302004141c004c100c49808280e40c0303940d050304140f045602003001500c01d12140d502d000c1240d03016010a107843c00c407a040001280103c000c0740c90b01419140c09a983e14027000036800f841c0b06000e0450481000c0c90005030740d0400456000384002c1481c040803030b5001c142e9140d900590507600103c0e66418040c84282401241582d02c603004503a009406a5184d940b031038aa544001c40350f004000005114500d81c1c09440514071960041703282485030f0b01e690409050070340c0c6550306110600106140800c03594440c80c0c600609581c3d4100d071a00c1c0c40360200382200104181c01c0038000500081c480711000303960701440c18402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 469792922 1250 469791672 469791691
    0x606042003010f060801121e05071d0103060507090302090106030216120c0b360a0503070b041104052701060504060f0e0a05060307030201140c01090b0711061b0c0a0803 74
    0x3682440c80c045c2c42d030030301a000f81d001d91a080d44039100240842e002200341d26109400006603050034a00945000d065800c200304505664178115100320700303811400c0c100c9004d1030090080792140384c400c0e540b48256001c069004440900140302940c000d030010b280068164229a5035009180c0781d1104031a21880b030a00020041d00358041804402104190080e143c40076641c806d003005d443d042c8824410b0381c1401d21202c00c0c007003d8a1903d005021050050303400005407651220749192000032450203c4040b00ca010042864030b0441c2858440c05100354034036006c1a62503682c2c60300c1c40c81f5030031048000b805199201c00c804100d9031600d015910041000c4136602000da414101d82a00c1c040009080310f501a141c1b4040107860768002504d0400c482e028200300e4030300080b0030385000e40b1784901801c0c2c7c0d031203600305034209080080d130071245407003280c80b5691030480d4441d03a0600354840e40b094440740401c80c20742500c1c00444429000a0860300b201504440401c250b9648034507840c1c104803841e942 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 469794172 1250 469792922 469792949
    0x12030608010b010e030304050d151a010206090d0e0d052d010e010b09040204090f050d0c11010302070b220507121b0347060f010f02060604200301 64
    0x1041109001d4585542c0c0300342000941400180042a0391f07000340d100d25889001c25100e210244245015241514421240180103146c5603003160024802640071050040c81140000f44004c4004070701d0340081700c003503030b1814007540c284020005019080ca1099969019490082c007402d2010410840e5038400c0480745c417840b094180240342114200c8501c07103080e904010b86a02540c1c1c806ca4007d40c801d0341107400003020459030601e20580986c48100911502c9080b18068849070400305005401e842030140780400200c04004405a000c0c0c85d10083c600d440881c023080440034441c084021100151901c2c4114030120b4540302c0c81c10350260f00075152072000450300424860315208021900003180a0002600e00c0c66481520b84d848080300d5020f29803101c900c440d94041107444580c03205403003000020100a00400940141c00d0641d80c60303108106c903044030b04895004040d0090000c0607a0082c141300d5841c0c00c04e00c800761050020b0a0000b40b01080502c00d07100b08080918080d00b0320382210304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 469795422 1250 469794172 469794179
    0x90b0a0804110a060206220c0602100f14240423011208040b0f131404150b04030609020402070204050f0901060f050603041e12030b031b0306040f030c120306 69
    0x40607100395402030040c401108140204d6400041c0305800039941044200d94003000c2c1105d401c10703401d58200419540f0800b00001e1030541c0041d050410426040381007210001003c40c82040b680d05040106406d05104009007120b0701400c0841c1c01240c0504a9411244900000404642c2905006920400c4900000e00903013a462039050140c4080da850f4406581191590000384c0902d1040080f18400000c3d04406820070109803a8601c4500400d800d0081d180c400100c4a4402c038042240640c0c174100c0002d0001c0308081098080b0b40c580300640c0d01d0141035440303000140010107001d030782113502000047c0c011303103682c403c00744140f80c0c1d0900c035042c1e0309109a12a082d03441b11350020400000040301442581d40d020100c0e60046d82c42841e0070104000700410700c0e02140448805405800810032001c0105d400d40c102c0e003410342e001c806580d0164042c0a441a07900c0320b048800303416900038400900010902d100580b4040e0103410b10341046105c5540e03900d41007000c10115800680c03102000c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 469796672 1250 469795422 469795433
    0x150612030306080a3807110616050307030c0504050d031e08090d26070509010e09010e180313060e040e0105070f050f12040f020f240a090b0a0804 64
    0x140a0b20801c00580101a102d0f01c3d00c0c201d00c5c0006551007031840d0840520714044c4c400142c9015075000010000700d030380c5000c0303401400301d056480341c2120034000d030400140c40d05008600c2c440380d440302da222a030441d1034001c000c0b001070168950140600c80100f20100d200d07511182c0980101c3d00c26901e0819045d5420441540c10220201070014170404000f0f04c29001e4002c110b0442c0402c862500041021f40c2516030a07420f00480e81d00a03034000e90205220280c0d92000003000560800c1c1c075030b1900d00482500340904600c0074170588006a40c0000403a42a400d40d900400c80030b0703800400c41c0e040a01c5607200501e45600390f404003000c129610100309540c1010301906142410b100001c110500d4500000303031440754a54040403c1010001e4032419a410000c00d50310280c583c0400d403d0145841d01c1c10594824480906a2080200c10401d128619084500c00308080101c2006282c43c0d030500420300b50b641080d2101c1c028403007481c001003032116000004e42000c101c00d96600c9540c5c01e160500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 469797922 1250 469796672 469796681
    0x40905011406270613110d06081c1e050424090f0b03041209081203090f03030603070b07060b1005071a090d0c0606080303181009030c0206071506120303 67
    0x10600e006100e00b1500342c1d0800340602c200d51003507081c1e45030380300c2143c040005c0c03004040c0c002c519075903088045292003410b06e00b0342c002002d5a104070b0413113003561940560b0030201c00c0c020002c0400500500c010300c2501c0f8025040710590001e50910b60f0400d919400100c040f01c0790301d001c09106000e484000e1214541c0056060001c254120682100b1420072003220403a01c00140094a138240070301c144e03a01544a0254840200003484c10359148072007401e500d82150307005640d40c9200e4403411440c030005203004801c8900030680207004010242c07422070781030225041404280c030300c0c0750b441003059100e49903600e408540b40001e030f5409941d0354035440d05500044200e410b0a1103502e40008015094100042280e1900e80b1400c000b1220189880c000015040d03035001050300d40004000d001100703010300321800003200d040042d9003034070486404090860b0100300000c0c0008480401040150510800070484c585c06805040708505a0001d1081078580687c0545100480c2045603018503505226 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 469799172 1250 469797922 469797949
    0x307081207030506101b03090503070807170304050a150507050d09180605060a030b0406180213120803010501031109030109080c0c0301051509130f050109060c05070c14040905011406 80
    0x1d034400628007035200200451a007406c1d10041003d090401070916004213545801170400400702e5202d00d448440b030365110311141c420303880d040c1c01d40f000010b8414804030a50381503500c060482825140703040e0551a801058002c02c50074450b0411160021a03014031100012000715201e8800107450000c5c3c0c4101204e50343c8000d54140e15100741840596203170f404481aa5000b4a404180e0009032800200100b510380d10040741d01e1610740d030710f200403042c50300640440b81111180f00a070a54943d601d0144808000300105031580400c014826580213501141e213904610f6005c5080c0140d050102c3d086880c0600c05680c1404049a80e002e01901085051091003040d00203101c5420320b441401164502105d40605c180c0340341c00004c2c01001c010003007030300b42c03074200c1078030f08a0901905080f4020000007031b05482d16410554030400b400d0203a81195052139100120381a002d00c3e24001210501104140d240d1080d2103503050008074009016141c040070034034a002e049400c1441c1080301d103100c00031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 469800422 1250 469799172 469799179
    0x415090b06131e02030601020102040b0705070f050a0f031502041502070e09030f16050c100806210a0b04031404091406030f070608060303041d06030607020f0309040902030307081207030506 83
    0x82e40b20b202e001c2c480d00003c00a11401d1070141c0c0f40d45030710340140d0180c00b607038210a14908002c21840203101001645000b102d0b03e28480704102a2a40280300c0005141d0240301c0d0103003185502000003c0d00c0134506a603804641100508188e114405a0b20030001c4003c82001640b1a55061140c0e030340100481d908003901c88019840e260322081c1e002c1c1540505030110f0b18604d290000078050101c04d101400c02c040c030050642411042c444e00242c0040e10594000f4010b07a84154440b24200040315500102d5000600400f96860503036148400400300420032410006a8a08079000c3d08c1160054809490040c40204a400b240c0c00c0400c945c104c001c185510070340c40618190b42204010030580161202c52134547c601d6078590300428914030855000d00700c0b07244210965010340100c9502280150411070648815232248070301280d8031101040c0c10102c5410401c10340f425464290300807055284060300b5241425440c1c0c54001c1d1035000040403011803c000000c004144e6450710402d680624200e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 469801672 1250 469800422 469800431
    0x10e160501090b0f0408010c0c030e040c0503040f0c1a09130515010c050309030304060f12050601090b0706060803030408090a080d170604090204110414040908030c030415090b0613 79
    0x400090041440f80f2840100300000203040000289136001c07240075000c80b000030b0042006584004000c0034a052059001401340c04c40381040c0e240c0749c01040009038983c0da410707085894548170a80300c040c42480803070301e904010100180b504c030b0440401c8602910203da0603164101c0a0078002e10400103815422980d240008020100c80c0c002c50070f0807a03500038642461010880c4c034010307265100d041e001136458880810009080d661021100302c048009646254080103c442c001e0191501a03800502003a00000c0c00e121105610010303021a42c003035003002c50742c1d030fa59183d2039003181d00655043e02c041d6030019158501b030402c0e0080500500d000001049211507a00008020304261010340940c0602040030032002d94a580210054a40091040019007001c60b004940c5134031074820402c0c6035881c0d000e820b100380340a01c502e0b5801e68000280d02d1455036480784403a119400184116595a0301403400a0a1040c5118076045584a46201d146508000e001c00c40f049103460310380020325090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 469802922 1250 469801672 469801679
    0xc0f04020708120c0c01060e0103060c020610030305180d0f1208070806090601111501030c09150302100c080c070306050a090f060504021f021b0a050105070f170c010e16 74
    0x40300c11500d8103031020710f000070301e40c0b5100440700d201d01c00c80c845440c866091820208000d00c003c12440c0c101c1e40724240810521560700c0702a40c40d20011181141e400c0c0c0e060104202185c0150010900080103c4058503040318817000500b01e4016000103444840b400b0340c07800f0801284000c107060044440c10030000d031f071504601c010400540281258040e21040d00414000e9004400036482d41d82c0f400240d17402d040d05044540c0ca04c400034401594582c42d16403000035048464460b1543e040101c4900900b400d007103800b40080c4042000c50841004070011098000c074401401070f0565038082006441c00078030b9410240259040070b881403050714500211310001800d481c0d400510300d0b621200206599499000080103900388400c181000300e001d1804503501c641c0400c81e200c20184000201d10420105011300030404050700525000c2141000703040c000c140107680b08880c4501c10b8190780d00d004a41c1144281981000032076040607910341c00f84141480051040f1010099048900d8500c0340c82e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 469804172 1250 469802922 469802933
    0x406090311030f030307110a0b25081e0921070c08160537030b100b04030b0a06081209030d110d050a140406020a0311070605031902070506090c0f040207 67
    0x102030461b506004a04070356072100c5c1e1041c050008015081302000da03107840c040408416482e5120031642480200e184100d4501d0301900301103025040d01030780c1d013521012084400100301ca0140c16144117209200001402c4042032040021040150200c640c0700e0090740b030100b0356441c2c0c0b504007082540052101341594400080e00800b00e0b00100d9081a450404074070003503c3c071051640400d84500c0c0840130180e104c0c0c046984204903481100d0054195540b81440ca07032007000781c02420341c800c1040100300082107500e03000540204245000003a40c643c0d0b045201d1400c0445000b9842c802004114940355140c1440744501ea20101c0c10203002441048007074039206e2861008040a01c0000300b030106442e486a1165524149191085503855440c1d94000c0d644240d45c040440001e400b80e181c01004042c0820351500b20380c60740c0c41d59801c0d81c40740350100105540e5500c0380c3c1c15096080c803c050104e041001440d0060003280c014101d515000b40500c480c44500045041c0201d004000c0000042c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 469805422 1250 469804172 469804177
    0x302150105100c020f0a0e01170f0307030f1e0306061205151003090f0b0412050711040504030e03160f0815012607060e0108070e090f04080c030406090311030f03 71
    0x2030b00c40c9001c60301500d0a2002424040d800c603076068224001c01d0001c110004100c01882c180d40d00d014590311886000c000080e900e02d008000407030389400900c1104002405000c2803010f8100e1800d024401b43e814a882c0c0c030101c28907031a03030030000382c68010401040d5001030ba1a47da0b404510024031003171916100c03501340c90003440c5000d8000c03501d2007820320701c0314801d43c8903490003603104c4404120003205013404d21510030161003d41d00304c0694a000120746004c2d00450b440c4030340c0121110780d00782186040000405000300240c050101d044285101a1b5050000c0d03002c6030013140c011000c403400c181c00340185641f50b400c441e885900034a5221038104c80b02a2060450311a8942074641c46410545606a091199a806820310907200b021540c66084031000108034400e0765100700e80e80c0c40c2c103012a61760451040c56a009030445000c90034074000f00c2c1c3c0c665032050064108a1800c0c145801d09441c6a001f40c0c0510005640d2000500401c507d64280b280c1c0400114014401c0180c01d400854903031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 469806672 1250 469805422 469805449
    0xb040506010512070e0d0c0905060f0d0620030403050d0c050306031e0111190206070518040e010908160209100308030c1803100c1b120521040f0302150105 68
    0x10400b090000340030605c6402042c0c03030b948018081c204941024034141c00400e0f070324041d00080c14100400070798103003000c00a82d101c02c00d00502170150f0707860302e4030307000003c00c07042030700000365480d41440102401c8070b480110b001c0c0d88a0b48c0ca40b5940e2140e1164842111303001d00c000d0041010030400e0061956000170039180c1c0199481c29008410844107403a4014510080030304031100f40440c69155070a840817103201d200a071502034850640d20440215910b1281f103249401505020a009055003404d070b0214890300f41d03540001038203005689403e1a10740002d16440250a00c10b00c0c02d4045003050f444840d004000b101103402050b007565103119440c0001030004540e1100418041d100000c1e41c036603210800805403d80d041440042a940050070380d030861400401c000b044104200c242443c0035070162a0001c4d074002c48948040021992a8001038490140303002e803020702114210b81c2d400c040e0045d8401e081c42e441000d040d01c0c004c0e0174401411200740d918465400100851349804045042c40c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 469807922 1250 469806672 469806697
    0xc05010f0921111f0b03060c03101710020f12010e06010f171812180f030c09040215091c050613030c120c05030d0e07080109080414060f1602040b0405060105 69
    0x40070b90b07403040c0384c0c010007160000c1c0d5450300c00c07071003409002c0000c10000c5000b04014404085030f2611445041c43c441e101a211000341d6001c1c2c41d5240040b01c00303034080c05814124031080b0745808803060f150046003000b80c00c86600d0150201c14001ca541e0441c1c0301c8004070a0604041e03103083d4103d10000b0b6950b00c000c005030b400c00407420460305883c02c1402100c0c4003e0b06400038030b4546441c00c08403c01c0340503081480e4018401410050341d02d250018001c820008010300d0307114150780d980d00340300d1300f07001240501040c0681444100065a180030109510b8001c4180c0300440c20101d0400d03c0ca8414040c107545014640003050001095010041c0e035002c1d50880d000805d00c44480404903212500d0100c09009800003061a0303894001c260040448c0310003030402c441c0317000e890f03918103822943c8142e0003c3c94040b007080104031419070f00889545412004017031030b062050034000021142e11070505c1c012080004052141180b41900c14401d9540c41a501000140f0340500084c001d445002d120141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 469809172 1250 469807922 469807963
    0xa210f1808070836040c0c0f111311031906050a0303080601050d0204080c010e100906080a0f0c050717090901060507020406081c1202030709060c05010f092111 70
    0xc1a80f1964002d00401004200450121441320f90408140b840d05a0f1180d0b0030039200c5003100d48196545540c49400560b034070601100380d5140000360984101031500b05107462100c2c03c0801d041c1c82104640c12400083d16520310344044194620004850710000051508078140455240c0503c0340d0203481e85800d00c14025140c00006a5003800b414200b46010381c00010089821035000c03404691011080e03d13036820890103041004100f03140d480c94140011006030701040842d20501d9059004411428001010351145082e10b0a9038094071545001c1940042d0300b8003001100000c400e14a00401089420009110000385e03a410042c031844040000104407282550f881da8441002401e0200c202c4183c941941c8403819010050031070b100c045450044044544c1003580200e80c85a540b07590b44440e0581080400d42e1a03401d24102507540b50740c2c0d1003070000d00041c0c03441801c488501800d41807261a100940022241648100041c10000d041030300c521380103c0014006016482d0300c003400e1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 469810422 1250 469809172 469809187
    0x12050a0e0616170f181809280f0317150a05040209180f16052a160801020301140d03090b030901090503160b1e010303050a210f18080708 60
    0x4001e030246010a00d40c1c0207000524988681c05c19940300c802c0319040c0c9507425450700f011841c0d45070100440300c81410b070b0032040b00e0740803880010300d0074888030510000c00301005045441c0d0485a80b14400106e0103c1d40400b626113504454a02c0c250340803d1702e568040d02c212100d400701d29031410070b21490703015940100314000aa41c2d1403813200140903c85402e4145841c185181c500100030035140c48000c40007850380d10301140e00c100200d8010b40034408045810b0200954003040d180d00c039000880b203e0140c0d01d4042060110540310b80002c0c800c1c0b000250301d9504195020040d4aa02e440d61485005003041c0000000d400007480421140b0a5118a8a81d618058110701418031a980249607000000d4504036200c1e8100c0300c07d03101130040003040d02543c7d821607101c5802c1241451070789190300040041000901c910b0050003803540c2890220450404008030380c820f8954030148091a176218040941038030160310804400b20015102001c544046072110521489004009080e4450009215 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 469811672 1250 469810422 469810463
    0x40509090613200d0321090206040e0c0c15070e010f0e0d0323030a0b04061d070c02090c0d0c03110403060b1f0809010506031507080a0912050a0e0616 66
    0x20f02070340d00181000c1e062410340d1400a054100d0b901c0b425144a6a00c203400510036101c1c0708030301a1a5003c1c0c101c0385400d04104801d01c080100810801d0290340401618004483c1408001c001e1040f06160901d637040803e0064030424054820b181040055450b025001e07500401c00c02c42d019054602819074a29418210f5800c0390003041088142c00c40c01010f0090900c0d40c3c000c41c41080718207010031000101e04204801d0f940b0383c0c400c3d0000c0c51111441010607139003180b04560042528140742100d90b042e940828010030003107a220041234000700325004642040d020b400010304552a08100c80020182c0760400c50103140000f5185a546410619280c5c8640c850000d0460354074118401c508001f41e4010500c4030102e446000320b50800c008520141400035800800c0d9007001d11402182d9600d000c116084640241a26421a2aa400e41010030b00b41040001d51540035a41e056a820415001030091140304103501d010703000030081450488020703140c90030740c5039206000391100117086c000c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 469812922 1250 469811672 469811723
    0x50108071413060201051b0403020616020901030c0303030516080c0d27020111010209010c0204050a1506020102190c080723160f0e07090905090f0a08040509090613 72
    0x16002084000b80c80c2c560303411281d06160440e08a0b50081c4842d039242402c01040c3c0c01507504880541206020520062406002800300120041d00c05403021020ba00000d0050300207074002c1c0d51142c8000c0050050591600840d5401102085183c03407a0b10750b860018102000146103842d8480b02081003500100170341c004400b444015080442c17171403482c2e0b41d8001003907000c601c01ca010824280509040c035078180291080060140c44501c5e5003241070f002e01010f04130040c0584659583c4211034411034a14100138405403c10740d00041c6c60b40310940c42030304214114a052414072141301e1150000489600407904001e6002c140010f001d1080c1015104420740c0130000c0c84030340100b0607000070780e1500c0034080084070030310039446000c1e66a400300300920100070fa58103400a4041303a401d0020f030280f504010f0300322440004031140c440100300000d0078200040421100c2c071400050400c10b515060001b6504000210050b06c0203041c04000c4503003075445000014050601003440340440030f0f80103075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 469814172 1250 469812922 469812947
    0x110114040c0902133606050a1703030c090d0b04050a020120060c16140d03270210090b07110306150607060525110114010f12060b0a03050d02060a0b0a05010807 70
    0x800461941780300c2c05020143c2918007810740510780300400054691710307040724528640031f40341c080c5285458848070042264040d03044070343c1082019603450009081c81848e20321960062020382195200d600c00142607000c0c20064900c000304c1d9440301d900507030b030228156411800c80c071003859403801d01003101000e508803808081c000341111488480200c5002c10b4148008600c3c0e0380401281e0a4a031500351005842c00203034164002c2c0100410060a16054a8241c26200c2c204180340e580e60f0426072009500030f8000f220b4429007445080310a080c00c1002d10340202c0007407980c1c851700a9140119495010b03400340600129141d07008034089080000d24002880c44282140103250840c803030107441000214201c0466601e08801001000004542d990680b00140700070740d49685002c04e0303070218190000066540039502d0840c00c2c00c90341c1da1546400218816805001e00d40031190010341400802440e0065044c281242010960741c0d401015058030780c00d0a003c1303907a880b040300c1250541450700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 469815422 1250 469814172 469814249
    0x13081b011d1e06210f220201140a0e13020c2a0616050c0d020a051002010f15031203021204060207030e0301090b160c0f03030c110114040c090213 64
    0x5074000b0390301c81042122080301d400204e492913030b11542c0ea90307101d0702070880e040c0d285100d568a00050410054001d4130b5542c1c014034155400c070b4101800c40c0901c7e80f14446000108100d07007180c0196082c0703111540300104d00c200c1c086007040c50501001c1c0d11503514840780c0340c05845101b025013401344080c80c4060000340c09802d041d21112140c451003441007044809452a1144a00380e080303514015060f01c0410754050002c2d406c840c5000103100c140c560a0221400b55501d1380080c00c143d050510510050741031640101038040e1460414000003924200c110f070800d401000b00b46e920058030384041d40c10031341c48500180e564583d0304080304c06000c2c041c1443e41c1075003040320503410f0000c418401805400f120700340480310300d88408151900e814281004101295102080340132034040d500c020000c26860600751810403040d03100c00d084a1501614900b400c12800902040c041c4800c0c6200140c600c0000441c50300b100602c040e40c0080d0b01d03103d030b09040c08007107001251010211703ea00c000c0104c00c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 469816672 1250 469815422 469815427
    0x60601141e04090513030f030507030b0411031b03012108070213060311101407050106050604090603060f0207200105210411010c0c12050313081b011d1e06 68
    0x240481c0e000d03441882610209820000890240c00040c00032603801585038a43e48000d050301c90040d40a0000201103030149955001c04032130548882c0990360120f0038070b108099992401d00c440c0f41c04a20781000c030b00848e40007440180003c550108464003641640c886058a5100c0d600d03042095201e105c10007034105104800240f0440019000315090f83e1050800000f814402009e0002c28203401e2040c0c8000b81c03088140c9008001200001c0150a000e8000400c24a840d000858025841a4015840c1c0c7d0354803002042802040d1080c00c4c2808a540350a5103084010b4982d069003448008181001410402d50025a030b030048085501120f00d0003580e040c04042c0e048038416080080f1410b03220905207000c40c1c20198400c6190810340e590005207000c10900b800e00303070200c0304040403003240c41c0d10041142d41003d94002c110480100200402000c040d00059280c032a01c007461400380d8144080013003c01340036941ca00070001c0b07908040e100c0200031289441642008445209800d4100c0d000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 469817922 1250 469816672 469816717
    0x100c031b05160816091e0b0301110a020f010b0301050f0106030c0207050a060504060305010519170c061308010e0a15020a121d07170a060518010c091a03010806060114 73
    0x1c07401345942441300c40d585034015036405500041d5600c5203140204011000b08201da00011a4000b0080420140c00025100d8124164200c03c0e849000c141e000342e8040d084840054a0900481c103ca0b030040e03000b4809400c0421845001d100180a1001070540b10310740c4081d19031003000510010200102007510859440901034240d902c41e01071040024203101c00460f440c140942010f40d40090043d0b0701d41054903080c0700d01345440d06079503800c000d402042c140f0040c90b5143e60241812074201481203102c507141002e020b0854840700041509030304070718503030804195000054035168012840c050381d15050003004880002d030b940130204205280501000c5400c0703e0040e201c1d40c1c0d50313184045039034154445120082007084010501e0f501d5000280c50000114940c00c000d07009800c1001c100c080400e0b00801c9400c1d1f40044505000203032142ca030030882d099030710b5480d84502d40f0141060385075505210380c180d2a80c0700140b5840c1809280c145140c0010406000c40381c040e1280050f4086078a003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 469819172 1250 469817922 469817939
    0x813120e04151202010f0207090923010c0c12140301121b030f060b040f0f0c0905011119081b0d0f0e06190318050309100c031b0516 58
    0x200315104034000c1c0d14101d9009000c88001c607850341582c0c000312109009541036401140d00250070343c1d0090031805030201c009450111030040905640c800c900d805480004c00001e0396401ca042602d02c00710f03a0504a401c0c03100e80d089010b403600903401840c90386c08802101029a0304c096204c80b66600d080000000080b05000d408038025034034881e120a201c02e100c14088038500510a000c06080348030110701520004286a01610340e050000c0c1c130104d6201160308098044911801d0b10021194071030301c8050400780c1c4240010041d20b0242803403500c0685400103070307903202d10001000f00140c0c075801c0c50780144200c86c002d481c140c0000c0808071b0b416030302c0649880d0f00d508030f01c244203000c0760703441b02da0190700350090007800d01c520000740105081145018224607400907071601c2c84245940c4030030080107180354000d648642409540119500c084180921800c2c00c505a068030420002c0344172038002aa0160350b01d1070501c5110b512241c2030019061241c01d040044001302c040b000e1207000001c0e02031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 469820422 1250 469819172 469819187
    0x4080f01021201150f05180607030509011101050c09220e0a0309060906050304030f0c12021b180c181f0806120c010f0507080307082a0a081312 63
    0xa241c14440c070143c0d036200030140c100d11010300e50f0000706000814416a0320300c0350000d46900d40d040740d81d452104083c0d00200d42c5036072128000ba000250001480d264550300a04500a500c03c000c00030002c0b447c0244c01401e482c000d0034900362045981e481455000035031440070300440d24010f0010840b00c100307418995a10003100300c04401040c0340030800120540180343c9041204c070661500d07031540c3d5aa50b0112120501ca00c01c40c02400781245044021440515000b00d6000302d540003050965502800355200344440701c00d440c07144250340c03c05c2d00e030100c0307141200384c10248241149881301c000c5001e0516820070b10f40c0c2c1c29048050002e00c1c007040810780001c603003660080e8851746d0190300c0d1041401903112040c2c40b42c55941c1e1001200c00c400b940300d0000d0740340c030f40894134003142485429542d03080689c1c82541c40078001060700d018028a60b0720554040f265040400b80c07141000251600701250380a90009034051003180d4000070380110b011240070f038600e03900c00b1500e000c1441d004070180481 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 469821672 1250 469820422 469820437
    0x702060d23010305100207021801061d120a062706021206060c0d1805040e0309030705120607080a0219030f0c0224040602070b010b030103060f090206180604080f0102 73
    0x1951030702010441e00ea690070071416241c108010f400b200041118400c060b600410b0300306c0e003080840664a400aa22600c000e0280401c1d5031113501528030100c00c031840306916026644201150344191811110000d11080b4180c1d2000d804145007201c0c0045010510030a81484400b10201b2020000c000c055801000e08500c006c03c18555600c4100c144140350042d0100885030342e01c41e840e484480d9004a414044a1104504200750151504045000c0d50f40102002529034808524192203103424044540a010140c94034205001042d030042d5a80c80c0181c500d5040c08070754400b00c0c0382d60807035804441c4c0640000d00004810701000000400612046a01065040c40d10b03c4e13403c210362010400c450542011280c00181c6c40810701e4405100002074030440703099900700201c400080403110624001d12030220ba0766141d614504000c82552a0780346041281450540000010303070720394040e65102000341c03040d61108041030300407504034400ca8100d00ca1510a021310190040f60540040498 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 469822922 1250 469821672 469821701
    0x8041520070b0709060e0f311b020604030302030c0415111605060403240501151112030a05070c050115030201091202030309102319230705030702060d 66
    0x1c5581d1580104c4644169024820008075030303950040840c0fa01000940e0b004100500803d101e602e04003040300b0f80c1d509030b00b01c0c41411003680600344a000c0729201c2d02214001c1000c889141c6c0c240c0c1100203440f8080104010b051640c040082009140444242c8018068019411410000441d8082d02d010035901e01070b4051701c81c2c2c501445455510800b00000c40d04050f103421b05060031a0b540101290480210480c3d24600303032880070500e025801464001d003141d0320720a880f841d102000410304206d91000341c0e015400305580d0b8200803428000c881d8001c130b03140000296504d48000031101441c00317160150856007800c0e004104035580042030000c6a1003600c8840c00c80e0750b40d1401c003a01080520300130394141c00910110b600390500f40c440c10307110360340351512410181c042da9245038802031140060b4420f50010134503000500150a0701c2203600b189050600c05882100d180c10481e665074250205c0030540030840c10f04100041081e101c01c140c1c0103007071948404480c0c2c1402c0041c018400100e40c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 469824172 1250 469822922 469822943
    0x706020c1905071206240303140903150c0d0c02010605012c010c0c1701020304060c02010e2805070905060103140103050d14090d0308040506060a060804152007 70
    0x1e044030403100300e900c00798404050020b06140400700102029485000d5aa0301d442c0d012100b800386d910461614101e422000242c3e80d00c1c03e44c1001480c040d111300348503412590800c250451581c0004440900e2413000718201100e40c4e80c5d031a040c1e84c1d170150440310802c103418038040311440c6806410400030f0b04c0d402c2c5e83e4410811000708a420005062000d030001c6029038030307804880c551040c13004400f198000d40c01c14541c5d95486500ba4440302e45400c40b4542d41c0d41c04424001046028020821043d0f1640f0080c46201c203062a0580c84a006080440082c0891201c91035003613903d00744c4142003500b1000b5a410550346644010181c9812680280040d25020001d659041043c60b4a07040c1d17900300004000e407004140c41901d82c4940c07000e590002c450b083c4103012007584c803440841075881c409c0d56080d0b120b041c6407030810714142c4c020b08501d02c40c450300c6070240315050b4000c641580c80750b04012020420a401c15024008141503500c5e560a10a00e00b03a102c54240c0c40303070060800d036128030b05540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 469825422 1250 469824172 469824193
    0x30608010c0f080912030a02090d0218060a05041109010c02130c031d060f0708100306020a0e0909030c0a0602070f0606031a01080c060d0c03060509180f0c150703140706020c 76
    0x1501e0f00f80b4174807201d10200041c00890700b02852a8040d0404040c00b41044400b00c2c0103400080b49440c1841102021140007810003895041c401001c00040034203039024045481c43d940b40c42e103540200e2210074100b012410329034041d9540c070559041410340c010410010241d440c10020090300c030941c00e4098652030220842901100024454450b00380b03014007500d00d03161604200e42ca2040a071000003101906980840455483d100601c0750b40300d50b0b100d41c03410384140307401d1241086d00200052031342d42044c07100c080e4213000401c828010382c1d0711200050380d4444c07900d0560310500303103d28058585443c10102000b040754503441002e0501400028501c181e030f07100101e40c0d555001e1200341d50020380620000c0b255070001c0d000b40003041264100812526110400310300002021103040300c0c030034000c59058045103424481c104881541501400c1844800c4005c9105422200644041e0380d2000642030705051240100d4003c190304298100c1c2d0345d180509060000c1d4200da1030740007150152108071b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 469826672 1250 469825422 469825441
    0x90a03110a0209072105070801060e12060703090206040b0a092402071206090b0702030316030204080a0308061c030210060e04022413091d1b10030608010c0f08 70
    0x15021a0b078000e004284680d90401c0c1281c0501055480b50a020b00224610300e9484581c040d1070300c158a195954a41c543c504140204106400a2140d006008246004880c50408202c2c00c0c0c2c040300381c1c10042003155542c0b000c01d01c2ca2250354040c10004001141e010303c6150b102d1440000c40300c40040e10a0340400451460385244240003040015a124030420000c00c10070100e1546401d01444001440a0147d103510800d090116003c1d40160000800c005004510b825014855900e80c6003c43c1064102180d2a9075500280c9010742400308602c0080c21565449594a0342801e10f035584143c4050b8a00e8041e540b0400c038040710f401d1508240001c80d0075a8400340291190750000c0141ca00d4451040d44845000d082e202c0364064028100440e055500c00c003440703c0028450b12100044140e0070090b4510540c040b0404c280c00c2e40c01003440d4035603200072090b41301c4402c1030488420809080c0c1d00c100307034000e00c0700d54865070b12035091a82402c6002c2c0c004e0f01004024403280c03034082c0555618040b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 469827922 1250 469826672 469826683
    0x5061c0c033804030c080d0b0108010b0403080f0c1905060f0f060f12010b030f060103020a0e070824180a060504110f03090c120a1401020a0507021c020405090a0311 72
    0x90b159070080c80004000d02c900200240d50820f010b42055882100e0545650449a20a032107040d0743c01c0d00c56840c004156444025240188640d01c442c074102400c41c1d0301d5204c144914104a000d100010414000300041401803199030802c03400d0521001d600303480e021340c0304c080454110303039094641400030701c0c210b80003c203051180000515140c0000e80c940200301180345809481709a5640c0e9480b04120ce443c02c112102000ba04000104a50343c9988100800c2e400c03103811104004004006000410b500310812982110320911038507045a0560451020440792806159008401000d2907000ea54880034040c000c030242d02051000d251564140800e031440b00d4901e60038500104030b00040b56400c600a503420003071203415111008030704000200d4103011402c4604440e0882e04817a420000d10500368066804104020340c00d0080e554030107449805220f0010f40070f61403d14051000400a00640c2031040c2d008208002d103040c0104c0890342e940200c841200800c064140080c04108005072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 469829172 1250 469827922 469827983
    0x80d03110909070c030905060406110111120c030705070b0f040201110a120e040e1c18050906090415050403051c0216060b0303070803130b010b0901080a05061c0c03 72
    0xa035000e0f140c0c0c180841d60f9190341641601009200036012560303a03601c00040c0001e183c15606c7c210780c10080f0a00a003120000145000c8000342000680307482c0c80c10020440d07000041c22000c60302c0780e0300c400041e5140e104140009001e6000c0004214242815050f014081d07030007070ba6200c099200c42d003803650b699101040040d180c91301c844424420741b0b201d80803942e5072a402a002040c0350007032281d854a8075600c01d4081541e024590444080c81d90306c103000314000d522640203580007514000101d0240070005d44070b24000c4030810000303001c1c041e0000303842c484081418020050b5160a0800030600e4001640c15009589054048003000d4414000d640c0249050100702c017010300d0035503580d40140307482e001d00e50301030205014290118100002561194004050390700701d809491034066520300050b0000303154140b09110118499a120008a5000d900740ca40052641c03101d000090b061294076880101c512080c0c181001000044030480c0f0443e0722075210078070487c502d03a120740d1201c5403c94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 469830422 1250 469829172 469829179
    0xe01020d021002030a0b0d060f150e010b13080f073204021b03041206050601090612240605130e060319020a030c0b031005030105090709110f0301080d031109 69
    0x118070b0045205107070300460300141c50200000310600000c0110750b066045000540300290345080007500364610340a01d103500303055040d0315502d06081c0038120314198010b0149070014000410454101d118810240c4080c1010700111040e40c0075040b407840e40c8103201c3c014500304582e1140740300b10340702203010341d12040d220300b2a0944849141130103000081d01b11100709800b6912600b20740aa9010500060010b441900d141e160a200d050400109940340a01818100461070f0010810035500000c001071081c00c0d41070111304644141d90440a18001044c5c8490107488030400040450700440104030600040030a000d0701d65035032092820000040302c0c03403500354005030f02055410800b0388111041c1d6100400e0407420640360b4403140c10b40502a0400b91241500009010301c0520703040d01e43c00103100440c0288801d140c080031040d1240c6251207114481515506030f401802e002d0700035600c41c9103e82c0d1020751650f0b0348401c1140e603540600382a2000c249880c04e8403a1104840d000ca800c6c418025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 469831672 1250 469830422 469830433
    0x2090f0103150b031003081201031a060a090207020f03030a030209040e010603030f08090712080a0206130c150203120c1b0303060d080306120d080105010e06120c0708070b04050d0e01020d02 83
    0x2a01190f650b20042224128002c110008000500402c0250078107403000b200c810034560452600640f201c4c1e110020640b041030540c2040400c2d5186000c0200b551003800b00540c454a192011032007503100c84000b66030500000c070b1690780307242d40740e030141c54000b40446050000c0f6150460460896016000c05800203441001e46004240a600002e401043c07e07402c83e02034a564001a410008000e001207800c0c01000a004c08602c0d4108030040c0c00240006201450350f5043d0b40e43d0141030070074440e407000c0c000b9540b115284d150081c4180c4610341e025080f90030b00d80c031b442080d03075209510540004c000100006c29901a82100105a910440d8090960900e003105600c40318010342008140344d0307004801e40c00c00e6240401c01d0080d039030f0401c2ca07134440034a10350400d40050018035203c503441d4090341c02880144803ca586440094021100100c45542c54a070780c2030907081442503903405884400c426060004000c80000c0c140c031a0807071030703440003c002145401241c880120000640046c2e115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 469832922 1250 469831672 469831679
    0x14011e0b0708090607030c060e07091b090603111312210203030a0902040e1c2a060c021e0f0c06070201020309010305090c030f0c030601060c0b131506080102090f010315 74
    0x104c001000c1850107800d07c001160070982d1203a09440d10440c03d48080d8000c3c83d42008100780b02e00410004190106030b4051501440900908000c2688140001c068850491001840c420021a60010f0b40d6100c42810580c40398440021074805841c11100b540c20b0314a4003203044032100c11841d00c0941da5029500c1c54850550302d82c080c000b80001a6406950340d00410180d507c1013010030380e40d00707101030aa00010743c2c0120107080c10107100e89820f81c444d00445061581c0700400d00c146481507120700c001418010101d000c07031416507204148000c20b4050000001902c4d000140c0701e81038650107003102c3c61110482d09005090003400c134000e02603801030007075407010740c002e4106035030002d144000c8502d0489188002403031315883d46944101e0b9000807084600a0606006450241401d030401d00503001711541c0c2e0030f040040042a41c83d016503416104810400301440781d40d0010b0b403040040c45415240ca104034000e40c03140c3c0c0020301c1045031050703040b0701d94001d029104c0c1c41c84142d456080c2040c907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 469834172 1250 469832922 469832929
    0x31202031207030b1f080405010c09081e1204030309092f030a42030302070312030603050d0e040513050601060507050f060106030617010207200414011e0b070809 71
    0x14110300580c2d000c400200702002c80a00c0d05ca4142c9600190b40d65200d1030704140c142a42100d01d1810540300704400c1c01d0040c0b004080016010700744101d08d082c046400140c52200c24140440b20b000f8404038070300041c1c000285584a01c1e0b00041c0d414030800ac103c2c165605200c445240c586c2992105001c01c2102468403116000340616400f84d40480c02003455495075110030a40302c4590900c041d41c1544007462800031040d00b0940c211003130322100f124038007819900c01951700c034138900c0014084425100075169952003a00000015503004040b0f6100f03038103680020700382980c0d0009003401149014001503c480c8403a0707600e021660490080c040c070b40d080107070407646a402000280c581c5c3c813a041e1401401c030400c04c049402880c007540c0c0050400d090007041c4081465102d40c0c0d142c00c0e80148080c60200e0321007140800c00044040a60b08c4058260010902800140c10368800e00440e1500000d50050081d012a60000c1d0301e0301880c001c03540350190100c083c010910701038448901480003414905 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 469835422 1250 469834172 469834181
    0x306090601050a0e0405010f150801083c100c0f0c030e010507020d080432091e04050c090610020a021003090210030204060e0607031b020406090f0603120203120703 72
    0xa80c44d103841001125120045001c3c2d44003039015000c03500190782c00308440f42100c0b070002c440c541c09241040c00e035450111529900e400c00011032075029991a03100d05c0c02c40014440304401007404401010781400101d219465805d01900c05403a0b900b4807400040315031040c41440c802c031901d5160400419107603101150301c000310f030101905101c020003020004d070b0350341c54001032102d100301d2103180da40342448c2c00d80725424148006030528140040070108110040f403a0000051026503001c00c040e502c04000c40c00d44c0c4d03086e440d0501d00342c0c060402c1c441030010210300142950801d854100e410740310304080c004141d00400d80c50740183c00003030811005140c14141080701d0b00303403840c000c0b50059080e000104c0a8210304285000300368005000c00007940c0090465408013400c6032050b040c01c2440d200074260088605c0075060901040a0404c21980c0c0e030b0388907102800c3c00807001c00100d00100401d800500c06408140c4940c4d100010f9001818800411030b0610544c0407080c40b022b4541480c10f90250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 469836672 1250 469835422 469835437
    0xd0323060603270118120201060b0414041e05071701150810030c06021b0402031302010309060f050a1e0614010c03050702060d02031503010e031b010e0a2105030609060105 75
    0x4031000310b4510b640c0007090144160341c5e24003402a22021000d4603041d54500c2c600d0000f1419039040000411015410000307950444294000e0f2410203404d40e00054000c01840308140c00090801118000f1484203034000e51180c40a500c0340e007828403a5814000362004244944442002100c89500c1602c0c41281407641003462551030f10011526079031000b03a801d55030b400500c010380c01200d500c000c4d1110581e000c50001d80a40d000c5246040008074030003595540d602c040c2c1455200c800f40c0d01040016405040c010480b000704004c2030a11100c190041c00340290512406400d20b1640d5410a2107480743c40221741441000ca80f040450000540301c5407c00c20b401e6062000521400c40981c81c1c0c03000824071110142c0b4010392324a090f0700028440a80c41020324013982c509400c0001b140000402c5410841c032404855480f416501e40f842e024000c0d203140048103001f4440000c0400c0600607030b00c2e0003111045815150441c0c4518200d849000444049602c0768940c1c0c082000d55000c3ca0003003e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 469837922 1250 469836672 469836721
    0xb09150102160b0c100e070306090503070c03060c030b0315010302091003060203010920070308071404080f010c08090615060f0d0c0903021005090a0509180d0323060603 74
    0x502035052103a03601002d01e0340c0700004142c00000e8055110314244180110b400079600200704460010400c550b855080340030003043c00340d5426104003448030801c02d40720004ea0000d4080941903da141140140c01c00180b2080460f00704010115280340c04284007189520307500c0341c100142e203503808001c850000640040c03110302d00c017070700403010540ca800254049d02c0f01a0b00454040010410b40034130720600641e80141c4001440088000b070790121105410034010f00c0d0203100d581d04020541050b102d2540426090b105556040350541c40640000002e9005600c4100c80c3c2d9036406401910b42000b2242c100c0b070965108542d50581c0f51078005080001d04100006081504205981e400c55421801c1400821766000081046140154090302d80ea00310b85022030030610660003081c82d0031100c0c0510b070301c1600344c280024180e003035586e4000421403038542141d520740d0004070007034000c040508090802460403955000c0c85001e000d803590240340040c24482c51583c854101c0d02c0d1840303940210310036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 469839172 1250 469837922 469837933
    0x604182603071710270209100c0b0f010b0f0f13090b13020a120b04180305041a0304020a0b07060b100f030e07060207170f010207031d040b09150102 65
    0x5100655501a40c0301d1900c40d03c4a40e82502000703a140a1400001e1030990b031296082030078024007200041d24210201e01d00042480c1d404401c2c41507001e0300841203965000001d01e050720882903032112480c014a806030b0840c45c247d868104040b00c03600c02c00d004e504131600e0b04000d0604031041032030040098440d41028642049280a405d07910340209070302c00c1691a485010304da00034605020600d2140d9030f000001c5141024983d8040d10503001e481e00e44010640c1c1d40049040c0d6222600003001e403461100f1405040803030b0b450064180e07003141c091808144000301c11401419030030300071240a140c0091003908010710382020490302e94066802122801c0e1504101c00007502c600c50024660089602d03044091044600000c003155118418001c50750300c041d4041200d04e0700030134050b083c2c480228112451224100200e4a8803900050908141d0310001d80401403540c01652070000c00800503503000b04900e114104420380c2c0c010070316258084030b040080b420380d14180309080c01c0c24006005545 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 469840422 1250 469839172 469839233
    0x10230109060f05040e010b0a020609010504030801170f0601031a0109060506030112020607051f1431120903020f01080603062d01090f0c0c1119210506060418 69
    0x2945d100a0348490b081540c04500c4144041e01404580e42c0208444020011850152002001c0d168103204d40070f40e012000714041414107003801000d1034a28450102d400350b594901e08003101080012030420304c1c1c10648000304400c070503405950700300c900091255013164201110003815035401142240d10407000c11494000a605001110b003801c9295000c0003004a01e0800c00c003a201c8510b1b402c82000e1841d000c01c034980081000030781c0d5201c3c410307100040c02c0186218004000b160150701521403001410201101e95004c0848020f0301e100745c481d0300d07038000f24100641d5016002e0ba0201e5050b0400380004051010b54a6065416089080301d28000061702c80441e02c3c84900703800c0b00b201e1a0311000c550040400b6805401c071a92207a19000044e1800b036218207040c8441e0f100c511340305812138400e600703080b00680400c5000c4d007011403104019a6421080e00500021450216818024480010b05519207440740c20307250a1000d0340e21800507807580e510580740700c461003840c82c5460440e4008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 469841672 1250 469840422 469840439
    0x1912110601090c030f1b0315321c0312020406080a05070504050411030a11030106050a030f0219020f06010801020c0c0105130e1f0906030f032610230109060f0504 71
    0x7041038110750158120070001c086c00400b6110240c03580d01111052080c2002044019007542c80002c0386c0c01c080000c0d83c1c0c3c5c01c00c40072545072000b04a0507800000080001da40c41d0840030081c40b1030b0710985403801f080d42c0b480707101801c0c0d004510034500891103440024030000c41c241c0129078840d04500e04245001d1f01d41c00060211001800401c2d048000030042120a005ca0700c6030300600d05244d00c14500310b40c50100700600a01c181030342d080805441d15000d015101c841e4040d161503000f942c44402401d04103102c001c0d0b840b030030494502454070408000040301d81c0d0610860b00c001500c90080c1269422100040d01d60354042280210019015440000c1c0c0328088a02c1c40d02507480c50000b04000700c0340701c02e04605100c80783c002100040c41c104041000855101c2405e00b5582d140c100580800d05048c00e100151251003400014078002d14100f261013014820903105861111001030f8220001c082041900d0103480c6669010501c00c000511049010303400980b0b8880840c5000c0c0d10709520303014207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 469842922 1250 469841672 469841681
    0x604111c05120409050606040506091009151d0910050d0f05010c05070c060801060f0c0206070b01091514060301120c0b0f0403060507031a1002030c1912110601090c030f 74
    0x402c10042c0414207000c1140c990103501d4010b4821902d0700d0615040c41c001a071030384902600b1510039041010b0b008820303030003078005d8801000c4841c001c403126204680e003d801c0f607080582140400000d035003c40e0252409503207040c02603203151003880c80d141c1841c007480b050041020b016141214800030020010707209008070035000d01d1a5841c651038001c0ca15080b02d2104641e000b0740c00f4800c083c070061000540c0102c03071016980c1c0510300100071010030700105c0c0c02c620841e00b0140004250742d001084850094100c2c00500740204221035a46646400008480324030b40c2089078004403c00040082071001d0190f0a401801140c018441c15a1500d426556900c100d60780681c50f800442c04000f84507091080d150b000316642418000030381b00d44800c0101c1c1d10805140c41c403c07d521450b000d1624401c10680c4c040301003100c2225216504804050029200f10808854a00c8202940f1440c14451071080c0304500c8c44000600086c0d0a040550016107080c0461101b019030b034080341d41510b52540203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 469844172 1250 469842922 469842943
    0x30304090b0a0617072a06140a0207020603040b0711190606060503090a3309050d02070b0318010b100809060702010614060c030d0912030e0604111c05 66
    0x9075240c020000c0c041c50a00c1c99208805000c00c2007402d42d01a010110b016038400c04d0f514080aa145013500d10b03076800141402420f40212184004500300041580031190b01e5110080d895580c3e510700c0340c10000d0b44140d240081d0071400501c0420001102d280382d458001980e03042200c1001032004015180514035181d5000b800d1080c031594045c000c492045001034145441c0c02c1c0d01c0d500d0300300045076803007405c040b000745029400c0000d11015000c60f4124603151400d010a11170452a088a400260140c03400c140ea041c000c0000c2540ba490000610700700300e80c20001c40742d045680c1e81021809408042c03061100c255211440070104bd03a540c119011070441c127890344c14881c103209028a1400000400100030b5a14144040c0540da82c410701035215100b007103a031a41d5034007118000f0741c03c50240e4000b4110705030415484804000c08280588400c546c9690100301042c07480d080c03070340e03a48070070358026090701c2c4c51101c480c0c618244a0405a040004540301f215454004c0e0b864a180080a60 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 469845422 1250 469844172 469844189
    0x9030221060f0103170306101110020d020408010f020405010804080f160b070206070c05030409021305040501030f15090f06020702270603012f09030a05102711060a030b030304 77
    0x4010b0003045170305140000340103405200d29082d0314104001c100210090441c2d0b00a00c5410206190003040030050010b040046000030f545a2100c040404083d401c05d0240c60700c2c55082030b26207030031105148291000c40300c3c1651341c814136440d140c448900c2940070304280840001d0800c0183d65071003c00c0d5910289900c68010605107103054400241004405412001000144c0744034001094000041e42c0c26101d42540040e030b51000581d100900864650009401c181044c00010501c140c04070000032041c010107041b4410810707407480030b04455090000525016120504101042069010f4020980f014000c4e10741c03030200706000c5040c0c41509001451101c2c2c010104016403c00780992110b0012880401c0344203507058201400203040e100605060312404940e11009075002c00c4500c280c03a8004060b075444410005070600900041e10702d194402d80304485099100e000d07070303206082581d000b070322000c01026048108407140d88490034800030140c88030340c0a2104c0e03070140002e100030702846 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 469846672 1250 469845422 469845451
    0x301c0309081806120114130219050c010b03070b0304051612030309080f03130204061d06100207030f0501091704150c05240411010f050403171314040b040c0903022106 73
    0x1f0041d0030300b5640c20384102d040c0184030034000140c001c40f10160313486183c10480e07120080784a800b801020090038440d410302c160714001503c00e201400550085000341d0550324110351a41c40048001414400d41c900d210074005c1c0e00003c03d10a03130145a0262003000c041d86412500821941740382c0064400c0381d08081402e03941000c500e0710303100c0c0000900c0181c010501d019001348108403800e0b00102079078090740781d801a80040074424080c0c1d4002d15803140300c05100d4030342424060300034009200c0844800f9141d840211101141006441c1110b4580d82602214082c0550031569600d500c103086030244540965000341c0107c4103402e030b8041c01000030010755841d01c0d0504603600f003030003038030b540c14080201c861000240e80310341100c0941e6000070415110b120000c0d140c580520422038141440e035050700c404140e0700d0b01400500c12080c4100d0b024024841c02e0801c0100b19415130b1541e40109445103c00c000608040e4409144901c08060f81019408056210b60800c10111001050580103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 469847922 1250 469846672 469846709
    0x100608010c020f0f071802090405040803040605061c150b100f090e040b010509070e060f1b06060102031c1112100605040311301c03090818061201 64
    0x100f040103000310a034401044100714505102d500c54045000390707124503020b42c91491500509404a41d114080a4020031880c6014100000f0503001550111222030410000c2091840c00400d010b03048004100143e6a10005948041203a00600700100e1520388511114040e0342d0b82d00480c178224249511444a42800c191009240324081e40119000c5061034003880007040c413080310513043d101c0907148440c883d01c4000055a5030000d134140d15a02c0140003070301c54018070031080a4030503642802400507007284104291911040c08030b80b041d005a10901ca91107201c08902c40b81c010300a4810000100d6124400e10040359501000001441d002503505210b1110020201d010042900740751150401e41541e03510326058110001c010b10030288000e00880f50180482a0b0341003148440e001603115403142a01d94550f045410503001d03138180c0318440031440703000b800341c50b0902d40d211001928014180100c0100a19500d02c01c680209042c07202803242031840d10f41328044c000202e00303080152074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 469849172 1250 469847922 469847927
    0xb0313022107080111040b0906130b1305010203031e07170a20270f180103050606041406190503070602060a0c09031a2203030b030f0c0102120c100608010c 68
    0x6299004045981c0f5221003015041c0c140c10580303041c1c44404030301d19503440350300000030b5a501038803944086101d644ac00000d110f11f005401001141030051003040b0107030340c0720016a00d81c00222840019103944003111a00c0c03204084086510100c1400c10301162100c60083c929822811562a0242d940c0d80e600c15446203030707107414100075680ba18160303403070501d807410701c030b0301044c01040b0504400d0122009103007280c1e9428800f409055000c0d09105014140035001e82c9094000e00c0207407614000c00c8080307034050600d40142e09681007044845c01d010745885003030042d0a1148852440a03125071b40700816103a4060100e24010b080a5000709a107040c041103000841e12280d070240b00b440740c1310700108006250301120459510100d140d4200d25550013100e2800b030b10407800c8024042200015032402c054240c2d00900e0001e10640840d8102c018100b00e03642d40384046502640581c1c403101c0042100e12100c0c000744100c22039907090b64030304141d160090080e545642c02c00c00580e511034280992841c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 469850422 1250 469849172 469849183
    0x31d01090b10050f1003020304030201021219060e060a120512030f0403030507090e04031b06110d06050f240702131406030106150f03020c07060801060908030309070b03130221 77
    0xf80440d51003449940c1d550009032000030500900d402c5c5034002c40040e060600030b605071403404101071186203991400d14001002810304034000d020305407a01801044400b44402301521558001d05180002c03420041c0d00c5800c000a5003080b82e080c030801c0e22100480d0048030143d401500c0c3d08070001da660520f882c019090b40c0004110108220301042d0801171aa004040a0b41040c0c05013801d0010000020101160440d44000508070030b0800201009840c2404010300c0050102e00040040c40e03202d0007006030310086030305000c0d4002e03c0310714450700903012040e07204000c1d19044081e40c603214159002c00e841085038410081c801c1d50307134440c0c0000032904409003644100100c0c0200302041c10030210b0b40071a159005c80c002000162060080503070301076412904040e0140d02101e514aa440800a006901c240182000514003010008207003c000082d2401001d9940141c440c550400c950b4612036040144145400ca410b0505940540c03070b420070b180c000c4039070300000220810310700f00300074a0407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 469851672 1250 469850422 469850429
    0xe0120040e010801180605070314010e010f12021e030a141b180a0b1c0c08120c030a0503130204090302012412080306151902010c0e030d031d01090b10 66
    0x1e0341008121440c400d07010704120030851b4410030000f00d640340d42310204e00900e608441c049098011070001718800904441d06412a111646508121034803030048244401e0711100c02904000e05286128400790441040820030b03401800315500d000c0f2903260300b007030115110594cd081e5005407442480704074107000850003503003054445140ca0080061144081c440003040c8860566580c2c90086641d5164800300c102d5070003403844e01d2501055030506050307080303451013111401e2044000c082100070700719003607560141d5500051403c0c00340c0d00c8030a54684e80000c2941071a210721949440060f174442c800e482070180240e00005119207a60000f460080e142180441c00d511214000c0111001601305603c1c02c030f0303000095948a8850f0390104285a14034003203100345160220f40010740407034021040d0300000d8180c0c028850103034007280690b03012056642254158020880c020f1700a406500081d0000321440c400104406200c0600d078211154103074219142190002840740d83c0b412500d13300c018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 469852922 1250 469851672 469851689
    0x100203032403100c023a030216060b0306010602060c0a0e0102070f150311040f0902070203030d0e210310090203100b0a05070218090a03110c04091110140a030e0120040e01 75
    0x1c2185018213060481c200f121049456212001c507a000d4907c03940594455400002e4100e054051528050001e09401d00b0014041d200300303000090281d1000548a0292164094451908648520460380f60a484030310030306500c584140001c443c108050303610001c00c51919031660411010b0002406d49008c0d00a2100c00c0c4d2040c0400d00000300c030741200e48202c8400c40d800594a90062001c68114040d4141d8502c1142c9450003500c8020800300c0c0c010750440004031941000c601011510303120740000d035031f1200e11210040d03003440203203a141c0c0116000000c008a81101c665a800044075952009044038002400440c02c0421414006600d2218011a40c088101480c10441081e603032000e08002a04200c013189030031400480500074480701c0000508184401700351400d1824118038482011070042c0c40120006c0348042c450054260350340c801c9250320f441c04522540407005800b2001d0070420655807801d403451040f0b0004006105103007003d290340e46591a241740c0119819059210980 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 469854172 1250 469852922 469852963
    0x204030501141005040c0306090e03030417070b04030f0216180b0a030209040204020a0908160617060a05190803030a050901240902030c0408010905010b0f100203032403100c02 77
    0xc00700000386070b8050b140c0c05d481c00180c1c1c24003401c1c114007500b1130f941314104052900c1c94442c3c07000800f0000b0762046010340c0b9201d00c00c5210b620068521b119407240946494036074008200002d01c1054040f41d0049144110752104c50030950508500b142d0340d0020b030364020404100c1c58040018055914022000c81d88e00c610646960040741c1132410090009202d254000b562842050081c0000d0019200420855080e070070b15200f00000240c69000310b50104580880c1c003011440303200c00e003512131003028000c8400c0342d00e46820300041505d00349a003108440e00f01800300b207600082010f076100b070151480c007240d02d0a00c0c400c25421141c01d035054180309c940c0580d0303008104202c2c540341001c882d800800142e5a50711070264080c24000c40d00840401d5081041c000c0a008054119a00910045031074004141410b000c210350000404107940168000740002100c015004074110030701302201c3c0070142d14a482600084c10040c00c4001c415031503a0707450503100800d60410260b0400c83c000c40c0e0011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 469855422 1250 469854172 469854181
    0x10506011b06020903030f040f0602010506040e1506061c0605090906070915021606020102070209060906010905010806030c0a0303020d180b03060f040905060c0d0b0a0b120a090203060703020403050114 88
    0x180c56450380c0c80505031640025141000e85c60810440b00410544090316071a01e845040001c4860003a126610056003031402055880c5030a124402817209460001c211900b5000e0712070f03010000c02080981d020506101c40c04548120761424000030580403c009403060810040141c1440054800314182e80000300f00300031290001c210b001138400300e154404411001d440204d01c0d1000500004081d22440940020712a170150041c00d01c85108641c18a099500d140038000c4440701151950700040410300104403a5001d080900e400c03440282c00e903064011503501152003003c1e5a4402c0340164802c0d00348000e06503200d0107076003d02e801510f000401d07a1502e100400f0390700010302200e1160010303651480e00c540c0e46520100d8496031110544540389082044100260000702c0c0c0c40c0742803030a08915110920301221494183d9810303110807800e20711000088809010010455134032590b588030901c015940c20402c040c8903036504d5a0243e621411071800a0035142c0f0188201c203003202401c10300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 469856672 1250 469855422 469855457
    0x40810050f13171c050117160911071a0405060a02071101141b03041502060f04060519050c070309050306040c03020111010f0f0b1c320f060901050601 66
    0x540850b03004690340c00c04860301c207107120301c0b0710540d21603031189900e600c0041c0d070700499a00024100c621501e141f2200c0e89080d1603080c0c450130f54052201da4840b0540d81400b2100307580d4132136035081600b003110a0070260b466071078003050103402d01d4042021202100300030070000c0c00c01980d44e001000c0c98065003008402d41e00c140d0040d02400d01b403410f000100012820807814030068412416060b00a20603030040a43d000351a0b90140c0150320218401e080c111000c00d000003030041c0540b91300f500c0c4c2c501d199980d0b180d5000410000e0030aa84d4802d8901c1d1944041d021070086600512180f1072542c0e4078159880d02078518002e0754416400394114901f004080344e00b40c0c4000084917020709224051300341d4004101d00410303103c96001241490000001c41d103002d168420208948155121110560001c5421415a0342c0f020300411400710421207401c01c104003403084d1390070b40d00b81d054980c2e8008240c84142c140320a0f02c00c448030303da00403400c01085003024001e9541042082c01c00344a1403105640340b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 469857922 1250 469856672 469856701
    0x71214220f061d010212012115050403090f0e01050120100c0203220314010203010f0603110405040518160b22050d050303070e03030f04060e0f06040810050f 69
    0x1400b620f686804040c403009414981074207104442000b19924292100f911a906400380201c42a03508004a0400340300e000c014070000503504403d000082107960068540030340b00040c811000c125101000049803a83c0194000240082d081ca80c5955818000018022996440490550000094900940e002c08542d007000c0d601d006074042451910b60400341d25500c41d20810040540b0a6008515260048404101079074070406683d600c0c080c0c01010a8241d000c00c2c02401d0322514030800400c81540250303c10518403080040d020708080d82d460004040714400c0b1004100c0c0424010200c1d00e002040c8400c0d081030402c400703031040c02410411414024090102e56100310010b8070f07403034002d080500010b00c0003000002c2406820050500c0e203152a600107070b80c4000494015542001549004819641108080f030800340c1400e15051045886903200780c00b180c6c004880810860958540f5402000a0481080100700e0300104a0040040f03c4005062405880da44001c0c0031000100000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 469859172 1250 469857922 469857953
    0x6081b03130c0302090c07050c180f0a060308030a0504021009181104030602070f030f020708030715150f080c09010308040902030c0c0a050c1002030316050307121422 73
    0x100300e80400c8030b0700e00007100c0259a00041d520100300e0040000348601c0705c004050305445203003541c600010781010b0103019540081e40b1403000403064009200b007101c00c0b5210781d01200e024400700d403031507aa0302d404034541c0c0b081d20808c509a844804100c01c0d801c000d440316900a286180030981386180080c00b009200240400d081d038652100e540e664140c2c2554241c40c0a590812411580d688042c0390003c204c503400e41045022485025101d0980342c004070b08481119400d4000e03500e004003075520a111242d07010588440b8540d41c1300c164000855820b580000b80548481059001d410694003d240024082c0d034a0321900b2413100500008480360705036003c443d1b8554001da01da84170054098a20b000c0d550300801c0901c01d0100c520305100000920703c01400f000e07991040101b000000480c1c80c0d1008545550300c082c83c3c04000101c2c184180c004540c890360503e080700e183d41103144c042d0281e131024402c0c504140009000d00c017000700510000d00c034034680030109801da181142d0312900d0224030001d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 469860422 1250 469859172 469859191
    0x120f0f060324060a05040501080c27010b1612020703140f0c060d020c030d062103020a0f02030c03030a171501021903020313080604050f0c06090906030a0c0f06081b03 73
    0x3004030f009511500c2150000e0b0000410501c01076840e510600c0d0b4500840818601c04d039100f0340140c150402203600c4a02c060300d800003424140c0c0c00c0034511003d44d8400240c0160b080c00d030b0410880814602042e08450f0b11244e0301070600350b072460400010034104000c0d10071803501301640d0405c4580002a400041071400d584c0c0a031620340c54007010000340966421890745000000d80441283c40b00c0d40204184c032090410300d00c400340645001d100a010400004016034465a034030303c08136011181c6184032750300c000c3c11500794070004070200b400d64002e072140700007103a00803010741c0c03e4a4072142e6856002c06145c02c100001740c4d941000079926440c2c0300248420020216070030003414030030710864840c290070b2103c0700826a0386141041e918002100c0544542c011010200410340000c2108010031400510f40c50811904000700081004080c01c00d560500c500034031480051140051503008082c044c0c503180c3d52501c4c0c8440540b09410003840d08007190400c40070184010301d0241541d8000f071490 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 469861672 1250 469860422 469860493
    0x9260f0106061b0c0f06020303070f0306032d0819021005040b0c0a0207120c0303120b150c070909080306090708280b03100f1805060a0b0105120f0f0603 67
    0x103040850030115241c05c200200c0c031021074003182c09030700000214010206a55002000b0a49240450880d245404000c0c021400010510010b83c180e00d80b60600380503d4501c8003108200b5a103010180c0d03c0001c0f08001c08803641584841d454050140ca0980ca9031140d05000310301d4180e46444034400d0003003900500400200313410010b94800c0001d40c01a01c00300a01054404c800e0600340084010b07403004500259009030b103070b001200e4502501100e004040c081d1041c5e48000c81003840c140d004010901404c0c40381c0c80740080d800955010707a01340e0070300a098542c1d0301d04024040c0042000010102d030107000320241801704451050513030702e02008641950000c0c0c806d22654600141000c03818895251003031132070500c000c2080368032540b076a81003144100940750680c294644401c10b4444060096040b050004900c3d001d26001b4200f41c06e01450050300d4100501d84407a1901c4080e51828140307582c0d0007c2129031201442c0c3d29030043d030201c1c0202150115400c060020a210003080241c1c903020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 469862922 1250 469861672 469861727
    0x129040b07050a0c0315060803180f01050702090406050426030f04020f0d03360b090a1a0403050d11061f0b210705040518060109260f010606 62
    0xc0c4410070603241d0141308003c03a1541e906009400c0040c81c0001e400c2c2c685408130008010b00000704a0b035076800240b19280408c00103004020400103002c102a041c094100300c6a00140e4640f401a44600e204a60000300c0e400c5c03600300100c1c07200e5000803107103500221101080320394407284142d03503201202000e8440e00f81e440f440850100320451107101c3c0c0017440c8207404400c1681104041180741098240a5240d0030103a110f0a40c0d01c890240101d0140c1080d1014465281c200d0000d0480036409040c649001d0350325801000604400d0001c0c1186080109052040003400c2c00085007050661500e20303a140041000e540e1030b80c4000e040302e84901500b10082d107010440140200007089a00d5415880e98249030308450800c80a14011100c2c4c41c0c41d6001070103c60140c0b05840c19034001800703880d40702010383c40581020001038042d50510049190000b4003001102c51104041c0030070442040040e845a03050340341115503005074041da4184042032100b5944203c0030300c0b1700703100800342d004920a03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 469864172 1250 469862922 469862933
    0xc0201051c06151e0e10030504060b0604060c11180112020103140709060915020303010b03130c09020408011a10050a0e0907080103050610030b1303030b04140129040b07 74
    0x990001e2160361420458204884c0c0001d403903425826401c01c0002810f2004804a4140410104966005202c040390210092007580f00302d2340180704600000d1424049400551590071039445600005c0c03000f42d2120402c858000d10110b00d1b8801e640004042c80290301c070704004001405010949000c00313000009581c8260400548400d0003000610030703080800d4004d1010015002c0d260114900b0f500000b02402140707031290062007240e001d142581d091010a9080f13500280051992040070f09009001c90b880f80e644000518070741340016134413440c0c010b503942134031940c0c0c0309035048861610741d910320364035082910103050506141441d5191180704050310480c40d80c01d035250b048005501000301c01c6422107025416680180100c500e16507034030080280320001c600009000154003800f04002c1220100c024402c107100b810081184d08461000c2402c580b8042e4403440903140c0c420041042d01c2d143c2c1e012091183e900d1000716281141c9694122846c41548a00e0840c1c1e00005900d005008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 469865422 1250 469864172 469864181
    0x501060c150f0603030e0406060203030f041e0803090607080109020903370503090a1a0d05040827010807020c0105030f27010203010302040f090209150438010c0201051c 74
    0xa050b038002c105a60b26420020701c050702e0002c105000d641b0b00400030a13140d0001065030701c2110b0a1811241d19a11603031010528407440e00c4c41d91110811051800000759074401844c440c80001008158505e003070100101044010780c01140d60a00c100700e1340c1001e85002c5000000510b1107081c44811800200c0341003d90000c44260502c4044204041820001c0c048010f04d001081100c844103000d0f01c40070b4a08000c824100c0704074840c28100000300d12100b16410440c1d0050141ea842d50600b05102c2d1031000380c0c00e80c18010030440704911582207056803c006045c0d042080b5200400200040e00f00213455403101600c24440c03506002d0000344101400880c19010340c00c00724099402088034041507000c0d41007130104070300c038500304600701402e05154400c1c1411315400400c0101030b82c60b00000d890703015100700c0700c007500252198980c03548503402c0c03018900310041c44503903075800b001004580a80d518900d2400360400040c2c800040160382c1c01016103000011000c104c9140380c0c1d03d010580c0040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 469866672 1250 469865422 469865441
    0x106120f060e030f1615020909011403070b0c01050a1d07090203100504090503041d0c0412050c120a0c12030e1c0506040c051e03100b03160e09100501060c15 69
    0x4c00c001649140c0030f070440e2285001207105000c0d0300b85124081d50444181c0c00b0340040e00390001d0007180100019520341c00651112040981641ca00356107690a802c265030000d40003400300e030f44074001e110800301c16200d5a03c2c280303104ca81420b10101c000400c16251807040c8620440a0340110114140b4814050f44d4001030900038420408030500d0318120340c0729089480b6203012501c0600071200c002245030007142c0b00301c80010402c0e20305410400141c43d00c0c80d40d00c070300b41e0307240c40392050001c1c0c03540328100c4440c061029a4010003407500c4500e0b1111301d02c10710b90090b800c02d01c107403008076002a0300102c1a28198200321410302c0380130a1150710706481d41a4000280c190300c140000c0c4802e0001c146100702c01d42d05e05035003020403d0903500096803850b55251256801d43e00901d00a02604010b40c010700c1141c0001b400e42d5800c070210042c8021a141d544c228050141c80c24081c0820180d04110700e510549515106104540c502200500001e49022010701040f00c404201c04008215501c000c2d444c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 469867922 1250 469866672 469866697
    0x120606060a0c02030c06042d181a04051f0b090315040807050d1205011e2c01090608010e150606090a0315050402100207120f0606150806030106120f060e03 68
    0x87d075a4481700900b15003000400418140444049110a03105d04202c00c01550302d0054000301c4100c0d041050340062000b0000345540c0141101d240300c882e9128002c0b0750244007804864483d903c1410300d001500210760380079070000304040000c2d0f091500e011a40d07008211002150007a155100c1c20150300ca44a00c2c00000c0142c003c1c1000b01846030340088516401c2d503040796040029a03240d0407203240c14800d10065248040e205542000025244010f58511a4902251540c0f105080503000160300c2d0a8114403c03075601c40d201405074940034030951078103200801c0107129514010540411110020340903e003d600c0c0020803840070b03114004050015580030a95000c01c2d144a641c0d03070001d000030350302203100d81d28000300e5103a028800140c100030f554004d01c650448110756a10111595a030103001c0320007030b88900c1c1c00503c1c1d00c04501181103412440c0c035155401d24140c020142103801e02c0d0409104021f503400504c000c20400c102c040c0c00c042d4031034000603484c66245141407950141000c01d582 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 469869172 1250 469867922 469867927
    0x912020109080a062412120e0a0306020405090f0c040308210a0903020d02010510090209182a040f2117072015180a0b0405120606060a0c02030c06 64
    0x204138003644809100f0001c50480f42d01000d40820031010760400b44505030903600044951808601d07840c05030b60b8122544d017040700d12a9200d0001c40e502400755442614841d6012904100741e04210540030f512854a160b01030052610f0b003400040c0307004501016001d0380001c1203030101d484d5043c00c10558a240100901c015280c05004036000d8081c5000031001401070420401c40b135801405228001c10fa0044d543e07192303c1c1030078610002504079140040d0320188080924000c100144e02c03042c01610070071400030b8000c1e5200c00103000704001801c41d050006082104008250030342960740140d172040354010034070300d01c05031104064851001010b0000d2042141525041d00c04000400e401842181c07045050001c120364040070701c28002e00260841300340b20500000c1c5c0040401085c414000103604420b401140004c510003003500c3d040406001000a001c1c0326500e80182d107032891006100051465141c540c1c0860680d01810080304180030100740441c1c21503500b84080c60003548060800354 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 469870422 1250 469869172 469869193
    0x6080705040f240806010921080706020405010225030201030f09170301080c0415170304031b03020418020a0b03270c100c050c01050f0c10090b0601020d091202010908 73
    0x4843e840d01c005004011000f00c07a400f2050703401070311014400d100c147c482d08580340c50107500091540c18075900c500c100000d04a00350015807820068820980a8140142c9132801c04001902e08140d03c0e40010700c040c0705444410155080750321441c00e6a03420b180124010310991211400b40c503285030010006064080821000d41a15029504942c1103c0480d400030980805200454000c1440382a0003200c1000c1031028806074203480d5098400c07002182c3c80c01d42da9031180b0524000c80c401c005070404600000b0001d52400e4002c0c0131803948040c488248000503640040c02010b06c4d44242c499400010000441414480d00003400d4a80a0030b0400c25504542e4206030700c94816401e030070b100781880500b2003042e42c86150645061030b80040100917020110f0019940c50b001310002e60b142031420003804c0c02c00d1a040c42400110b606100c00403030003141c0c1e0300c0c2200c45000f00030306c49411948400301b5140e039294400c501e45c1c00c8560314560440080754500040710ac00035150000f00080c031926141c10b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 469871672 1250 469870422 469870439
    0x301030b2814040c0501140712050702091f0501141b010b030f030d0e0a020d060b0d1218080105071b05010204120f1a041101050a02070e190e030c0706080705040f 71
    0x680c8a21321039180740f4582616000103495100351201050310000040c40750760001044811901e004016500b04a410100650300050301c01382c017290f81d1200f4403e41d2308032801640206000d000604402d0909a142d505991141c0c9907a0158046400c0d00314007040089405440a52000300b040f2070180c00d69a181c0c020f035006603a03e41c000c5403181c44070303854041c1103085540c0200e901400c0d1039000703054000752521502c0381006000341d6000c00303038000454803c03100001c18589201c1c2032003150391280070b5000c4010668481d4020164880100c1c1c0e4100000c02c084036a022a45c0d2641680d601c0341c4d8008012582415802030055410141d100181042c1130414081c1c0c48103c4c00c550b9100e0b403070005021611000d080d0780c2d04000e8034009d00d80e400c0c4030103600c20741d80140007030000112180f04940c80c4039540e1803d050b410f00155408a9103561400c0b05064041c40c0b07000d00c0c0202a101d1006601e44880101d003140e5800c0940b00da0400c020040003c0740400d80b20314100c0b0001e184011805e0003440e19503c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 469872922 1250 469871672 469871711
    0x8091c140d090f03020606101e092d15020705090c040b07030e041b02070501141b0c03070602010c02060c0d0e0604032c090115090905010b1804140109051009110903120301030b28 78
    0x690b000c182030bc01c000070346001000724150300040198082e0045514103010b102d000d00000c1e085012221061201140c003020400150400c94066035800c0c4568131060144021101c0000c468180e80b03080f070102200058001400c0c90427030714203103030a401300031003a84405224011504c1840009044021403000302d180004c00311a4aa8100c3c00d031041c1a0791041d003a422681250040000350700902c0010b0150701241000c0c1010180c000d101262041640b1402400d00a003160708401007040d004a4180080f00b40410143d18003c244c1c143c400040e80c1800950035420512a2031580005170791403c000c140f01e80a06801005900e00500c65544c490306001d1042d080040041c14120650030600500d140030300400c6040011490040001d07404d000d020406480700501031725400310540c500040410451081c0c07044001d42012013600c1d200b189081600704403005500ca1aa41000e20061020864030203c0b250404020b042400d010b6584a03440e061b06440040881006c0b40b500071007201d1070314403098 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 469874172 1250 469872922 469872989
    0x1121812110d020c04020901030e01020307120506060a02070e04020303070b0907030224030a090201020313030c0e07030504053301030b040308091c140d090f03020606101e09 76
    0x540c007200380e2030103070348035a82d00b40d10100c000140e103ca003510340c0c0b40c20254000d0440744010300d0042204241c0c40c10450070ba17442078880900142c0f85000031940a01181308043e00000d0444685181244080000390b80b201c060081061421681010604560701002110b0803c1c5d400003120003985820061981ca822140c030041e40640042022006c50f20304036801c0d1401040c0007140c1d2400c41d02c403a05254020006124100c0c1548000c00044581a8802c01e03103100561058035030308445030410344c60182c0c201c0302030210010b050800041c08002403001c64065540510048803407407003407031044030307200413403101a083c1041c00300d84001106115132085582c0c0300d18065218088641c40d000c1d1840c0d41c5d81110b164440c40404084c4002400d14030400800004000c00308042c1e050031003001c0c1e8941181c803d0141180c68507101045502010f0701401000c0d03008400f101d9022900c01e105c80702034503140d040b1300c111030780c8200310794004515405a030500c40a030002000349550321020b4014490580320010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 469875422 1250 469874172 469874177
    0x8070e04030206070509091303030f1b11010b0d080f070c0b1207080103110d0302010e060705070c0b040b19050c0a050d020f0c06120621010f0c081501121812 69
    0x100050760b136601036001c03a440342c50081d040d01e10564a072541c8400c0094190340803030806031207028007206600c09004520180750442c202c10070308101810007030042110a181c2c4140369040649282c81340e610b030b01e07a9202c0d842d04040010381e108031500c1c042040b4841c91200401c154070040010403c881041d010b800c4035032031050750709800d4603111b070f081d43d09407400d101c0142080310611a80c91305041c0888520a610310138000402c0d0400c1c5044000d09140080703440100040e0045800c000380f00410488500410136880b0051800c5d04150140000c0d03c641101154550040441d03000140d10410460305c2d0380d0a80002c1c0c880c44402031401e1910751003062140300040c0b14208042c01204404110700c2d0002000400c0280b60442500c010280340c04003e00e00c5502207140d820450022203010403e512941c2107a0000940090b410050000c4510341c800440400c880302041001e8454010500f80b03010009081c89024019681c403101c0c0905480c8124042800707040d401c9000304400300c1308c1103030031107900d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 469876672 1250 469875422 469875433
    0xa02090613091d0a02090103150204090e030304020a0617270a03080a0c17040f030e0a06090f0b18010c170d020d11030705031b161511040f0501050f0408070e040302 72
    0x28843ea5845404e0328021754411811401003001523a402129003d0719156000035007895a60210101101c02c1c0070031021560300000100021440d185800348058901d40c10011004017a90341041005400280301500c0c00c0146101081d0318420240e00b030b0701c2502c4040444003080782c98940104070400940b00d00100f0b0703051003800302100b800f0b180d404403000d100500c0303000540d0b40e545402012600e01c0c2c40c180c0502a0114181030070740c48580000c40900401e4032015003051070180d642e00c0e01e25140e03022400300507003880005020078800701c10290002c024a012602c42807141440300d252103131440c0550900a00140c0d95418844540140111840b650810003204c20480c0072101148811904100054020000a0305080c1030854a102000c40c0141c2c540c200503d030006000780d0403258205580620390310704c56031541402070040e01c0003460302045050415190101801895645001e0356040c07003808190b00250900c20030035100200848402c640c18299101d82040d152402600c0590050003036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 469877922 1250 469876672 469876721
    0x2150a120615020a0201080604020d061509051507080a020c040609060501090b090d0803042603150d0c060e0111150405150408030402060a021906060810140a0209061309 74
    0x300a00d0002e80c1c402c6070042d1036094034950044507120402002c42d40e025a003402070881c0c03c155803040d1070103801c0385950407150313141352075014011140c55032100703100f4403180f81c0480c6072000e09015103140036448040191034540e071007800c0e4107040c4500b424030741082c0350480c002080c104980004003111000c2e21110801500c444e5150000d200c1c103042250800220030307080000940d00c500655102d401820850308000c1d802c03600030400740b0000d0044650490110511180c055008840700c03e1040031241c0003881829695174a41481c440d100388410301c01c565000c000140d00540c684103924503900305035114403c100c001301c0d000d044107440c03e0314070348140105098003c00800307141d40030ba5000310f2008d0a55496500300507503580611956802c600400c081820002048644031200307511070000858200e060114540c50000600703010703d0706504210080118000010110707811070134101d40540ea071161603020403102d204580303161001e2a40303040000344c15400e9500c400382c03543c1a10122217080c801e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 469879172 1250 469877922 469877939
    0xf0a0c030506030c10022e05071d06091c0804031e05070b09060409020c0f10290102070b030f0108010605011e0f031104080a1203060602060403080402150a1206 70
    0x101c0b100d54165115212458080c640b062904c805061984100c50301c5c00c2e400025490241403988404426146002400202d0300c800d0017120741c401c0c60f41c0f0380903091290106d2082c040d5008903603400d000340f000007100343d0785891ba00f10301607080450510704440b03c036051504c88410f40c03191000707035841c924519a0345900300c880040c2c02800d80e08840105080c6090600850b040d9200c40080e070342c0140304010020744840c482c00a090310390182d00141a50000003140c083c2000c0090343c80c080c00c103141514000c0000c80305080c402000c500d0550003040b9410520041c0d280406c0c940021410200c04001c00030701c003401c00c0d11b160603180840c0003030120341e6a4000542d204401005008620020080484c24080c45904104040c0f8600e280210b800c14100340c8964036540310b500104c0064001240f03075010300204400b1211220b4440c5400c20540b880c1c04002034403410302810040810911501080555680d6400902001048000356984c0e03150584054005000d080780d0080c66130400f24005402003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 469880422 1250 469879172 469879181
    0x140904110c010b0f36040503070b090316080f0f0c0a050f0a0c0b030603070915030506130507210b0717090111040519080604030e0108010e130f06090b0f0a0c03 70
    0x2c000ba00d015050381103600b011290245c0103411100c000c036140807041000101e02d04d603c0c000c50050003d540e560400b27080050300807100030240b009a6000300001c2c00500d6120050790403d5400940c519103440e450100c04c8114450a050b2015804010882000f10140410501141d82c41401240d1040f0025a84d51b81c9038001c1c01c80151441c5da81000411440d03200c04003c603403004d0001d0035264415207511448088555000c445280261800000e208000e8208005a0080c4440000c0c80f6484074030350300e41750380705424015030034141c01a1a018050411401e82070700e0b03880d4421511307201071400c44002403800e6650750410209080700800b01f50344140610650ad8800300038a82546882c0c100000e00c40319255400f5038880d050703034007400060705a0050000301e0085110b60f45030064614000c000414044042e00b1038880741e104281070080250644e800e140155a101202031000465820058020710340d001000e400c0c54405401c000220061603e05403155400200030000b000d0640021402c45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 469881672 1250 469880422 469880449
    0x80415020c090c250501050702010c030504020a0627090b1309020109091509090602041707150c17070f0203190f0215040f0e06032b140904110c010b 65
    0x303114907011915001c162401400b0102050410404503420b1040502194001e01070685946e555007050141c125428001c9408a00e074514040c40a410203800042c01c0030943d2003103405100000511251500710000d00a00c00724110b11a41c1000d950340724110098603510040912440c1c0804c09603d0390b520070321800c01600d40694500881c02d0501c0c036110001c1402c00755890b0280000c0b1070000e00d042544c081c0d040060311075030700583c84030f151a9140d511002c001042010350703041a902440902c0341c000c5601441d50381752820a10310b42d51410406104000081c0b013081c0946e00040c508148450a06100400c9100341c2c111003440e0f0307101000c5480d860705200c00429010180c4011805440e020f19480c07600440403410b41c2c070b02940d903001021040c1e4582e000d01886032052003040705620b028070551000c2007846600d03c01c11070f41074405c00c101c141c251000c0e506208040344036400c0e1024030410303500b414201800801200481d5080d23410242c000d01d0f0300c1000b96081030b00d66074903414000d1500002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 469882922 1250 469881672 469881679
    0x61107050c0103050c030705070b040320011d06041511042c0c090d0201051803030c0607090e010609090c020a170d060b12070f02010f14041209080304050f01030f0603080415020c 78
    0x74802d02ba543d50364088400b410030382c108001480030a004c0c10707000e411184009e86920002914003806904503e0380b1507044840c552030f070007840c2000b010400310054458041200ba10000b6000c021b0000000c060007280c01ca1580040303011140d0350075a0421035070b0440c945647c00e0030039490b40c1c1d080c14034980d8840c0c0c50301140c100356000b9a04005502480c041c2c00c01c400f10004c0d403000614502c0210b03155030070a001c2504182d0000040c4a1100d4200d00c441c809800703070606403a41c0358100007001e40103001a10032251320303958030000070301000d03c207025130796a560748804456243d04550380301b1149034000000c0500322529100f4002101c2801c01c00b2202900c0400d181030074607680d00034082c3d03004110301d80d400d0250b54898420a903d001144146142529004811044c0d070505003041d00c11550f0081c1c3c50010701c9210320080c002a41e00009540480d20202c69040a081460340100c0250a0061482d98118200035010040100720b0001c1c0c025900010b882030b03158000d03080300701e139980009050942c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 469884172 1250 469882922 469882927
    0x10f050714130302120d12020c0a0b0603030d0603085a0412140d0e1c0c0801020306180c070b0a060302030607110d03090201080f04061107050c0103050c030705 70
    0x201101c1c2280900202c100c5410039003451640c80c1c01007800c0b201090700500b8030b500910310b00452942c000f0f4080740802081c02003182000d0002040355030781c40240b0405000807040000146203070345c0810441d41841c102440030700040e550b91400000ca604a25000d007080400944500f40381c1e0090b03811156291400044135184a246203000d90201c410b4541280040802c2020010040072001c020801001034284a184100183c100540da0484001c3e00000a803c20803403d080a98048604c1803122001c41d41c682180c014154032054103034a21400824850340788a000680365019805107106d05800d490005495800301c0e0540c10701101214415203440d814400280801d40d40902c199026003540310015403c1d03100c0d00064030b81001101d8940006601021182e170340f003020302c80c030700034010141014450404150300203080b504009000003040841880081c040c0103207a00140c1e0002007402c1b1066541210b4281310742c4402c1d0440340c1c03c0c0403a081602091411103c441142d1003101c840e0740d82070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 469885422 1250 469884172 469884197
    0xc01020f060c03060d0f0c0e07050306100e01260f1810020a090b030c030402040b09090d0c0c05040c081e01050a05040e0a050601331b210809010f0507 66
    0x4030b5400c05000039030403410aa1001d4000b40741d00701d4501d03291b4055004075100900d007104060700c0290060003401001410b0090042c6901ca120b4101030a05103814121029110080102c80303800c0d00e401c60918054000c10480303a10448092141c2c0504064842c01c0b08503603c1d110815891100d401c800b948035030040d4512581d0b0b10082d4081c00704001c0c5d52600021160303031406400c950ba08203590010b0781ca5000418041143f425214a041c0b80c00d05440c07000ea6880d14004090b159031303400b0721440921410100da031080104051880002e804000d00400201561840042c040c45040320b070705101d0740ca20410701a010000e800214100c580080a01c80309500300401d00014180361100749910b8820146200c0005400b403180601030000b8882c2030117000540c203c089500c80c84801c17442c48420940c1354100c4120b5126113090841440080714100c2ca400f00d03c8c1c00b12420007002404c2c040000d0389106a10381c603500c07482d0350340203c8c3d580000384408000b00c0c88000c11600182c80c0c032004112005e4022 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 469886672 1250 469885422 469885441
    0x915030201112d0c010201090b1f03080a020106060225060507080c060f0702070b0f12040c0b0304060209090a05090601090e0f01021605071a070b1b0a030b01020c01020f06 75
    0xc400140442041d210484600b48854105450f110041000d00d1032140594110a00401c49125415002d20090024001641301c3e06511f8201800c025814010b1038000005440a94400001141c0c0001d600740e4400008800900a140078010b00700140600380d00c400c401d4900b9040442e0510403055031070b02c40340c506041961903921084044a20907002d001c80c072070045041c803116214140390000d900103407504540084c204110343e040310340e00342d009002c14007a2400382000d9481d800030600b40e050582d142d40c2004014403889603c4000d80b04800800c000070014560058040c000003900d0361180303a180d2a040205482e4202c8182d8000d80c8000d00400c1241c01030340000407040c5c000e0059540d054028041d61b826a800f40041c0ac0ca00c078803228102c0300700f1004216540c001d181994406005051008642c9000c4c8906007010701004601008503045c0c6c86e50f141039000c0808110310842d645c00861401402801c2c0310140c0704d015000e264070001c10341d400031603010401d4176184080c04484d500e4a030704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 469887922 1250 469886672 469886687
    0x1b0901050711040e16050121051e0c041d010303121a0a0f0314010e1b0118090509070503070b07141212090d0318020105090102161805010915030201 65
    0x980300c40c040c000c1141455103c0d48250803a051407140a4450b02000d480341440c1c074020303640418100700c0c03403500148112103015500c501e40700c840c0c500803503552600300041600380d200810b01601c0270002d100703200310600004018411100c0c86804041f5003e184034013020580c0c1c0920020700412281800004d158900380d022041402151f0110389280d01000046804001d540c2c10504488003001410306c10700192103282c0040102060083c08140102e00d800c41c0c44045140154404404040c00e02c03506038010b0742e500e90b110302102c0041c00b64a6555038001c0c0a0002030b030303000050b801202004221800c0118060b01030317914200c00d90349000250b03910002c0107954803802c5200f500902d080a98011007002c0100301d020343c0382c02c040100381000409982441401d0304c80000381481c1c10311829112040d02e607404a40340c2c090900d152114400c00050b400c1048162840f140304d040264042a8500130740712910040c142424100700750383e294111102100c500996826070544203140410056108900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 469889172 1250 469887922 469887937
    0x70510080402010c0b0901020703080a1a0d06020f1603030c18060e0d050304081e0109020a15020c040516030e030403020a090207020303040812120c030f0703050a0209130c02061b090105 81
    0x40c00760612800340c40705c000f80841a5801c0005940009102e0180759101c042550404d01e524000c101d803030f03041c1180507040a40c0f134a4146c000c003030000c80141031040350f60507100c0c18a9000c0026075100301c0d000036180d02030b07032800044011a03c0d090038080010312071500b128140c4000b181c0801d0986c02c00d001624034910070038269510060114103000081c00c140301500040410a0061002d00700008012100e00310085640c1035aa01d000102405651440d1001080f107003000b001003a1460b01a070124144111030001e150031600f00000d0203403410700c640050702051115681041a10342d40c030a5a0f13100d12a612002e94402d52507a03041c0400d001c2a4010b2944510080c1201c0ca45036444040740d080455000089030b07452008202e40c26007070302045455a02c83c00ca01e0100d8a9490082e0030307981c102a025181e0320406070b8440000311901100d81c12a03c0c108402040402c00c884240145c80141242c4180c94005001e400c0106080000986046410100b02e074480c40c1042086401146c1d01e800160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 469890422 1250 469889172 469889177
    0x10515030907050f0d1406070801080a03140313050604151d101a13050405120909311b080708120c07050604031a150f1c050610080d0207051008040201 66
    0x71940000305002c001b898001c038008082e280074a011200940015416408000d80c1d8200b140004006a44180303003980180c101e0180580365154001c110082d1340600d04010400e00c104020702c002c0c400044c421015400c010721040c840340d80703920014007400d90710100d1003a20b44e0000041c501c1c014615000850945c070424203849103008a4400035090703041c6480c031141c00d50303603d10610003440780910144a03808103a5803920315003030b524000b01c0c039110802041081c046030700840406060900d001002c42001109002d080d1118050400042160404017800c880d860740703c1d00011910000b00e095000c0710b0b400d42c060007145000000f450340e183d104010300d24083c050450045a41c4e036030303500900302071070241c0e44002c4501c003820744201c031002020300003204084036001c10000076030310040b500030309840640700107101c900c0c1c0e21051400c0141c07404000301140600410000150321a0108c0703803c503526a400c80790b1500d01c0500c10390711480d040c003d0700d401040050b1320911082c080c241141d0403a1061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 469891672 1250 469890422 469890439
    0xa0c11040e01020f0711060a05030402280b0c0609070311060f0c16050906030601051e1c06020a080112030c030503220308060321040504110c0109030206010515030907050f 75
    0x1201c030282241c0c0302c00d1001c0340741000480c0d008107100504400228001d010f44000f0701d046c81185d800380107404000c10003031061240c0501852500704070080c0c80740c090740c6103941d200c07000c0d152843e040203038200b800e0481e0144246030015044600004001040342e41040301c0e400300d9804141032104a038003049020741c603208200320380175001c503040102000c50a402d8414458150411042129007003000d00801d219034071020040c840d9a9460070200f942c0c1d00304403441c4100903000c130003081512080c03a03d01c43c0c0c3c2e0003001845a05102103900240362a5400d607850701d0141c0c0e2291a8541079201c1e01d076000e400900d0039142000000e0094000315040000002011007850a0a1341d1040341c0da514003080307001500034018464281000c01000001000d1410001e01c81391030b0101f0080140514030405100346d445915040c400701c110703030483e0901d007180402805079100710304010b9601da03420300c182c42c000c115141c0c1b403121002c1503000b5280078000d141c020380080c4d4a088100b0441c128026003107544140310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 469892922 1250 469891672 469891691
    0x40902100f200706031a0901180b061201030507060203030405060403200a050a03090b0f3405060f060f1c0516060e031e07290a030b04110a0c1104 64
    0x18a646158991030300009044030f6050550040a49480048648690015440d0912540d8650100c6810741c2d2501040c1c0010190b0522140c2c050005c41c6801504204000f9210a07501252403045040e203000e08202d5044640e951701c01c070380d02d12044038050125000403010a0009129a6605104041c00d080380d20003410000311290409441840440300e0b80d100364908800c25411540480060944600c90741c00c00f244035910043e1407203a20429200090629148101140f4a1560780620f003410700007201681c0c4185841c0b580c600c4107032080c1e44400150030000b4410318060310124070103007020705050688031428650b0b4030054450b0404450b207000320304100f0358910703401c0a00001040181d8a4006245071101450700f0120084141655009480c009002005001800c4422140f0540148003070f0200c40420000c44c0c592003004040340e4500041e080e80580d407640000030b4560089604110a074105008408184202c45030140891011080c41c804a01c01c00c900c4200c14001900c0800d04801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 469894172 1250 469892922 469892957
    0x706050109050a0b01030b1005070512030c0421030914040608010c05341203020717090316050a09020d090b01030c0e0f0c0d0507020a060920040902100f 67
    0x980190807081c2ea50b2080181400481c028299500801c0c01d0030030008030030a000c120072000e0f04080d0010321a0004081c400c0200810070103404210140c03072281c50b0301b02104420006d51191103504106220041802c001c002a03404402d00c890307054440070009440d050489003c101300544d200e80c040d90b61080020102005e00a551380e48800c3e50720701e5a608c48101e5140c1d034407072404207105a5414003a240e4125034504d8502122178941020455122034a0001d00702d020f4460b0141c001c0004c09200811203202c0d403c04042c3c00c0c0d00d14114144c420741e01000d24030743d034444024410b556004e150a2001c02c84a55990f00400c000082c400f404580d540141d11030741002c80d020380c4222070080c05410200011501d144103190002c4401236001c1250424540c5051280a48207002005c19580c3c00881c10300340c000c216964034164401001d008a004174104600c21503615860318588610001040c41e41e031400e441545000c0398010300048031518241c0d001c45000c2c401c041442c0500181c420300b003003c0700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 469895422 1250 469894172 469894181
    0x504051c08130605030117071409090a14030403060f0513080d060f0b031012030504150c021011010b060a0525080c0a0320060f060102070b040e1503070303050703140706 74
    0x1500303480c2e81c5c2d96035150100c0a0714400b00180d8115071500040000d104030316030000c012100303800488414059441c4c0c0d03076911f4140059000018440308058094050700d0a0220240c0120781c040c020030000192003160403c207a82c0200c55803806400982d5030340c00003404050144c90000038290300003850548511000d80f0600251300b00b1280c0300400f00030001c0e03849001c1e23081700140132032407034441c500721203640c000c2e0890240b40500b4107064213000724191110b20a602c0302e02029001880395008003020307500600603024500011006500b000d081042508001b001c50b11282c4c0e49a031140c1c07815607442001a42400403008441e01030004200d000081900c2002400821621201802250b0f44614016140b81d1000c2c0581d49041e111021612a031040421f8407030340f00741c908042c0110b507524980105e08150301604024007500011401141c019800f0406a1080c100c070265190018144c1080595419442c80010700084007001884000fa106a0241d1000c5148601d01420a07009683c3c40041c1c0303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 469896672 1250 469895422 469895429
    0x30a1202040b040909020a090c120e030d18120f02100b0a090e06190501050d1202010b061b07080f1f0204210308060414060f0102030702030601120b070504051c0813 72
    0x11905c0d035103100190328003c2c071140d00a0040349030400c1f81c1198100e010f001c0d000c0f2005912501540d690000084100c1030045840e214000d5400300958031207911a8080111006400c0e03480e141c0d40740c1c0000209016036010210300c038003a00241400032580d40750001515000c80b4103904000007041c00184072034240074100941800002030116840c01c560303485440c0c0140700c2903195190601e40100081e0311110f0122201e0398009034030008400c94408103a0262a440c01380c0e50b008000001c044c0d1140202c038202181c2c290342e038826500700d20340e2010300e16a60220210790900c241c02c81d01c1080521404809001514400c01002505203586d03003415001c1103040c1003007510304640e401c14030010940d201455075400f40b0120703070410000c0b8000340c0220b04840010700c0c29019414880005540c2c1c1c1c020025500309680c000d085600a41e1201821819001c80d44001c68268505402191103d8000c00c20396040d94006006241c14450441c10500c0480c1c2083c002d4070340820401407203108543c9a142800607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 469897922 1250 469896672 469896689
    0x21020301031209060e0409030c0c14030111120a05090703050f0c010305090d090303050a030902090a021902060403081501091d060a08070612021b1507031805030a1202040b04 76
    0x496240d801c119040a41c08a902c50801c10a0401841959004024101e50031001d0741e00281482252609550811080c0d0024190401034000086d10629456039500245002da00a010400110348040301c2c0d40120010b40c02c112019200092040303140b940541d0f40015400304480219607a503da9900741060312061040c1c03600000200002e95070503001c1c850300130a0000041503c408810720091003100c1600004007042000155040064800d402074544141c0050101e03106041a140c2140254450b04184005041070a00700d4591800402c0d1188929007549070500c456441c500380c131040f000c96002003414400300c400081444e0143d2034011207104498801c00078141002c4040014060b8103a103e54074036803104005000d140e501c01d0340c8900c8441e105801503100c1e0140120102d441440752902e0910340300c0d01c101d10340c2c4004034020f40383c0590999142089941150300c4110780703440c0b0740c650150040e8420014401603600c02d1120707002212a21134010f060030b44034044641c0a900c1580200c14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 469899172 1250 469897922 469897927
    0x8040204140106050d0c03020d060e041a090601060e130c03050405121e13080a0302100b0603010b040b0304050a0203070602030703031b0801050d0501140a05041b05060315012102 78
    0x110304103441240210000c0562107407040d031500100600c2d51081011054009885510030594076004e501070710142c1c20f29850a0100a84a5514004000d002c4900f698150070f07444113000d98240b0b03442c1d1140103400a40c0944600d80c20a1000d41e1440107401a035500b1007258202a0042042032003135481c0d550480d68003151900349420114500341350484158424441004002244000000c400e00c00440f6484541e44031881c04000b2500c0141c5544074803218000e11244204044d408601d82d03e001d032441c0f604101010040c4184103180c0001d005404141c0300410040c0903021800f8081d59000b4030500444403d001c00303070f0203c1c0c1040407541c001000b60b03001282040c100b40e00340c052480003608110040d44100d02006000b041048188034840c000d0540d0200c420503c00e080d00305900101130001c3c1680541801a03050006100440d01034500a0344084010424400081c1c10f604a800c0105620300b913882c0e4031b04841080f4a10200c441c1070140300d4202c04a8040c560140510543c045880140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 469900422 1250 469899172 469899181
    0x30804050306060102011a0f1305091e0106050d02040207020f031c0f020102120403110703054611220b12190b04060b03030711011103070b04021302040308030708 71
    0x10325140b0050400303819641047c1c01d00d0540f1110504d41d001c145000c40e481c07010300a85002150200000c24041c0d40140d04180800495140c0000ca618170340b025102403c0d501c0c0014000b0b5403c0f04c98070b006650f03000e00c25403035000c050b1510740c01805a26000424510603104000002481d280312009003903c1c060841d400e604580f50442c002c1800e00103240020352400410b140c1a03504c9201c0240003c041c0904602052080c40041140d10090f66120040300d01d1041070900c1c1d49800404d1042d0104c41103076500b464080b200c1e01e031200d030524680401d544141211103690f82002c200d2541480c1b80c010b0700441904c2000001000f20940044a1010006180704c00400b4404199541002c0c56202d51050002e4840c18200c440040001604402c1c0f07000300b5211450140c0c0078100c004001c51789803002050480600103581c0a12094034000d80714406242800c60096845c1d0081580280c003084a031000200581842d001d000355041c60300e1401880d00c0d4413540c5a14064005507017541c0041c1030b000800c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 469901672 1250 469900422 469900429
    0x5190e0601030302011503080403021201020708120f161205150406120c0909020105030103171201060e010201060e0c04030219330c021c0309170a03090f050a0e090a0c03080405 77
    0x140308006000300b110b071b00c1c181180c5803001c26100341c2c80001d00030a41006c3c0f07416204000e5042c0e030012944240d595550f0300102c0707014507040105981d240340d5103028601041816a0350f500e1088028196203c030500c212143c2402d1004000c0203010501e4081c0c114000c02d615681c1d440b03810003400c4104502c0840e03100302d041455032064079030013030f2900c01c0c50f003802d0f0400741c0c1e044001d890459500034a00001d40d40582140c0c0a80d00800240c9403c440303561001051841d00f0986604110000f0b80c02005001d51701c02e00800c80001c03e03074114094603400c02050000d8185034511608102d1031408812480c1e135500e0801203000424440c1c0600001c104880c894040307520700c101129051286820007151444d500090a41c0100c01c0c006202020311100c440209400354540c90b00a0a103c200c2c00a103090140f0400d0302e451482904071300281a01101061511040a004040e034030040e03c880c178054249102031000703102c0944480d410340315603804e61000410361004240130b18418130304c05886615050a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 469902922 1250 469901672 469901681
    0xd0303091b060221070c0506030a0209100815010f0e100212030f06120a0c0608130b011707120f08070c1701020403060b01210203060f03160302090c0f030a05190e060103030201 77
    0xfa40040c01300300300344804200e0910140c02618011608150343c1d4680c100308000034401c000b941504001088441e01c040c1d50031481a600c44c80c001180260b07843c11074001103801d5030f50078a030080400e40d60f5032130007610300304210504041c2ca5540100c84019400c4010308200c0c2e04200c038214400c0a00404201c824206000d01d0f40f1642c241d4401804a018160f0f0390950081c41801040100f21500000500040b6a64554070045411450003445544c64601c1103641c6004511241040e03c0380241c001350741d00203504074000280e001840501c01d000145c0d03800c02203034010300e41039a108181031404145250402c4c080442807007075200050b81c46195280210030350780c402606505211030104107102c1e0a10b01160220410b0501400503070b00d82d9002c00086401d03420780c680300e030540706141100380140e03030b450455030589008441000f419507404000100a02c10803100c000d2100d03080c40880c115900b41c0c0c2125401001f00c584280003071070021082c0d001c0351000c41d85280580c4c882c80041040c103070203108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 469904172 1250 469902922 469902973
    0x40212060403051e0f03131b05030a021507051606090e060102060406110f0d020d0e060415090501060e0c070b090c0d0206070507031e1208060d0303091b0602 69
    0x644664036258602910f6402010038210603041c085181341e500402013401c0b2410001504181900c9040941020402425240d0100c489511150407240d058005508141c220384006008201265907642480500c495802e4001c0c2030000902aa50026030240080008950440307410456213140400003070003074509a202e0201140d0240a0182d5640e0200d003041d071103034001ca40410b42c0d01701b00594075500c2c41801e40c4d94030f020001003111403500c00c5c01d4008121a040e03560080c4601e00d021400d403a01d0b01d5058030000d11581c04011494241c00294210603001809500005039050340c80901d414007110407100e50204000000301001080460600c050b0060541c1e401446280030550100e42045100c01019114070340100d100710801008202c03c6c0c015607072203040800002d0a0f1510078000401e100c0d0102c5501c030305445106400c0b842041da0ba489910f0050901c0d149000c0c9841c154010003001c0c00c2615407181ca25060301c400c0e01c0425240004102503802400d0019504084810f0a0103818 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 469905422 1250 469904172 469904209
    0x9030d050c060c0a08060904051507050403031d010801031b030b01030f0b0f0126030d0906020c06010b03130618060908030615030103200a1206090b010b090a0e2205060402 75
    0x241d41c1141e1700c550f003030342d00000c1950900381030386036070030294070700001180008a400815001c000c1c2c800c1d800740c080d204a034820b441726001c1c59521441241010b0b003080e43c06c0e0009001c8401040070a1202c1010000041002c0441e03da40f52240c4545090034000d0b003040e1201c0072003130410070412180158240c2e1240c404508031402d94105019061802891100c240000c80c0c9001c00e40301401040c01102c9880060070700422001c07046140c240007940021480c00301c140112400050b0a04661080ba449460b141c0561400c0d107000d03560b4840200b62240038a10199204107000c0b002507454440d215040707002d4241907890780707064003c000705503086000d124104603080c001007000800220b00f03481c076092414803e400554485010940030b2106601206021031b49004030380c00c0c0040d0758042c1800c42e001c0c1c40d040d80d080ea2501500c00b118410301d11510f800c214524001c026400c80064200c0e0418408400d44250501348400b00091a8810809460707a801c180c091000714640102000008031080303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 469906672 1250 469905422 469905427
    0x207140d020a23070e0a0c14030604091104022a0c0f0405150a03030f0e0121050601030b04091a0114091b04090e03091516061109030d050c060c 63
    0x2500030b441d41c80c0300900801c900740002444200c2c10031103c1c3c0c80d0b0810301c104104e900f581e5480c1c11000035001e081d156480030516120071003000502c00c1410703082d090040c9040702d14544841040c030004001601094a44021500707560400e9580c0d030004011403e043c3c03403d003054904a000b98920344000760544c510759031080b01039914548591044420382d55003100c00041590790000079034103070007079030100076484690000088100f503000400c40c04490303450703600c402d541c1d420745006489000340006440d00c1000b580802c0d100064468200a070701c0700040c500450381da8440c0f400700341600c0c8000001c41f104850360b000760f000c40c840c214a02c1e005045003e501d0814402880205108100c06844407601d000c50844124810020b6801c540080011580c01c0141c0f2000302442074030ba402c02e001c003d00c03a6200320300890f00312441c43e0a4403d85601010014030340034255580394020884054000e620200500244095560a00020088200646400342e0301c506400d41b1509040c0020803041560005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 469907922 1250 469906672 469906693
    0x1302030f1b0f04020d051f0f030201120c021612140105071407050a05150105100c050d030e010b04020c07152f0c130b01020f0105090d270603020714 65
    0x4646100391500540b03400c00707118200e50204000c0e00c00e070311450300b0150400c018403100e400c2c0007045c000e0030300300714105100303103030b190110741c1560041ea200107030004100410b103401c90806580000640c0344540119039403c4024075030f6009440a99216455410721003508006020031000713201421071040000700101c2c03406440c09440c0c2008042448081200400d0346020031604000110015401000316690b911600c04c13895030032842405414082d40710880701202c1c11b4000c040c944000c981c00f40103081c080100f0bd20480040100a008084a6494981c000b450751118802050b040d100c080c0a03141c4141419054031640c0000040d403410405612030241c07240024080184500c000c121440f007a080c4160000f030315100d40900c107035511801142102ca98030000d0b03401034049030740a8003501c121084481050b800c07610216281ea455412250440d42400d214070884000d000d6510940c44042078154081503244000da045500480d0340003442809101052441254080740c910040003000d91 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 469909172 1250 469907922 469907953
    0x50a0b100b041203052104060b0f060901020c0105180a08030433030c0c060f0905070909050601031b08030c0309030709020a051207050c1002030f0a02070c0b031009051302030f 77
    0x3e140300180c1004030110b00143c2c06159a40514469203480d8542e00307031801c2c982030110040c4070f42c4014600c10400b043c81c418a50410005a605121050300504003000002006603000c1e402051034a5502030340c0a2403004030340d04c1039402401f4009010046484074100500300c108429034003a446584880703903241a15504240c1d1105c682c041a91801040540348036a00ba10410b14005c0024103083c14100390001441071503016038043c0f402107044502c0ea580e02c0030440e0860b0b03601d08000c0d0543e0003400c01840402ca6501c454580d03228102c54440c0d016540714121400d541016059401d1604009001c0a1502e02000840050320600f81e045180803031425015025108160481d4101032130000003c1c115030042064502458000b01a90f00000000c0c168400940c000c131842c5140c80328070340204450990740e01c01c1c1d0300c003180e0003060109000e040c07200190090f04002e01094400080e00d102046140d003901801740203e038030a04003400c01402c1d1042509120208034403400301d03403103031240d2681100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 469910422 1250 469909172 469909199
    0xd051509070302061b0102160f06050c0306010c060203090304030b040c03030f0203030613050702010f0c09030b0109051e0a0f0c08010501022a1c0204060b031801050412050c0a050a0b100b04 83
    0x2c3c4110100c03060f02200c4201e400f900544c00b100d00504008c0f0b044030144910032414a4605205000401055440562052241c00180d60079400036070b1801c4c113480012016402550403800700d400702c0c1e042035581d9944010150081300c1c121581d25014808108054110a0100250140340051811403a1000102d00030000d2015003003a91034450300400c08440c001e40c0300c0344c074041440c4418482101a1031018000b0000c901c4100c0e40c00d40701100000d1081450701c120350042d40107006054140440c2205007a1005001d408940010798811079014904034600c6100c8000000e40c80c5e1481030f614000000e81001c03805120f0030b865201400b0070700796040040304940c48070f0b0401c5400c06040d04c104921482c48490000b4025049490079501050045101c405544a0326101300b9203207103401c1142540303007603a40c191030050403480600e01014100740208043c0c0300240754442201c6940d45107403209850320004080070f95400301c9a03001c0c01a9880b40d9854200500b80c05070070103103094a4114070803d0361 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 469911672 1250 469910422 469910437
    0xf05010f0806040905071e0504090c0e0c040b03160e09060a05091305011505040c020a05060c03131506050909030c06160c0b012309060f0f0303090d05150907030206 72
    0x490040009103440d0f40f80d5000900058018048034801900c654690014000303070004901480d041c04000100d034079003400340d640c40a60244039190100c1c034000503140309141c041c05d501c0030340070103000100d412141600994442e05044080d440b14900d562005084185100381e128024050001000001c2e2903104e8400220707101518041103941c0d0300d200c400a00c0444074401405942004a003c8041500445110584034100c81c10444041441c406a0303503501111700052841d00314900280300d2074003a4002d1a0302050300d400f4540455130998170300001c040e0144081804903524070b0705000504281c0881584803c000c0c005518049986503015903071480107040d402c40c0e001d0700002c1c0340d103a07114011140c8039603800040e5403c030703584452034800c07141e21040300c41841ca6124815600c81c1e280000e0f00c80c3c02000c000c3c01e400441c0201000748040c000b403200358150188001c0081349910340b07405042c1d04c0b605008402800205c515613003403220350080603000d030b10f9540c41140e050000d81e56040445522 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 469912922 1250 469911672 469911677
    0x12020319141209090f0114240706020304020315101401050702040c080f0c040f0b0309010f021b0c0103060312030c0c2f03060103020a0b031504090b1f060207090902040e010f150f05010f 81
    0x1231804500b07240c91210101c50509222900103d9007070b04110680e0041c6004504c21401c0d03800d4000f000e516411401d000700d07183c0d8440e402c8884104410407001000d036001807018505a45040159004207091707860602252000600c08010490503280400ca8160040d18500c00b8a24003494408040f505139100d000c0c0741b042002c00004145002401d41c000f1055880201c002c0d0340341e0580410203160060b41520688080c010b0010044c0650310a1060100362940302c0340e50003152a074410200c0090203405034620600031000d6112001c0303942d4040e154102c03000e000c9195604410105c0c88852184030f29020f034000d5100e480148016a41c0c1c02204d015074014101146e141c1d503c0092544200c1d00c440a90de40003440c008260041c000c86840541c4a142c4c0c200c1e5000c03031145072204d0500107102520440005800001c400d100300c090340e4101c14481d40c0010008203002d0040e0f0042c81c21600c49600505849039500e014207a50074480400400070241200d07800843c0d40340c0380020b06011015040c4404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 469914172 1250 469912922 469912939
    0x150e010206400609051e03030a0b010e031b0102010c05090303030412050729070203031302060919090507020f0601030f1506121b12020319141209090f0114 68
    0x15400c00d00c0d0502c844a001119000700d0440e402e051000090246280c01d441501400481c00c00340c4020074030324642101d003000210300c1c654aa101c5000148580c0700740904015180e0410861075404000d17507903c0740112490100030a95500000e42104d020114590500c64180f10000c09950007005480d80f21b9044009a05504103d8400305d42900c07030041c00520310307603843c04001ea91944240c1000c1582402c03c0c01182c0c00d1710f501e0700603a500d000803912000303004a144503203801400e043c03010f400888400b1b4440d80c20041c1c40f121441c4514401e8000084041d0b458007007000c11030b03042041960f04464100030381019411f40d03e403054002990307113019241c0c41c215242d000d480b03101c682c0035500030b0000c2e0203803000f0746c40240380c4240f6051140d004d03000352a011800c0462016035400e20904084d03401401851440c00c1c140b4031040c0d07080c00007800d441410b66014540304415040c409010403420004034607554100000c02c000400f4806414040f144c0c03907800040c07141d00000c01143c00ca1020854040c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 469915422 1250 469914172 469914241
    0x190b040e070c050313060f030e0a02012007140306010f061e0507020402030103111f020705011227050607051624180204050c0a02030f0c0f0601150e010206 68
    0x75204101c2c03034001000c51000040328000c8180d04242c05d004d5a82507501d41c44480c20910003281030301c1131030f014403c81c0e4000010340700056000700c0f298001d860301602c030f12188030a000d2081d030820307010340c0c8240800c0c5008640c46040d460207101c0306001d04003c0b04514903d0b03003000e500801581035000740700524030304007000c0e40205014170152103106500503c2075640e50785902e080c030303010712417621030501071559003c3e0b44050340f0400000b030410705450742c0102462442c01004441d4884034504094560b503071600005d05800c803401c0030800d046c050000d420311450032890501d00c0c0c4200100f80744100502800b6110f80c4014080d0700300c00d240d400940c196850060301190701c04105403441c120810502d0310703115900411030041c45122140c021074041065075101740400b0020300c9030310130140068104200017801c80754a075010700f0402241000700d490118044420515141d420381201a86000044030b0886c1150700c0080703010150001c0c4094423650400d00340c0000348622010b50806180118003405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 469916672 1250 469915422 469915427
    0x1501061b0b010323010c0815010c05030c06011a04080c0d150501180b0102010506060304020d050a0c0b1206040c0918020c10020405090f0408090418150b190b040e07 72
    0x40400340e00069040c6455950f85040035100741c0d1001100501e4540e1020002440380c103200d00f0300c9030001a01d41c0c004568800c0c110340000d5840400407818000110406804620100b010f040c010300420010041541020165800001090200780c07503040c0801c020310000c0340100390341074009815511042c04021324501760035104900680084040c0c50a000001c07a414012049549011010010003c04107110300481c00ea03241118070320b40000040000c180103040c0300c0a018043c0c2c3c018815520004159507420482130280e91104280071740c04160641c4403c034404840d6080300088030200702d00f00030810003501d0f00c1c1c60b920030894940d904040c000781180d001e404079070320300fa000c8041d504400d40391944a00207420502500d801041c03001c000030060b110048269020380c1d0402841f50070312030200b04100280150364010109038108102800020741c890745800300440c8040c90101d0004200001d0001d540d41c900c0c1d00c1d50f00c0122aa00c10000440c0303110841d001e40744001c0b0b01465503a0b801009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 469917922 1250 469916672 469916717
    0x100614400902030d171f1403030415020303010603140103150c091a0c0d0807120c03090c061709010b060a2a12080f010b040b0a02100e0106030302010608150106 70
    0x703074044c0201d11401c07079940e80c41001034a0a000e0030406926030344a00c1c680140000000717403840d4020300c0c40c03c01880a00103225602d001410001e0844c1d1810341c0754071b80d42a1404a10301150f01581c0084010b12140b600346c000d030400120300c00c1d0103d5003589142ca5040b100f690120080d0092a903c0741d00c1891135102c0d0090402402c90310210b0380d16030103114205107a642c0106c2196a45000e218140d10f4020b124141007401900181d4403038252180b03100c4014010031000c0052010b15649101340000615926201001001c1903110a180110b00628401d002a4010324501c03150b450034601ca41e50380d60b000103503000a4510710386008107003030164403510360401c105c20351540c4211040d41e2008111901074200781c1c45040d80e03101405c544924002020100080c014844035a00c1480f09200744211200600449007903881219284200b5030380c9e0204075100c40da4511002e944410041c014141c090040b43d00a001b100010040058003020028001c00c060250908101e411542909a4900c5050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 469919172 1250 469917922 469917941
    0x12080702061e040b07230a0210030609060b0c01182003120f1309110409050a140702070816030b0a1d0303100906050f101110061440 58
    0x85459550751030b10803024503500802000c85014082c03100121062846d03014580403c00d10800a12004c440c95003040611700321316001400301903071040009003800d498011480145150f403502542c8082801c000750940d0203d88010ba4040c9030450710200003003a0344403100e10826004c200601c2c0c10314400011342484001c0401e6211a41c0108039a501e07407a07000b00511808401d514035090080c1e0300c134082d1080e03c20300c04110341c2a00003400100240652504119800341c4070002c0095442a245030344e0840c41000c0c0c0b46030005034014201031005600c0ac020340c4a05403088002e00da2500d1640d0b0f42c02d0741d032000007407509944030380742c1d1003110b100d1034000250f44035103440c0d101ba02d4582c60100c0006441d10564458009002d0030040c0002c0d140c10324000c841c43c00440039103442a0882081c0701515642000074003c929407086420240400c09a441000041c2c482c00403200310401540c010400c51900c503d00250805a50000100240030454213080c0020007a850078039216548811082c000e041900e0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 469920422 1250 469919172 469919227
    0x907020f0f01020d150303080a021c0c0c03031514040c02070b0d0516090806040b090c030712050d09060f0305091005010801050406050a0c05041a1605060f011208070206 74
    0x2801c0e6030141042d0081c2c803c001007100104090050444010840c4c04544000341c04a4800400f041060005030000d20801d01c0059921014a81d048403040490700a070003d40c000070b00214198041580c9405407038001d1701d4032420b50020311b0802641100303203c004030810f8800e03075590182441d810300070301025000f03101071201d1540703e201c068183d50180030101e91101c40442401c81071902140140b400d68182d0f21142e00400d01c0303034ad6903924801d50030805055503265220301841d00c40c080d982001820058030788801c809a144611745030403850b01046407912002c1c0301c8034903028404151301c000b980300c0e81005868042415100c8051050804400080e50440f49041400108407980150016170240c1d1003407400f04041e40e10420800100d40110170b001d40003c42c2080f0801031610b1018410020141b4040c401d032500b080058214a094100001210650049010820b4a903214480b03d0f0041040300008140c6a00302d40e0381200d20701c01d02c40000e104420125102d40d01c5055005100700703c03112030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 469921672 1250 469920422 469920433
    0xe03071707030606091a0609191d01170607120e060a0204032a120507080d09060818030706020a020309030a0303060906060e030703110d05150f01120309050907020f 72
    0x10031030140c0728003240c001070ba6624207090002078292010b12070a0702080202d26103142c6828100704211495200d40340841d0701500c1e01c410000032040001b08500103010800340151190281d01100c0b0b5030314070580c020a9480c00d0880711400c03074040801c4065120f0310314a440c0d201c0401c001c0d075800c0201451130b2000c00901c80c01e01040401c0343c9a03401082620300401d04000c940035074000b41d000d1009021003c0802002d4007500b0801200d01d500c3c003000d110b100c0e8003610301140d00e42d9442450101095200c0c800620030541c104407032900103408580040200303100340704015145039010381d030b0310500e50014411a030016280c10715034030038000d0721008039008042e01e1a810507030600401810a9000d80c110385803400c00c00065503401102d01d8074281d0000b601502810b491500c1380211995890002d0f9040141401380f100060414048030984036211307800b038851401c00d1440c104140d14144c2000110041c040c00a80109400000302d90482d101110143d020360395a600880c100300c030305582038140d48101c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 469922922 1250 469921672 469921709
    0x31e0705040501170709051e270c07050a0312110a080106021207050703120903150507090b0903101d030c3313030e0907120506040b100e0307 62
    0x20001d00032158266107040310700b252001e6002c1c2c2c0250656045000c03580301c000401c814145070031444d494404404810740c019540c4c402107250301c0035854100d00191049025106240b2951880c0c41d041381400d603502e814003c040e990b4598590b00c04801030b003405100c0c555010b0b482c415400a03280c081d40c00701215140c20750600090100300c2c00b03000f608058010360600d40b0061958070103541c0c0164101e0300628840746981c98640c4059041d0040c1020403501c41e00110200c2c03003407a03400d01c9000703c010740000c0340c4c40d103564020841c3c10702d6006038244202c02c212002c1e1590300000d01611180f02c1e06c6001994030417010b11101c40d0140d4884680c550b0002103042e91321503034041500040d0380c00041b0040a001d0b00e2618041602066081042d17000b659500850032112034445420b02881c882e0230000f10220054000030304000303044820300001401d01c030380051288810f000d4035422001c1524207100c0e02040a000407444030740f801b500000c0007042405060913239802c0014000500c8480503174041c0100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 469924172 1250 469922922 469922927
    0x10905060d0c0303030209121903030906180c17160902030612060702030c120301030803010e0c0c100204060e01111011070b0114030f1b090a0f14060103180b0c031e07 73
    0x480141184950440c02c5144090000031039809401c0f80c07001d104603e4027445581c2070f00206840710094a030555070340403075078021000c1e07120300407164000c904c0e5514452a0024102c002aa001480011031f00707d40180c0c410701c0300038541c8406445452034050303140e6541401080e0340b240e07000c5112000b440744130244100c240e000b00081c0714400c0f40c0d0054583d40400800d003407105110078400103000010030401041940c845000094101c0c0e11100410f2402d0010600f01d850140c80c249000d4407681e00040400c030180d084a841840c1c40800e0800c1344444800c0e240340d07034507400c01303d48030340040d80c460a044100e5031208048480441c0c0c00104900c0a50b11000701010301001001c0700760003031043d040c1c00d00c0503000c00201d054242c0e07165800600301c0700340c3c98140106420050700003001152103900240c1410a00c3c0100403403290b149400020310700c1c00398001401c0e10100a02e2003100391070820a940031548080c04541d12940c92108681d481e1107005100301918414501030100e209030310180075040b607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 469925422 1250 469924172 469924177
    0x6080705040e0f1515010306080606042f0409050a09050d05090f090115020f061003020d02060405030a03030f05060d05070308071a070201060806070504060206194a06010905060d0c03030302 83
    0x6045c40d0140a0b0296150043d4115451409580e400d0352021000885034640b0b84c00030500f020380000e00d06080c0240c44590490341c1141904c2a403243c00120b82404152200c0c8111540010041814010454291641621002d0003204d4408000c6c3c00280a04980c0762001c3d0030000c6c0c04e000e00302241541c1c0d240303426408442c01484450040c043c1800306a00b10100154050180c0c0703908002a0000f4916820060710010075070040307801550a00c000101c95800744400080c1d14003030703200421728141c0d8448100c1280c1d0020800f40c0300300000c2030390700c000c560300041142c1920340c08510195141e1040c2011a207507140d0b020210301c100818000c0020315903041d08420202c420850840d085515040400c1e106402180203440c01030f444240041c031075a1014018405010010000291500c00c02d40000c00380c1841c12055049151010315682e05404409c0300c0001b45607450b540da8011030110321940d52a41410701c2031403001c07502c0d4000325070700d581c4040100500543c4031142d5440150ba901d8045d0194 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 469926672 1250 469925422 469925431
    0x9120a020f04020f04151205040f050606090c0403030e0d1e1e020d020105090f04020406030c11060708070c0303291f09150302040906032406080705040e0f15 69
    0x4196201d103609003410700d40240e903100003840c070096003010b00700004030403180e01d03000b400720410240319040d0550442078401d40740168081e141080c901c8070b40341040d0f03180403400f0300344601402d880303010446c02e2a0408256000e495251804200010030395000880d951541741024103002d03e035442c0c2560310300b0f2600000b40100c1c400e104c5002044600000d0b5000b0f0b46075858041c0d04402c49d03410306401903104a00514140500414200d4500d00050201e402c0382c10681144012983d10f0740200b40301074000342c2c1000b40008101c0100b0300340c603044100030308100c0041d10300020b00040c40c001c0d03c1054001d402150604100e88031102d11040c000c544500d24210107903809000e48182d0b481d900340e0614607480b412038141c55440d00303641035107402448031070b100b1a807115000301a824400401c10320b4260040341c0040d802640200d4820501d01d00c2d250300710401e4100d440040d03140c05001c0080035400b1403650308036101100c001079a104010101c0742425094944841e0300e0040d8511101fa00b1412110382c1d024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 469927922 1250 469926672 469926679
    0xe030a021c05030714090d150204080127030c051c0e0405130f02090a090b0901050106030e16060c0609081b0c010215152103033c0a0209120a02 63
    0x41c00500801521140720942c0c3c08000900d180d80c440134500344130001000000c40c00f9110382d0901c42c1031346a40c40200c810040302e840742c82e00028100254a030034011001078420b04401030851604028440c1e184180302000141844900c5103110284441030211543c0110b18030620501901ca02038024009105103100c24842c0e071a20300403591506082d07200c040c0191348583c1d001c94241c020380030060110303401060981569256401c41700003421454486004030710307110010881d035050403c0170b815a40720300450980d42d03008100107804c1c16941550b40b412503440d030030280400551810300401800800300040c2204100003001542050802e0bd010003d1082c0400d50306281d40360307001240c81d150041181c401e040a058003180b8800c6044154502c0108000c04c1c02c80070010072000c162000c0807003403076100641c2010041140440c0034140748000c20081d8031841c5540001d00c10b400540580226000007410144400034045520903811101c2c40302c0010001040c042c5060f28581d9980c1c201e400c228003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 469929172 1250 469927922 469927963
    0x90b07110a170d08100b070305030406140c030c2a06070f030c02100218040626010b0109090b01020a0506150102120c12070807121101050717130302010e030a02 70
    0xc0b800c0010203011403040c00e03070b00500110600d4880458841d1400740c060503450717070101070000f00300502d480180281131084e25a01e032030786082d040c92801c4035507105c11548091441001c000c940d080c880e040300c3c4d000384004482500c920920015020481c03054482144100c40c00c44404d401c0000001c4040c400c8180d66180980c01861140460540381c0f410154000b682c040c141049182400d60050110b044081040782e030b04004090014090318401c1e40899003d448109030700f81c6d1860302180c04043d6802c001c0080c8150950400001c103280c04600c0303030441d6507545041503800741c0c0c4280014140f807a0020200d0b0954100113480b4880031440c00300c0b00e40503114201d07101d4001140740041c0c603200b030009000341081400c1c01001d004c00741c5c0194800c450a03801000b0900000d00d14200d900c0c0f12903030b90741d241122895103c418508552001d407400c002d110441c6e00c0030b0b8406401c81c1c019544910505107060004901e46016805421380540c5082c0314000859000b03002640080c08a21424040400c0103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 469930422 1250 469929172 469929179
    0xf0209070c0803010603091a010b0406020d050c0c0f040e0f01050601020c0301050610080601140a12060501030e060403200619060608070207030206030411030d02010b0109050f011b0201090b07110a 86
    0x1280365801c110000e1a00800b40010810a4006c0d070040061500170309588104007050000c52200040c01d801c03e0f070076130030041005d1154580c1002108850240750030b003903280c030040c0b0400d00e654118031140180318020a0111441944458010a40c2c400c0100112109d031101542c04030301a1904407002401881a184801c1e1640340500505010303007400f134080d80364006d0641e0110b591402c0144071a050150040c08076200016810040070700302e801d030b0b503241c0755050071158035000d54010b036108a04040c1450f0300c9004090010075215042541801d04e90600045410048500c060240070071130706005000c10060040381001406845030300c504810020300b501c461007900c00000c02e84003980140d02009040c001401c05600450301726000d00c00151a10500b0000a4500550361004100507511020b00101c00d5030403d4114000c1e2004803011400700071040002800c400d041074504000c100100c00000559014504e048003511103007a000c0d81d10080b60800b1004610003044060140781e81d040d000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 469931672 1250 469930422 469930427
    0x90204050705130e1e070201090c09020a0e01031d2406060f07030c05010609051f06080105030d031a0406170c061207120b032a09040804030201050a0513030f020907 72
    0x40e14081c00d2903d2112282d400d00f110080c1112004050003881429849050a0390780e0403803d2500c900c1c0360b81d0010514035068a882e0315040103a6100b00c040c0c0d4010710240c40f00c0c50700640e0030715642c0f0007843d0004d41030000c01c4044041c2c58050420038554041e1003190954602d484110043d840c0a102040c50113803107000500c1700c0b43c071408000c0c0c21051414004800000d2048091031030460054002140301c81d1189038210407900709860707408201d3381d407500580b0341d0f010303110000c0001d0600d03040000d0150b1401010075200c41c0c0b245042400c0594403000032000c0f00c091410b03407000b45400380041140c107489130301e4075030340000c40400b1a40300c0c41440090807803031808001700d80c1403107401e00c0001c009480c0c20038156000c48811111080d5a03440303540c0101e0b00c0d10108103100801d14503001200210400c02524140c2c008542e10441c016840d80d020400401e8840d41203904a030b5081c81d02c507507198071503030003254240501e200540010070723822000000d024070034100a109500032079104d0910340720071009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 469932922 1250 469931672 469931677
    0x30a03150302012102130b0301031208090607050d0e0607080108070b18120f06090d110714010c210314072d2303010e0606030f0109020f0903030d090204050705 70
    0x3d0000d184c00605030300f0120702c81100403c04400620250408081c83d466184030b0203d9001480d041001000410500621811805100d070050038003c0903401c2111805444181c0107007440d050000008115003680c08580c0088800d2407610150baa582c1410000100301f0002845060618820b510f8003003012000f140c1100c45007602401e14103881c140c00400d03c403140b03030780640142c128000c20313901d407201071014081c0034840c090034000303000f1505030004098a1105ca04c4030300c0b126640072413000c0c0580046c8108406445d41c0900341119600010300c1d1013034003044080c0114480d07008446a40e2a801d406420201940c00e55200c050000e90b90b0402c100c698441d0000041c104c80f02450f80d070080c1002021079030b07041c60030b545850302c0b00c1010f211280901002c060070000300c815001004000340e512010380e031600b00008035a21751841c208441c54080c0c622060044503005940064488a040c8111080320fa4400016080d40e440756450710031300c40240a44402030b4051420000082c0c1d02074800d004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 469934172 1250 469932922 469932929
    0x306090b012403150513050402120714190314030405010f0f0519020f030412141203150d02120102120a290a031a070207240c05070314030a0315 63
    0x58644902c00701c100120302804420800000b1302441c50000300311601c2e5001403002e1148844004501400c01d481445000c0d00101e0400843d50401e607011305c0185501900c8840d9044216440702c0d0704c014802025884800e0790707100820084602c000410510008000360088174802d0b211005580344086c4256034820300030501100040c420018100c1310f0200300da07603070007130441b5104444102248e140705910f07540c000e0b000050300340c41140d03601041011b0204644940584e00d005000041c2c40c404c0c501203140030140c44404003017080b0201d0401a160322003064049034005100100051649031038600170f501101e484d4035114150000680f280007540142c1e000304084030031071080441220503116481402809a41d40501c0015001000c10025400c0303121403141e2024461180c202030101900c1c0c5892584070078401d1000015a02180180c010030303809141c0300d4180ac13112001a8680907040ca10143c100810740e9034143c0c4130441821000004d821b44945075181001000c00c0500d52101e00203a522 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 469935422 1250 469934172 469934219
    0x30a12030c030207120f020a0b090f16050303030403110307021c03020616050a05070c0f032a21060f0504151104030510021b150429011502030c0102040306090b01 71
    0x40d0400061403040c00806919500c2d0f1040e6072502040f9034465a49040170b4401200c207500c010640d0351030781400e02106073301e20601c40c0281d00c1c01d4901340100b81c903400020000b4040c0010b0180a02c01941e050040f516256402099025444200c034101c1e52500c040001c20f0300180700e1000098429180214400807401d0709032909410a00d860804541940c4200c10484030400741c10000551404480005400f9503ca20394510010500004da0f01050210980c5040c1051036080200a400d042c07240070005201d0300408050048031609000c80600108088403c07000d180004000038424905071503501c404034032f0401c0c02081115204280a40103070300019000c3c1e0040b071502c0611054660003448941040b4009409010ba428606030400305c0006400e014140100104810041d00789050244006000064000840c080f5180c400e404814003a0850800310100c3c400c40090007002642e501000500081d0f6440780c40c1d141280207441001c508459a000d83d10000ca14070045145442c01002a134 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 469936672 1250 469935422 469935443
    0x7050f120c1c15030b0a0f06141f090b0901110604062a05030a0c0c0512030f0a020403031b110a0b13050405060d110f130e0d030c0507060515030a12030c030207 70
    0x180ca0f45c03003030101c0142c03131380c19190790780e00f90b80510359031600505001301400910b5118005200090090516050741802c14107181001300b441c255400c040da40b02655a00c00002d62140303e840f0041c3c803c2c407050038210480e031003800100000c0155503081560802c1c6814112081d100502019504001075615002d011842c14400648030b051990300880048000d45401030ba035524585907503003060a214045800e510b400005c202100d8210309a1030f80004181e4801c51800d461910000d080940c0b800e078101d801070141700403070f00b400140f000c3c1c1d280c10840100302400712a41c641b00008141e0240c0807034080750440c0800000c151415109052203040050310b01c0c580d2140554800b12641c0d207240a89900c6021303400f40c071100b81c5801421603480d103801c120000c0c40c09000d5042514150000303003180b04150800c03c111300070a502400f919082c907400703d40410b02c1e40300d0102d4140204030b000300c001d40600c219001c0d40180910ba9006416440440d181004650407451045040e481803040180a42180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 469937922 1250 469936672 469936679
    0xb040b03090703080712170403172e17030f0306190306090309060201051807060302090a080d0302090a060c0c060503040312050a060f050d050607050f120c1c15 70
    0x410011503104100d441035511140c1c0f41d070b40b21000e0341c20050040e600e5060b0302103e2001a500f100900c2c50301101c21042508a2910b503400403c245041316211085813510004510b094441c801040c084540d00d01c40030100403000e000112024803244241c188100c2e030f100346526125000300455a020f20718402d01455951100280300c5141c00340f4240c0c0039210200c0d800003001c210b03030b413041130480ca103ea5180410311385010f80c02400d480000d400c031140075a08040c12420303841c0002d2010204c907550305000d80c54007014400200600c0e080d500502190154107016003043e645903005018480048503034000c07581e19030344101e03086180d041d0010640720b41d150040c00341c140614080e6920070f2003490320300d45146003480c0e03440559505032103240d030490321604180304400c2d80403460005004252256501d00c10641c07036080d91a00c02070100e07024010000340c0204209200b00460b40d1503021030003400600e09001fa030a07446c44d8808040c44281001500c0100c10030240360040c000d64170422110300790310505 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 469939172 1250 469937922 469937939
    0x1b03060607110102030d0f05060a0914042904080a140313030804060b06070c03050c0f0303090418050a0308070f0906050d0c051c020301031103070e010311130501080309011106010b04 80
    0x3610ba140d00d056220030312890101020701e000c2e191003140342c0c4801240340d040c0704080c0080c4003515001001081d0800d107105035040044180164415003107101c0904d402e03145810036a03240d01027210104580c3c018800c20041c0300c9040e00605083c0c0301c40da28039141060403d003220a902080c0c500d0b103d2026082c80a00c08284a07511482d0005e003d81c07000181c0c0d181540010301a0b81c400340c01103401160303421040040c0138080c442040004020350360f6440210054002076140c1c800d0a540070321407a504c0c000619030481c0c0c27140120039541c0c030600322040f80b441420702070024203040b038507100000c1c82c103140282c000e4841c4412000b10340681e00c40702c0c14403251602600240030420800000c20505006030016001e8120844403d41c260601c01a80d07035045090400400c0c0c0c510017164005d80c042c180c100407500c3d25180d0241166001002c0703180b0704c4003c0300041c035450b9110801500403400c0400109180d0030110050105c042c003601c441c000d032084c403404180c55500034442c1d03e140c110103000c04c00c19103e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 469940422 1250 469939172 469939193
    0xa1106101d07092301091a0909040f020d050a120912110d020a1e05040e070b0309030f03011508070801031509110a080610120213020d020903151b03060607 68
    0x68250500030010303604c400c1c00d030203840607901c090744454042c010804055604000380c1400b800c0041601d50740403000c000e03000c007148a520b07200e50084070682c0c001000e005241c1806403605030b00500071b01c100c0c034150402c0340d56604151803c0e1140032020000c224094060041807003110354283c180b40358514903480712420701070502d20458110104281483c01640c800d89941c0c0a403148415003a03e9003451000b8525a000da500814007841c9400c40d0000c800c00300241c410308403079400392125501d548100c115402d501070000a000c1044001c00082151469082d5401c1c2c400b00f1551100300036950800d00301c1d410035080c130014245054500303914140340d040d6040040c541d4060084003480c441804082840c09009038040080b40c0c104000780700b541034501d4a1407000341032950400c120100941c0015909222011320408080d81c0020044440511038042e546002402401c1d151000c0405a151505540450b0300c01000340c48409461400c42c04c4406880c011a000303000141040d50b00d030303205e4240d06d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 469941672 1250 469940422 469940431
    0x106080c162f060322050a2009090316021e090a020c0105070c0812100521010e0304030c151806021b011d040504020f060a1106101d 58
    0x5181d81c41c9002081d2605110441e030802064919982c2111544150560a1609100307204080c01c0080c00342900504030740c45001819410443d09460b502d2a205140c81c200340001841701d50451043d01e400702e42124581010031054803408100d90b1503000c2d80c1c4e00c0344112100c1000c1340d00c0010586016061400c044064094030b000704807c21011b041c00940417000442e9001e401d00e4002418450703540e42805041c0d0440c0d00d0b4200201818080e503960070b070500410030050707212540c010010301c0101500f1a02c0c0c0041c100075060048410701ca080c2003c2c41510088070040560a1140032009188004200c400f207d401009213000b60381808040c0d0042440c0110a01c10024420611180d042080e06044002e1805800401948207540141000c00851850882c140032003d00c0d4aa480c1614604407480c04c4001c65001482d0f503514400a06400c20380a0f40c29000340d000300d000340d07145030821012132001002d482161300e00d03500da294002078850940901c3d1812011080c00e441803011901510381c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 469942922 1250 469941672 469941697
    0x6180c1215031103160e090309060a0c0501050106081513142a0a09140103060f060309060506030a051207050109050115051f0e010507020406081b03070e0106080c 71
    0x490040080d940c159500c46074481810301c05031000700208021500c1652000c0c0040c0c019150003508104400504480c6200b2250350000e1140041d0f441b0100303104031000301400074000c54480c06c00345002401c00782d810000302e41c250300e80800425682c3c0103000300c2c0d00c29042c0091000c25070040b642072141101000040050458907291008001d242c00c51566114075500369004e0b1922400c0c40100c1c1c10320b810850494906a02042607040f02941328042c0010f42d8207030000c544400e03090400413401003070142e201c02449110384c47d0225809a140e00040945402000213000c80c0e1030341c808040d00c9200425006107190700c8a8101100c3c400f07510b0113006c500d80a00c0c000210700c6804d488041c01d40b09030403060443c1c0030710607405001c50302e40070020f028196072401041c0040c0d08540b002810346942c200446051000200c0c2c403004555690304160003425030407090310f1017103400540c3c0984410341d00407a00e02c40e006003c4045080070341107038154101c1e8466034980540e51154410720103550f20105a0329407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 469944172 1250 469942922 469942937
    0x290616020303090a0806060a060e01080609071b050d091a03041112030309030a122921030301031101020a03090612060e0708220b040615050a120b0105010306180c 71
    0x203903441da510440202988401b401003032402c0d1013007020307092403a0040000d20503a100030044590340011540d51108054940813110b071104441a1f4030050b07000d080840b13414a490244040103004a11601625004c0e01c03000c0b000c03078544041940000000c621f150705c0c00400d00006004c5a20020100300c4210068400c000a90000c1641400c0d03030310072100801039500002c0c1505c64661b000400900b018203902c001c20030326001c03610320180e0885011071044140c0e0309200022840e80c61070320400241091504c1c09925103900400f85444e60000d1100759400e001400d002825540080b80741008a03034196070b000c06050030030005503a113540250324816203a0b61588041525030b030000304940a602e8030b1302c07204c50310b00e4508020380b0480661051107001175000000ca800095110000982040c2c4c00100414084d6020790f6240105455511044d400008010005117901c0304144a000641c02141c030b40340b0aa0b07ca60064080c0c0780c02d413280000f260f021080ba4059150f05900220a260140c1791090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 469945422 1250 469944172 469944187
    0x100f020c0d02030c0601120b06010e0103180b15030706080a0e0a080c0c09061f0c05151303030e030a0509010302091818010f090b0f0907080a06290616020303 69
    0x28502410744001d04003590000903008241c8108000043c01002002248410b411495a80c42c070f220301c010701000e06001c04824804260b82c004d41000448624441c08000c800105090800c06c8940c19215800141800c021400080c01c000c07034420240c42c419205c80b90305403514210f80c8000c22228401001e0390003406408000900c0c071070010500000c0140041c103010400034200720f020b203409020b0620416048401c43c20041c1c0c41c0c101c1c1c2c040d581c1e060900100552050404c03030300701001100b10b820152101030402511014081900400500950701040301d0f5030310016065803407107403100f181c1c0415814408606107610980080c0011130015000c09001c8481c0c640d03500c6040c00550785074030301d108160b17040c0307044000910a40b10048020304003400780c580192100011440098a00c1003189102000261040c9040110000400f507176400c070342c1020054140b000c001d00010300034414540e8448503c010542809004200c161401008a0700d00401030101208612240300100d815020501c03120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 469946672 1250 469945422 469945447
    0x5060d0b2208030123030d02071509030606080f060903030609180f0d0f030b030303010b040501031d0d0e0f0103050f070f0201110d0f200702040f0e0a0c0812040503100f02 75
    0x5500174280500b011814140314000300d00b040e0000740015000394400c2e801400d081c5e03400100c035030454a40148154160b1380c21079044881d2803450f08003900c1e4504203c0d00054100f00001e90300d980d00314400585507151112000da40d240e00c400c1e1030580e404065171012a46810400e01a00e50725040324040307824107810b254145051600885880c07021401d100c014a80d4140c140c011045010011409185590b040c8602010140210300520341051740c0c400400c582d05c01ca00000c559000695012a948005480401403a00004041c014040d01e050011044254007a005140c022400c2d000c1041d490b07555600119851080030014000f19900c0710404428003942200078150448119004036250016500074001c1e41c103d48103900510102d180380d400c02c000b5030f200740c0d08241c1c0e0442e270110b0104400d100080141000144e80781d041d019840490041101d482d00e003074121801c840a880c10280b581061825074006ca108045d01a002028001907108140d486544542c44d07111005082c0200c500300e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 469947922 1250 469946672 469946677
    0x14012607020703020a0f06021905120c0109060612080306090408090409030905040c0e0a060c030905180a05060303030606090402071b060507140d140a020109022205060d0b2208 77
    0x1000c0582c0000e801442581010041c900c00351008031910130810303291981c029901d5140200703000591480c0e100c40c04c10003c00348a106010160003400d20780329000d842c0300a000340345032841219024500080001c400040444401c03035160040420303030841d0350f10000e101c50800c0c000c108903140c400030001d0814560340c0c0c0c0f0480554500903a6010174a5080009100480d0010001c0d5020312070442c4c0098a242e440fa2000801c0c0d40c3c05241c0700039244071030700c0c0684a000d02600440d5100755000080100c0080b2550304a20846891200b03102c242c40b1312080c1616407006882d565027151040020108504150300140800c41c41111861a02c90041c0e074400c05905550b080280001c80001e903c0050004151380d91a0107110300003d40320101d01d101020f4403240300703013004c41d8103803d01044900340e044c001e502200f40c05401800701c2c00c6000c015824400007030b0386554080181490503001c520f56081c0f00401c2c044880e4006042030007901e030000d000c0c401c48800202d40c0a09401500703400002010f5002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 469949172 1250 469947922 469947931
    0x220e01050a06090e420c0a1701030203060c071104020c01090b0f3d03050120041805061215010509060f1005160606080d0e0a140126 58
    0x6001420b0342c24022503100703035042c01841c0c0038154030000041480c1c1c66003080303405543c80007070080c5d0911091154603000d440000c80407201d22046803010490400340d41c100401540b06a5540d0003887d00f40316086400e8980c0030700001c0d40580c132007030000b04901181e00050403a50f008241c411842c428080000e4241e034018140440c3c503946811500c0204852460304540202d000c0007281c2e0980381104410300641038449414144890409104000308440741104000c40a0000001d446584a01f0400e0103410500700325124070a40d01280003000200e001660150703074105141403003d00c003103803000c1c1c007420000d0030083e8082d0300f002c00030400c80803c000030381000d100780300e10820543c503000800c61859001464071307018840040a003401035481e4203440070304e040c3b6418a16100d4446020039000b04240040080c251450320b5004106076100088a45c0f220401e65284e6442c20700400500801c064188038400160388440d45101856002d00c6260b500a07442400f0503038070a5034250b8403915182c1c10354 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 469950422 1250 469949172 469949191
    0x501080a060e06070503130206040914070801150c02040b03120d15061d19080a050a17070f11030a0c0b0a02070b090109090513020613090b0f220e0105 66
    0xc11400410445000740c28520748101c000d49414507020202504600c0001c20543c00c3c50251490801150740303188c01d4030060600b03a5810440710281390700c0003814074411707951803001c1a0310100020b0b480141d6080050090f002e5a90500030484540c21b0201820010900301c1e41401584c07101c240303100300c4e0406480c0710401d003d00410b80c80001e413482a4186107a42240c030412286400b04510310215040e650700c0300740240d400d02e00030b0144180c030021240040c0c100c18500c1c010b0620382803d10400140c400c0d8500d0003000b41c9100710208105080c21840344240040110400307098401c0031945a00003412401809400d0300c02e48000e030743e1401200c841d5900680c2140f08041185a18968108005400741c6001c2d294145000301d03110003c1c06400d400c4c403d0441140e2a640010030311705560f061032444a6010300160345070940c511000310401c00740d000384042c061400d550f588a03454449640090050007518003043d9002c0c0c100306250305050005003001071503d541218034004024072420b48284001e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 469951672 1250 469950422 469950433
    0xb0603010f15060e040c320301090b09090a020d080f0903060703020c0105072307060b03011103010e1608040809040b1201022101030804270507030510080303091c02070801050108 78
    0x10f001d8400d0343d1100c0c1c800d02807481c10050102017a0004094180c840b6020850a824801320103042041059032001c446c3e0500b02000010384c800b00d03900a103001140c102c402420035902c02c0c24255603001c03c070320f01130f40c8640c8012000000c222510000c1107501c1c0c0c030b0f5040354a00300447c00480c1c40c209082c1c50b103c00280c0d0004003009600310038803070243c11807a945440d240c070382400d04400d01594480c3d0f28807841041d000a14404100d25039201414405c00540280040000301c28485443c2d00244150917442112a00050b0074140c09041c084202c40d041d100d002040d103a603103a00e51582c120150190f00541d4072142c201a41e51804a188014201e64002603a42c0d2001915900100f250780001c4044500d1140140001040581503405584022581401e403035160400d01c041c0c8209880c1c0044018600307014060b4040d03260704500c5c8203545104003080500e0365514915921b00c02142c9095585c0c2000840b1013602c024007445d02003002c0d043c811540e540c1e0b1070750152421250700780d02109065004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 469952922 1250 469951672 469951679
    0x60905011d010c0602090f03060a060f08030a3e0115081b0d030509090f061c03051206011101140a0c1e0e0105040e0c181c0b0603010f15 60
    0x44460307600910504021124080802800607100c0564000003e103807540100303110a1076244c0218603840f140000b8215009030500c007407104000c010b1806000360f441c030780c40d2000c640b00ea070005c1203840b02c00c01c070754800305000606455800200704d05081c004a5007600e480603000b869030018243d0448540d84000070340c001d8680c00d8145c5104480c0e2000c50a5000144001c90224181d13081590050080c0c0d64000210721a240407601480b4000646134007000c3c4100780b048482244080c0f03407003500240d43e020180300704e4194806180b2403070300005001074806c00c4094481c3d40340716800354000c1c0041c10604a01c04d1001d206070309580340368040d500b0400118041000c1c0c01c031607010b003e007084003d051603180005d1085412590001c10304205040c0f000a01c08081e0f2640b15500710b900400b0229141c034500d08003010741c440b45078008080301003e44200f0b80c3c0e012a40c07504105c1040140c01100045503010401e0b5210343ea81100141069459541e50324062141c101038094100c40400340700c403105d201410f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 469954172 1250 469952922 469952927
    0xa0b12031306090803220b0a050c010605150313060605060309010911150406051e13140108010e19021c061a04030b0703020708070c0902090103061d010e09150106090501 74
    0x9182d4008010800900b404001420000c802c461325060f1405444000c816021661600c03058240c0c09001c06410000302c501000d40d001c0050454011410028006603591360108180556041d1020306200003c0001c00c80002d24140c00840d4036114000200d80305668000044183d0800c45804c0340381d94564450f81c00700000d000180c122410200c450b898544801d4108513414042c5000762814800d0002e003901c41c10100c49480100d02d03208280c00d66036141aa0b0000c0d03040c12070307403280345803006c200229481c60750b006e02080780c16030740c0da42400f100550f00c6120742180c1d070382c031080e010049a90030026076421611182c04100d0320341c401d81005c51b03558548500401300a1691440503902d080c00e000030710010340003015460300030a440ca405030f201d010600300940584103081004100d0041c40d1800a2062810307000340862400c262402c000746a81c0781200026041c02e020a070341c0c500e1035440103008400c184804036400c600d1030401c0303803c1c0300a500c00c007181502080e0416000308010001c204072079030303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 469955422 1250 469954172 469954207
    0xc051801020604050d081b03070228150c05040b1305010219080d0908090907020705030d03060803121e040501020d0c0f0e012003160203010b04050702150a0b1203 71
    0x81c40284100d10b070039158507803190700494440d0100041c500209509106040038181200c52100415a50b400c04140c0070351781c0e0390f00c0070540c608818401d0407907100203007500e4400c8506801003814000f88600141c884001c00d414081c440a0140500020812190711070140205e400303825410301c030a5060a001a00e0020300211200d84590328800980c0000d400509803501895040000715540300b20380307440401405a50710759a013001c01c8030104415150b0010701c0d94101c0340c040d070aa490b50885010704806440d014018240f8950042005001140201c020564032540308420f40c1043d20502a403002071481c03d84040c0c90580d0013045e00703850b0b03007964410790503002c01d142460000d00d0b420000240450078502036071810b1000a01c21002481c1c400c800e20ba40300b004071020307641c0d280980c140d440407610407404160700a61910601000c2802c1c10f100f414051802034000381700f801d640c44525031000c0c90050101c2c1045460302c500c112603407558500401c200313014402540d02e42d008200c64102c0035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 469956672 1250 469955422 469955467
    0x612050a060e030c0a08132903040f290108030901020714190b03070207060c11100215090d08010b21040503160605010e060f010e011202090307030507170708100e0a02040c05 76
    0x3102c07045a0301c8541d86540c1d23020403214003681d00d8036207a613914140282e48a01c50700c8040c10b10300340c0c40e24503111500c0308410854200c09000d4641202d9884a59040e80c901410180c1405680400d03800e100c0d0008901d2007006040d0003c09062010b0507010001100c8182c07030b80314506030a804800d00918940500c50840079218030300e424555034030305848040c900700d40c0500807402006c540d00c0070348019109106e444400d1201034410720b9030f03080c5484200e542d011440d15060000d68410001700705061300301c08a5001c60920103040c001c9840e80c00100e15404000780048801d80310400800310b814201e1800e4100f040c1c000c0b040007030103601d45496a41d2052008100300e1007440908181c000c240e8100c110003646c01030030b280403d502c00b8405860700091044101e420303410f00c0380000c000b04014002400b001a075015180b46480b0710f03541640e071541d54006000e03052203a003101c8068a010030702644580d034400b00207002c8502d4413100e90007040448106091010009400050112114805030f1811000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 469957922 1250 469956672 469956689
    0x319020306010203160f0b1f0501050906031b28090b16080f041a040927020d210f0e0d020915060c1f0612050a060e030c0a0813 56
    0x3149840341c0001d49a10402175041070690b00e82654009010301e4683c4039102c05d40c8107183e0b035011308102c80b43c146448201c40c458031911305840e02c08038080d4440d9040d5024034002820103411502d446103c80207900305410540c0b60701100b4000c40101c1d4980c44074107028106070003216601210121001031004146821120135001d0400c2925440300900c10304007000d41d0000310309600c0300050711134070829108079441012000d4502c286009140d010380010400c40f125a0410402501003805218481c0d4201d0700c007042e03540c0c81c041510701609110642c096010b20402c0084101640350340540c0354060382502000005400c00048a6403d40041c06405400310031145007407202e11030350000b41d040400400c0381102c2110313441c1d1201182c41d0801034540308000340003580c0b48516408003550310300140c030143d10440c600346400080d03030086007101002455003200140c0441c400b44e46a1101420016502d103409200400c580c40380c802c1c050048a540ca4418440d440d6200c80751040c3e04007500217a000b5124 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 469959172 1250 469957922 469957927
    0xb0307020c180924040b07111605130e030a0e0613030f0203070503070b0f0c030708030106170f01140118050a0807030515010b0a0c0302070f0b041502060708060d021212031902 77
    0x10000d0380c19903c0d59205501446d40070103540c8a01003120384000c541000900c6104050b0703006580c0c5800f04c103c1003a2030069426248004a108034902510000071501c00550420480100924403c0b040340d00c2402e0041c20140c80c01c0060001c600b00000585d00c199820b440701c12040d0300314641404244001c5c4012401010755a04000140ca840d01c5006544501d00400240c2481000345c2071040c2ca12142d001078a090312507035100c0000d004581441b414500c484040000609101d01e03010352581a242c0b220b51010034081e040c1c006441d5004084080402da82420400044554034001500d014000e0b45010300035251840c5005403400303018481c501034107221400140021345079601924100300081c50a00903941140c14160b080c0001d98019000e2403011140104040d00c0c0c80e4000c00071180c0c40842009809100304040380c49680a40d812000582c0d00380210f01c0b2440c10840701070405000520307020b501c1036000c18481c40e0419003c0312035240a03011042050070145a9640c510b4030046c0a403c0d40f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 469960422 1250 469959172 469959223
    0x8010f090b0a18020a15080c0415030f0e0a150b0904020f06070c0806070816081e1905090a0201080106020a050607030507120c0201090b0108030a090b0307020c1809 72
    0x2101c0c0c401090740c2030240d50340c084401d521907550454803206401515080c40e140e04d51022403110000319440c0d078040741404000c2410600c210701142e08541d540b9450030300501013148106e01500d0310180c610380c160740303d090034070702d110050201e144180e10800039282c7c2c06c1c3c05524010243c0d000c1f45101889094180200400b60301d440c41c3c288581803044a10729503c841910f040a5610b2140d003054445104400402c5105074014040134001d1001041450800c44511011540800101c5019604075203099010040310090a640c0c0c0c9c0142042d004a284000d040000c1821600105e0710300034654080a40d210a6503000701001c1d000d4216031020300542055500e0b03050b560a070240444042568440010b40c0c030501c1080b050510b03803c0500103000c01643c06400a019044205041d030724080c0745400010a81070000031505d0181260b04c440602070b14201c40c40b156901300820650540c01000b0020031240e4a03103105054108015088602d107040156401c2c2c031f014a6010b520599001c408405d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 469961672 1250 469960422 469960433
    0x3020c06060d0f08040e041b080c090c040513061805011d0c0702041b020f0601080d0c1406010f0e0901020301030b041104060510091712040302010c0620030108010f09 73
    0x507540a6010740d03841140148514203088882101c100c080e100200104012a00520110304030740030368003540c9070b0b141000400707800304103007409440785c91640d030300840f46c64265081011741940d00c044030703109180c1003c0c0c0d03070800301d0096080d54658a120b02d030303201018000005120000360068901080c104015070401c0200407241c407846104000c4800340d10001020003081c034089400b241d40c042c0083c002c8a400820314041c44204504010150286206080c09080001003950484a040c40100350b14406202c0540d149007505800341c94641d00c4110800340580d08100c80340c020700c881d040582d6818075000e10140b142e28041d000490503401000104046080e138260140c100c2e0300480d100120800c0741c80060020040d40d445280c0206940d640711b003180f500008254100c2c0d06441d200e680d07591200c3d50300ca84961707000301100d4200a0078001840554442d2030060510307403103200000b4040030300c45050300c4504070801501c502c110000006019108080c02030409a0f48030340c909000701c0400d90383c0e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 469962922 1250 469961672 469961683
    0x1030b18070b280e130209060403150e2d0f0f0f0d0c11010815040e010b030c1c03030c020f0109051e1b1306090524060406120209010903140d090603020c 67
    0x312445170740c2ea80341071031081c603070b99044071190b950040002d941d8075583c1c644600091403840c92500c242c0d10f000f40c0404502c0340428024682248203c10b5541d078140701c11501942859692008a244299519141c441500b00940d010032107001008024444070317460090318000405103003008204042c66440c0008041c0304c0d9004407000c090070000b10995410940000f00401d004550b5402030920183d001041c0065110815103d8280c0a9440849150043c03009100d0341103980340c3d44c40503540051003c207120307071b00106405e08944183c51030390303410074511801e4400e0008140c0b00d0360840c0386620b80c05014080c42d145003c96100c040c0421301040900020200c0f01440861302640d4090740403481c1d84031aa00c000e01406c02c41c1c01c204101d04002a46c514080350303944840001c11690140a42035160070000c1e942150903580c1c58a418204082c48840070f90440c018040c10702c298a034010000804242040c81e28000000051200107183e10b402401e4512035845031090601c100850020ba0101041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 469964028 1106 469962922 469962947
    0x41505011e12020a0509040c05010906111f02041e050306010e04050d030c0309021f09091a06390d05030f01030b18070b28 54
    0x1040980d41104440104000359514100315015403200044090b40c0b002e00000c046640d140c0101354410416142100c1c1e40710110000d01607964020b181c58001c00b02441c1091000720010402502c508541c0300c0105141004118041140295011a4028500100710345100320320700058408c84106406058424040e00f0000120a02111030030760065405c107001d001500b1103d1416002024501c02500c140b44e242c180590140ea540d60000800ad0341014482d50440c0c4084002890000c50360008001c0c1894003038a10981034503c50100044641540e596954400740350007021402890514140903d052004505403005159800000000300808840150108000944550004860451000c0440b034010004502140421b641041c0100e910079103079504030141c5800d00b00e036030701b01e8007400c5000600c0040c1d0040c0320b00071154104100a819031f12440100c4020a00800c560 = true := by decide +kernel

theorem cover : BRFrame.Cov 469784172 469964028 := by
  have h0 := BRFrame.cov_init 469784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 469784172 ≤ n) (h2 : n < 469964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
