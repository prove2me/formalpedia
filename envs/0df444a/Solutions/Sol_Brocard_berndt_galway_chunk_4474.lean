-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4474
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:44:06.732175+00:00
-- url     : https://prove2.me/submissions/f91df75f-c781-4571-ba73-262555ee39cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 804496402 ≤ n < 804676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 804497652 1250 804496402 804496481
    0x7141803010902130504150b061c0603022e1b0b0603070b0f130807030b0610031e0b090a09230f030a02070501120203100b0319050c0a030b040605090a 66
    0x13000101ca081901e02005440c40c1004450340103420f00240c0d00450f9500425118100100748020240c2c24141c01c00d5030081005820003544086078900d00c5004400e866800300381d004403800c0d501c0b0b41c2100d4403000e9925480e034919048106540c1c001a8000444426a4940017940074045645c2e0548800d440810b0341c000b424000815280800c0101000700030821040003444c00d18007900045045803120f082d01c0034000c003030314003901060501590b224460b62090346140c9533140c21001850807400283c01600c5921ba104d407151107030030007060820700b80d0320440c140745504c00b6000071146030b8421000d080320300e951219846401440c8044000410500007003405110660150142170305081c00900005410800c0703668040c418410072180c010307481790940540384147c00043c2c81c0d0780e40ea000c5500072425603030084500d5091200303105030035100a015103601d03c0036803802d0150150301018402200c1451040c00d607c003146901140d21424550300c458045d045080408550002c0c441c1ca2078000d000410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 804498902 1250 804497652 804497689
    0x13092d0216050f190b011a07060c0f14120a0b12010204090b01090e07020d0c06020f0c15011202010804020411120f010302041a0303180102070504090606090507141803010902 76
    0x3d071118044101400003525840890000c804880b8651300d0386081032105000e00010342042c2240e600000e443d20064a148580c4085c3c01d201084904100915040c1441104000310744500c1d100c8609841c0307502a501e03940031045080ba015511b50002130003803e0f0100490b5001b1340c000c0b9855070618000e00003040540701c69000452803002e4a00018514107080d8400d140d070803141e5040c08080c1e94003240c1080c1c1c61449252415060600341043d50080c4110200c001c1440710008100000d41c2c80450401c0d402202c01607180340503a40e90b900400b600b8222413001340050107500024006160540c030a1148220406115082488600022180610646000c18982d14900040045250600400c01100e4038000140303082a1414046680c078001c3c48903041c0d8102c992107000500341d100308010300050600600c18080b101c018100840102070074060070b204070b4106000075801d103008038400340e021910582c2a91070f00034891a40345803400215007080e45075480740700c1072000d030b0f031568115a036280c0d010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 804500152 1250 804498902 804498913
    0x402030723091305040b060301090218100509090c0907030e0307170f1611010e0a14010c0602040909170a02030405120a020303070303020c01050a05070e0d0312060b13092d021605 78
    0x901b80544280f000902140c402d0b0b04007156500140c4445260701049402203810720301c0c9407a41c15002c1129600c0b600f102e50800d4081041205811002449034102d1130207482c5850356032a05d017412002d9070300c42020b200c0580e1040048000180d05291011000241040441c2c1090180b20400d04190700c1081a64159800504030740302b030050803444c503054004c3c03d08140c1c0b12400c40401080c40c0380d06034411400d58902c030b0031040103a83d014034401e9103030590104045540c0e949070004080189a114800e0b16201044410000172030081c0d030880b0b4108007250015824035240000304843c100301e0110386400781c02a40490b60040e00d040024110541c4652809030b02c4211801c202401c40e20001c020141071400c060900481d10f41107103054205540c227030b03151a000d4066040981c0c90b2507002840e049840c0c540741c3d001071282e198202910460b401d49480304100b0740d039801c2600640351403241114250810454202505401d140c21043c0c0c000002005800e024070f0a40e042c079030545122044c0c51a4104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 804501402 1250 804500152 804500161
    0x40b271204150315060507020607050616020f0307051b0102163c03030503151903020301061d130f150b0a1a0906030a150303020d02010b0402030723091305 68
    0x1144010094241070f1070100a20446400c00fa0986001c62141d40184000010a40250340303a01e0122242107030000e0494015045c40394900d2041c1400e95801401805440e10030361444d2030100864040e00d8000c0020000013510302103441c20840c24000c51810351281d0340ca00e5551358202181000200313008035036a9031a891100750048107150b85c1032090344282160309403800026540c1c5041e016a0740500c0c0880e2030f036036011190010f1250602c441c0390300c000b510b40714072262590580103601341da20a400134003815030345034000342c400c440c00c950000011400c840010020f002d2214081038244c080c00322558510306680300c070304607480d942c65503400d52619100d0400ca1810a103250034010f190801d2014ac00b292500c00310381c0540076070004140307e62000004a680f08440740c01216103c00c600301a50041580c070726010350380c1c06800070a0750155090501c10046840d01d4800d80303103d421a52281e000036041801161040e403190144042d028805020300034540c0c980c0c00c484441008021380015142c1007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 804502652 1250 804501402 804501419
    0xc05060a0507020c040e19020f0a0b090f0906010818010204170d031b05120c0f0f03040c0801110d0c0201061701090302011a280e0c1809040b271204 65
    0x1401d01d1041c0581d05143c1b40500c0f21a00207030720581c207450f102d803009201d0300510002e03d410900740d4111707511000f500c1d80801c1d034071012030040145c1402251049025120b40003401090f00c001c0342c605000c42c84039000035522040484880800d400007800051426444000e01014580d19104a901c96031081c444140119014410740c41802c12031100303100041100380c0014000c0c400c405001c00c400315220003052480824400751131094000307000443d2551001a08503a031a0011141070b030b01e8181030303040011112410312620b2580c000d9110359514000c03c4918050151206008000840d941c40340002001ca44604c0c52070035030502d180c0085006042d90600a0070354815400c1070042c4801200108241c4e0b407980c004002402c441a00740000501e1185281143c000359032100c040141d05408110700141c42200501c0343c1c5031012108501c00040c0d10a0118080044074018480c1d0080000f059110306c1000d014184084402990781d000700031010b06509020b000c00c410308000382d022409004041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 804503902 1250 804502652 804502663
    0x6030e0d030e03040603020f09040615080c0301050112180212060108010c0905060304020f180408190c0b04030e0409081b01060b16020409030509060c072409050f010c05060a050702 79
    0x80007450305020609144440d603440f40b007148210010b2590009084c0080c412000035180315a00061003007103510b0703485a40e409048204032441002901c0c1c500018051003011090364165070381030392000c035505440700030900100382070b000705a4008502c00301400142c1d00c002d83e40c0280100b0750702501095140203038950940c0c1c00750443c1428030240480c05d10042d121042078070f03407287e011550700200d014050f020540c070048880d150012802400104018899624014420103456000949561880035000c80d51703003201c0742005004840707000105001c00d01c00c1e0f070014225030004000248a215030380c1c074480b40307034400d0001c11421603440031400c50b80301c428480c0750b00810044858510f000c02d00000301c1025946194028460b9a5801c208010326201e5401c0d1407030705071301034100d0b40d41c1c55800030503640d03c9000344912920300304864400d0800440030400c0c01b4084001d912554001800e00b01040041d000078542e02e81003280c00d41022021420400c6802e0252009260001c0d0904141c0070003030410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 804505152 1250 804503902 804503923
    0x6040819060b121507180f0f0603020a0c140f0307060b0405090a05030304060e1002030114040507091805060f0d08031b040608010e06150d0f240510030b0a06030e 71
    0x1412809440c0035043d10104861100030032000e0b00001d04d0765a84c500b541d25448026100000320705c4410b001c40c1c0c1e0b2414110200c03d80303540b1800440341076a610012411b91143d0038030080080e41c200399910014905450f0105a90501d0040e5604e6442e5800024507507002100e050b0351032070300c40c036401145040512610f5041918031015011007403d81c0c03140bd560b440068401030841340d03211020710043c0801c2c800302d0b03030120354103505554950f500e00c51542040004e089441c402d42c0382c100400c42440c000d803600001c030b079402d0070b040b501c480445c4601c0c0d004040040007582c000400c017290341000c1d603407550141c58007481082d109459080c40c24400c4001c04611200a2400a00304002c1c0200758010030480c1c110345111601074400d5075400301194900b4151106c00c1c1c0380201c0422600742030151030300b00c1040c0425000d020040c891400c5a90b0f40d0040e481507001103031903c00c140603c45402c003000d449662004609010402085540100b442c02c0705a82c07194002076580c00d110544d90600788201480c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 804506402 1250 804505152 804505159
    0x131527050922080d0b030111030405011b0e06090409021018060201060b030604180c030c1a0f19051c0c0e010c0308070e03070e0c18010c030c0303050606040819060b 72
    0x103140b01405050591031407090702501e12040411034402045054000c10030040000d0028460740344468185c004075002594100c8265080c50b002440c6c44041c070300340002903e181c0c2d0310340113a01c0c44c0c00c0c248040380c1e000051240d00184c0303440305080036803030b0390180606428071a5113075510107100b03040061131010260030080859040140411583c124041502d801c54021100004e4041454003404101006000000c01460503240f00000740200701c14000116511440c16044c0204007080c100154400c6101c55080342d40180000b4901c41c1204c80110302100d82410118982821908404950320394814880c0e442c43d2601c0c0300c611300560080d60101801001c0c01d101e14404448e90b40034150f03030001005441084562060f101c4540d0f0204140703401081428018030560810300c00c0e0340f0b1036501a8881015200302081010300e03e52080c047c0c182e149030155070303141e40000181da0841c0030b028050481c03507000c5424000407920180c14462403050445894801402001d603180c614207944142030440e10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 804507652 1250 804506402 804506431
    0x20724110715020d0207051905071e12050705090a0e0c040606050d0f110a05070203070611060408090d120509030607110703060b041803170a021315270509 68
    0x301080011800030048500140c1c8031070480c1300100082c061104040d2040c440c0c11009010490107500a905840c040c0c1c1c207842e609a1a00b1002c6d5404007079845040309030014040410500f410a03001e03076140da1081c010b807481715a0303440001d0425501600c130214803664035485907080c07010410038600b80d400141d030107100c1a0701c1d0840142543c041c5800190629449034280f00d00701072583d001c40c07102d040c49000c15440d140c204000500390307080100103c1c02845241c0011031298001e4452561111055000389403984d1155100252070304403140c2d140d007100c099000580003e0340c0004a014003100da64039aa2076800c00e80806141c104041d15a005000f02c421916041440100c2d455099035048080030520244e41c0020400803e0080c420074112403007141400100341e41b000c0c500d61030a0b02e4809101080d2111f03511001240300b1040d8034900d540709607500304091801c80c840b021400c892403c20520f000080c03003440031902002d40e40110118a405070502283c41c3c4000103c0c2c0100d00c1e0b500380c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 804508902 1250 804507652 804507667
    0x80906060d0219051e03011109030a030f1e0f1818111201080105090706021203310c080115182406080a0b100801140402072411 56
    0x80141c124084060b00503080e100e0b400303801c00d071990b40d008001c03c40070342a00758040180d2a081000001016481c1c86542401d507856800e100300010307601c25030001006001c1d04201684c050715107c45004e610b9040c064100020820103002c144a11001e00c100e4440c2d02c0400460305000b01010300c40040e11070003000302603040c03101c404403010082000f0084000060503103040c8408441e1405400d1700c00c00841c21020001c01c1d0720b2411b4208502690310340301107400c2c180c3c4078002030341c89408940c5071141d02c40702072000450813140100b0b8101000420040c0b2201000070300160b003080380d540501078070004d81c0c91200b00f000100074410715448090301c03404114581e040c1040d4078107811040124200460b15440e82850b507a0000034040d440d4003401d401e20f68810ba0350138011300700303e10440300703580018a000c280d14403d003000c00301c0408004069844040581c20051480e084001c10174115070026401d0102c0d00024414924002c0101640a1030030490f8803070500000545103060101481040c041c400d04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 804510152 1250 804508902 804508909
    0x7090f0f0c110d0f03020c0a15060803030c090904030e031c08010b07150b010327020109120209070807030f23161b060915140f06060406030906020706061508090606 72
    0x2c0028969182544e000504180100e010307001e20070540380d1500900740c040c0100321040c0c18111480112080a0142c01c2e602d09034142c40e030000702c9802507010010004120180740c4050b80d541e205109080c0281205400c0011915062403a629010710003110444020002d4000001d14010801e07200e001c0d1078520507580701b04200d0621480326100c03680b50000c07547c007680a9000048108c4070742d11400031882e206500700350413080228050f4040b17041d007a4040384481040400c0390800d49c02501a48030340c0ca0b4070200311400300f4000c0002d801c055a48800c44101d01d081e000c0c1c02001000800241542240c0c1d6855682c200340c003501500c02860b450303800f000e174650001450050941a156405c103602d026061110261481002c0200b04101c0c00d40301d155107541c44c0e808115108032201025050744c0e40c1480840c0414030a0321040d07440392060008019403803007600444500351082c0300141c105802aa140c0b400e48100790492030130541219884d400302d941c407000341d5511044403802004c130b40c2000800b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 804511402 1250 804510152 804510163
    0xf0b13050306070c02010c11310504020a0308090409080c0307030206011e031b080106060f0e030f060c16060204030c030b090114070e12160501020c030c0a140307090f0f0c11 76
    0x4c2c140101c8480f51414840c10745100c103c0c500c0301038000089c1140c0b502030031010103110b071280308100c0e051088884120060344101c1d44200d9024100a141d01d0843d00e0340a5650005020b203580152152450000903500c11b000d01030164031840150b0f101d240ca460081e040210582100c0281a040e62600001c02d5450805404494014045103850015036481070355510701c0d500701070b24960030150009080e80d40b10840c0161440c050303440440010580c010142c0306c4004201070403440e0b11030b6011824110071800101511071841c0018907280352556552001ea030000d85c019910001c03442400c005008060a29652102405008200003110034281100d19900500100c0821840710010711160301d664905911400300039081340d09521290394102c0b1030804a000c0d03980140268002590b490800107200e0010402c002c11084490342410840000c0c183d88018003a450b00c1521800103060045104a07030701d081034541c001c20035500c03000d1211b065500c0b0b00c040c40c0c1003010340c00b419622020003052 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 804512652 1250 804511402 804511427
    0xf25091802100c0b07090e060928060512070306051b041a07050a052b120f090b130209060f06090d020a0503071805160207060309030201060f0b1305030607 68
    0x38410380c0301c0302c0342100f01c07003210b00602d004000131000e200740302c00382e0780249264046032002d01c0350300c01e1503503141e0520000d4081582c03110b1403c40c2c29848554001d4102c2e0945200c10129000090616640d0340056103000310a00021110340045200f0301c103010041c000c95900405103080444001900c07801c00b46140700304e100b00a40c201074041e1646001d0b90000403a5401600720048070442840ba0408a03159600b40b072032801d4610310441c07104d1190120703040c607800190403611400c50306c034a404c10301d6014244040741c2c07942c42d079640c221030b01c006070b900000f1130b00845024603041c804040700e10502c15114400b50000b8420200c0c1c20809005540714011240300f840165200c0c01c00c00c0191000c5590b10702c00d500010ba06000300307800800c401c24500305184c00c40b0940901405a034480d001940000d00e0680b040b81d005800420302880154020b030001c0311410300c24400024241e0390740c3e81d02405028140c21000c0d420400140504802c054441c1e0b50019000c11006040035090204010309924903000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 804513902 1250 804512652 804512659
    0x30d080a09020a1d1b040e0405031b0d14040b0a0c061d0109170a0903020613030501050a06140a0503330403081006020f0303040b090f25091802 63
    0x8200c01000c0e00048045580640440c681c9a120180300d00c0c24004420410380356000000003c1804420700102c010140b96208440d00d41401c2c650130003107445000f0029502880300304201203182d0f007026403490b106849000523203401000042d00030041c4040128180d50321105200c248007840b158130403541d140941d410310701010195807424a02501159003404062051610034441101040d0000c5403d0781c819090041020303480c1005074039501419a0b0100000c1044006000608000340200100e4000c3c0c4040c001c2540d80365143c0e401d440f41120111141501c800c0c0c108209280c0190340280070b141100c0111203642481c003c2a900c03a080d504030616640340c8980303da01214210381c901071800c2030345e80e1205646410f08026002100c1a18580d031002d1b0008000105a4408905591252003080255255854949900700c4440e00909940e640d8011f11181c40a40f0004002c0d48000300000708100f1001303074181d045400c0350511507004404584c2400e00d080360032074481d4600d90030950f045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 804515152 1250 804513902 804513917
    0x3020d0c03024b070f1802032701060e0901021228110a0806030d1209140f06010501180807090e03040b030a02030a180308060108280501080601080c030d 67
    0x306000700400f06554040d030a4042914499003909940c00d908803c0106884210b664491355240705010001c6144550040d00c1081ca03041c851600030780d00190740103212080e2207090301e10001c000021103002d81040a420740e45d42c0070108070000c08501001c2d40240003000850801a0b003800108100e80020600782d45002c1c96203d809030f03800610302000054491440c204110032820800c1700c0564040d11500000c2040803000030450b24001400c03250950040d51407017108907804603c0e00c05000c00744400c895000003a10502c410450401100d14114000001800e555140000141c6990560903440c070000034001001d100c074a100169400c00c0303aa9080001402e084511841030841c020341c0c00c08255840004140a82d80071990003541c001c0c403400c83e04101c00c010850210300d044c40403001c01408501c3e10b0000035010343c059204031380d01460102c42c00c1c07154800c1400c00b5040c00416802052129039580050158000421045001d4501640100300640d1070100190f07a94030001d45800420000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 804516402 1250 804515152 804515203
    0x40b0108061212040902091302131e05090a050f0907060c02091b160302010f05040c050402031e0a150f08030301030b040602040e07030b0f01021b101110060303020d0c0302 75
    0x108850601109003d102503152501d0b00703505000b9502400b40c01c5c3c40307000b010b466507004a40d5482285c051b03c200c00b141041c1c0310f213820306031580c2c00440c2e084c021004250400014040e00c41202844c800c1c51440700000716894804480310181710003a0580034954001135017072100d00d070044a1340a950307404544581c120395515211050007810340d50034528882c400710381c000d000085000044c0000380710b41c00038400b07a80c040040c681220802c40300640240d00066003000030341042c0c1e0080da0811540030303088001200c480c4900301c249000b900c1e81d50f0703000d40d103100380603860030242c4d052130290840c1203080e11401e29018042d55240012f02024107903d000782c01080800c031311941121700a1104007100c00c1c09240908d00a00244104d1405a0103030b0108071100107190b2000c02c0415241c0c041103c25103050300301006101c800641510140d040c061911b01c015141101084900d004410b00d02c0045441411440c00030b00b46001b142d003d8081c00041c000500001e500402c078000c0d07103c00d0000c4074406192 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 804517652 1250 804516402 804516439
    0x70c080a11100903030c12050f0c0702030a0c0807140609031506060714101d0604142a1c0b0a02030a06151e02070803040e0c041707060806040b010806 66
    0xa242001c904070520f090100010190160020f031651181d6031a180910b410003004481a5501100e6004081e04101c0c005521484003101410102d40050308841d0000c1140e50f40041c40c00403500040300d164003003402080540b9099510080311402131f90b0302818070030400c000c40e99640622200400300702c801d01c00680e064a40c1c030b05490301c042d00041c200c803016500c201d041791610200008102080e0410120354000a03c05194094000d0020014001a61541c0b1030b04c0a0013013441d00f001090250241040440403201e09120801d510034400780810070010040000e06002025440394848034945000c0100e10707001d80341980314194100145e507c0e52800800c0004040b00c1c0c02080001c4607035071851416550001c40e00d40d80351031454540b000c50281c610242d0395040c807407040340c102d644100700a20014260001c055000481e580704a414030b41c48129a106508840180b05c100d544180300801640ba8800d50309504248141c1d030400c175045075000001d1100f0307002003109029008590070090340700c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 804518902 1250 804517652 804517663
    0xb0a0c08040f090b0105090d0b0403051c0b040c11100b1503040b040c0f14041508030403050d03060e0c220305010c050901020f030c071809150e0105070c080a11 70
    0x40d8803610103a0303110740300c120707646605920380501402a0700d008030548455008804a07109120004c04404c00409544c3e00c9100c604001442107041002c28800b0021004d1055030581b0082e000c036601040061b40c0341d051000320b0f042d0380d881408022280f00c02081021010400704000021480c0210750301c2100d40100f40c42400345400c00e980440c000003000300344000991141d010b01c2c82802c0303040d14640c1d610b070340c010340e41441d0003007264084001410380458609540700610000e040f0407281c1480d6542d00390709003950003039441518075030040400440c034954140306400140840500400590424030109803041c000c0c3c002c0e840c01035125015005c124103403103030891700942d407100081c090a14204401030207504590b2845001d44542c0b04144a2540c01200341d4843d01d40b00d40080c24814500550050100000000098a19a68204180444c407168003548600300704020100c0c0c00c00c1840f00c3d05017150001050502003041d8021800002004c60f41112004404c610748010407002c8081e0303a03803e02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 804520152 1250 804518902 804518927
    0x5010b090603070e0d2003060123010207050414072309010f0c05010c2f03120402120d03020307140c101505190e010501050c060f0c041d0f0105060901090b0a 69
    0x5210710b007000403411780d5241c0c006e18052007241c401e07045018565100d500f80682c14800000c0c40c44a801c0c148881c010300503106051044446660b5a500072404541016103a4180303040040300f004181a001050000c440c19070781c09009442c400d14070090040d0161421150401103442803168803584181c0101405c103801000800040250600103080d030720300c003120750200072001c3c1c3d90a1000c0702e4071140c2604481e52032000e10b00d44882d100001c000018000c2049038029985508074400400c104000628202141c41c010703640e09080360042d0205244182e4032a071400308000d0001d15020101e100001070b103480c080840e000c154844035011500841d0401e540009d00820081001e07200e607a84042110802081011566240d000464407032203500204011644410041803d000c010618290310564140c030103070a19489058880c4908a40e104c2086a0b50000e01480040350003010918014103003162194a8001071a001801c0300507140701e001c0b080b070400700305e2016250103800c28a041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 804521402 1250 804520152 804520159
    0x31201180f0c0309020307050a0f210c030303020702240d110c10090204061203080f0a06030807080901090b0423030705210d08010b030604180602031003051005010b090603070e 77
    0x80c60b155280050040501004c1a03210348140c3d100080c181c10540030340020396583d85548070075542041098640ca410011844112070084460308002c504101d1a41001e584039a80250b51001c40d401044444007007011008501590564070750240b818080031541140d184040100b60801065940703400d80c0210346070b00166008600404503413007a10341c440300030248201c45c100500341d1200350303109181810390380060203d4102c10128110b02c5101c0146944418002c0c004100c5540b00d03552002c903038100400c11900540301007030190841da00210804044c1a000f030304135080078901008411500c0c030954010700c200143da6181017803518144100809041c0c05080409050542d80e11680f90700d07100051f41e81c860040e615102c030064410b106940c1207403151240181103031200d50410000304082600041e0045088084100147d018009584126102c00c0c00c0b81026103103040150818104410100780c2520b4100180050701020f8242d841040742a90026101e5072200300c103886800f08410368551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 804522652 1250 804521402 804521411
    0x1407030203071401021c1b1401060b0423030316050c0d0b01030b010803130504020f0d09060b04240303030b0d051501050f100210051306050c0c0f031201180f 69
    0x51010f442c1100c035075000020b070700310381d8a081d00c0400064660301e030500e0310001483e07651410790f200030b00c503a1078140c0d1070043c00d1440b1420a50410a400c4441d503900043c94060003140402080703000e09004d2032103200090200f00d14046100010352a40b042d18070084074881c00c00038410620404000050f0300d4803001d0710b1000b211301d00c0e0801175019175091104951060301c0310b0020076500400f100380c40110b1060749102c2c40c20b030f04110401003e900803503030b014074203041400412100e01c0d850182a8074207000703010000d20342c5045c5050000380d8649424002803070344e000301e52240791121910720508603505894000381032400500011100199888040c11500c10803550b01424203501401038105c0d202119051800d00b442c60900c00480360036811701c1c0160300300c1071080e414603007960071895001d90303040030b00c454100d00313565182c0841c0c0c406d48002d040c080003c00c2d03124011108100808240c0c14035002141445840788100419050500814282e2401c0c0d007464982000d09402001001404038403e01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 804523902 1250 804522652 804522659
    0x31003020405090c0f10080610050d0c120e0a1a06010e2d01170711010b030f01020301140f03060a0c0c140a02330903120715050105040506010903140703020307 70
    0x69894403c4c80486114203042080020a490482421080300304140c03039504980e80d5040c208407080b00c5e2541d100d4140101007085108007031461003550484c00d21900d4220100703010840220480e500f526486112340e000c807041c4800305124290354602c032001901c07001031079595031004841d4000c016088542013403070090380c810101901901c030700d0704800c0c1e0510248240030748001110008013000f8030800340a800000725114a00c00e501c04401e0a00000c00032a0101030a030103e8030b001e0740b10304640c95a0b580440140400e82c00303c01d506401c450112041c58002c1d0000d80040d440d07103400707070a03906925640c0d8039208055001c1d0581420b201d82040c620302c0c0e000220210980c4400c04004220f2203521080140003030560340c107400082d01984240d03540d020300510f407000e0f06c0c190720062400e9418070408810522100c4031074000d1007054410180700134412021040d00342a01c4041c2c00961013a42020100542644d000710340c9412203800860300104d80f20381c2120301d0309205c07003904083d415004180d00803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 804525152 1250 804523902 804523921
    0x90304030609020d1b18050c121b0a0507111e13090c0b04030209060d0507150c23063306120106020106300b2502100c020a020a0902031003020405 64
    0x3c1c08440424094681e010f038600c40600840380201e030072307a01188040c080308000240d81c00c0d1003a4044101c4540042a1101d0a0959a036400842010001074400102842046020002c3c11404401540d040806042169003140801102c003443e6010b41d00d00d0a21a14510503a00030310f000035080042c002c2c040361143c100442960244c00181c0c0030740e00000c0459040c0c10116074901c90280c100019105d290b050695014486004d030720110104160551090701013070950032205012103900101c920a14030104080b400c09000804180c0341c0b203d161044240004203028000c5141602d000a142c031100700b000180590107907412407030030040d0a40020403010780550100e03040d0392120040e50300c007451605104550764820503000d050b20002e80c0c80c820014041801c15038100141e203150024404618150006480140d80108010703030100c800950344803240d209001c1c0c90081c034409003200c80125008280100824481c864034290b00100049080842c854214061a8014010b1002e07081c40d4109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 804526402 1250 804525152 804525203
    0x90302030a260c0a030b0612010e0108030a08040b060a0902070c03030201050c0418050a02120a050f0c07030f11100e010207060b06070c030f06060f03031106070503090304030609020d 80
    0x10740d000701e4070000b518101c501009042c00320828007601c91480503603c50016001d00d4100303600c89030030300d80c03520032490550303039004007800c1c00c08400b410b2041c9562524641649056040c1e1008030260010072001e0f0348039034040301c82944036401c50848202e81c0c03600c49c085004103c1d140d100b00710719440800c0c0402008104680801124040d90081c401070710b0300d0354441800c0c81240b1500080b90039038115039100f07040301d41000740d1050300000e0042c00d1900030a1b90061904044556545099a44c41003001c2c9001c4501c2e003e41000c100050300f401c00503203903070241030607024111040c1400590014411541010000700910030104030007400740c0c44a06907a00c2c040e4100704401c03150b42c1c0c01c200c01c001141c20020305903400340e900b0414086480d03255499015030012800d070b0588460392074a0000c030b15603d0400451700107600c6944d4a1410001c403440d10350a011000e0218010800c081050000c0c10400005460a490300008000340203210740c0b00051400d030b05000000c01c000340e405042c0e03540402200e81c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 804527652 1250 804526402 804526417
    0xf0c0801030b0f0603070e0108012003101a090402040b04090f051005120a050d020d0e06070b0c0d061d06010e0a0f05151b06010f08010501030209040f022e1115040b07090909030203 79
    0x804441d1100c00202e0807045001c2181c0b1114140d0f80c08030100282d43b0750b000680303010b80a04400919012624000c541030380d00540155801100010302002842a14441e06c240c40500d003004103c81d04145017144802050391150500c6008012114840c0e40d50a11a0b80c1081e035119046807540349140c070300692901504143da1010545107041a03030181803010465501710b03800f1101e040543d81d41c0e812412070307030864030940301c0d0709540e90350214001d07200f00800300c0e40c0340703408200c0c40c0c040c0780000c0010100c2034040340c801d018046070201008100b90a180410507920102c607184540000c031050060140600c500400705e0324000310100c0103000005c148941606d2000c1d01d07440d80c0d2503c424456081e03400030b100c0250403071208000070b00070840e4510340040461008202035040000e600c90500b14640d901811005920322001d02c410305500085802d00b06080704000c0e1852940c1c42c0c045040c100c0340207002500c0c1c11803440c00502100d10030184a405421584000c01c040045410001d540f44c00405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 804528902 1250 804527652 804527681
    0x90c0603060512060a0e0f0a0302030712030b0904060209060d240f03080f0d0615030626031602030304030f0305071a011401030c0306180f0c0801030b0f0603070e010801 74
    0xc04074850610085643d8800741c444010115501d032601c07072a00408000d403403140c040c000d0000080c0d0150051000c401042e000c1ea00640d101e41084c20f00d00403500c21040440306041c40c00929100545881c500d450b4400c0c4c22141c016240c1d1564404113410b4821107003040c20300340c50404151946101d2030154402450885484042e8903150704214010243d50300010344516000e10a60801031444401400d0a4821843c0464081c0d500c00f006c07440c1800309000c0c480420f0b00d5043c1404620450040b401e10200341e4550078280700495801c040d101d2148080b4040c070070805001140075034500300216001180d1103140052000e540c4e04000b0301c1034200340412150000142603420b41e134450403501c1416601c40c00d03102d0389135111802c0117500400741c005d480c3c42410340302c00d0002201410754020300d080c0b6124242c04510285242107041c104c071000440541400a180014030116400103034141d482072081554000b035869450000345051841c3e4030608140d1524000443d403403d06400640640c82c40c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 804530152 1250 804528902 804528911
    0x6090c0303031e0403050f0d0209010f020d0c0807021923010309030e0105072613050a03080927042a050906060d180302070806090106140f030c0301090c0603 69
    0x10103869200940348101503c4480a090040741c80d40c20f41075400c107101b828194a01030484a2181854020b00b160025442c3c2c0070031002c0309941c01002c0312440f0243c1b071025169240c50f103071300a8230014a844004e0030480b400300700036085485035002c80701e00b0704600700304032102a0344050b42c94044610b45e0211034251620f00103030f0595400f07030090240c95507154403120070382851003004441a0300610425038207048d03c0712140790b04230510080c1c1d1014a0780c2e400c20b646d50754880f00d1412802e444035030140740104002d04040003c6040201524004c0d54100d03070010b2b0030308030940c82840e2000811403015504d444407080c00100002500868010300a00c0e618004c4082c02c4294200c0d1240184203c540007440040012360a20303100c0010001d141c4090000103404010100100c0c0800e60200c04a01507071000809100c0301c0800c001d607039482174240e0001d00c0010700301281001284400d071400c40c00f440c841e050364110b6a81c1808644002a4013030000c00080d05141416080c0507100d100f4540480e161 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 804531402 1250 804530152 804530173
    0xe01050610030608120319090b1005010c0519170f0306040f1a0405090a050a15140106020a030e0103060306140402120a4206030c050d03200c040207050609 68
    0x20f401510100d4030244094400315181601c2c407040e590000700142c962015030122009120003510400801b680079140600d45031800344042c070a104059004141403201c0c000d0600000f50001034044400303281a01000030401d07152410b400da86401c0000c0101042c00030507080c0c981a119000f40d07116200403241401111380403407041084a40d200d0743c510501e03d460b1a80303405420241c01094110b0010b00c00c45003010340ca9107036035052450040c0e044070303188080c42c5644503201060060301c410140480818040d0b524002001c1e5494030580d800509000c071440582c0b030b01368041d60142d0001d40c0c1040c802e04c01c5070000f528010003050b085404038450308071002500d1090500241e440e058680c0800d6071501007011030581104103101d90b8810410111240d0700b00c0710109075141500410440d00004a5000c0c29440c112100001030340009001d19104410080400e512800892111640103066004180703035820050a014480007415001800040d03ca01000713000580980705070648010f40354600e10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 804532652 1250 804531402 804531407
    0x307110c0a031110200318090f071404091b140316080402030a17030a06140d0b102313090f0b090703050a15181205090607060e01050610 60
    0xc4500000d850310010840203c850b08059030560050340045c00d02510b40c00b100c00d2084c0d403421108030354031126000822003680c4484d40200c014128441103613110420f1400340070031111104020b01140c1003152208400c1c01c80020070040720007401c0b8000050100103924104040d1075044242c4240c0015260a151102118040c003503a0164040d0700752814200100b1004559031507021700207a91601848506c4000518000300814204030312841517500e9141c000040c0c400c0b64513a0307010a6120043c1c13100441141e80c0c5030b400100113030340030a0460203502c81c01c0e070b01e4145103681d0300821300e5281c99002402040c50500c8403000c141104403001a0700380003103d02c02e8141c2c0c02c122001020300721007045401c001920149107562244401d801c43d6200c03075594440c603107442c90720481590b89208640c111004808a03000d407100034541c0c0418030062010b655103465241151584510030004040b40314400341c0d94500455a81940200040c842c583e8010002c038001c0809564103803040d4000340042c0101c50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 804533902 1250 804532652 804532669
    0x30608150408030105100210020c0717010204081002030a1419060602030f1b030c070909110303071101032d0e060609040c0509070e06070f200a03060e030903030307110c 74
    0x280c2c8000c034241964a41018440702611000c100c0d0300758000c2e8261603034140083d102900040358402c0052040c117140510500c10040c190008030040d900410040c0250200083d88144000c5105001a920780e141d511301c0c07009203064000303c5142c0069400748071002030300c170781b410b0480540c1600c10483d040c0e480505a03902d126140b00b08030001024000c1d12106018130f1030b400b4842085070185c9180c9400c0c0e22842e41084102d400030044984d440ca0707000103000640548030019141130f4006c500d00242a2a00c014508c0301318980360416442c3c90b14451001e00003007480740340e8500c2500c1a42e0302c082038502d00020740341040042287e80b14030b44c001603080c5840d032a039600890308070240110b1542000d0a11940c48801003110040c4240910888440d494080081c0000b9006108400d40c55450f80340415400d00003501854003540c940c1814003aa641c1c0314004401c880d440100040e5281034941301c14154092180340c2a0703d40070110400c581541c000035100310005150080d1042d05a141c010012a00f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 804535152 1250 804533902 804533911
    0x1d070f15030b060c010603122609070e07080a0c0801030b130501060f08030306120703150f0b0604091d03041802070c0506130303080c1e1c0204080307020406050d0f080a1e03060815 79
    0x52252791000c0c00311040888007560071004000c19100002d0310b50070200348070007003681e105000070140340030844a14441c1c0720340d1000c12414904407226514540381d01d101c0000103840140106001c84c4040100102584900300610489140b01760550f0756410131381d120780045890901491000800240b1141d002c0344c403105880d40906440390b2000191081c06c010030061140c154100d60f200501d0800d941e07080040c00080c845050b01041e0440c00684c0451041d02805400f1040c1c5d0080c0710034417400100f19881c00301d00c8800a40117807036807a682410240342c0440d5100c281c00810001c0c120b070301111094162010f1301d00946440303006840385081c54169129541c07407480c0350301240d490f01c000d8500b01070060106402080640b03901d242112a00400c07a840340e8421081580001600f03821801d0030300036100101001c89031100280207580300c0c038550700c44070b00c002450403a0003d07100250b613000b180b14102e29105140c070f60400484603030002c2e0041156000b5200184504292007441c81454150548036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 804536402 1250 804535152 804535187
    0xa15090501030515010c03082d060310050106050306061606060b040f0e130204020a0c0203101e0b2412010b0a0801231c060509011d070f15030b060c01060312 69
    0x804080c1c8080700d503080042d05003640140c2c00640b4003c40b01040300d842700f000c070140c24200030904000d400c162030f08628402c00d21480d0f050100400410341c202c42030b00d5100380144d403015035441c240c1c2c00350f2a445410800040c00310340f0748980440c907402024050070994030810700c3c640c0815191101009844003c80c0c2140b2201d862002c60b000600701a0003030643c220441c1403035040340400d0382c006400c2460b506a40d69280d40d858102c9003040c60030b100075000d618640d80081104600740c8001c0f400314690f426048002c00e1a1a6201215102090450345d40070407003d0f10814558540c41881c42ca035004500c0307a40000c1001c000440d03604180900741140c01740090300000120314507802c2c41011200c6183c0114459046030001010545034000e162182902c07400000d4082d05c402d010480c040341811440310503500489080c001d10b0303400d0404405032440241c11170f4160445210031400360801a00301a000440490060189401500300e00d0a6a03c500324107002160910001c403000f802c2030030b484c0c4c0d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 804537652 1250 804536402 804536417
    0x51605300709050d0816080d0e0a050c0d0c09110c1002070512040e15060427060807050123070c03121205060303040e040f02190e010e240a1509050103051501 69
    0xc042c0034440340d81c1c2c2410302c901142c034280305500c0510b1003210388274840e001054010400420800038140b0205100c40b40c1101d420040c0000c40d2100c0091071202c0c010071028581c2d6440000b030007610b0318292a41c0303040e85401c4602c40080e0041c054003940106000300d40307901c260065061000c0c90396040d102900c2111180202980d1040076081c428100f41c004950400710811010605a4220001198660310485504141840b03c0c007004102d0f0090791048000790400a028890360f039000f54940206480d00000b1080009080e0390b54903c0c1c803170320a00410607550310303071700104008040601e044400502d407102d0008000d08120007058540880c0d01951503001003000707100d1400300300c1d1001c0d04140107021008c804807003a804030744603003c444881003000e410070303504000b0808000402c601410032901d00340b00c603052044035418096807503003e800c00e02e4889000e80c10a510b420381d0750b100415411912020126032150050b14003076440c01400c2c002030038900000c04031024140c10b140b080ba030682d510403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 804538902 1250 804537652 804537667
    0x60f0f080607080c28090e0a0e2a03031c150501140c070e01081501090209010c171603030204291213080c0c090a051605300709050d08 59
    0xc09901481c0c0080c44840d21241c05c0190f85800000c0c040703141107a8980018090601c40302220040008024000c81410030508121215011403200301c40200031141c80420341d8140701c8a100c01c2c1a6180c03103038141c03201098000c01200031001440e500c444e020420851040080f08210400216000b181d0208084c0e059510042500360000e08450107040d054070710068890022001da0b00d401e070300030781e8580c1c0111700c00809442d89200c1c9034010141e05204514003240d03080003074565444041c014140c1da064000240d40c80201108840c010b0004030040804140c0034503020780290028050465000d0030315042a201c01c09001c02c5003201100c40d500c0e01d08100d0b0042000e003865000800c4140101d1090308041d000030801809000705da01e645010b0148850b020b010320003580c02c018498001c03142800240000111076142d4250158240e1504d40d41d2030502c000c0e48e09801030b444804010380c0c2e40654850700701c1c041c0d01c00e5903809101c05684900711180ea90040007a48c569940018281210030004d80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 804540152 1250 804538902 804538921
    0x1505030d1e03110309241302100c020402070309140d080f0306041b0203030f1b0a0305060f0d051c0201020f040611010f0c030c080105100905010503100801060f0f08060708 75
    0x640301c80016250115842c0080110410a07820a41c1e4000b91607002d40c1420903000c9130604030071188440161030003107d18080d000c40c4080e240c034600c0039001b0410000c1350f0380400c1c03061b400b808250f5000b5200f55690801441c0007803034003070180301301160076240003030602051508041000045800005190030851301ca80d02000c280c0c8098241c660141d41c600c21701c03a409601584402c045221134010303517141c1c030b0310f4100c5a0031018000c0411a900c01030000e0f1091902c2c0410036038284505901d00080e031392b603503e00829840d840760360b00140d00030349031581304c01003090014000c0c0005504841c981150b03120131805a0030b07402040032001424206020603c141403044107015a4220000c00204500d480c481641c4200c07040e107800c243c0000d8032489200f02040d0030104c4140100400d41314090743d01c0b180e070b40007000308070b85002c1c49040140000201d4907021030070410501800303284000300b141c40e6580a18480301100c500c903054500318400d07000590703940301254651061440c2c2c1c468444507950102c48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 804541402 1250 804540152 804540197
    0xc0f07021207030203060f0f01080319030216141b0f0a2102130b09060d12030c03060e0a1b020601050d0f0302150906070210050c0f030c0d020703031505030d 69
    0x250031807841000380c00805030b9030800069000d202255803502950034516230071504410141c01115140e4001c00500c4140e4402030012400c40c14030b840d005803034000444180c40103c0030848003511401480c0f5609202e2040801d03404801820058820360081d428403c2c0140c0d9510a141c540e4413260003042001100e0300c15080e41c0080c1580102d0440c80070161303001601100039903c0c94200d40390b50b0301942109041c8900710a0b0010340c11a8400145103082d5540303103100040e400b1074000c050b115415000081e000c1e03000400940a812101c0802d8500511824001c152504030484802800c2c0315882c101800400c03024140d510161510364940c0d8136403200707010300041c8a01102184079041d4502d4042c059074070141c1c0205034030780c0644bc803814000ca00074a008129421450900d10340300902a190f00c2c068212032010324003102151312540c4102c540c00c21400f03a04403c5c02c2260000501108040e0b05a0181c0040125000c0c1205110303200c800b45940d6104080354400410310b81c50b0a02d4001d03040040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 804542652 1250 804541402 804541429
    0x81501170708060f04120e0d03030b03030702031e0705060c0c0f120d08010503120f031603060302090408030406060e01080c091807030f0606060e0303041a040f030312050c0f0702 78
    0x101e0707031110780d14070601d03140c100212040c182d030f02c4045040c0010850880517549411100f40791248004040c480040e00c0081050002428075655245641d02501c051003550210394000b02501d1050420348408014944a1001c00c80d841c00b407920049900c3c41c2020590b5803440550b8000d191510341e8005004004144040300c990240711001c000c54404e42c100003006034040305030744170401c1e545804180740c5041d28206038080c0000e0b092001525808102c0240c0380c7c0903a002e00c1c2c1034a8100d0b0b01c6000e8009007181c0c0c1001c0c0d00a00d0b60000c000c24405040d0045009604c2510b08100b035036500d0f40c0401c80114203000c0c0100c03a422407a00c0306c2d0b8038070b001c0d0b118940009407404051007054001d4811407600341207620480740301d00941480024490710380304800050013a814008d82803011034000030303104c0c801d0b400b610718200307041030380a4101e01040e400d440241c03200744909030b40c090710307420050800343c0c4c1c85500503401420440080c81c030a0581d81901d041c040180d98503030400c0070f02d60801c000d034404040e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 804543902 1250 804542652 804542699
    0x80f01060b0310030605070c151b050f0909100e090d08010602070f142e03150e010e092a1009150c021c11030d02061e1909050313081501 60
    0xf23111101040225a03407150405c41d80000003503c6c051407002c0450031410501c140d051002c180418045800000704071081e050045409030b10540c0c0d00580141114026040020b068054004000003c100003628008407401a2100368880c0e0381d404003217a1761003407401420002d4100f80400c0005400c0c10100c0441b1101c014020b4650740d15030482c0b1404903542007800c4000581e09942588642d1b05881800070b20b481080c40f01428608203c070410703509906205100c044880100009c03818042400120b007050301408298071a1401c0c1c40d4400c6035000b01b4413209105035000070b42c6108060040e03454608a402040c002d0244001c0d924082e12051a5004141c0c3c005e03140c101000b40003101a203a00040500c10021114114a00414189000c410590380c00035588800d05012105c0001030440c90100c0c2c14600d50212981c690340c1103107890b04040d5480c0704481c00c21004030100600030000d065204514a40010099520203441e40d903412040c40342600e15900200501c03000260101c0f030b500690384003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 804545152 1250 804543902 804543917
    0x16050109230d030207050406050616030806030a050a0c180c0e10052503030e03030c0409090303020c010e0616230702010c080304080414010801081e011104080f01060b031003060507 79
    0x9001c501c2520460b00b0880068004080622091815100c0d801c0600380c01c1c0c806500700404440341c0314884601342805070a104149001541c03940e410407a8880850748503003a540b0044291815189540d02e90081c500030110148014017001900e1180071030802c440e5441d1102008641c080c4520803002d468042e04001c010040c1c000301c5c101415200542182e4942c1d4241c81840504000301122014101001d95401c02c00a000186240700f00307660070340c2da940350700080030481c0d403805038000c0c41a20002c0419508100c460300e40d800011501d5071040e002009026030140d00748404880b49100b44003100c440852014442035884104c001800c03815106050560b52840c6549400c240d0303403c1100d0440707007504002401d01132640502c903485a030708001e003001c81c2554100840ca903104d510305000ba4880c1c580607104420444425040420103c4115820035071352902e0b440040d0b00c901c4c0d480c1b8001a19801c0c42d0001800c046a80112449050143e04428036181941d44480180201406140410101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 804546402 1250 804545152 804545219
    0x30b100813050717030d0b0a0302100509041503050609060f100e0406061d04050709050f07030207240f20040b070302010b0301050705070308090a0c0b21040309030516050109 76
    0x1c0d48080320300021204e000319121103098482000351500e8102d25030003010040300420058031002c09190400c00d072414240d03103c0e0b440002040081c0402c0e04102a0b036028403000100744200030820078000d88040003074070016501c02c1c00020205a0580d48903242280c9000200b1540c1810443d140d0054880c40000c81c20940e29501c1007031020070b10000b005040703400824882005002c0003280f00038030280d00d05202c1071400303103070764221392800528980515800041a03003c004200040781d1000c60089034001c241c03941074680a00400c0c04040c1314566034a002108003000c1c21001007002c0070b0203050400c501d031a007004c0700c850494000940c100c003075640382c207415512603030203000d101c1c0300e03581c1036a0b210744500c200c1c100242151b101400d40c0d405a080f42030500045003814809070b06460100e40341d60703a680c0c059002034445650300d0700f46228400e080024002010341c8022000d00301c9025104440808485114034002000c0300d00c1414089500d21404002803103217001c001000a45011030900c00620 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 804547652 1250 804546402 804546419
    0x302010c11061b0903071e15050306041d06072304080a0609020a090c020312010b0a09090c02100203010b120627280f06081b0411160b0403030b1008130507 68
    0x16411001d80c015855a1f041c0b000e803240e0a10b0001032940c45c1c403629420740441c0e03015049220142280c1e0041c0c1d1685c910031500c0304000200f52112854a0840e82503181401c07004000c00e0891102d444280035415030742c02250103080988055903061409450b21080070b80ea224024801414100d03007041c1442400501142c6600c01d409285546401559540c0c1a402c0c40c0b640e2020f05800c0b009a0740020f0100c424001d0384078070450240c1d10260341c0080c1100240f502a0710f405030a101d944a00d900000001c42d01c0321454000d02200a41042c6070710440c1c03205820048034003000280294440d10400424804003800403013582c11800e440613418054500c100105480c0f110400c0c22261184c542c40340d88115103040c81580020540c480c040c14440110038041c41c240c03d10045014821a1034140005031007210030115040102d00d07882444110006142c000440c1208036410780c01310b45040400f81260404220106c1484056918400d4941d91445800048804107000380c43c18480d40c00c01003a0603c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 804548902 1250 804547652 804547663
    0xd0b1503010603061d2a0c2b0318080d15080318010e060904110d0204120b0901090b06121c050c06150a060f02010f15030302010c11061b0903 62
    0x1580c3d0307000701d10303282450300c51103c111510004081c02000702040001030100c0204c030109001c55605441040c160509002659004d494481c013518091906a0380e01c4801844c0c00040c07850b0314000384840c0d0703580104190111001d40d41840b0b80902502c010100080342400100030b81394a0000000346195044101c503080d264a4000000640c000107040e125944000c500d40d000750301c01d180c00a20b4910f050080351507406400c121602998841d1000d20442c0000c205423819060303041800c64803143d13980c90f08103480e6006a070540e42151044045581d200040c002c1102c4d140d0841e840c465141c0740e004c00d00c01105503071010800f0781d0286101e081c02001ca4040c4c4d00c0701d445016561951682107078804241066405001004003903000320300500e4545801c6001421035070342e424601101c903105841031340540320f4088520720030743c40d09040c4100e00204240354025607001e40d000700402071300300c14140d0303640c5024110700d040c99100c0d0000801d4108054004442d4014118000c0e0500503d1f4004c2450300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 804550152 1250 804548902 804548909
    0x12c0705040315090203031c02090907230a0206010302220515030d170a02090a0f030609170304020d060e0a06140105031203160c0f02130b040509010b0102030d0b150301 74
    0x15000140800900580042c030051403d41c41c0410401240303558000780d60f034400c44411803402203030800800544680d55050300c01c080350141c18140705242c40a40180140e4425040d0040209e0084041c90b41c00c07050380981c2c0c0c0c10700c1c0640050400703908640810010020060f540c0742c4c0e1044507411081040e0307090080e40e0203184804c40b55078072249070b50101820507401c54901d4080041014540048401d268809500030391908401030350380b0741c6900841c460401c1354001030b004101c03201002040000a0388203c0705c650150010004820200d8140e60240c80705079130180d4000b002068810101c0d4883d844924084c00c0c210446581c1d820b1a03403030006894406041d0400b081055004005600303003480310311103514a80a94070328500c2d001c842c410613659240c004408001000012004108169006158050700101622900c04281d0104400340c440844154000c90030600810503055050040d42d81100058001d10b0400c2682813801000b080d40524040d405140000108914840709000b103028 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 804551402 1250 804550152 804550157
    0x4080d030e0d030b2805030a0302060f1501051e0c070303051809010605040e22050d020c0a0503070e091009030c05060105090421020a020604060c0507120b012c07 71
    0xa00d0516211141041c14100511043c5800e007640d02e5107030b58a803a203000e500c150080480350301d8074460019010301c001ca070b04910b0f014071480e82c0301c10038107400013811482042501c0c903803881503680c0a10b00c41c80c0d4451210190105005001c520740c180f4400f80d4a1020351125107145061180440006281104076803064020610005968801f607401401d40340c0307150300a40b0704c80d0680d4548407004000c1d01c078610400d02911a0070700460007410346070804d03220300002514a050081501c0c105280c48100f000724040143c4136440d17410881d03050603043d03c6d0032184020054241c041c40c14100058401c0c000b07000d00d030640260701400c1e403284001c0c8251035400b03000f5610080d000c0d80e1460040d14228040e00040c0c0314a452904004c001740c0303501442c161070303158419951311150070000700341d01d461040c09000f540b0003000308012441030380c000300c078851450103041110103130360f6256010050070031100d40203042002c0e50001485080700710070300c4001b290b007660000c80c00240d41d4a0380e108034001c180c410200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 804552652 1250 804551402 804551411
    0x220308042c01060e13060f0302100e0a0e150103050f0c0c0703080708070c0602030304170703051c0b2407030e1305160e190e06060708070c06030c09080703030507060204080d03 77
    0x403942171003030903d40074820901c0c0130800c040c00c0981c0d082c2c8502a52000a108400c4928043e614501c038a8140344552000351001c1c2c107454492440c44417080c0704640880741015411400030603988a400b80d24082c0c0e5003082c80102d9a00d80002c050394a6105410f110414880d1050000000312076000070449680510b81d43e40d11002107181a50903c4819404070341194014000e0001041e859032036406001d034a025041d40d103201c14a4190390900600105100038002c034403418038490610313000a440781d00308481c128549214410403410f1294a00b0810008080602c05200000d000d140c002440d50030080c82031214481d1401c4080541d502203503c00e840100511403964810307000680b11040402c200c8a0b007980d0301302c00c81d80c85017488551048044800c1c1403c08a021501e071003088503481e5070800d80107230b52030340c03d4140000c001c241440303080300107840e204250825034440e410040a44a01c90f010b80290303031450b00d0860b0207420543c000c2c0e404503403c01000403149010007820860700c50307075180071030b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 804553902 1250 804552652 804552677
    0xe1215070305160206010603021c0504060c030b060414040203091914010513021305191508070501030501120b0a0b1e1008150d06150803220308042c0106 67
    0x1c06581c4050641610319014442040480f5004200281501d00e40d00c0c0058848546d01c03610151702d00401c0790400d19a15260500c0309000d002c2d0881c1400c60401c1d14280000c3c0014818030200c1c2c4110311482c81000c50a0055100e246499001150004006400c4800009039004400507010341002c0842c1c15908101142070520000c0c080c2d03e0b88040c0000c0300e10039540715070b0046254441130788c2c5c0030320f500bd42d01d400195442010548411000c4000d0100f0024841c022000301000c0d030981c02000340b90304c140c85000443c2d6101e406214141c40c580c400c0302c0300c4a041596812042003003e004500c03040c0d21411a2402511401e05030805001602800c50011820741e0903c68460b80c030721401c01c01c100c00d031020000b210b070080c540d01244140aa45090660307050741081030081044a42e00d203288140700800180b03900c0d00002074403250403030180c4075005d03401c03d910140b13450403103110080a52809104c10891003074424405203900d50300c000354265416000a0201c91410240c11182c00b0030103110354813 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 804555152 1250 804553902 804553907
    0x30f05240a0b0d080a050304061b0909050901061d070e0d0c090b0102010e0717030909041101090b090117180601090204060e1219031709010b0f040213060e121507 71
    0x9030b1040c0010703205890b001c56035807501c01a611031000c0441c00c0c064000013007800c00c03034298800a02266030180c242640301c0b070035000420081e514420300528500300b80101d140400107114440031203252a01e5a0001480e101d04408901703c01031604c41032000c201344040450326000790100c1094420100d580303015060407466011180c0c0c0c000d03224110780c90440c8901c0d185d040020a8420f035460704240444107031075030320352504e1480b40b031010355001410321080c402042040100301d104070500b602c502d1032244d01e401d1002070038040c90a1007400a1000092440d1071202903920b03642005485048070f01c0382080403202032a010081c0d00944003e43e00003420002d0300d6105203800241c4000700c464242e84094007401c0f50790381503500c501c45d40f115240c10040302014050900303104a0030608089034a0b500d0702502c003034000c0c00300800c450f004580c0c42d0168801440c6c1403086501d041d0980c9005a5402e040c81c0c0125003244080389115001000c0e05c00b0b0b950303c1007080140e030405502200400c003640c035142100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 804556402 1250 804555152 804555161
    0x4050106020a020f09100302130c0e060f0414040f02070f110406081c2601060f0c03050a08090304080703060f06080a03020304030f02031518071e030f05240a 69
    0x10001c641148900b08016078402440120000048921071034035191220b0b80d401d2107041d030340025070150f40750803044800c0c03070036070401c948654230b0792100308184034404148861b501c226968010480d00400c801c5c480f1a0380c0e075110343c0c40303174a0151000900c081d0402044040743e0040e40141c03081d280e111240820807c4411341300c03281050030344060095921748110941e84598501c0010f01c0c0744402032034540c1c880e104080c0890690030200c2000001c480c040c0380031101e52800c2c05060700040e005500b8410840c01070018001940d03044d51454a05011110112940100a060031310135010030040001e075000c04014840c080c502507900000c40d8030003612040c081b6144ca61059420740c0140c4405d0012a402000369800c0f43e03000f01c100c40038141244002420a82c80311950844140c4040500898050f0301c182e0744412017411084444403600c440072280c0211420a0460081d80c01c0641403000a0880a02d0305400d80f06d5011240e1096510300317100b2803900080341c0508000c1e0301d0300412078103d016009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 804557652 1250 804556402 804556409
    0x180516090b1806060d060e0f010602010c0f0e21030423031906060902030a0b1c3206090a0c15020705011409120606042915041a09040501 60
    0x2010440d0a0712a4045111451409148920b420003800002e000d03445000c1294026031055808000d025180c1070b00b010081c5080c3e91007042d40e40c1030400810725500512071441d0581c06038403400c2080749000c00403200000ba040d00346d13402203400b01125050349404011440520b0041d005551124181a604820742110002542c840a60540281007503100071403401030102c030a0b00011103c030074509052000c1d15003035112510851000041041c0890164010241000111403090000031011445810000d202d80302605095004042c1211800c0a0807002c10002e00040441010001d4542150a00c0c1080707500c0061900080080e40c20002e20216010107050382c1045007080b1480202c00950301d0a80c0e01440c1e040c807040c400f41d001e03009440e6060b2100b5503c000c100c0c5110400810300c540e1580b9050b40d40900031420508140030745804039042044800c2e0740d2042200c00d03000c00d002c00842415048a04001c11810800442c401c04840005007052102d00c02d030641da50030707080600085542c140d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 804558902 1250 804557652 804557669
    0x2a060718030b0a15080f1006090b0906090702011806090b06030601180207021f0c0c1703070f060b0901060503040c0b0f07020f0a05060d1d0c0d1203180516 68
    0xe500303000003807001d600142c02084000000402080300038218040c40c540d078200000d10300c40c000541c100d034140020303c0000b020881c502071000715075801c2030a060790201c09219074000b10b0040000e40e1814078180380ca6003c040342c80040b03840030500aa20300c1524203c002503c0d980d403108001d50600c038110117040d420410030f4009204075031500c0362100e4022144841c05d0301207600001e041055544118030341c414108030606503c0b415140d510083c15980c9059012101c131100200300003400c044070717001c501c40c0d07407030340b00142d860801c0607540c410401c0b1556500b1100035560b0001d044003030715103c041a01a1680d522210395070b04241c2010000c6000aa002d00003141081210380040d4440c0c0080c1c0c0d8120740d06075401d041c480282c20000701410000d4000513009803020034800c484990640244440c01d50320580745c20f004100d10740d010740700d280001c100d540250354180c00400148a114003e2111203440c074000070150354991203501e6104584c00d0030f4400707610104c080c03450741032894842c600810004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 804560152 1250 804558902 804558947
    0x106081303080c0712080603010f1b050d0e0d2d0c1b080d02030426030f0c12040312110601050f120c0909071e03020a0b2a0607 56
    0x110440310011602990040c200a007a40204484805601c1520b040c1c591004014000c4658000c0044c81102c045030000d10a42c2413821103114a011442040c01480c0409000718010b440100c041c0c03080c1c3d2290150311500e0b96114a142c11840c41480044c91036101c40c0c1c3d40c100d1400120030b03100840d0190400c2d84080881107074000803101d070001008590030341e010045003c0c0015500e03c01c048070740c066101411360b01582c6070301410654040000c0040d40c2442514140e900b03024011040210003505010603107605c204a03040140c00040d018020030f6400d40c088681e140021414501030350840d5104584030700000404200003500043c2c045503900c050300c010041585803500080b4400c5840341020301902020040d00d00c110028800340c042c8500c058000d10072800c286014550711040c0b40701da40103a42a0002140900c0a03074100700040703d4008281d070003010308000394226154011621001e01190f080a2030312008000c0040742c5031034461101400c02840d000501a02c1020110041e50004014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 804561402 1250 804560152 804560161
    0x11130e041b150c1109090105071704260705030706020403030e09070207060822050616020312010902280804020f1203030c090d080c01091208040203030a0c0602090a080601030b010608 80
    0x382c0c005052882403d00d01100c0c0b6480d581032808081846200c2c03290844004010010400415013142c1e01604c1c47d65120500d2001007070001024100c140c40050180050070b0300c0b400d20441141c40c01000c0c0c0455113181e85011815a101ca04d0340d03200d000d040b038a450300810b0400501d50083c4072180001800c2c0d41103011440c0c07290009450b841c450044e402801803110206080309910401c80201361522040c04e5082401350800503a2004100ea01d0020300f0420704004640714404800e5035103800321054030318010b9082c81d40c2ca0029400c2401c4034400c03140d01c03031200500c4007101403140d0b120343e025072610765150a045c018810660b400200c242d004c6c0d0840069034292440000841c2da0041c502c804a541710311144e40010405140103c002d00b04007004500780b01c0c0244198401030120b881100032a40310380140b08243ca2400b811200a5810b4000340101d54101e801a900a21401d20a0000501d031101d8200000e800c3e1205400a00d86603102500510400100740609400f50103223040c05182442c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 804562652 1250 804561402 804561419
    0x70614070f17041e090c0519211103190501050d03110c03120c0d0e0901060f031b020a05010e010b0f0607030207091109100c03021011130e041b 63
    0x104200080550b0341d100c1c841c1005401180990300a407981d600320340360b41c0c90083c004840000c0c1c1c6000e55800d85140c841509101800717002203c421641904844800107465481543d0452442414204190070f2071322a041e10507030340c4941280480411f601c00d44030f04104102040d004000c201e10b030642803502005005c03070307602c0b14108138503a43c3c0342c03801004161201440070309000c2c82010345038240c420903501c08000d10301303c000b90801c04860b0003218100d82941d5000c980101f942c0540c2e40c0c00105840060100b5480741d944c0300100c0300d550a0100700071001400c91a000c07070786c4103070f241300681000c0c1c040780c2000028080c0340c502c103074100300a108414a10b0001000601c4142425101360400103182007014000e000c910021b04030301c1000c0202803201400d11220b0b80c05125203a01c07401807000c0e0146c1c101c2c01202c2241403a5016801001420158943c80d00140740b0300800d440314110900c14002e510501c00c03a480b010300b010744518812800c0c03e00e0280142e01e582080701c440c0d0101001c040c84000e1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 804563902 1250 804562652 804562673
    0xd060e060d0809040c030207050607090315050403081501020a020a06200303013b010303080a0e010c14130503060901060821090603040804090e0604150c0e0d08090a0807061407 77
    0x140d00b03d4000410450445c400d40003403080d00700040c0b160091904101d6100e0b04060f400003100e0040060300c82c080c02403ca2013007211001c950050100303180101080d11807134483c00004180307c040c0121000115190006408103059030303c1030001903605911400d415514500c06603d0315040300080d800d40d410540b00039919804101c03512405520040c0c4244a0a09005c0783c00074a08031b08100b0156503102d08000300203c000700c170170004d51424820b85c422900c00c1481039030040c0386165101c0044418414510b05070358000740c04480907452025010400b50b60500080d03020700c4500000048ca81e24200b51503082050761081c0254002400105003030719800903080350039031902196503031f90f13170707920340c43d00e115140a16004040541d1034098440030003071001910901490066030804800c2c5c0c1c00344d0810f02034134070015543c0700159044080d0300e101d0904007910609580f0036620701e81082403580201d0040501503122000c3d59001c0d950411580e904030081c8150060300050692614000b903e03004d0310403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 804565152 1250 804563902 804563917
    0x10c09030f0c0e0a06030c0e0403020c120f19060b04110406300207020306060a1805090a0605070507140d0c0b061f050c0c06070b041707080d060e060d08 67
    0x65420307658603420800c444400c01e020340050341411019007440841c101c0100035602040307484944503074002c9190080c141d00e81d40301d01c0d03040d4020003030f100c0540d00f07105007005207450000d110700c9a2026a0f00030f007024403e1030100d4079a900f40d407800d0070507030034414290b440a198150140e40b07041040300f036a900b420102c03030070b80745a820720102c0708400c000050b0700c2d60741d8002c0c0c00c844a0100b1346c038100820040d40040648a00031021180d060700c0e080d040250021151054450901c010603880c010480203801050744000180107403400e030340b059141c040c04e030b40c2d00315501000100002144030800c494045111818040301000740364030f110100c0090408943d036880513051b80980360005929aa81540042c4203a0050a160344901001c610180c12138101100020032030042940c0500d080c1441000c3c1c40050341c0004a03804240c5907519241a4800180d05d4648492400c22680001c01c0801d0000d081c0502542c0000034918a0b00301d0071903060b400a40001c0c810f4880424800214040f4410790b07004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 804566402 1250 804565152 804565163
    0x501061d041803140702150d0f1e0e01060b0a0c0b070302030f0708040618030216092a05040b0f090f01020c0310151706060a08150417040306140402010e03010c0903 72
    0x50321007109084c60306014080d4000d60000520480450348a404406803140304181c2d401440000116000501070b2038510b1708200d041e1394049501c1030520b4480e0440c500c50700b40900001740c51901c448400302554002c114403008203081c800b0a0040190420509501c9509440c0071419814941c20071010102e02400ca10104255440820188031a541c000c2d0840181d403110a00321502a283c00303500c0302c0c0c0b20007403405400c030700110000c1c0103086070040c9410300000980004040c02c031185d52008061049414104002c010b00c80440e0281c004002085080306060049440e061000304001d01c2142e8100b580c1e045421450608078103460014003c55290030690001c1000d85040008200100c0144e010a400404640040f00c4a0f14040b450174080c2c181914001c00c0c26413104462075450201201c04011405002c0008001c206012480341c0301861210141d03103813664035280c2d60309890100b200714a922201d401440219a04a00003207038141c0c081e00244000b440444000e03240c00b2091001425 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 804567652 1250 804566402 804566417
    0x7030b06060d020d0914070e040204150513091203020a120f0f020f0324010207031b030c0b0901030c0e060d020906070822060903150914010501061d041803 68
    0x11541d44801c1510322820402c441151194030440242c00904580170003511040c2108198015030a0045030300720549000300c00300142610b0716802d00000b04200140903401c80c9659401141958524540070080714149101155009160503c80400c48818003030b00e080c1031041000303220044c0c10401005901000003000100d5041a40101c80074081c80e42070304128a200140c1c0340308100104010710302800f103240301e00f41c0d080c024241e100130090f80c41c1001409640400410070000e494141140c0a6040794404090041d40d0390351070320340310140c0703802c4241101000301d000061560b00d1322402c0350300400e038600941030302e510b9000705e50b0610651402244017a00042c416000c0d0300c0b03200c102c81085038441078455a480c0300ca1705010110449407001d4004106c80320000980c0d91080086009407508102c00c0030b101458048144010b00704a01e04452500d118800c41d282c0d45003e10515000308070b241c0b111008102c0c10315050380038a07403002000c1e12561500500d960003c444ea080c80081e550302d82000030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 804568902 1250 804567652 804567661
    0x3060a05040903020c03060a14010e0106020a02120c0a03200102070302220b060c0105040b250309050a0c060201020901091d040b0601090e01031a09011a1504030819020c011107030b 79
    0x7405c03d685210056054132806043c08010f40540d44503100c0e031010006081c00305d07607c4050f01d40c610f02007031049400591003c4941b0025140489064100510141c2150b0020140c5008200b50740c03150f600a41e080c898407803030400340f001400f0226002c40424405806024195400101e00541d0342e4094403200c000101c1c60015050355034013a5a0b4046d006002d5516960740034407441c0601001c0b5401c442035203060001c40c1d0303180c0706161400880c6c0a0642c1d8425182400541280142031880060307500740709001c90080030603407140c3c40401038411640003598034003109001410825481c1c1c0804049800c0c00d15416110061812080c6c0007940032030030160b81d4a070b01e001240e60519030f82041c500103203114000010480351011a40175500e2031454200c10781c0c4d60f03030f400500302c0300b042c507220502c810503444030744183c40d000f010700b8403190741940d40c41d0415807a502c8903803443e0030110252121411149a80c2c401a404019492030703103100740390008510351645030041d1900024800100042d040b02c0104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 804570152 1250 804568902 804568907
    0x100e01060902190908060408090904020d0206070f021002070303020604080901020120030a0f02091e040f09060b0a0801050415020313151a0910180612050d020d020303060a05040903 79
    0xc000d0401050a43d103503007200500004000c08209a1404034030310080000e617690001c0f50175842590080021418044d52006110844000070401c0340e010003d00d100c1c200503510000a0401035000304402d031800229032040c416200d950b000000c00f554407040c41000003d40c0003480550059200c0b0110b6110800c1d0b8006034054510617110600c01c1c10340552600c80c0c0c0b02c00c040a1171181000c801d052140c00d1208111508034402c4055903508030308442d814500080c0c0300040c001f0035000140000603440b814000040c01c50b01364a10840304a80c4070f0340195860301e800000a0054040c0100803c410300302680c890324015100a071850a640d00400007030f000c440c41c02c15089002c0e030041e1400000011070445000206102c0000041c04030000040d03c88505160b04264840e040c3e5200040b000b074104408242e200f1030168010724044d440ea00b000c600800c0c0b20b42c25240c614400c1c00105100f14050101038200008110010304660081c4200b02203550703821110320440e80151000a4002c041d41000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 804571402 1250 804570152 804570161
    0x91501031a060301080303160e011719020f36010c1401060b04080105150105160c120c170309090402010806190b0903010c080408030f1009090807020406090509100e01 73
    0x358000400303c000900658040020351241468104400d02c1c0120700806540c1459103109041c00283e8429804032400208900380d030304240d51070030000d050313008403060b030341030741d000107040e481502011231401d850041c0078203980c08894a160b085813440009a0680f10461350780c01e1401d04200d17491106006000c5030809103900030031400b00030f01034107441e5410a040c17540141b00300002586840c00180f8805002070340304444140503592240b0b46030010200341c11407006d85105496045402c00001030444000c02440041d510691041c41503518040e66559801400100b0306c410b600104501005a42d402402c1544551309003060106a1100b0b80440d03a900b4a4180c601c00c44102d140001c110320041c08003900c2040e400f01d0082c000007001d40e0741203070f41c40d10a40340248908410b10101e40044003024040754844860880d00c1c070314650303c9000c8000d803118003006884000300020382e9025810240075840c0504429181440941030541c18590780740560004407081569582c00703640c19010a401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 804572652 1250 804571402 804571451
    0x5130c0908030706060608010509060d140304080712021804170f120f010f0f23010c08041211040203360a05070512010e060c0a0e090c071109150103 65
    0x1c403621003c41e450710308014001c3e0302580300070a45400000034545401c94200d88900c401400700b00d070200581c0d88403000016169101d000602041c000454612001c00409000301121301c10504803562500502c54504404450004401ca03080200000b04020b4900c4103250b100b00e107149540c821181c04035036800d0007205107046980d94144103000705c4602c2d0030030581c140c40e0829030400c2e0b0030344d85140c1690099598421500400354140d4440601225034140c0400c145042c1800d00c9054400c0c5d49a820942c00743d00300704030b4440c2d0700c11031506220f4466461081a101542c04600c3c5080240043c009446100c05c0090032840300c0c04181c2c125140307481304d841d040440d4000c40300152807904c0c01c2601c480403401124090000c1d90308070b200340340c4140124483c18a0039005003940da00c0f00308410041d9445400800c0030310400d5855041e1a4545c0010340b1310950405860546800d4140307411003c0b4548040b07c14803c0c1a8201807003a02d902d1202c2070030500303200742000aa1502c0303910f44000304954004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 804573902 1250 804572652 804572669
    0x91e06040504050c09420d050c0a0206010902041805040212060c0d0e07121e080406050304030f030c080703150e070309031b0b04020d06020903100b040606020705130c09 74
    0xc1884580041c4a0191060305401c0340d5842583c010350a1205802008800030b054111403c00d407545901b6044000481c0d81c015941c440d07141c1a0010b92850a88409803081009144009214140d090b4180710f554003512011000398507240c64444120b4000c548020b04003c400d9a9002080455071070100c2e0401c00410882500d0140c07030103c04030102c9402245100031424101081000c10340c10200d01081a03404a01c1c0d056408011307921545003c4542c4584041c20450506244002c12032040113000100030b80e5581a40d039180c10301d0000c0c0014020402401071506050242000540080710380d42d1090003850002507003452840c080e00101c405030b01c80c640d00e20181d028002116895000010154001d449e0080754103030901c2e4034042c80034032103006000303040640d000c41c0c010714005502e454a03e00032000076040076403031130009040402c2011000703003241c0d80d44580c041c5070601e402440010100c0d8000760048500d81070102e0070580054400d01886990b5800d000025805a0500000b420118 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 804575152 1250 804573902 804573911
    0x605190f021f06090b01030603080f0309032203034e020c1b0307030f0303180516030203060106030b0319021f050c01150b090f2b1106091e06040504 65
    0x1645050020302c80c13405440e07030490400715040c1455000380541d03000c80740c3c0000000c0c40c00307480702002d664903080604203803050300081060304024144440f040d42c000701c0500071440100c0c95803030040c24004584020318221a5094410b4a8100c1c02c864050b03544002d0b810040c1c2c0011b15090032060320701c40b5121510f105d03480814102c0b6110800903c070b180590744c0c2031041610141070310416a50340311601c0010280c03125801000c0000e44240c0000c659442400c0400c80880c3c100e41d03940d170814002c0d80303c0102c402030001081003903250810480c0d004100604042101141c03d002084c0c40d03c411213102503d241d004501641107464031118034000e801100070180c00c8141d07034413004140d58071240e13000c441903007804101c0c0c1c442040c03880316100300c03000300c0b1403e40340040d0740c42400f1115064245440c3c1c005030160340b101ca69240fa42401084401040c168501002c103490300880610a0a0b5040d0240005001340301c00f17030321000448410780710684000d000102100c80041c41d50300ca00e400440e0000d040c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 804576402 1250 804575152 804575203
    0x60f040611010506150d0c090f090c081f26030f0415030b0109140301060906151e0c0b0414030706020c01180b0109020a03061a130605190f02 62
    0x85000c010901a20001d00c0f043e100c520402c211040c1d460b034604002d00d001c00c08041000c8459102078510161820302151443e510300c070802517110158002c015480e1070740c03000001254005440395000c01124005040540740b4075402c400e51800d4000c01c00004007541402c0c00300c208844d101e0080700b640da02225a6510080c011103007641052040e80000c07000d510300c0350050f80c041c5c06400340d9031006a4900c010790b071400700c1c000c8403070760000f021035055545c540c0045028451402148041c00c02e82042a48548200d4401401c041a5040c41c2c020103000e00c200101240c0d019820701f9103541c1007550100795494900308000c6188000d42c4515607071100055000801c101c0350050185100030100030001c0740a005041010250f285200a051000242c010f2040300450303401790041000614000400300d4541100b4a401c1c004000e8000c03900101145942801d801c0c090312101074005d40c0b500504000e505190800c5442031010a0428040030600912480d4820040492660000c0220340440d150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 804577652 1250 804576402 804576407
    0x60a0e1b0f0d050a0318030b150d150c12020306100c05030c0a05070608011508040323030c121303020c0103090303090819030506010e01020a02100201110316020c090402031506060f0406 81
    0x90039132044010076010701002c0c100b0b42d03e08882004580c2c00451030b40c850b6a1301980070a61481d4002040e0b0310403c000648004100358841915401c0300c1c5000c0001c050780c40800103031000235200501e0510343d00400400035140c03180e541d8100864070f6401d04240198442c58110301310301038584007030402d00c203180304003040c0000002c07520100d440790b4942130b030300785d0300d810756503260845032014400424440004500000e100d005c400d2282c00200301124683d5100c0034010846074800d55203107049480100d10030b01600b0403441c1c10b030707003210007071502c0c0688500c10b940194607643c1ea164030a045c1b503a1407410109050082d0801e80031903a2143c14a0b0303980300c3c1c0485403c0300b021443e05400c0060720349000108154081d001940046030141c0080040000a030300304a4076485640c410003c55480e400203000ca081c1100c003541c041ca07894181004080443d0382e0003881d120b50b001c240c9114000500078040562008141c820b002c0e038141060180d190766103404968248550308032024802d000090004040e075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 804578902 1250 804577652 804577663
    0x6060f0d02070204061203080f060402030f060d0302031306080108150f0c090301060308070305030405160602100e0f01090f03080a15090b120d020304081e120319020714060a0e1b0f0d05 81
    0x85400141c00c403540c550ac030910040380400c64a0108800708680490304a240030070141e103c2a06c00e20440313107051000e034040103410400d544000041071a2600500101106110202c5607240ae084405550324003004801c04101e000b6114a69045001078681f90f5610290800303009503070044680e070368070711603032400070000d030300446d001d035064020949006103c40c26512164200c5171a64005d014404500403450024087c2074007240183c860081552200c240030b01072045401d00551480e50b02c1c0045060181107103500901401c2940c2c582005080000381030407180099410080c03000030340c3c1100340b0100700400720102100074184108040c6444172a40040108240c4071030304c2c16650010103090404078601000e02c408004c641020000c600c4500b50b2070040c55112111400c00340300700f64014201c108070390010006450748070b00780c0900300303c52004001054010710044000c000c42c26803c8034650303c40300c10010303508816800001360401c0e955403100c0d200c134807e80200085242101e505d480c55956 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 804580152 1250 804578902 804578911
    0x40f0201030b1503071407120e0901060509030714062b0b0f0616020d0f060903030b010e0d03030506280f15020a060506011b1a06060f0d0207020406120308 68
    0xe03007002411810b07403d182c240c80c500d40c0d003c00f01d201d00715121a0010383d90070500c4800b90112213000d1180901240c4074400c0140740394200d44454003898050000c0c0150711405800480134030408010056007920b0001e440801c6035211030010707642060742000603009114012056504c4030b450030300c50036038500c440036260319842400030800205840d54180310305c03040c040e401150720200c01c0c042c076480c0103410040032810510060a00c1c41c40140c95440001c20fa032165015075440303607100341102c10150180f140da4481e03802404c01e00d948041c8400010038020030b1440060030952643c0c081005038540700078407010010304503092000301610080c010300d8100c0600c6400c003810990301c0001005000c0034484200582e00b54040d1202002c03d40b541c03800b80a004e01018100440007011000c4006080750803854580314201d400480e06012080300c0188401400c9a84110000c00007641811140403c49031a5424a0f034056103858450001a006110550084002c4174100f1849410589d0226072a41300c1d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804581402 1250 804580152 804580157
    0xb0a030912030e010e070f0513060302130203070f11100f1104080a120c1a0c070204050903030a050c0306130f0e0304031a0708010e04020127080d022103160c0605040f0201 75
    0xa202c0b800c9106a1b0b00d20051003003005100c2856403e00c014100032003440f00a0348103907408900c0998940c0499991070300101d40284d100e60200502171403940c40958090101e04610701a40c910001004403070f21105000088984c03035558001060b1040c00c25003101e040c400b001c15445032526039032180c003515188070f48000c50b03180000c1092418414040d071000016550010182008100c0601107070f01e914101a0600f12801d2051281c82d0041e46c40e805000c0c414840f00d0041c688904044210070306440d80988142000c04092080005c951260b8401148507031890308040380680600945400070320565040b070381d080c08006004001c3c00401500708103800036a60390005031b9503401c00212000030081c042c0d002000d450002040156105e04210012030038458010724140c80c289034071403183c030380340c1d80520602d4108a4207a0b01c05501401902e242e24054079020785400f404e00b4010342c0ca448010301c0c24074002c610750700b01da8030b0030710600c41b60302e6055200100700194141410414882d0a00300000c900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 804582652 1250 804581402 804581411
    0x30c03121b060106090b0f090406120b090f06070e0d0c0801091502070305071709041b030b030c06071e050610051e03120307050f030a0506150a02070b0a030912030e01 73
    0x114400002c600d4100d0341541c0d50303e01c0309404c03e0303042d8185038001034110007445014410302a0a69030703441010000c1140c0542c0000c180341d80e180a03801244010400702098104211090707407154003045243c1e020003146001c034100e4140c440040c443d0002c4903005410b080c420754010611000541c00b2040c2d003405180035018410809401e202607104911000700007880520001c1d0020310b003203100e600b034200209010760810000702d01040899060417545186401c41c10281c13803940c0d8161042c070444107415000742143c05080e40100b0010b00c01e01000a01e603003840066078400380ba20300c40b184910b5a00c0402c0d101e02c1e051592080d03040d40412b00400307202e448514564800d403004200c00140303810000d4081e111606d034088503010160002803c1c2400c6c080200070003209142c50344d0042d4440c0300d01500015071400c11409000c3c1045c0b403100d150041c00b02c10031070340d0358440d00018881c048411100c100c40e520080703420101d000e009000c80081c074038890404200052a0590400907140c0e40b040700801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 804583902 1250 804582652 804582697
    0x1e010b030a08091908010f060306050702010204030b1303021c0c0b01060503010e0a0506061b070320180601031404030c15061a0d1d0d111b0f030c0312 66
    0x50300c901010300020200c0b402042000d1079400d0002030145080141d0042d135800750341e80c5201900f510041401d50505542d80d00e03040c000c02156118094000c40075100840c10241140d84111402d60041c00320000030070301e4440d000c101442000212101381250440b800c00440500c805081624001c104640080650001040d410b01c110306690407035501c003006003ca600c80c404803800800001c1c043e550481c50406c01403045540d000e44250351030000c103000b4140300d451400c1400742504810084501c01d46449101c002e43d588030206113170019104580c44000752070b5000141c2c01000c001c0e010703411040020302004185600034111075a100e00854101501e4003c020300441183d0044c000c10040c1e40d025403d80820300000b2010705000e4042c840002142d0380c161000c042120302120840107aa400320b084e0b006402c0c0e1042100760000c509900802e81504c0c42c108241034001c0400d49980581503c03c20380743d46640800600680c680041c0a1f201581008a040c8a15501c02d0a40848034000e04000c4d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 804585152 1250 804583902 804583909
    0x9120c12030c050f09150c070602070e0108071502150406021804050c031342021201050405150414090c0906030a120203130e01240804020f060c1e010b 66
    0x144000300c1d0780e254640b034458140c032041600172640580d0807110081c0718083c41014500104000043d000090400600d800f000038603080454105641000341800100f15403900041c10405580f100f1903802140c1c009028120f1828052026034202501c604c7c082c00203210701980200010300811390313289402d080da9024001607400a450b09440e01c40200002030300300e4030b82c007900482e5500c00c070440a80c2e00c40780018450b624055020100f10a04c2000320410441000055403400ca14940000d6040010000140088690503c9020301454a0304000307006106411005145140c00402c100540c9a04e10328104480c8d400b2292646a84610340456200f0329005a11038490100103006200b103179200c3c0c4e50421080300340300300d480640c4000d00010a50103a0081c044c0050320f2026020070300e661401810f283c1c0e0358074418034120054510405803020590040400394000d4056039201d0f000c1d0f1002c3c2c08902d4500c00c101c450401406039451020140301c46080c402110180000280803910340c00c0b041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 804586402 1250 804585152 804585161
    0x70b071b060c0c060512011a090d080d0501080706271805060112090804090b18090607020d0519030b0a0513050402090907051e0d120c0203060901050105010e040e0109120c1203 77
    0xa000c401c001b41c030040003009030380d248800106104200441c1840050008074510306468030040750080e00100f4450800941481514018803409004015a51620390007805c1c05040f409008600032440d100f1888202d41e642c1c107080108903000c0b05005003402c0140c0031004010544085001a894840b00b80c003030405405021642030700000d00d0381c9414680200c1d28001c04042000d99005102d20a0307172508114281099440b5011800141c80795280000c402401e14107101250b0041c0201408034401050703500181071844806818009080018180060017280c52588015881180d10304034690f800700d281c2050380218400c2d03500c00c046440e0302500540360b80250003001e8004010b400d06040300518100860741204001d07090340d86100040e1102281c0f03040b40401e08021612014003c0214202003003001e40c0600010020456541407400088c24040c40460880c03056495984802c0c0404080d4408031200b5800900c0308401c44d02c068000d0f00300d02040d02c058a08440001b030307000391580240178 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 804587652 1250 804586402 804586417
    0x11041508150a1404090602031602070b070b130507030b071121091c152405010f0c050102040f1502070e060312070f020a141002070305070b071b060c0c0605 68
    0x2103400b2007400c003400640400840124658442d85a03103216011903418401180501c0350301c400421410303041710010345043d14907848111808001c01c078441c04600624540c0d500404000b1807622208400c0c00d205140c1000c0350000f401d4040c40700c05100d03c01d87c201d00460241000c1405a40e07100600c6d20110f001155100065944058108045503440c036007240040c00d400158500c500d400c03412525007005440d00c60902c0000e05070f461504c0901c2420a40c2036200c40e400094102c2011070824000030a40e0b0350400030711060098501e0b0480400c10290140e40280c102e11400c0421399030b4406007002403440e0520a9070160081000202c3c48124400b001c600c00c0101500412840c00c045007100305640c80500181c41c2002c55410090042c0d4036090040001c1403122800200501c0c584104680100840b20302c405540c00100b040000600100703840c4d00312103070300c089280c4a44050030300222840c10304511850025900d0300c0415001c0e000402140300c28007850a0400d02500c03228191124403d104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 804588902 1250 804587652 804587659
    0x1409090a0308070c0c081006050603090c040c0e030307050105061c0c23030318091005090c070602071403430c050d03080405120702011d041104150815 66
    0x4800c00003190240c04015009181c80c50078803150b407890b45405502e00c13102d0b004040e03190454510714003441a240244000b45c502192018954101a010340381d49165050515001d140c0b50700c402113456014007640d0074824009815030703030f44a0355880d10354028003084a00d5449603000030420090f240170b03243d04281039a0700c884110109410b08410500340c08800c0e180301d1360007040020001d000c1d03e0134800342050410074070300551100302007010802c4020004040f201000e250302d8040000303594401038a074005c1c1042080a54455050414401038803604002600c2620a2000507000071000802088014606030b100704c048080d13030701e1001c5452501e50180c0d400c41444825035aa140c0600340140e40240701c2d00405030403070707640c40206101f003048502c168081241e4504120a1003414400c41d5030a4012802d29460110076500103080e0051700c2c0345501d1600078501040c0d4141c1c42d11380c04103480c0e40703041c441070703032210384d02d034072200d102d84d407803a43c0c2c4c00082d5121001c5103034803040056087d0000c5004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 804590152 1250 804588902 804588913
    0x20d1401090b0d030e06040b0f03090d0e0d0b0402131121011d070c17040302010e0a030c06080c120c0a02010c022d0106090501060f081b04090f02190306140909 70
    0x391405c440d603102e1030481c01da1100d4100800124180024000c0641244500b0a20b480f8640108000d090005a1116500f4808600c400c40722a41c0d50940d141d08455205035141110b4441e8004070701c0b54050050100205132030610707450b5000c0d01c110007130b254881020f602c414440c2c2000d4403010903c3c4080c0700c0c18510140240405000303148891010f40d20201610303020f4026801034035801f02c00030070030b51a0040400c0003e41802503503403281c207100c5800750941d00c4007400b074519174840300c681c2941d200c0d0104102a21001c10a100b00f910201e0ba4041d04904004020342441c4580a07400e2b403003820307900050362800b0358501c10280003003001c1c400c17000c3e08a682010030b80200c0d8102a400d00b00844050195642c220100d41d0804902c036140c00380100350f030781203040301404601800c040000703000c00e29040d01345026650b0b880c62030300c1158262090401d001c16200068045c1d54041c0c0210100102c6041e802082c40302c480358958000001c031840c90700c01d03282a0718028103110754444c007928400840d4100f03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 804591402 1250 804590152 804590179
    0x1b020c0d0c090f1508070f061b03120e0a11010e030f0c0f03151f05220f060815060108310602070501091b06170c0306010c120c122d050d020d1401090b 66
    0x3540d14000180034110011424003101c48ce094141107a1540c100e400c0c0e03d4104140c491540c0c02036110840080a40003818070321440d80d82c050b40d8040c0122003900c10f000c9210001b0300390b1000e014901c82014410030b482a5418800f65030a407903400300c00d100340030700001080000c0a00e0160318021300b041003001400084140c01c0810006021450184020180c48503030014111300200301c44241c81c101d0005464044c1011b2000401000e40508034640040410780c03a801907100982100645200000301043e0711220303441c0040103400740b1703200540340c0d510300b500200034000c050688502080c100c1c120626203548070b070340654060600c0b00030600840714038000180c8148810b402190000e0f014100b100348102036584d94a10090341c28852030007c2c080220300810407800590510020f8194242110103c0c14002c02c0b98403200e40c1040c04040b244090002d460b05406082141c07000694100195912840003030400041d00840b6060440c001032000005181d0805100c2d1000784680180000c1001f480d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 804592652 1250 804591402 804591407
    0x30803041b0f080303060909160b13090c080603010605040c05070b0c0405150a09060807080402090a0618021206030606010e1504091b020c0d0c090f1508070f061b03 72
    0x14201a0140c0070403410340030035406840081c00006149560080d0ba5900e040818062080c402604603119580003940c9e03100c80c188030881e400c00f41c4110290140c0c890b000110300d45e007010065404048102d2a00390300250441c1d00c83e801034400c40c0c040c1c000348840c80c0d94409100842d5420620000020414443c50b030000304180ca0031908501104245030600e40c50700c00040310807040355011481c58800045130756205801c0b81582c4000d04450800c0019440c010102604c00303400144000e00c01c60303100001401c0c203a0b456210300c0141c90041c0c1c81c0345001110522190003940003101c144543c504030b40009003246000941d481c800d01060b9900c81450b40b101302888804102c0d99000c000c560380902002c1407502552045041c11801e422618085501c5000041d04105840300e100380190310301e84a0394082804410940101c48011400080d10900e05070b6410040111501c8007107052041e80300007807103a20014907081980c90781c0e1001300d04a40d4034807081d100c2c4000c0c03100700011030291180c00c40c0840e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 804593902 1250 804592652 804592673
    0x1d120901030b0a050a0605070b0a200d0e0729090f04020903101103041a040b04080c0a08041508071b08211810020c071a090d060204090b0a03080304 65
    0x80003510f481e4210303441d4000074045811540200c0002a40440e141d803c1c414009013140d00b000044008000362807040c401990149410f0f81d00c4525180d000824614110a039448151440c03ca402601c42007074a400d03003c0074070b01c00c03207080c803030300c0e20301100205480b802c00002c070340800000521100080040e03c041c04065086801c6032030f4180140201801c4001c40d600462103003150520400c1e07035038602841e1140041c0f900000d15010a0750a40401000071180d419860700250040006616080c0d05480b0074a407550100004142c102c01090000f4482d0340d031058810f080003079844410321079070b80743c1040b20000c9440070100343d2a1801c20f03001c00401c240d14001c02071051181100c00700c02c0b2169040114050007502d0301450410103001d840d4a1a00c18000c0700f80d04070340050154070300610341e80351990302c1106014058040c007980340e48180381e009200454041e4600501003002c04111418150029003040c42400c01450034200c0345544c80c6031400c41d00050700d5000da00c03503045856a448550384c58 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 804595152 1250 804593902 804593921
    0x10021216030617030403060c110303270322060c15020703030b3303240301022206021204030b010312020a05030c01090201120b3d031d12090103 63
    0x1036540d02e022800581010360000c00403150f4008540d1780346503141081c1120303e681c0d0100c003000b00124440502d5030707001c401c07a038115400400e04000c04c2c054001746500c1e1b12002090242e14400001d1010440c850030040022078220138001003401c96550310103840380c03008810000d00c180c90403456211403040a60183c03002d00d0003032500146805405000c1081d4407200c0040c182c0501d6084d62096007004d15402d005d6240b8041c08820781141000c034922002d015982100a20414005d904131440da10b0950589880c01c42c02a0040103070454006031000480513405110014080c620061542c611740d40300311022680c0c0300a4114580c1e1075030701c40003910388030401c68000314081c004c024404500200301400349407008000005250301c0510024208400041760303455114104160b40071242e4032190380035000c5540f40351a94502c115010042d4510700901030b005421800c0c10503048900c0c2c1d041d48410911411b203401d610b00a03002c02c8203103580b5100d4100000703e2550411a481e0503510941092018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 804596402 1250 804595152 804595157
    0xb041b05090c07060507021203060f130f0504050d030c020c060706090b040318051c11010203070605090105010510020c0901170a0203031c0513050322050904060501030510021216 78
    0x285884900003800d4a41c1902c2c111003034240440c0040520455114440c0c0151141c002000c46052210f41e610a078000101b8a52041c00c20032242640381d29940c00c0300c100e50240010821041141c402c42c10000c0205944c180c8117803180840e00c102d9a8001e204030307980c0e070400790000c1080074908001c21015034032542045400c0c80c0c680c10807400003010a600640134a02c00d8a503c107031950301c40c0320007000341c4c07540c1e11481c03041c10f020449940e1405151b07180720750650811003489220000b030780107034514440c846004140c18a803600300401c091041d84903030b047e180121100741d08044908412a2b6451072408440d40c1b210002004002c0e410b55203203d901042001c3c82034840c3e1020540002e4159008034020328401582184400076a004501c00ca5901a04451526221002c41d0300c03104c1daa8000c003040700c0841c0e409070a4800104461140c244002c00c001000c80b181850a860198050002844215880d01c01e41204400103280c600989900401e812061103481d078070007010b078440107080c1441806 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 804597652 1250 804596402 804596453
    0x10e0d05073e010f030908090904060e07031b05090103020f090406060b07050a11030d120509010f090305120c09060a0c0819090e07091d042d1b030b04 66
    0x80c140954000c1803003214008141034220082e40005440c44000031050701c1054076054443c1d0008040754240c0b80f0201c020388030b0603440e55942c9072480c000c1041d1100d4040301e124162001041008481901c14070300014100000c01a580e0418000c18071000c0c040294401d4140c40c81c4c0f135040c10f040340000c5c1c0c054000c20f004a00300d65115091400341d44007080c266565004625290180305960185a140c440141c0041200d1402c849004060554030801c80032030350b0f22040490030f458400d42101c41200c1c0300072403c001d0314a0318a405400396001c140c80c0d03a407040e48030340000d0070300016105496002102401c69880c010340101c0132100d4420000c0d040710705510078400303100c0001c00040c0955580000c4e44030340002d503090441407440114010800b80801220403000e0140c0601c80046510340003464032146481d44603454150340c2280c090124100c3d2004c5030f840d900b80c044070003a41103503041c051002411345603100c00d40035184001600000e4100480000814002811001000103840080f00d4600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 804598902 1250 804597652 804597713
    0x15031103010605090a1401021203070c0507180b030705030d03091a010b04170a020d351e040b090d15050703020702010e0102011407050d020d1805010e0d0507 69
    0x1086800c00e81285000920106107049142881d034800c01c0a8030181c50100c0280307210380c00003542c4004941c808078040001001062425014210403c44075500c041a18041c0d526006600781e00e14920310f111643d01d0401c0300080c000d04001c14a60309848001e0042c03e107402c100b6509401401c90741c6070481d481c0101001602c60a250115594042e100200c2411355a074942030307503c851130401040f0903580d6005248280010383c0d031700074920340103503004c42c2c06a800d0f031514250304107060b05824500c000c020344140050041654600034070540d54070483c002e54421044c825004140640e029007050090100404407261400b0304101c4c050fa84a059642030207151104894159041510103602280d0081800b80440d078200c9287e2107411000e1000f0084200c0d42145285c06034006466a001e020000412282c40f510790780440b4061034122a007408452512494a10450030806090710154604100d40907801000704181c42010001d070355080c01e08030141c5a100100d1705103221000310681c10384080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 804600152 1250 804598902 804598931
    0x307020712060b1008130b060d20090c1314190e0f0a0b090402040b0102120a081f0e1902040f090b130c050703210e0f070e010e011503 59
    0x40d082d218400104000c4038040620000409201c909400c0c4000e03072040110a032805200802c05035002100c00d0529150040460341d0108602e0300a488200d03800700401d411190f205281c3c03940a17055495207a280e0320303404101000d000318038810030381c8a55043c00304808052640c022100f2003004000012064400f101c0b8003100e98940e122002d48502101000040c08016411652190080800388a0241c2c0e1000103401213100410080c862683c034111100c46910070040403808050303841000380d50b9500d411000c1c0c041e220485140320307448221000b980140100b404060100c901520b00f29440391179104255100c8101d0003080491701d6402d110000f036044001880d00010420100c6c0003034110790341c0f820b10503011020b1030a88c0d00903080888400d03500740d1150840345000c0d014500b4001c0200400440b118100c032103103039038810908281c450083c800340802c5c0d1402e905604011614036560b00e001e4000c01d004c00740300f1011801443c1004103c0c48528440e5100c141c0072510300001c0c1340d05400140c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 804601402 1250 804600152 804600179
    0x405060a1e0207050c0d03021b0f0d1209051207080601090209090f1b0307050d0510030c060e0f090406060e1609061209050709060515030105061b0a12021501050405040b0a0203070207 80
    0x1500103078072014444012a42c0c0103585901002c041d110303082b1840343c48011855903600c003407004203540702881d51202a070740300e00303403100207001c0003401031040000e101241039440000340540342d400e010b660000902052140f00b160449800502845181c0d600d0440c4901e00300c1d4000c0485202c50040e0071b01004080b5200d000310f110f80030320340300d60b138540b122813070450104c8100900d400c0c2103000562050001c200d9001003042151351a00d062402c0e408200d006c103c07442400c9000d01e0304081400244000c10109422440584240f00d201d26256518625882c50041601c46c071078021075651942488414818001e4111010000b900403a1070300d040d58950340342411729444a401aa0340310400d1010749000711201e1402c00038194500d04550408002504610810740c58080e10210310b0341e40d54076a1010301c0035641c801d80150105040303005214010707441d06048410b80101c001d01d8000401ca44c030b05480303018081e0303420130050100c59640c1c800d408000d500141c240d83c25842a03200025001c0c0000b010b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 804602652 1250 804601402 804601429
    0x21c0f05150f0c0c15130204020d0c0e15030f1b0304030c05100c020c0d03090b03010e01061704050307020415050307060c05060705091309021c08030405060a1e0207050c 74
    0x801909900d005071800e9803201003d45405600a020448000d001d4030015146000c075a02c20a082440d4481d06403030300c0074051004000703401900110305402441080d074083c01002c00c4984610301c01b0202d40c01040003101c0700c3c0000c24011075081c40801c8480d1907035006a035126002403209580c0080d00346c034168464004a80440c0003411401d640b000304a01802002c00c4070b0f86d40341c003c1c031072002c1111019455201c815140c41c05140340c18000003d2501c601c4903035000f00b80500c01656656110748450341503880c2400b84401044940c04002c81d4444c950036454852030300000550308115107982008041c1c038803c0d000030190a002400403030740e44d0b410700200c801803015807514040c0b40030a241690800400070883c03801d00c0030034000040180c981310b40b001c00c040341a00000450a0b030038400980c41e020b10503004401c00c0c0d607002c00707001080300d00710045001d43c1c011403c4411755a18008640c0c01e54500502c4610030004065a031401d4041c1e64025010a52080781034581e6030342d520010446241807001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 804603902 1250 804602652 804602683
    0x50102031509091b2701060f09050108010302040b0f0901080d110a0201020a0b18100b030f0f1216050604030e1e10050a0314010620010207021c0f05 65
    0x2062001e8001810001c881084050391001080d150603922035807220054460b030a00c0003408918600c00c0d0359081c04040c0c1c1c40c8402c400c0c0e180c1c1078028420405040c0300900944000c2500542490101c074061030960741150016912843c03035a00750f60922010307114044010b030704031000148140003507546801b22406002c0410041400c0010707030800409955080b034080181ea001030b48002c000d81d07408102c280050340c2001040c00142c4403900e0600c007a07500e03510109003601a080c001d0304a046160001e51120008501315072882d101c00c404241c64913450140c42446038054004000b80010000203088844584050705007a075034651140c07410f004048034202c000410040c40040e451801c10244040c04800d507180006070f81280c408100d02c00d080e000154103110b8040b0b44054100c0c071a400031100c4201c0c0b0703c0415241c2d6511140909402a541e006100300403000c40f920b0902d01c0c05100f99201a5002130402008504040091071140784d48a020b5030240f6a10503241e0110b03004100f4910b2003a9000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 804605152 1250 804603902 804603907
    0x90303020a020706050405030d051b0102030108010b010905042c0102070f11240d32070f020f070510110d0c0506070e0d0b22060905060a05071b110607050102 69
    0x10307800078108001c0c0e03040001807003410720040c05140c03000035880b121086142416540c8140420a03540f0304400d0f800c2100d51980004000705180d80190090400388400782c0324502c0e20740d21501040141e070081a101440700910701203104003c0e00c1e860055001484a1f00011310304509512001d2568441c51002c0d220242e0303a8a000c0200c0c01c1244202805a009881110002203001c1c14100d843c41000079840c0b984e612048140c084610a4100b120701c0400384420401d0382c1a4030a0072911000111140000704003510b110482190000c600e2841c040081c2000d800c030b5509200030858111100c000341010040c1d802c4020041820400100d40d4000d030303a07140c001141520f49442442e0100081880b41000035a500d004a141c44a81c1c601008607840100c52600e56510128034a50040350301000d0720910500c004a8284001070f403007600c103a40110261145541c56640c10b0003903031000c2d2079843c000b60508803140d00c61107505a0039900d5900c40d003540513004144034002407081c0c2203080c0645240c0d600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 804606402 1250 804605152 804605167
    0xa02040908091054050909010b03100c1b0c09050f0907080a020901061d1e0a0801050606030f0c0d09081b0c1c0305210912070818040f09030302 63
    0x800322000001080860142011441130300c9800c00328180340d01d6116080c0c4607000a640d425500400f0060000a08404410710302954118042d10492143d5406406030074a8401c00741c01902031148600c03055190b501c000c5800e640d100084880224054880e40040000411003822074003c1600800c14449185882d00300400441c4c00d0604d01c0e40b01640f240e00031034003440180ca8030400641190060709200d02e030003640c02c0b49a482c0180c120f0380c603070b070040c00084c4d1050780781d2010a0811610805a40001c0c5458032420014200c0c2c03410703a0b0107644210180001548510b0802069074001000321506017002c0d071100504060302c0c2c21181c116115075000c030741f80b4400c000a441d50817444492500502c200c03000100440c2940041c0740406480800d250300440c01d150149044a0403121903007144410484600d8500c13106045c2900e800da02d6020384010070a21802d03910030382d4603d64111484600d810440d00550306140b40010b16103030400c0d04c920340c1c6c650302030f40c40c418040001c1c081d031800350b40c2f001e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 804607652 1250 804606402 804606437
    0x11120c031b011205071e1809051f03150e07030c080a14030a08060f1c0b06041104030b07031503052b0212040302130b13020408070509040201020a020409080910 70
    0x11031143c0203410500e480100329041c3d43c007070510b0f0150680d043c003180034142c0c00c202c21954504100141801c0a00c1150006100c645a030b2040e481243c00341c040030b92402200d00071b110490083d10014100c1207144840901d40c1e005980141c0301002c0c3d690444003081d0b40d030b0342d0311a402e02032030303110104940003540b88106101c0c0950350f101d00b11561001961034040c48440141a03480043c186a0103124071004000023610381000000701c039411600400c081440c2450f200d9082d02c0c0032100b10707001d10704089070f03c003840745018107880030749602c40c0d1001c1090355281d408a0081400d84800c42c80418071180020104070140304084102003684000c0f0203540e00526001c11010800e04200115404807a03400707012410102130b6010b5075411601070542c56800c44140300502201c205035a800b40703003a034081c0b00c8030744030740d000380115507035403040c2c0d00c15603500d0080113940c810445010340960002c00d80c05005181c158841030096225403d00c03420903d003080400c000c00460101c0401007840031030400040ca0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 804608902 1250 804607652 804607667
    0x1e100302180a0e040b09030c160f06090503070e040507030f05030a081b0a030e01021210060306061407020904030210020d0204030209181e0f030d1a01080411120c031b01 74
    0x20040d58442d01451902e541080044401080580030440700030110f145280c00340103c542248080c003c6454161084506c0603c883c010310548503005134800c070004015000703c90b060221003005025142c80c614040c0b08100790a00240200d8080c0900303c8040000707807000d0744480309107004070010b684440380307510090002e620140001c00600e40e46202020021704140846000d10150b107804120741e11844002c43c003a00544a04408202e200c0c410004010074504c0700c04212190341d03405110250707035040d00385c648001c10b456826910404010520160410a5609421034484d1040392039540c259071012040782c02c658510850740da00041d00b0000d40c80d02c06402038001d0050071811340d4606503445075955400c200e8030108948090760300050004001404180400c01c003c0040d60b44d9048426038403c02031107100388070841218000d48a0900e0f5101d80d034498800ca03801a01405403a01c03150030891400c0004107025814410f5144484241d2001e002c040200640400710b103d400606400240c20300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 804610152 1250 804608902 804608947
    0x7060203150906031905030c01050117060f06010c080a0e0301050103060e0d0813060902010c0506010e160203070c1a09041103040204050f04030f081003051510090b0f1e100302 77
    0x500c03401c014804203640100310f02d81001d180d508200103400186c502541107020310110300030b55501e400e0002410001c0525003102c0991751201b5107600da500c0c00b03000369850304162016800150710700601c20005007010000e000b804503d05161110f02c00510009003940d070241c000300d134826220132140034524000c100c0f4500e6410281807826552520100c92130070100071403405000e644c0c8a0f1102c1003564014020300424641100954103035603190b04011522200c242c0e0030780302c90003040b009010310500c0031040d0b609070780d8020400d6145a207404030052000d803240c2c42090f60f1080c00c0192032000c0e40e9601c10f0544034500c1c082e0454480c038080c0100130441e00c0051561240100030010480006d41c0286000d17882055410254980d03200e0310140d80d03c2c224180c200a00074416200e500e000181c01004261003112603100151032192542c03a2f04003521900c81c0c003503070062455400c4407041d00c0c1560f00e032a0307000c1c054008403484035507001c0051003c1c41222040e8011036400103c40b41c94644244110100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 804611402 1250 804610152 804610159
    0x1509080118030c17090a030f050c090f0f07020106052d09101a0415080412020c061b0c04020712020d1806111204090c180605040b030702070801020706020315 69
    0x1d09001c2d84002e0041422500020440e81c03619501500030303081c41007554803042c0301526194505172203142090712a4511a4161064411070701d0b03407000303031070400d4030948104e0811040c0415a22034018607000041d010302103c00355500c03486e0104413038441c240c2c0d203ca000310348101181c490880d9100d01c5801080710b0001070140424104119980904030340c1c0804a50000c40103c0440c0c08a801d407281c18084e84e0040c481e910402d220032031b1038542c0700110a0142d0f004aa503188091541c0e50103981d107131807034a0180c1c0c0010b0b00780040c000c80240c03120f0100c10442090b042c1c3d144400c46c01c0c000780032a4440304080b80e21342c001200300c4140c4ca5040000c03100003802c40c100443c030860600603d42d5181e055110744010062240b00103107542c001400b80d51900c0c1d6011501e280c54541310840c002c040c0ca4880500720001d40141d03400071140c481d45c600e0380f08a80003030320b500d071038181002c0c88104240e00040c480029840740e00c200050b0808248014a600f0b4080c0c1401078590904803820392105226040c028403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 804612652 1250 804611402 804611441
    0x140102030601090b0a020a080412060e010603051926070b0f0402060930300a0806060c070602011b0e031b04090803040b010306110313030f050415090801 67
    0x100c0e40c00040303030802e592010b4104c0303459140e1000124a0100810401454100e02240c0001d140c90700322481016648600c0e8240709a0a050004908035103003480701800c2a8007130080c010480d82c000920904039800782c0709200f65004080610004007980f0002c0d01134107070300011844c0600941041c1310380c01160442110000c3e081c1034001402c0380c014007500d18412800034003a0f120007070b00b20341580742c00c183d00c846003004140f01d42d50b49038589a411021882c0501070b089401d504e0140005d4a9000c5030b40c544100e800c040c2203602c03c131200c0800904003508030360108850f0b9030300d0300200520402042d4503400801c01e802100a903a500324032501c810400d00545020b56a181d0380c0100c2d050148100d9940c81c92500f20340300c03000a010b480c05c0ba0018214040000c20700044c001d00d500c0c4103043c1e80c068001800001003100d104445e5110888407071380241e02d843c0414000900c01c20300610700a19502d0b062f420241c0328081d6002080e8551203140100b503100e00c0420a50030b0a01900243c9000d0401040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 804613902 1250 804612652 804612661
    0x3060a05100836010b03160e1501030204080a050d2006160e130f0b0d0f110f0a1401110706140c0f010504051501050607031d0414090a14010203 63
    0x41c10302d880030340000141c0048035a1581a164403042e8103510400b091140d400c82c0805440c1503000b440d03807142c3d450107030103269400e44481d11210000740460b0584402c0c1030b00382d611a40040f44040300090703200d0405070204000604074a0401c04c0d510014041c0740070317050784103682001a2103010250041e0540c1400411951070032000410046d138411903054a5140b040303002c4500301c40200c8a0641180c1c04590001c010001000c103902441c01150b81c1c00042002880005c10404003410487c2c0c02401003540c01841d10000e44849224082c42401428404214891800040704040c20b40c10a007039000307000780c0c88020356a0200360314100000c0314000d080c0e80c0d810400c2c0100700103955170845c010018000742c0f4016101e010001e900d13040b0304140080060b400c01385002500e640142c05543e0090500d00004034003891b0401c101d442040d41915004840c4680d6500c0310403c41009100a600030b035684081d049020751034510030720440e50100940030100540c80c0020001400e80011030b90744e8418030402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 804615152 1250 804613902 804613907
    0x3081b011406010c1b080319090e060d02060a1202040312021b010e190302030a120f03060e010302040c050904060303051c090b040807050a1a060a080d0f0e1503040803060a0510 77
    0x3541c01c940020010321402c4480c000317125800400c1c0d008550a10000074001110141d164190751181c040da541c0440d80707a510490440000829510389922810411007a001480d00f50020b00c060010b80c01c2c43c5c034150001c1324032941240c010354419541c407515000030810444e8180000e50605132002e02c035135a0000c84800092562400401c9580034203a040c61044003490004265001180d000702211840e81003803030901b00c0000050002c8010400400f844004103010340108000e030342e40c00d1584160303681f95800b0000949605013444c03003031010030403586800b0703241c0b80150b02c00346010761101035032103840104035070309500040314940145241907040000582d0400556030001d4000c4001c80d20344089050050401c0c2100e06e000348002d00342e0341c1e000c1401c40d00c1508644a44c0c4102c1d0702180441e511450a85c032040d4030203525000a0315400385c0140d5501030001d41501c10f0001e4598510041004a5010541e20581d02074035124800b1040141c1d81c03603d03080d0000904410703100c185481420440c007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 804616402 1250 804615152 804615167
    0x40302010e0105032503020d1e1409100c140c0601080c0d0809090703020c0d0e0901050103061805090f0a0501241503050408120f16021b0f040603081b01140601 70
    0x80e41e185d000801d08000d840da03c80e4050361151241070804105950480600b401101408101c0c5a8807908144035580c0c0468402e1850b4414502c00001c0d210044803407141d10001c000d021010800d10204400c80340c0c0208002000e05110320042d4003c0c141e55041198152030120111002c611404080d0b0000300082e51100581e40310080030381c1c0704840c1e6107500310250064010300c0298906445052102c01c03980b6880524080c14250075a007045003662100e00450541d1003500850040c40d02d10400400c0d20422544250b40c000740460540c0c94640114810509000149000f40d40c01da44541040052070341c5c42c03d443c110304000c0d5800c800c8052500ca0285001c846d43c0990358140750303070f0350001814800600111881d2070040300d410349407850000840034000b8003d4425001000c3c0f511580412140001101e609424825080740c0f06205101c080100600c1d0110440ba0400d442e0b03100000040d50781000f0b4100e007400341051507103d0003002c0580c2d085581518415099450b080144030480e41c22012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 804617652 1250 804616402 804616441
    0xa0f12020c0a0b09070b1215040b0109062105090c0a0b070c030f08090d060507020f0624040f0507051e04030b040f021c0605060f040e03090d170708040302010e010503 73
    0x54000b45503843d940c0d100c5c2401c000d603000211405e00000c2c6104401ca402070503078072805000d103149110783d25250900c001c4401028440b8040343d0704120502089009130000740141802111007600c6003007454485c400d0715010f40301c4440e5548100341d074529501c0c1500048006e40702082c0741c01c1c20401c494451800003500d5200c040c00c00300315911a901880000011138044c0100980b901002d40081c0c5443e80007417100b02c0300d582c014010109100302482e004a0100c1c0120408002289070f07100e0440c0b44140d00e141d0304e500d580e02c513a542004070511071150085038420001519100d84a0328020b40040310900c0c1d420802c840d0b05400c10050000480c0d042d50903801a0b0006140d10300c1c0d1081e03101080010b003800d2110144414000c010030308000c02c50b00102d105074001d844189219002c1c40a0006981008940e01e129030005d000000e4641002c0b405d40ca0f44a000b01c0c80d03983d080010f01600d540990201205990340c000002c0e052040d545c1000303001e0220142031a103540356150444000e11440320151 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 804618902 1250 804617652 804617663
    0x40303020d11030918091e0c0315040c0b160c0b1306051c0b0f032d1501060e0105090301090f03091a0f07020d020d0305070605011a030411030f1f0f050f0a0b0a0b0a0f12020c0a 77
    0x3b0b17184450b1000070104464a64485030b00da100c2610750ba81c0710016080209180c0744501c0342e00010a4441c4100103541c0009040b00100600308806540c020190404211041e08540c0303c510140c4141d8080051041d24100c0341000d0041c0d9000120313400d41d070402e03082811025403007011001e14800800715000c0c115441c40c40c058426189450040b90584603c082c03941e0316600304030011080c402c442d80401c110728400d0722070f449403a070b032000e6045031601c0b0482d01d5424070f1014442c0740c00410001000b801c01500c000d0858100a03880c0c6e0000c4c1603041c8032041074001076004129a020068240b1543d4050f04210348000074a04420341014223a10000700020807480c071412030b0140303a460401c00b10240881c10019a00c440a4203c4450720141c0d40383e094014560418500c11081102d03485030b1406a005590100501e17507468240c0c40151100c500003139082503800900040c3d0381c4500340903000c00069503513861000003074010010030101d03c1c1c01c401900e1510400c01b0440707c0344001150000c10b544030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 804620152 1250 804618902 804618907
    0x3050c04142a03070503160306151d090907031401020301050d080a030f181a01030302190f06141f053102040303020d11030918091e0c0315040c0b 64
    0xa00301080c480842c550614503210300881400301458015015600c01c83c41c445103400d103040421421010764406205541c0a580034601d66240b107445001c00100369084001ca4030741c4020313030710701044402d42c0c11110542c0c6600540e00600801c82c02600600c0000c01e030000a60465040000049440003449802048810001107000c0c0040c066086821905071a8600b0044c91f0b4064180341043d151900c0f084800303d5284400c052507030003401410341a6a0150700401000c82614060044610300240c2910382090005141e000070300c082c06030f41d000c0744106042d448182010707900000000c8a0743d03180340740072641c01000d000d076450f840e8100e0116994000700e50402011200480328601a500010a0103400040c01005054001401015034841c03542c032420101e089400303180d100d010344c04044c0c3c0d200301d0342121010410f290100d4103400c010040f05444a025020040001d1000c40056125880d003040040c000315140c18080d5000010060035840d659107815071b20040f40207030711f004506819802 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 804621402 1250 804620152 804620191
    0x3080a08130b0708060a06020a0c050402090a09060909030806100210050606070507080705100f05070201030911032e0c050f0307090f091e091a070e041503050c0414 72
    0x1100124101d03401146009040c10042802014000704036040c0d80207081e9001d00013501480000c442c900301d44c2181240350511b0400080101035804090030542c00015403c0c0030ce00001c2e6031250320300900d0400c8000602a00c2454042c0220700d00500e03c0d807103a07944000d0000c0032600441c0c0400c1c80c1450031b10000780c559a450010b000c500441001802ea44030709180854806070004071101607540031215031032080c0b2101003c441d14200d032005500001c030103210a030019406600310301c10003071041803000741c0614488007192410908580c06e0009051028030107003940021a0a1a4907980300c9105101d6901960006000d903c80c80e00d05080401700000001d80c0b00d0711602c1024040c1001e4104601d03001e64420090001d440c181840104240c4040500b00c1d4090141c418200c0c100e42c40340000c04100c2c000c103840001000e0081445041c031185a24180c4540d449100e550b04020340f401d15040100c0c11410424030340780300124038a0040b841c02050b8102240b0040c00c0f01e82c400002d00752070301460103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 804622652 1250 804621402 804621421
    0x15070903051204140a0518042111060606032e0e13020a1a07032a050f060609060f04021806040f1809110613080d0509100819020c070f090912030603080a08 68
    0x1616901c4034088045407085203546540070090031510002207045903003a07128335041141c03510040c0c8110729411044190101c2a203084111001030528201d01400000c0d5110038404120300c00700c40c81c8034000c4c1020180c0d0218030704100000040c0c5140c05400058207503041c6019410710466900be4140000c210004000b4003256090000c1101c0c0750803040106805460020385c1ca242d007002c5002180500b0002810500742002c0e03452140038014041c1d44210845420310001f5880303070000c000c820303040c0e02c10a00d01d03496440092000308252251507501c14640440c00d8031499001d400c04d03103002d040500f0100445c5004c0c04445107004110f80031540d030600c5203c14403012040354031002c4217009010180645580040c042c00004000391044400c84080c0d079801c0b902c3c2d010440f66100c11452000140d00c0281701c41c1e000d08000c5210000300c07120030ba02c4040b000500942580013071111030700c500c01c107020040002188030100031581414484941160340c0d105480c0100e001c07040420600c540064607002c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 804623902 1250 804622652 804622673
    0x106031e0f0611031801020309030901050c0f0114012603030c21010e010f05010503040b2e0f060906090609060c02040603020603090d02060c0c15070903051204140a051804 75
    0x7548402c08004095120503c0b4041e40c2040301c8007802101c01c2d10001c10550418001c4911800314040035602c0e14074404019202c541100d9440100740c03050510046030140300b4807840d500118030795070f641e05540c5407100070300d0101d4141d520807400180102d00040013500003c103490f0070403a029503083c0c4542501c001001c0502503c0150711544441c00e0000490141103030078281a00c40204580600948540040d242c03480103170b4000b80101c80700400900000d240010b80e4000030100010b1000022180c0800c01d866009504441541c01c8045810807000c0e4105200400802c0745040240c0e15905c0c056001c1c2078440300344646400d004103120a42c085544a034040c00186a0003058251203080804500b0356511582c43c00c1009486040046805400c400302950704900740500244516114502c0b801402c80700a40202c0500c4270b04040400061000d01c035011315616400c1030f0700c2d11107180c050202c9000c04c0c15140705010b111156814002511070310951015150300000e018040e880d90f14000740b544 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 804625152 1250 804623902 804623933
    0x606070219090207020f041a041e0c1e0309080724050112110f0a0b0c0715110606150307030218060d2c06041202010b040912110106031e 60
    0xc00501e50042540355880e8050209140252850071034a441c01e01480b0407070700c0c0c40380211400080e0159003012481c1c96040108181003154001d911355100f440803c06032045194100007260031000c102c80300504518000003c2141440c051081d4203468480110b60f1240d09806451028100c2d14911075000a00e40b0509040600d03604205a69441c00d042544a41d8410101d454480d08820610180750402c40d83c086140001d14a151080c90301131302d079809600103140a07485005030b600000d0326000011142d1030171001611152074418000d038101d42420740007400e082c42020344242c0d0069080400c002d4070f9101c1c009040045e42c030300c28050385240c4504011003a642c4174100182090180d0b2103900701654145004690030180d5070180c80c040c843c07000803459086107502a400003408116410189003a00c07406000000307038541a50b01003003d64482500903200241071002d80f2249950049554030240c25520007044407a0039555040d007100e10900505143c24203082022061102515003030254 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 804626402 1250 804625152 804625189
    0x1b0a051207210e060106030b0109030f0311190807030c060e1c0908030f0d05270607090e060102061519080105060a0f0b0412030c060903020a02040b0604030b06060702 73
    0x551408400040950440080d114090150340242c00c22041460062581c0101d060000d081d403a8203002040f001010b610494504100c9035a40c000b011070440580c0040c81070182d641c41c0c501d15280700700d40d843d008200741400c2002e0903600401c00803407031190503109080c5d41458000b550202a04248001d41112031079a0300c2d170f00485140e0030a0b101102c0c0544004602900c52400300d0340d0b109100b944030b0003640c8924030034013003c0041390030505440d40826400b00200e079102c02000108100782c40740610003105044140e1105040c03200745600215408020500311402c034501d4600000001c0d00c2d00005440d955954411050528603559040c0042e42e903050354a031401c0285540e107024501805d002d8801c1c40c00b078141e40740c011402441c9a184c0005454441007000d01d040c1c90091b4000fa1080541c0c400c1c0d00700260000c800c000202c041c0560302c40d13030b13000f64000e00800b459401000215489101210f01c11001000300f080041c0c45441c1141d030240c421610f2a441e1007950010035004402c40201194 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 804627652 1250 804626402 804626437
    0xc030803131a04051b09190612200d21090911070c0b090d15180809010e010923130501060906110d2f121b061b0a05 51
    0x1021904408a1145008404450000508040c5c80c5002d25180f91030a400400320800101c2c1010780c40001d2000c600c82d44000102d85a84101e081d861490401046411100b07080c1e01c040c0d070103240c001c90400c1071002c40e010400c100d0980d030752a0f92400b01120503d001c04c400d14140035681d0090b03102c0801072401d0341c000d01950f40d43c003400c07680c00d078401182101d440e0240440825a040840152010158081c0c240b041408494a0310b03401206400668612240c44040a01300712074503410840400b4800c004854030303042900000340c5500340d802e40c007034108442501c0422046505a2441c100410032480401d031808072003000c100f12071403216034070080f1400d01c80002a900d030700c011410304070f501c01d54501144c4541d070041c50b0384a804038500500001c080c4c41400203009c0c04c0301c400090344080262502588030440507024100b2400c01d400248000b404100c1c4c9400b0080090720182c40e60004014081a1070442c10051018600c0c44031003019a10100f070100344140900121141002007142084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 804628902 1250 804627652 804627683
    0x7060801052101110c12030112020d0f120305010e060405060604090e010908070b0103151506031e14090f070506071716050c100f0c02010e01170a05010f0b04030c03080313 75
    0x4c13031039001a0100400f03100d09000000b030078940301c050340d05948442840c0c0b40f0740c4060b5003c02c840100c03006030035a040d107111190000020042c0e15011500842601c020810758504513110480510040080d03016a0412003003244540e146004ca60550f145401c001440468442c0ea0900408000c08000c03c00400040d11030180312408580c14100c81c07240041d1f072400580740c00b0400640c0c1015583c002d805040800600401d4003980002d4400e20f40c0d1803040c1e0000c5001018002540e40d8056541e11100062040c000e007450180040061003160000a010080c03030100416900d1064600183c0940380603a5038440390400141100c4a0f81084500c00040d28124106691581d014003100c5220f41441c4403901c1e581409000c00041011494682041044207500159645c0340c00000b40740c10004402c10703564040070302306082401440e03180e034005150b42c1440400d04416110340c000c0907480205000c1000004c500e4045801529030200c5450748a8980e0007c201d40801c1100009000c1c4401440a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 804630152 1250 804628902 804628931
    0x50f27070b18040605061309020d110a0e01030605010e0604030b060d0206041409240d060b06390304120c0e040b1e1006080402031501030515010807060801052101 71
    0x10342400702c08580400002d95510704000f210f01ca1084005e9444071101c604001c188156800380419520100c8089102d420805641c071f401d80c000071090020446130b603442041075138944101806480c0a003003070100600b0420000740c0a01662000804441060000a03950780703070155200c0400754080e241d140c0301d5480b256400b6a2010140e100c41c09031300250002402440c03640141148001003d0020b21039114900a206801080d405c060380e149403640004181c07511060002c007506007440400241d0746d06000c12076841e401e0151300f984400002d400c4115004900402140c0840d642d842060110b03010700d1030b0140c1828199441281c0300030050701040305000314024114402c0c8040d4104102c80240442640074500c41070392800a50050720100780070380c0c1d006404c1c05070014001801c8451940f070700749014140d0071003604100c4640d0800c41d1512001c842040200f40901148409400c42c1810000014801101407042030300c110f05217130751400080c0441d600c07a15440442c00c000c0c40f2104203191007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 804631402 1250 804630152 804630187
    0x30405060a0e030405060a1b0b0117070801020a0e10090306110301141210020f0f0708071b031a0a0f0f05071101060509040303150e19050f27070b 64
    0x2900c1c036030401d16051a4140084126010303164000c002c20704208111030112401c0105148035100f5134019031981d40443c5842d10b519009141c0102c8500d0140c2400340c0980c10840300354000300c1c03107a0041c01050f4030076400c11100403003944165801d802461013690226044c0716140c1c00507011078900b0901170400f00051009605840304040614aa041041d061014241c1b40c0380c0390f4221070704110458801101c040d001410b24010403040d042c05d1020030b40b240010360b0b0202c1003c80e000c0d00001100c0c001c0101c9443c5250000984404080e022490751300d405809c0c1185840315001c0c0c002d4240080c45405066200366000b41c80030300f0402100c400b00c7c2d1964000c0005486010118590000b4040391071414012541a2040641a001261030302d41d41075019001e040c02c50745441202c60300120340f000902c030040b403045803e400d5a541d016502c01d106401c03500054151294101035204204104d04079141e00e50811a00070900481586034074562420820340340c201103411400080d41c8100e100c0c00224 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 804632652 1250 804631402 804631411
    0x3070507030e0d030f0f09050a080309010206010608040b0105040b060d0c0807080a09030e040911130510150c0b06030708011505030609061614040b041715011a0d06050603040506 78
    0x41d842c0c04000d440007044266000c84000a00098034140800c0c0820f2080700302c0a011403c0f82403000f059900c4030b00081c1c52240b90380001e0107552010a031039407a580d040112a0061005041007519410680c98411044030140102800755803540071800c13541e00d800d0115003c1682640c4104030740c000c0c51400420b10b20047c0c41a20009480001107644104603100c0ca9011a03403503160740d030110704014180405000c40d06000d49017150031401050381616031181040030482c15241c0050b82d4030b000d02125090610b5034101ca45003a08880e0009411600920a00146500300028801e40c1e510341002a181c0015038200802d0355090410144e00840d03e4a8940c0568108605403015540d0710190a66a4402202c0c50901e4801030a40c20110301d0041c00d41003110708078540c00500d4141c403504031352002d074001e034400b900f01c10f13440410083c0d2550038080c0d000311107964054240c1c02d51526000000103100c8411391643c03500005600c00034441554010401410301610107070301c900d042d0902079229441100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 804633902 1250 804632652 804632657
    0x603070611031b101d0c04050c0903061006030c0306030c06030b0f15070201030e0d0212070c03051b040c020a111309050d0e0310150902030901021210080f190618080307050703 77
    0x1102d003410f4200d0605e0340d00d10162840100701c14a035441c1003101410014060a0000d90104143c2c44c907600d05216152107180f0021101d2026803420100808840070986410101450890140000b0b441071a01f001281c0b051720340880c2d007440c07ca000898080036021880c0d440401514103181010310381000d051001e0003600c2c104180d40662068984900b00b4001c0341700181c101c0e02e148403142c40d144c1e000e482014002d070313000101c042e140d40d1882d1a04180d040000054400e41124001034549401182c2004003540702524001c8201e076105d01c010032491b214103110303100700300740b200607945980d00c81d012082d0404201c0e81440c02100018005615040d1a02c1c0640071f50301e004032190180d0300801c800c0100c0e2541c0710041c241350100643c029003006e4010a059502000b0108802605001c21405000142a500c0d10700c0d02e40481c81c0d1800b101c203030ba403228640040e40a80340c0128403000b0700c2d40340f039000003000c184010440850384480546060041070600c011040c868205c0d40305000c0c011007440703078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 804635152 1250 804633902 804633911
    0x30c01030213090504050a06050403030b1302131710050408030a0501080a03050405060703050705010905070906060e010e040c0512010e0108060c072102071a031504050603070611031b10 81
    0x1400118181c0c8104420b089982007955401c00000b20140d21442d4020302510036906c124407a60b94140a496083d04e040d00040c0d2181e40302038070b615018800d5265411038800c210311b001000d01c00d46040318020303c00c031309070950314204901150400f40400d510f091014001009039282628104206400c01c7c2c0b030042c02d0754a0000081408003000030100c446c5c075015262141002c1c6813404101e415032000100700e003042424410384001910902071040d4243c1f2490180c15154203003904101190b40d142c0c032880422010b240c14442c180d0b044a19041d081e0000d44000c140304042c1d28003070f1014880c0198001080c0030304800081d040c0e1407501040d0503290120107603030103501c1e0001c840049009040f0041e01c03651000604050034100e5020b4428111003a0044d9150700790b49819070403840425080c1e2002008000007041031010a40c210511521400c8900300000e0404002280da80c1242d402000d045c08076a91240c1c2909100704291044a40f6401e10015108480d40d41c03244c07a06800481c00c080740d400d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 804636402 1250 804635152 804635173
    0xf02010c2310061d040b0406090b010e0f061c0b06060f0f0c010612031d0d020a060c020f0907020706140f04090b120705090604021e03040503031f050105030115051b0c03 74
    0x13152425682d061110185034040d2034944510710358120140085503090394035243c0f400000e10820010b03008107042080100ca07460b10246002034000010030031449180b007c0c4480b01c01214465840e11140d82040c40b0250075174400021856910503108401071486c808240003448046520041594241d8080203108050f40d8020090072241c032502d000707010442d0104903050712411f250740b0f0049503000a2a051064440b07070003203110010a500038000003886400310700154100b40610390a4176030b090f240340f401490110b4000751903074113502916081004070304a07022001d000c0d90507241d41249140466659a581c1c894841c02000e659103101d02038040c00c590b10754007100100d18641110f001401505d4240c1c4d07800308100c0294840d5081003c0d40c41080007071078a5041c45400f551050344a400150340d80d0810a604c4091010071084014580884040500c01664410706490440e44482005c0c11084e60022042d560b50003407200c10f40764008540d1640161200c002001c0700061010b4040c0c40110b80d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 804637652 1250 804636402 804636419
    0x6010314010636240803040506030f07201c02151612020d2a0507060216150911121f14010e0103120c0f02010c231006 52
    0xe40b40303d5070034090300481e503074200c642d4164821070b01014020f400302c10340d40b03d03c4616021122089070020f5241c100d8699002c0c030b049540521005081408001c0d0704062411000074900c1c4001400000342494040201c2d0415006a054011b0407003140f0860034030124000e4025510000c54038001d00340740e000710021910328008a0040310849072104e41507459504d0014a2500d4110345402d82c3c100215919010b071100e1851024008160718840082280f621070036030000c038000c0f01c12040302103108041c034051545810004a60440e94803000161710303031150b03400e01040107000f030301c0c00303401c0e841c5850243d0070014581e0300040c3d02601c1032480440c510401390a01c400d4501466056007a0b03130014903d88400386515090a40340d4210860100b41918250300c1d2011440082c0d0020040c0821680180300b08400d40310445c411101ca8504494008840c0d1100411100d01c500081d05018019404034140314113403100c200716251001c0400805040400440d90f26030211b2502c0c1501454800c0206040e00e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 804638902 1250 804637652 804637661
    0x130e041a06090129040b0c0a1704060518031c030506040c020606010c0311010605030a0305070506061005120723130e01032f0414090c01030b03120a030b060c0601031401 74
    0x40c0113019819115001010614061240380c901001c607240c10300c0001070070b10700340004080b11070b404405012900c01c64640703e2032500c220002480000f006000c03e01c441507109040c3c9240c2072850000c032500d02609070203c1c1c1018440c82c1040c0600c41c8046c406103025030990045c0340218020b41d002c00c07280a0000c03080761140030a442017030001d240c2d420f2100c0402c3c490f103143d06140708084000500c1c59640c5c40000d181c1150240100c0101d00041610814090700744001540010180c820001712030494400078140d1041c02405012410b640000ca08603030701c501e400340402116005aa8500403025040022541058000d2400c00400d0360303000c02c02040e66406141229403201070103010680502802892101d004c221440203010b443c500010396555015118400001260340c16207403c11488540c201040400454189814020b904002d61000100d20030000070860311651251868001280542920301e000381e840540403d5414240402090050403284a0b41183d0f034205045c40c512800d99 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 804640152 1250 804638902 804638909
    0x3011412010c02210918010f170c13140709090e01090213022b1406030115050402090a09110a110604050a0204151d01140a0b070206130e041a060901 65
    0x10b1300800ca5280c141c10418114820760105020030f281010081c0c0082240105085035000380700d00000c004000c10b07102c180d0441e01501c0140d8010381d60b030f174407080c0103a07860745040c010318000d1a00c1c498407a8001d41c1a80246219042e2a103005198100040d00804044450044900951400ac003001001c1c1e070501c130390401251302a000d010054089445100250040f20744405d808520369004102c00c02951180001c0030b008881c0000da01e80d000c40781c003840000080425020380e140800000c02171001c07504d00c00c21110100c6015980c1c003c2c1c10007140e03e07483c85503c20100d80342000c6c4484070040c851030281820319103a1352050541c04001004a5071101e080d41d02400e150412201e280142c28540c001d60a00300105030080420b594965084004c0c0d550020304880c101079950040c0f1929402d43d03009058144201d45d104580f605150010034140716400d40240b0419001614000450380c0c2d01e600c0000b13001052112210349064103250b41103951000540050074081400542c0b1454105a901d059 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 804641402 1250 804640152 804640157
    0xb0f0106181a0f0702030708010c180608130503041a1803060105090f060d020904120807081e061903051b010504261510060e120d050d02070803011412010c 68
    0x42c0742c1140002402030b840724640c0080c03c2c0040000e040582c90820044005200e0f6000000b80b030808000010075504104404080500c20100304211540e4000343c01c54000c0660745010300c4500e05498154a940f2032680320b1040c0c1d20403e80040004442c08001d030110070913202d02c0007400d030a00c40805032545001d014096200c2d010b4404110490b040d008001d80c03240c800740240d01c20078031035000901c080030101c6d011030300a0000302c43d01c0c6001e640400c6554102809042845040c20225a40250560001901344100803000000794195403802e810316980d00c0250103510000391039041041d2907032410f1844508040600e6440a1036511840840b422504450404801013030301304602d50f400c00450154030f90922400003010001c07502900044e01030314440d24598100c916041c00502005000c00d08544128850002150044004600c6024003075143c58041c0c1d48400d80350010000f0b014680010708009808400401c0b070103d2080c0840381ca0340308903000611b9190f0505101e00303954542c0c1041c0f00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 804642652 1250 804641402 804641429
    0x60c04121506030c0b090f0306070f0f091511060f0103020d0b09101517030906040312110102210108010c1e03020702040f1d0601031e0303090b0f010618 67
    0x106007410410306440c41c90a8010607215642d07152a041e0000d50340114010100c0007951030b00e2440c110325034079900c80003500603011030b00c3e00d0721014003e0b0115860140030310060f1408180c203103102c0d98826000d000050045d26180803000001444800e06141c40c4803540726000110b10000d5042243d0390489034020121882d420440e40c1d02c40c10100c0c09801a6054465409003100e12074050148010310000c07001581c40c01071a00d00032010104024100868076041008162010b894050498081c2d940051004404400e1a40101c84450820865453f03d520109513480020406041c580002c41107032595441c0d640c0300d9659074202c0d100110702130041850607101641c0e4020744514280d1400c0716003001401c20150b40c003c141a02c2150040146083d0740f0840814207040c00104d0240106004004000341e41c1155107441d51828000040340d07501c2c25440c002c0c010148a60005400785510181c490010b003000382c0c030701c417800c81c0c280248000705400044440d0464801000c400464274021583c0c0c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 804643902 1250 804642652 804642689
    0xa0509130f03050f071a0c040b0f0307021203090d0816020d030b030319050309060f1603050613020406020c0a05060309030a0507020d170a03051e010e0a0609050117060c04 75
    0x40ca280608104400340541032040001c0300213a44003901c2024001e20070303546400c035400600d2852020092582c0b808010922080c00020706000c26200b00b840c513001d900750741e921030307000c00d1f4030b07200d101400b02d1007070100002008032040780480c49545441c00c40d2a6484140c03202200640d005001c120208010383c00f0401d403040341480b94100342c96202001d03041d80c1c54600b040c0e140c0c0900c00c1e1440b02610120308000244801004204501c5a00c01004605002c80c3d0410900940000d030815414004064860300072174031039940c40901001e105a042e00031582c1d181d5554002c6d480d264480045440b40244400001e0345052400c122881071054002a40c90301d07400c3d420a40300340d00601c030b041c0d0f003186c8901c0041d00091000c0703410200501603481840d85880c8540300003400d8810051800a51240312516172441035075000429055690f0402d401420b81d071450358110003000740303070311100005040c00300010720503c6001214200d8261031040d20310ba41d840800103071040c800c920801e8051500c1e0785030301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 804645152 1250 804643902 804643913
    0x608011409151f1707020a080d180614070f20030702060301091b030c0c020907030207022d0f0f0d081b0c1008060d0308090c090a0b0a050913 62
    0x2940051100000300a002c0441d0109000319007810314440301441100f20a038400703404c5108541814200310821446181400d0700a444609101e001000400040b5550710741d004142c101e584009031009a11180c11000e0503c80054002c0c03c51003080d4540e02d402040005103c1d54042c08100c04a8440b200d03061092207030340f082c1c170781010030b4000c03c0e0000f8020b900051761404011070081801d6500482e03414150700015292500071200f210625103001122540710760070403214400241c04403402c030300903a80d150096019200780140258041c02c07012204000c070100001101e07481c082144466458103164060080c209401a94154403118002e2004194500b014400140900c43c01150b810040e00d070f00c51118071407a00340e4a110301d40120140c4001420030700300c03945d0f900c00c16180c00a442d08209002c82ca289031480b07000303010010392600140c042103080000300c0030564050119416403402d0302d001801031003180c0751548a861242d0000405140260040f4054143e020840b02d00c221256500e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 804646402 1250 804645152 804645169
    0xc0d095c09100b18040e24071e020d12090b0a0b0f0a0608040b060117072010140108030307080c0c0a20090901060602210403020a03031806080114 64
    0x34000c40541c040b0000c641c0f403a00c0b4002d0810301c0d0018040600006451007000141c842055001c00c0310fa11500d1001810315160080894040c0c07a005074140d10707111504111000d03245a60348056049030084403510099002400c110149441e60b039408002e40504414019262180c1c400741501b800103010812003105940aa0121a0002c045101c0c540e566000314117551880d074800d1020840c0842088103201d04d08010544c092424a06042685005808601c85000c040e080000b040280800c07210300c40c40b03100030708040341c2504044811008204034004041d0009008a0a08483c41e02c000542d075507002040d207014448549481404ad620041da600c401d400103850002d4030f2180103100c4011681c1402051495890490030501c0340e0f0a00d0107001c0700c4100540800340e10381c5421001c001d00c660116403165400756a15600c02400314641140c44540181d41010b90700403a002d200104240d00410000ea64100c2400080740c40790361440195070000c424801c0412420313842c95450341d0381c030b0010300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 804647652 1250 804646402 804646411
    0x301260102070b0129070b070806010e04021c061202031207150207060501090c0807021c1101021305180c0301090f090606080f10050c0d095c09 63
    0x10b06248040e02e51415500c405c1c0d00000d025084403c5510071068029107400080001042c42441c040e200d41d50383c104280d0041802c020403d1031030120300640e224042e45041c4400c018015903c81a4087e41c4030f103d0383c0a680d068030240d1911200013100303400103840308800398005000d0401c038207000c0e068444560003041e0449a132441e03d41d150300c002d61240701601070a4052000010f5940c14414044116009c0c400c1d100300344102c0c1020030281c10790002e03a1840b9100c0d02c40f48200803448401c41510071611407071148055500104000078607552565801040b00c4080320381103804195003107404002001650034269001c0b0070001801400e50a41200c52110304540c2c000450440c5501c413401204c0d2030b80c00c0231038542c0080107200c1c4c076135004115038003400300c2050003000b217410300c3e9102c11300c0c078400d031010100542d484500342c0313040c0011414030b041e1080700004907020380c00c00d201c043c412442c501c10008941510000b40c089850040b04842041816050700a0451a01c0c076000c21406210060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 804648902 1250 804647652 804647729
    0x3040b0f1303080702150304021014070b1515040e0f13020d050606040f020909041401090b07080103030f081501120b100c0b01091b051810170c0301 65
    0x2041e40d49001e41000c01e0001035002c3c00000361114800d00c1042100b034a00c0c40d1442d00d100041c02484050780e10240780441991080c240b4001981e0000c0740b12940b4080c0901c09016100e43c0d108101c080e0080340c01c01140c4440c121030030b00b200152013050510324011402040d00d2150f40e04001a9050603540d00150006c05101d10f030302d80340340b1981c00284c40d41001d060481e91600000248010341c100341c02281d489260400f02135081101810218405000080000d861440102064500c0882c03e50050004580068150480786481200a00541000c0c03204400160005d11484400c0e172188072101d0280ca2141c11401c0c03001d039494011034102e00c241c01c10a240350b580703032980a0281d9071040300348801d000a0701c40c46030094080c20700c1840c2c2034051380018012818045030203d0b20200618840f55074200741041600c5803c8189100da054143d03102180e04a00c02181c05103485030004046200300d0345290201040b55076080b0144040c0c002131050500300304480c10020351440d5200d10f558450031070788 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 804650152 1250 804648902 804648907
    0x7020319022109010e0307080c04151203020a140c15030a060b0a030903111605060f0c01020301090902030d031406060d0e100c020706030b0a0b0306040902030111090a06080903040b0f 80
    0x4809101c44200c221102c0c190100005501c40702e0358200d040864600703412000350000c00e1034800043e032600c0c0c1842c08113200315926444245400005001c2c4000742c0900e07407403080008250b140c0a507803000a54000e0310b440c210070440502c036040c000303036a50b1240d0014002284013110250812080c0e00f002e061200c0c441c1d00e40364003040c800c4018000d001309078642d50b000f00e801881400c024061031421000c0e100690001040003074014001000315003102e506a408990394544010400c1c281d00544098405550001000040d40c8003950007041d4a03d00890a4886d0480765601c150100c0f00074030321101070005888001007141c940200039000d000203082010415508103070a1a00740520000142d40e160345d940d1015040c140d04200380e801400c2c01d030030104924120840020408101c42c0700d100d8038080000002201c5455a2b040705080d00d40c080d00074054509119400540d135005030004a004040e5110009280361103089218002c071501800345d4940760401240080c50351004480c8401403104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 804651402 1250 804650152 804650173
    0x11802070302010b09100f06080c12070207031a010f050f01020c0609010c0501110d0c1d04020d0e19050d0f36091505060405010e01081b0706090209010801050702031902 74
    0x50103107545c0b2070320f2030540206d80c0d1810a01180c00144007038208004100700ca030100200660b08200715a0840c1100740f0081a90b40d5801080745071101030b0308000c000030921300d84441c44144d03c2c5044c82c1a5a21900741a12075a00c410901c402000048811130040e071050140c0d40c047c0c24528010011090185400c0360001016210303d805e407001c00020780035a440000c3e1403900b07c00c640c41441c250001500d49400d000300350785141c0c00b03241c201103501031107564001440c0c024031b006139000b00800800801600e881841c4450f04120041e12047d080c0d81d94099500c290154500c60586e198100a564850358001d030030644503000d08503401d035a0404800313414500700140c09004505000200321101010441c20700801c0308030244100c0354170150050030103100070b10841c1c5c0c008802c141d0815080c41c003900310344e80e0b190b540c9040041d41003080c2d00802c400500d20301400395076000300b0303091402560f554000d0b036a60107401d400c07a2030440e007010050b00700340501460040d040d40d01860164041c412505240720 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 804652652 1250 804651402 804651409
    0xa0f020a020a060c0201020403051f06030b07020303070e030705060f1b071203090f0b0a0c11120a0c330c0501050a140601181e080f0a1a011802070302010b 68
    0x10020494000d6800308548208003d0380d03020314980d00c070842c4001d604080c50f46d03841e59a00c00103980501c1d0004407201c00b0943c090702551005006541002007085507040c14a4040d440781e005840c018001003443c00500c0e014103001404108603013014184600d440a08425031115812050304076600100d00c0400c1102200c0402a4002030000700c8610101100240b50240001c0e019071702881d10f402c0000804c1140148490580e1000720442c04d0541d0001514542404410300905e0303e540c2c0b000c00030b07000005c11440010710143e0b69102d940e04014254a038048030741c46190104414a450084d240d1a001c800345070400829400903c2c02c048035100c00d142c0e503950942d40c080b01c0900030341d5030303901903c0c0703003500c40c0c80c3d965800c02c9c02801e0020800070300c030200c0c088415150041c01031001c0c1e0914071011401c0400800c0c001130226400f0799240302569584682c59010043e4140c41484001c22280c041c04c1120701c0441c1240c0c2e801110440300c80060049001a402c102e42c20b4095559410070f40300310b81c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 804653902 1250 804652652 804652657
    0x20d06050117101205070b040e191a1507120f020114060d0602300604051e06010813050717070806070e0d0206161b061119020a030c1820030f0a0f02 65
    0x782c0300c50b00c014600e1f01c4201c6030392100c540c04ac0c1806503410011a8001c0c52001c1c06441d00480040d2100c400b078040c1f0b055002c219214202e00101303907010003015410429402a0700c10002d0116a0080c8841d103004d0142c03101d40381040e0b41d06a804840402004002040d9500808002508030408000d00e081680c0b03941c0c101e4122440c803401d0041c05c2c010049a40f0f007034412158440a81541500801c00c0c21310b0300c40075802c0c01004141070020303200104e11a100ca8807224080581e0003000c4849048e240c03464204076841c204e06003a083c1c803400c3c00105011102042c05032203440203685488810032080300300320400c10f09810070303038000318100b003040c000b90100c080311310100d40600c21007841101c1004403c002a01c02d40c0c0b0078000c205454000c4034580f0000f140b20f8020800c100c1018034000d105000145480e6503d91000309040184040000c00403c400c5603144100d02e41c010402a2007104928640242aa401040200d1108100140403540c0c3c0010050304041c0741a800182c01e43c0d03403d80700b8100c1e07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 804655152 1250 804653902 804653909
    0x51509010207060f050c07060902211507030608030a030c0512131505060105042702190215060a0306331e080703081c020d06050117101205070b04 64
    0xd940000345041032046a01a0301c0348454902800c2003107103000e000103505802000b00003030544e91100420802d540c0c40180c0507510b8248000a4480c80c0e071904120342d030381c60b2800ca920440150320800204460700074450340c01101d100c0350280d4030380110303003104400528682842314280b000c00d1148280540c1051011481024500c90769080c261b40c5017009460f40074250a080c44040c1400c0c00c02c1240d90348041903d00b03c89003072903c009a0505102111300c20850a0b82c2081d82ea4400b0550700212210f880c1c039164483e00319000e0b9542040b003004030488400d02201c0c500d812078442d81d03040000640c280d1108207400c030582d280c86842440c1c02804001580300100ac0d42c42c0350090345042c040e45401c403142041c200300148803860528504050980c03030790301610010384103c802061840100b0191450035000d1400d00c00110f60302c1c0c00e0425204028021805054002144904440385007040904814000c9411000003551285020241c0c03100c040c00020486640c083d1000c0052044000d0000c0c2018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 804656402 1250 804655152 804655171
    0x403120207031a1906080c0d020a0503030f1902070602030f032d2e1e0e010b120108031c0c0905061c0b030313060e0a050613030b07020f15040515 64
    0x1681013154200e102d0f14102c0c070400b140c05103000020400d0f8072001074802500ca200341c42c80111016140000391000d4043da00840c0c060000041403002c1c01000e1004049000403980720b10b01e02000700c00102d9031400940201c8001d640704001c20382601e08040080c641c02044c0c500c481c42070003641008000a0a40780303510340043e41c031040c20302a45c0d1542c1d00b1000f800d070049008103030081c00382103500c1310466020721401d030030350280d240c144c00081100348501c0040e01c07071214140a2941d48266a100c19070009216640d1030441a001146484010007103505404003101c50500c0c07072260a0502000340b45550f04001030010300702c40050b42d82c54002c040d020b040c00d0034030211a044202c2e40c2c0003041c0c8007140c0c4013a200e038004008150f0146030907030000c001e540d00ea243c06590015101d000c50801c41e00750300003c0d03001102050244000f65580d1451007a40d100750607190103a1201401aa074500d030b04035043d11b83c0e4020b4078510821409000e00243d0180c004d0080b2982c0c45404000d031280e001099444420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 804657652 1250 804656402 804656453
    0xa11150c010906050703050112020d08070525050a0b071a071e020a060506060f0403030518040e030a09050406050d020906190f03140d050901030506040b06130f140105040312020703 79
    0x11451b030184a091300501c103031540400625440e40c0045d0001c030030210014010342c0007048200501104108070000100710840303d50340c0c49074108031030070269014841c56208107034000011554202d21000e03540d010740d101c50790603140001d0401e114402d6000515032070806c0307841181121003c4081407105c1181e2200c0d0003074414150a418190f040d1200144a28083e00c001c105000381c0d0f04c44481180e04036030701803a00baa162422050340d00c00c8151402c400b164014200851901c903680003100034080c515181c0c0300d240744030340e0700e07410b100999a41c0d00c142d80d40080c02441440141c1071001c0d540d948040c0040c00e40055014440d021000b194580d0410780311110300480c01d00030001e810020101c040c54520003820020b1000750000c0c130703d215015180d41010707115404680c0c551642d4110820360b84000700019203401043c80100c200120920070a039010040800c0081d03561200c5c55078150004043e55083c0c600790540c1c80b640d819986c0303030913001c0441c41425400408601c4103401c1540c0404070169501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 804658902 1250 804657652 804657661
    0x3060f24130e0108060711071203050c06090c0604050d06021b03090307090b10032301061e051204060b060706020d05010501030b03030c1b03010e07090905010e0a11150c01090605 78
    0x1c40d1800d504254804415200140441d80c00054510741c442014a402190301405407882030411100d036010f820705400c800149030805400c80090603c5080c1c04d412540590344000f000d80d46c444a00411681201d01007005004504000851301c4146021301e002502d00180f41d00c00e54662800a5109103981d0004101c601d0141340074844a801040b510303906208a1102c8000580c0045050f2421010305584484a52600c4040b803c8000b44513001111464290380d07465026282d0300c0194401c0d8001a10903040402a601075815640d0100381c14a4440680e6200d83e00c4500500103010381c903504c900d00340000c000182a41c0010154804079040206441d403400700094151004845480d01c07a4106208001e000100000c1c940c10a540c0e01c0064500385450101090042144041e07400c207a0007034100100d13100d030850f0880442070f88900000c2060741c4804040781e848a0885000a06a170010245401d0b10314041e02604802c147e0000c0e0a4508444040d203142116403444088071026201d40411 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 804660152 1250 804658902 804658927
    0x1a1e0a0f05180106081504060e0702010c0f14040b130b04031b0b1c24090e10061a0703050f16060501080c0607080310030204060e1803090603060f24 65
    0x24072500d000030800b8285505224000d42420401000ba130030702003070304c0903181030341d55280c0140c0002d1000c240034803014203203448000c1c0030700401e95003003010074100300100e03a429100300990000101100c1046042c01d041c03494501540c0c3c0091001e008911000d24003150803050b107030040004511400441101c0c4042e007100c402d240c5525844480541010b0207000e4040d181d090381503202015031040011805c2c1c14181c1500c44904200100c012003e20b484040b03079083d2960311078005041603004450b01030000c4003021b801d480840c0110780012001da4001c82c061000f800207007201d5071003410181d00b01202c1707528030000c1e900701c0049140c0030000091350a040c085144101c602501d03054000d42230100303100010540364421070360001c00051700080054041e030081400d0307801030360307009000b0b1008964132101d0804241c001e641081800280c0c0d4841d22a10000004480d0380310400350500303083d40c0d075007010071404100a411540d0070001c0c0303240d81c10900b4450200d5904d04d001011035180c03241403000c01e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 804661402 1250 804660152 804660169
    0xe0a0503070b04090c02240a1e1a03010209010e10020c040903090e06030706050406050f0d05040f020114030105010221121006120b03060402040e07180b01121a1e0a0f05 74
    0x40f2001d47d0000c000c12980d04c0c1d502140c2d04015140b14034243e1060b00c404234818020311180c414800b010103001000651070b260b0390400800c694514034140280050007007050b00300c1c402c00340064082001164080c0d030f5030429100d4503400c541a401650550180b28022070140c1d5104402100000c8054400380808040b060005030006c40943c010180141001c0d00170740b241c1319900803e410300c04085016021402c0039030803a4000040c4e60000d20640c101498212104880d85030b0880c04690740d8025440624149400c0c1c82c100c8505900034503d5950441c1c0881000c0c0c844078080568a50801010300014405035005000d80785200c070451a461405a004186600c04450381802d5410300d41541029600010f0064005404172400075410840c070714401c5c68080603034880d05000c030389a041440e00400350340c0465101c20082c0c8510303a209803126510382c100c82e4100d941c1c0162800c0010200024109120002d0703042200089141c20306000800190f0550103a0740a03120000b03e440050016050600c030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 804662652 1250 804661402 804661421
    0x21632070302090c16080f040305030c010204060807050705070e07140703080f0c040305100216050d210506090a0b033a08090607050f1c0504020405010b03160e0a0503070b0409 77
    0x1031350400300248104100000008809442602d0100d03128828244910842d40210b500008607a44d070401031510f14080c1d0018428040402d01d0040010000c50050088510301a0b004000c0d10b21141000706c600388140d00640046d040018100145140f10010f50051031294040d8480060a14180311502c140c0000181211403e900500c0104000b40e07001803c8008123034071900241e20b5524141a9144551840c80050414030514241655094100c40e0006d0906200c814415003070300400320601c240d42d000e84006070020300d04000580c030002d06502020380303200000c05448010a418150160030b508070101212a4280d441c0b01c0a0881206104010600e10390b040c04859071070100d50f25600c514008000700300784130001030919000c0c591300302240d401c0b0b001c414260310340c0204458802c0040c82c00701c2d01207028926200010034044801420f5a2040400e94142104002520401c407128411004290f8008209490105490341d0a000c1107000d0141d0040c21500d1300d142050320b03000ea400094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 804663902 1250 804662652 804662671
    0x10504050c10052a03030705030a060b1e03060a05060c0f010518070e04150513050c03151909050703052d0303060409031b03020708010f02163207030209 67
    0x41034494941c0c1c2080603141103092120044c00c040340e2201c070788544030803488401d00d06030100004010515400002541c001c02c3c40040c10040c5685848152403107101d51000e40b0000880001226103d0200f81d00940d40b240d4040c04041400d6607e0012403c1f94100b441c022a581c0c001d600c0d003902090091041a40c0040b600c2074281c003c0000c21506a1200064041e008016009400207014044a0718846525807006403080009191441d440d01880d403142400716914080d0102c08a0517240c0080c05100c803003e4481c2c810b2440d210350400c00c16414003507a80d4804151280c2d90328000c14000c5c0b00f404011405000031f00307858043d2030b50550940142d050500a00045450444182c2000200360b035800581034a0000d09004981400d480c45075086682002904140c6400c408040c0d01048a20031106110003d00003602c0c07a0f0310f11000c3c2e000e14410f05010b00303c003810040c0818401e02c85241c403003e000004506004240861950003814440d0928036640040000c00460509410241c2c1c800c0d240e2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 804665152 1250 804663902 804663919
    0xb010f08040c090203041a0423160504240305030d0b09070c030e01050d150303080a0629090306040b0609060f3d020f0105060a03021003150f0305010504050c 69
    0x30364401241d82d0301801285075090b8040005010850703000c045141494003501e0b021100e10700f0746810160b00162203a803d1022a07040340501801c88005198550304040600c4e00284500348070038400102628225003c0c0d4442000c001b0040c0e800303041562016500a0001d1030b501d440622208042e6001400a680130301c051904002e59558801c0d4400242c0781c1c540780c22503003101b070b602c01204c1e980104251040c80d00e1500d00380700d91101440302c15000712482070300e41c00c0895680c100c001040365014070810b141600d110f25a4242c2a003000012240c1a004400d1541800c0725900030902d00001254200d0b100c0c420346060014500e0134050780f907071040301110501c075100103c1c40411040e80c004c61b8088000100e51039001500e451501b004150900240d80e020003601c1d6000000790783c0c091241c1808103a51801011607554180009180c054030780150021361460040700c003c900a180d0031080d0310391400b280c18049903038000001040c000314040d00011405043c241402402c0c140c1080b10b40f80302d01a032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 804666402 1250 804665152 804665161
    0x30d090602060f10030803160f0912030509061b0f101e1508100b0f0d050a020607060b030d0c0201020105160813080c060a05070206071106010b0a020f010f0b010f08 72
    0x1062a440f800a1104405a4451141c000005041c1d5000208808400b00c100007002c06508941d00903160305545601c03042410302030543e5400d00c1402504a940c2850350b201000c40d00400040025400241c03035540f81035600109a014034040c66a90b10041e04030b103440700c0c10303c0020000e2803410f80c00c0040402042080c41d80f03d002e060030750000584c480e5102c00c941c003002254255510000c24061050303540f1b07580348030b21344001000258001886141c5070003160031a03092082d085481154010020004440a602006415000342d2411541c503619852075081d140c40c02e2041030901c0d01280c950440c1112a840003a0075540000e10140380e40c00c80202c04009075520018181d00540d0b00c000d06d81c0341f01401d0902000c0f41c411104001c0c2d26102e08014820389a00c07540c0305038842e02d00d643c255030841c0c455900488403a040151416820380c01200140406d00f85000104080303013290040761901ca084d6841303070b030a5907510284600c01540c0e80c44881440d5801035985c1108040b54a820f005074a403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 804667652 1250 804666402 804666407
    0x100f060905100c0c080c1905090a021c0603051c08090703080c0102070506010f0f08070602120a030603020d0302010e011808070b04031808070503010f05150d080d0e0606030d0906 78
    0x60301d20941d8801c2d41c18480482140d400b4060450030541c01500142d48140c03144026642ca013440c2c0b10b40c03070082c01501a069001c40301ca21001d003c0c4c4000605100341742c0c40d0240908081e4019100424510710610170030a04c00b049445030b03100440c440e20182a40c0c102e104c0d000300d0349542480c20b040920105104002c640307100800c801c0c0a0320744c006401c82d1a2030009810b1402030089010003022885075a00200e206610035550340d0440d43c4109007602d10f151a42100390b190304071031041e2009039100d1514817140d26404005400007004078580040c1040d541d800240304000e4840301900546d6552100114210080c001d04401421038900304401000c10fa8441407039104502010b0850b441c0300340400c0405114200000040360f102ca104e1504a440700011074a0300b026208080c4690f02e0040d00040d145a02d00820380725400b000350303070f08400d56103030180035003002c005804880c8502d0820032882d00c05410300c9403a02c0320301507900920b120f25112003414940b42040e0320f28810f104c040d8108200c15175 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 804668902 1250 804667652 804667667
    0x12091f020918100801020a03060f0f030f0f02031f09030809061605030901020c0303010605040602010b04050103020d0b0901060305031b1e28060606120c0c0804051c06060806100f06 79
    0x2d0400c038507481150303990826003581c81010b401a1603a94000511050300c02e81c0b640100e8152801060000c12065903200d004076804150300c00140000c0a1100c02000300303000c41043c3c40b17400d002600b074484040305c45119092207041681c440c84490742e6803402000303240e808400e19900011000003440c140c1480c5d40030790700000880200c84d04100001000a01d5400d0a40581c0c1c2e014503c80200ea4483d61075a00291094110b4000c441c015071038406414618500350089604894000d0110901110700d901e504002c07100081104c08190740b101400800a58104028884022000d410400b05021030342e00764142245420404403450981d051110000e0000c12461a12884403611000f4a1581070040d6414041b0440140500340b40c40070009859030866002c550400c4110003c12407240111415160019a0307503018040d0007042c80b00f0302080c02d00034107850008460544030640d2891503076a00098510388d0b0000e200d00d411480c04d0000b010040d20b2628003800e440c04400d900c0c20f0502a000f017915 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 804670152 1250 804668902 804668929
    0x14070e0a0e0705091017031c090219030813090203060f270106080106080a020a21090f0804031106070b150111010f0c0906020d05160812091f0209 64
    0x503941c0d003001008620003046041c00501002d480c0b0082403030b29101d000040d081c14842d1000c01c185016a0095219003c81114510f03007102c4c0d40d590192072500c3c102c13001031444c03100c22070b0080c1c140000b80c219a1400200240154441d4000c1c594900d2913115514540f6001c0d0300c0140e46a0060003400170660794241d60070901c044c1645d5007070420145040d1a1055407220599001070020603001003882980b250610381652155102c012458944038040c030201e1044151141c00603003a800c0c501000300788443e00c0c044410505002103149201a03e0740803104089400c201c0780148000703010401c00c80c80d0a42c004904008131100750a022150306c0d001000e2900406098515143c04120121a80034170410304400200900801001e0280b030090001000141e134034001140c8402000900700703100040c40260030606558042c00d14004c00c0102446002d5a0000c8804030420f20542081c030b401c640c0c086108100c014010240f940080c2442c6108402c401191042a401008030030a40c1d201d503240030044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 804671402 1250 804670152 804670171
    0x504030f020607021503090c0d0b1902040f0605090f0f0a1e0b12041106030105010c0303050627010603290f03120c1e030a0e061e0a0c14070e 62
    0x3000c50610020b003080c812800c0003544101e404144a0a0f2100078014512494100381290388201d864001c0000103207100714000c0c849071840001400000c410350340d40500e0090000d026090940399200b4907104e00d000d0b0801c2001990102d001121450110040c0c0c01910050310380081480c40000400d6205846001d24600d00d10b11242c0340744c03030800403100c000041050042c41d94468007100c00c8090340480c00d5400341c031714168440c8484d655103400c00440b412a60140c41307010714040250360039030141100034066070344554000070500200030744190096600c03074481d540c02e02a40c10508054119560f9800040c501c0c06e88008400c02d803008225904015170040754061491045c0e038001070311b04008411827040030304c0041000010180700143ca81c0c03003054a030100099107000030444650f40c2c06001030040015910380798211031030070720500a05450003040000d400b068040906007079103070700001c2c9201c00107080031001c009202117603402500101207900540201403070070245a00f03c42e40035100902 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 804672652 1250 804671402 804671423
    0x907060c030219061d060601020c042d050f010602010e070e090327100809060601111212190216120504032405071b0b180f0c0f01020706050403 63
    0x1818000c004a85012102d5005103d0a110301d10300038020308254529000001c1c500042c420300098007150f098460300040c1d000700180e01c070403c00c210281c22036480d4100324807680302d1041c000a40b02200742108850300c0b20089001c0c00c16000501c038242059004c0340440e4500700b51a0706824000c00c504080394013480d0303514150385a10030300904610603041603542400406020311508020720005280c01d450480b41034198103414407090712010800c89d6500c8882c0c101000081803903016040e640801e018200468090b650402c203040c803035510030081c0314071404d246020001c1c100150b07da41041c00c0300c0501c0641c1050142699032203040001c010040c00c01e58026000300c0080d229005560056800141c4140c07226030912003000800e50003c03420042c14144130000306d501c0c0c0200020707840c3c050111110381c01c509880c2c070b44c1c0503130440140080c2081500051704205900341002041d001c40340c0341000e044c505900404001c4006e0380c00034814150b421000c070030003200c2d400005550450340c202e040c00c03c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 804673902 1250 804672652 804672677
    0x61c03081603060801020705010914010c080a092102030424020604030f050d06030c26030307140d0c08160207060905090c0403020607031706030303040209040f0606030209090d080c03090706 83
    0x40c0544410b0708913400940c80422008217110054003c03a60241c024900414040f01800d030003400d0317032582c4030301c60089070110000c035000d104d130b66004280d0140280000e0241454540001401c0c0360b145000800591000c1014041c4114001c2020704c01000a00a00c9843c00c0402019407a00b000070000740520071604207031822540900704580e2841160175003041800c5d04e030700d40103a003000c0ca13010350543d02c403501d42152007000c007100000410010100c021070079a0b440b02000c0b02c81d000301d2034142402d00410702c003510000000b401184041013194690b003840303140c0404450605021079181c0402c40d4041d000030031000c2d401480341e0080c0d03841598500700c240c2e00d03252450f445103e19480250425000100e000c10300d40d00c440b00c0c00e50341d010112005096114001055130740c1c0810740707019500c242c40b0f0b0301090009800880a604261240802050036070360f03900041d981c0320048441540d9500500108902c0d154052016a84032250861140c114101080d1301613403841f1a000e04024064090f0740c3c10b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 804675152 1250 804673902 804673907
    0x4140103020703211a3c06030408071e0804090c0c0b0c040e1501020615130c0509040c0306030c0509040c0b040b0a0f0c0f08031807030803061c030816 66
    0xc02010100083d061002c042d0324030080c110803100c4964440415416005441c1c03d8170b00b10714040e46070f03170a44c0c2582070300fa00203a900e800941b00804507101380c801c40b103616200c1401441c4141e0098402c5a200c05682c14984000d841c03c1031605c50701c50721113a000c000126103000b82c8080d54414640010f0700426050182d444040004000c0d0a1031030000030040c0b50084074000b003042e01c81d42c20329000c050300d880d071640700a42c3d11101e82902682001000a00210b8818034802e2001c60051104101f404503409080c21a104401c046002503800152444181400e020302071441d483c0d031504202141c0b9540780c44003101c0060182c5c0d8469807103240420180440060000b014201106100b6903c665411344080254003aa01d0080410807145208510b14082d1110f800030075003014800111810039501d04905605c0101448234040345200340b9422650200b2400d0055445001e2540d6242011000c0064030142201103007204845031302e4010000394428515a0441e4251000c0324000714481e405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 804676258 1106 804675152 804675167
    0x6090b040b0d15051c0629040b0f130507080709061709010f060e04061b170c0909090a210c020f06070203010204060801090605010504140103020703 65
    0x2c0c600707101400c1d009010380112141c0070524480e151000a00b84611080c0c45001d450807007079010040081034454810b42c0c443c0b040312071a840e04a5070380b850940240e16400342c081c035241c464065003500c07040640d42c05413034024109140308060000030740051404482c9000010008000b16450a002d40b80000c15910f4565640502c5800385282107d8540d000d04048410340d66010510203402c003130300c00c4030064840d034110308405091508240c401c0e2549034891411440003a044040c1c510742080007030a2825445054481c582d6900750f05120078000c07500d130301e5044045201000688000400c60383c0c0d844c0d114a01495040480c0304a19030304600d040e00d080b002c2224601d06c0e2004d85004000718480c000c004145518100e002e5004c64260780166100c0000700d01e82e08014005000c040c018607020300701c281791070760400d8070f00348502450702d4210100b03038103250703002503414240f5115000c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 804496402 804676258 := by
  have h0 := BRFrame.cov_init 804496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 804496402 ≤ n) (h2 : n < 804676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
