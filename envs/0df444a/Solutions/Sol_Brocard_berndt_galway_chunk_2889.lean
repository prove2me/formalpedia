-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2889
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:02:40.230495+00:00
-- url     : https://prove2.me/submissions/147e23be-c4ce-4e5d-84f7-cfff47b897ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 519424460 ≤ n < 519604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 519425710 1250 519424460 519424469
    0x605030102161e020607020906041805060109140103150c050d09060b0f030a2a03080f030a0c0201020421110a0f1703032815080708010e0a0308190e0a031e0207 70
    0x45c0400850b005828110405030b0441005040080c03a80421030030403c110154070000c680349d0700940d004002100403409168801e9416000140341545181c0e14088244111000d0074000c58642c5612030000340640c080e40c0301c0c101404418403010650b031605400800720702040c240315219034103905040d81000640400303026032042d98a601c40422181b19a0047c841a0390414404421400400020102409410602c205954807034032401d0019001d015580c01c0c0d03554408581c41030004204900e803584175944840240c0c403556030030348800d081500c411080d1040190300300c0400ca130001180801c009482c8103c40b204d44028280ca1a9115556168841641d50a0407035102002030940004000c490341c160204805000031b000e8982e82c144140e5002c10f40c0024041d0704442c408101d0b615080c0640f18440c0c190304060b0041080c16a009409040003906401e0b08840b10841c1c122071009135800700d4a41c02044044441c074000d1480c0080c14101d100354130960700841c0002c0b22402900001d4000c00383d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 519426960 1250 519425710 519425719
    0x6080109061208030c0d0f090b0708070207171011040f140604090f02070f03030e0d03050417070f08030c07111f03020a0201230406060806070905040c030605030102161e02 75
    0xb09864403126500003802007100e600003006011030301422807042c0d08103009010710204046240c1e00306034071040c2c0c004114209201a1300100000654045410f50503034100300e401030707103420f201c586281c0741c00061107042c854589484082c482440701c070381c09042220801e11440034031031741302c4020400c406c5c40b401d869500903000307110a00c400e90494120041c4071600c2031005007844590f4030703200d41000420700c054011079645e0541d04101356050200ba25102d030b80b405e0920030390406503509001e080c01301c401000e20420108070042000804952801c903241c20100d0540c5130304215880c28126440300e5800c8400c5854450308d50510705142280116602031114400445000101e0541c080d46c440d181800443d583c907030b0744a030320343c0d80784810b06200748540000200514240c40c0100403a00c0c10b400540299201808110126500c081120b041d035400b92008503441c26040c0042d4081c00d00c9820055041d4004144d170310304100d180d803510210500035500503061040b10440c020306d5403203210000c4d412 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 519428210 1250 519426960 519426989
    0x21e0711040507030f0f0504050c0f0603061203070203030304061512020603150a090903090503061509070e0d060f0923070902070f0206070f03030b01170f090c12070608010906 77
    0x16107403552102d0740c00809030802203199200c08501d001107035003008000401c150303280700b404148681000245000141541d0000b2180612000a00c1e680002016179224003890350002a01d45030920569200c0c541c05001c50751281491300e09580940104a040e50030540030304c00018500d81c890301d201043d1900a407020b49035072900c000b000c64480140c110950403050454001403200954824403000c03d00a65a42030014140010942000000b407c03080c20b155103940b8011391540c6490145800c9403090034414241c60806002c07420841d0484406021140750074143c8000c0c650340e8200b45141440360003280c0c0e1707018440092100e45202d2407100421a844030b40d007400b402c1c51550080404500602c0046140c80c89a800141d09030b00c140d0702194442e20b071100107020160140100010b1080909144030005500c444840208030300030071050b4016082c42c0401d094a0b42407083e03000c54500905104001c0030301505040c1d80303194600c100c00000f00c1800001402000500c02d1100f034a8004551400303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 519429460 1250 519428210 519428243
    0x20f0606060318010b0a090b1305010807060c03110a06050402010e01111b0f041503020910030209070e061e030105240910050433030b010c0303050901060f0801021e07 73
    0x1400240c49200a10545d0307203074081c40040d9101080740c8014040c003200842d58410403820f00110788451515001c01c0ba01f440b005110020006c9441415101e803840e10002c440030303030300f01201c00c1d4200000c260541d0040140d01c1e4140046034001e14402d500070388460745803010020045910840180c14454103030000001816544203090b160003440d400201740c102c0c0d101e07800c0c0005040b42c0e100101417a020030314031020001c5007854085641d02c040704014541c0040e241da0041351201c0b034005c0002c010800000c0c0444000d41d160341c113484010143d81c11014070070701d1002a401d0f5941c8280070301d42c0306506109003103282c190f040815041040e00c0c014810301f451002e40621004110001214080c000c00780000320b540040305102011210300c0d0003c2d1100c0030b200542d02140b680644561800301400d04802d203450345d0300704050b03500c421750501e030004140e035589041c207004000c90b400c00c000b201c0448000060055054028144200710740c0c4911000418110030741d10b092148900c024600d8165409c07946 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 519430710 1250 519429460 519429481
    0x7110109022b1a160503070806091b03100905060d0515060409140a0219080712080f0a02061f0506091201020c030a030e1e0d050d0b100507030801140a03080d2a020f06060603 76
    0x11f41040700360141314443c52f02078491010b11342044034804c02c102c80c5c0000800400c00180601604100d041e5181c0c1c08809454071921b803106034000751100174001c088045a10341e250340d0b00c000070b07180c0c0001d01c5002041e60b1081c540d4030303030242c0c0310140d00c5040290350305030001201e1605203044403210320003851043d1806102004400307000c0c0090704d0301030b0309010a0341c404046030300400c2800360315800703090340785844000d03070900e015100d04201040050106c18040d0b916800100da2058000326075801c0200c0b0700118041c060301c85c00c0e0801030b10380804030b60403c1080d0140c00203d08075204d0810f848080c0410b0350000b40441401010400c55405036181f141600d024900600c0c010701c1103c00440d082d8920004145819010881075001800000f01c0b80d0626030b001d04042c2c01742c80342035000542c0b40028000034484400d94007014011802c001080354030914a68040588090803101c42c03101e400c224a02640c007552034810f0341c405030045c952042920480858114842c00e03000f4882c42c01d40c3c48100800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 519431960 1250 519430710 519430729
    0x60521091c082e0e0c1315090609060e01051c0e01091e02030705090916060504030b0f0c090415030f060b0a06080c0703050a0e12010507110109022b1a160503070806 72
    0x41e145c00e401c001440e15840011596405000f4540d5108103804894000404080c0350340c0c002c1003089280c1100b8403403c1c2e4403182d9000804c01c03d18040351902c43d46c494040c41110700c10410701d003980c6040d040390000b84040d0003620496000340c00f0481c5410814288552600c1201e100940c50342042509100510f003031141250401195011200d0901c400464000c440701180c11120104e000440d04208100c840061154007900c2828019068100b603040f0220b80c1c05091013071886151142070390520b60f551794a040c2e0003150000899000c5c3c00050500c0d000900801c40440d004e98000e1308003058103801559650302540d0340392800d501d0020981c5045903d500010510800c01c031003c041080b143c1d0380c4540c0356114400104c000a614100414050103407116600e00004130703410829a600941d0b1884036900c50b120a4050509104031408043c4440c0c506659000303049060b85481d05441003403a0106502c82c4a014010300261240b40f00c0035181c82c001101c01100140350180016403500300044c00c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 519433210 1250 519431960 519431971
    0x1b01030e06160c080414130c02060c0c0307080f04050f03030f0406050f0c150f010518060607031403010605070203070b07020906100333060521091c082e0e 68
    0x6160070703c5031641d510302281e01c15800110208a90411002a850280410a0399480d8464200040320f11a44040c0d1106802804031410a60110340145d00031820300c200c9102c1580701030040c4e0f6441c086514029141c020380034443c0603071001090005981400011a000e84100c041000d041901d07210b02182c3d00d604c09400c3c801c111105000c42500c82c10104001d5660076400003000e00039240c890784403021003505910040c841e240001882500c0220013050b13a4001c4001d8403901da4410aa0400340d9034030070742055190203100e000000084a40c0e108015200c158422011303240750350356034980703000c06020b00a40a0b50003956103010801302d01c0c4c5002d62540300034031800c000c114200c0c030000440d04486400f508001058420150b0b410f515950400076024180c20b04040b42045c40f401440081418420b034400b190a01d44008620302c01c00401038a4584401d601da50700c074581c01c107200102131400554421468050002c0072248100c0c1100c0c0f400062074030011400c0203d8508150b6154412010b882c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 519434460 1250 519433210 519433217
    0x602010c171510030c0e031b01050c010b090907080f0606060d021303172107020307140f121206040c211413030f0305190905100c021b01030e0616 64
    0x1520000d0300c855401442c00c0c2069213001581000129003c2e007400400c1100b00c1c0303c1d8200c819020150070030280d0f40c07241d01c5003c4c81e10725117401404018a005080089001d80d2200f0704000304600060b0001e0640b0607510203c01b55010000e00440465494009440d0190b100f4414010020021420780c05030591aa00703940101e04aa40c1c1e4440c190066000c071070985059030002010300a400d51175040140403108401481440d00c3d060f0f800035224015098010304128003c000348842850402418000752004e100355078542e1110704800e00a9882407024044190700701c800640589024854210322a140d0b40304e86030030f002c0d802c0c100f04003c02e84014203121690354140f5680ca507a0b400100034850018125a001030cc01c19080240c0040c0382d502c00e5100f00b40c244400c001e481000344135680001e049844010130407d01e203180c00303401e1920407461121640c1c0ba20600419280d80090000010020111601d0420f11400011020f0350b90114201010798003500210308620401e0380c45102c1c2800a24 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 519435710 1250 519434460 519434491
    0x10806070e180703020a021902060409053c06010f02070303121404060b0a0f0b04030816060c1205330f060414010201060b0408150405010e0a0b100602010c17 69
    0xc0d0225444043c0d85800000c2d03804030b0340c1440e164040240b240c03041c07944101d42e25155601d82c0001c07814030450282d801c4940d214400308440740f8201400d6880c1a4141d04049040a00d0703401510034070300300c540a207000a4082000c16083d5006446d4181c2c1616070364043c2152500f10b4400340c9a031408a86d01c5904e590380c031030409880b142c0e5031034824010740c4103503808940341c8170800800c1001081d9410405012254504c00c014240341d2000b114116a4451b020580b503103449144050414004c0030701901f40c0d42400c07140c2007c0303a80034485d002c85200c1c0600402603601c80090201625003440071940042d800422510300d1064000700a00350060005c0c80b00e4003699404000c01c080d034105521201c0e00803006075000e4500d4be028050107001d050030b03e410030b080500e444090342c0d40b100080308c010040c55034000410107001d002c0d04071041990300c14080700d910720b0080c03421000c41c1c1c0007262800070303442c00340700040b45603481130040030014021991aa40054040b00d5100c0b2201005441c01d0508500c82 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 519436960 1250 519435710 519435739
    0x220e06030d200d050d05010801020421020316060c0605010b19050310080a080c010c180e0402130612030e2e2c030105060f061806091c03020d030203010806070e 70
    0x40006040d640f0705503444d1912084ca9000d09400c0d0f4206804c203205590040c030080c8440400d9040c10150015150080c5910140d00d0000c2800c00200103c600c810406103080400e00070b4110801002043c1318110130062a80d84940100c154000c0000800705000301c2740284041500c58405103400071041001e84000d070b551802500e140c4841014102e8501c4000704240220a00038070a2082440c5107090045003194040c2001c0004403407402a254048601e0004c81c0664484d207820901d0401440c81c2084442d8484104144014003803008400103810740c1a95803240c01c0c100144800c0c041c2d0414502c036804025070034617410881e141085000c124100040030380654150841d8445c001045401c1d82103a140c030801e0500750780c0e0040155008580900c2c0d0840e441d25441e0881d015194a07000b45541440d0840018034203215039540c01d507010041800001c030948640c01d032000180d1181e0201d4061031150310090742a40030034404d60465070070030000a41c599004007409a44400c00501031500e40011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 519438210 1250 519436960 519436963
    0x10090f0b130b0a0c0c1a030c0a0e030106180b03012a11060709090606050a0f08070507081216170604020703050d1b080916180e03220e06030d20 63
    0x1403c0c0c0c4500007120708000030188242c140000d405000010f650088000c8095200300030752101034050700b0080e02c00501c24128500c20384000a80b190000c00074012290765510303a40c1c00b064440001e1054030f00c0c0c251800c010f8038051240c1c045034040c0b54007400c0080c1e82101100b0410b0911904c40b024400c13800203000a4440130b00c0368901c00c148544134240c80c0c3d400c2c20001000c0701c40f43c1d00140f00b80801004403800c2ca40e048030000412540500c0c0c80c020550ba1a00100d070140034446005114050102e40c0d00c80c030109812901d84101407000603000228420300c2c084940b0440d05c81d8042c80f20a540c004036941e81010b0700180300c6c0c00e0180c10120300d04403e00c5000300403a40d80c1c0600c103017410080788180c49500c0d840260283c01042c610002d0900750b466101000394a19140b248184a00d00203003d030400d4451a002620102090070640c0e4903507000300040c45019441351a4141c00c803030a15000700c3c0b490900a85580142005070040c800e0071070780700d001e8902100e55845664202a4a4801240c0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 519439460 1250 519438210 519438217
    0xa1b0201051e0403112b03020c120105040b07091208030903041805090715050a18031208010609061701031e0203070801090b06041803050a1202030f0610090f0b130b 72
    0x59042c10a43e0707403803a600700340405e0300d0460000380c41001180f00c0c0460f06404c4035400710107446191701c034000c6800c580c6820781c41c0411380105a0340107007500031013240d003440c1941710f60f200d640a14495299907880000c2224aa900c900502e4078800c0285013400101d41d8440145038002d00b04c20031070746482d03102e0404001c03401c40740a9072285a0b403640100440510140544401407411840500e411010800c000e44039000b803400050800000c10000d00c0c000000c01d49000041da0812500d8074000380701d80380108180c0007400b4010120f5050440018028440c207440007000001d40c00300c85840e421030b43c5410f050000d80418180004035040c40c1005a6000c1c01000002c00401c000080c0701002840d000c0107011001385040e100303602c0c011244007502044c844010b02c0c44d925150555860024510942e4851440741c0107600081c0b0103c100010704401422890240e030301241c0703c3d070b121108090110b90440e118050803204051486041000e0400c1c00c0c00391042000c9a030400044603195a010700c420f41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 519440710 1250 519439460 519439507
    0x120c090218030d021f0f060506070501090b0907050604180e1b040b01030b0603060103050c0c061609081b21060405060106170f01060c140f100f020a1b020105 69
    0x9904807031160345840e040003411507006050001d054800d02800490f1a000072200a49103003c0e150010300d04034108643c081d80160500420181c1c0350f094034101a4000e0240060844a00403944041112400001b403600c00315280140300303503e440d0a1800d984406950301e407501f1260340c0c5070b0391f5111070740130144560585101500b406100c0440404100016a141802c059060520b400d040c5c0d030158466408a90b446070003802c0105050300d40002c41881c0d44180c0c00700b444d0900402c805c0c0f010b4240041006108041c81d0b54030b090050381c40742c0180e904d0b000b0070104889442d000c610607610509020607144864800401c02c3c501840c2200051800c046044070304035903580200d40184841070b00b02c100c1940070303078910714500c110b480c101000351003100c0c040c0203401c180036460005808110b1000b007900c070b03810040410340710002c0c03005001555544103480f5000302581840d15a80354018188240e03501c402d241c1e6074030030052100d00340701c0000c50080c24040c1e04020003000302c00e40c1859803500c0508800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 519441960 1250 519440710 519440737
    0xc0c0b090607090b040b040b21130302060105220903050f070c17120f0f04090c020c04141506030604091b06030b01020303010f171501082a03030301120c0902 69
    0x203242c480d02c000d200d10090341000d2200c5009001c03e1000021600c00e5034152074051169564408040b0300755043c0c2007102088041c0000b5400030024261130414942010380d1003602102c4459885504021921402110303c2c0642064070606425141301d5800c90000c0c00e0007030034403a01c2c081c1e80e03940e00100b0b64084501565280c194600800401d0004207214800c04280c10107049450781c074140d02c0303071b0500c40e000000306103500200e56040005001b2088400034040e100040211000010000e502d4408502c0103600c15440c19030092006071403c44941e100e41141d00c0340d4400c5c190103604000c1c0d82e42025006c2c64101d940c034019040040c255845000143d81e4040000840303518200004003550300b407201a5046400501c01088407600d0b100307550041d2504003205012180a1039909c074034010204a202c03030801d82200000540c0c00001c100080817a01c10b035092010345040b8505800d100c0c10005100390154000c000402c0003080e032240b400c01152080c214030158903541e00344902640c000303640c000110b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 519443210 1250 519441960 519441973
    0xb0627070201090308060f09010303180b1309141603020c0a060f0e191a0c07120801052110050705040306060608071205060904060b0105090a17060f0103080a030c0c0b09 74
    0x4d040c3c0007030f001c0c0d0303008904071504032006c0b03841d1020400200c010303c0014140b01c00b0302c0c4a00244e2584001d00c0380036080020342c55442d07a800c041c20320906641072181a20b900e281085c40410000d21403c401c0c46480000b8098083c4002c1c008201c009521142c2100ca036401824021f0300003035030600074051000081b0710003241d000440d0f0407480c00d0403100d10b0840020305220100000081c03e01c010800c440c0300c055a29091582d460205031418841d045000b80722881d255007061800d504209201c0c1a0f41d81a22040840460411481d9900a8441d0915195030000c1d083c00e2503a10340c1d401540e84042c1e940f034102e040595a544d00004e46440c0e0704064042801c100400c04441e52100c96540c0964200c8424042da0504d903000c030794030050250001c2d09030b580b02c10700c9040c0ca0340500129210400040d0070304010700e964261401502e411445069042d003d8180400c2d0f02504100c1000d0580350040e00040c03400482000550081564200d14803d1098101d000400300d00744859940c4180e80c02c01c0507088 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 519444460 1250 519443210 519443213
    0x70c08060f130302100b181015020f070905070e03101b050901170903130801060807060e3a140c03060c04050108090c060301120614040b062707020109 66
    0x20071500007068001112030039540600460390000d00e514407840e0b0101c0c0011081d1440c004075141e500182100c14264400700103004a803020341260004541c0001c0c0514420082001301300e8403170314101465400b9a001041c180203644441d44803a40003070700c40c14012a4107040102080c10030740000f03203203214039640f62208240d6145540f0900040701d0b1070314080e8607110f0b0400c0042d140d2124102c0078030f00c1800f044000b03503007a001041102c00286190f40c0410000c3c3e41d1700d2408c1d028003100c3c02011414021050002443d40c042c115840002d1001041001000704040c020300324a00c4155421000c03c14050448410382e0010300440c1001e4040c0801e109801f0306520302500c0c0042240c3c0d200d002e0b90045c000c008140c0d86020607a4240e8200f4a08414aa1142c0780103915189000f03c00d580e0040d800000081c288050720308000c801d0348900c80501c41220b040992207a42101160081d010b4800200010303410301d040406003c0003007076000300c1004150f00c410549101101110b0490150795200080300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 519445710 1250 519444460 519444481
    0xa050307060b0d0807060c0212042c0c090d06150605090f1206060409080c1506030f0304080d11031603120e0316080a090b0f13060203091509010302070c0806 69
    0x309818040e00d880c440d03d0102d0307944582c284220840548a61394070090500c0c0d45d0306c20b010030031407040020310940d2502d490301000121021100700b0101c8180c038001d145010340b914034058600c22480e030501c030360912603080103000340c0451035501201c050381c1da04514808c40c0d0074442c003000038102540d1a603454190700f0040c045e510151160482c407940042c40c80a43c50301001584551040c0c040e180854610054504607000d4000c120030182140205078800881908840e981442940b007102181c0400440040c500d40340d10882c020002039030400403007a0310032400f400e90618581145411245031190085c8280b01a500321042100014103401c1d607030b001003115001c2e54150808070b4001d1460541180c420210800f0a0301c401883d0000125108814600070303c1103000925201c0b41c900d03511400841d00c070800d5403001c003550840c1030032404003142451002058807a40d4101038800c01e03075000c951000b80c040781c02601d8030504158081046400040304015900000d0034800c00038501d5041804409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 519446960 1250 519445710 519445721
    0x5090406081507120207020d0b07080f010f06050a0504090212090705030102040b04030605060a08060703050403020d0e010c03113906131406040306020c0c28060e030f0a05030706 78
    0x1da01035404001c2c140341c00340c1945001a08070401d814100c402100303d030080d001034014100d0103940100085024014400001c45441c0300f80010341d034151441e03031004641519010280299048000c06440078041c02d0301800c02400c07464210304025007400d58036403020301039a1009119405205285040c00302c40b02080000f603001d030800310029030030903007806d170b00c041c46009511000d04100e459502051454590f0064000903044c2c01c0f043d12104c0c9020100070f000b40c542a20214010b00c101d80c1c8480c6954411855481088816501e0198070500c540b03003280d2420b2440d0f02e4210501030025001c1c903642034100070000c40100207032840041c0d840d1402601845038440c3c8018040e2100304104132802031078a2240341914000040c0004019056000c200107002d20b41008105920001b00407110303410000f000020054112405ca14051500001d0510005140440941204000c0051220501980810300d41c104040d0440b00c480d0095117401d40f4002224030180c0d5260400203d52090040e1030103003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 519448210 1250 519446960 519446969
    0x40201020a02040f0c0e0427020a0905010803132c07200a150b0904140703080301091a0a05101b02031903090b03070f05070602071505090709090206040e071e05090406 73
    0x4108903544a48849035003003906050442c1c440850414100f1540d55443c1cac1c40203058217810070001581c4440c1d00c1c2c1d680e64000e490042c410f916407480007568803006028028881c03003114003e001d540c0d0b115541090b42d40003034000713418400300c100386020706548008001d0003c41e4420062449854a0800c58040b0341c142c880c8441c0142042105c150b02d48900070525003043e44031103548101440380c4442428564a074000800104000000250a00c15134100f94001c0b00d0740b02c03071445400c6803007080151060180c400c0c2500002c004c41302c0010079020b8070100300e440680c40895003003000903a0020b0b040143d83c00c07203007060342403140a4105040d8804600b001034400d410520b0700c0e5060081000c1e02415280800da810003500242c82400c100c4a901070b40c2e1501d6000c030400c001300c81c03080c0c0004d0207004200d0f034141d110b00c104000025084601c0c0610280690081d2019140030f080c0f100740a0080c9000f400c2800303200c030110369210300048200f1009680c140c1e903034525445074208001c05c402e8a020b07600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 519449460 1250 519448210 519448219
    0x8091002010527160803040f0b070521070204020409020a0305010e04030503040b040c090e1506030304050d110a120302010e07271505041104080610030b0c03040201020a02040f0c0e 79
    0x1080100320700c203c416103010a55032020140c81e14251002c610344030f00d0f0001210401111280044c1e4102e0010141040c0c0740129003c2000c4ca80350031809045004642002e040d942c8000eaa200c107000e0700c20441c198000b00c01d0607041c640102500030806aa000e44e00c0380140310340c000b0340c101c65143d045c8104c0b80500352144c08400d0500b0a0380f00202130b400003034806031049207540080740800c40d101c0e08410060619a0b014000c1c030714001c212170345904005842c10205252500061858078011085030107480c1c0c0140552034154141d10b400071401400c07202e2903045040128040b40819441c50b0a081a170b03c00c1d0300114805009110321400c4c000541d0010301c0e00c42e00950540c1284c00c0c469503015050409180000c0c0d4a107001d403154208000e01d03404590002d2400c42d030040904c1c1620014410b5030100170888819807625107450101156510000e414080c0403008a81694209001140c11030f00501c102c819444158001800329120f5080c0c40e481c0a603102c0700196030a41151038484041c1c2c0454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 519450710 1250 519449460 519449471
    0x141201030b01052e0905040903020309041d0723040519110403030f050309011d010f0501050303030412050703050405150c0d020f061f03140c1306030f120c050a0809100201 75
    0x703201d1902da0141c810102e6903024108051035451302c1178030103400078440100280007520b03031410041d4030386d44000b0b001c9010b03d00300300744c6142616460042d40c40c1000c08038000c098680c6880300920022809242a044284160400d0300007030b500c1c4d008541c050b0303001107900c000c8860814099011500f4082e03003100800300c02c0c0001c001194014000d072039400540d06026030780f80d03034110175603004040030704034503e82e42903105444010f40c805505c0a09001c0d0705060800190741ca41007017581e02c0c041281c006141015500030200020f22460103014194070a003000c0d0f0500c3c3d21400010306012907070b100407000e000e0102d40180b40d00410800580824050b001425000050651f02521600700400202c40c60031040500501501600d080030000c40d00310400f00310b15508641c481d603c5825458080c0d07c10303181d0b07280c2c00700811210f00c603400c2103a0f4041500320441400c2e64603001c5040c004070181062000782d03200c0d400466806e10591040a1166078815a1071059104210040322011900d83c11685060b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 519451960 1250 519450710 519450739
    0x20303100e07050313060207020306042f06220e0702010f06060c0f020f01140c060106030b12100513080a02010903020d05040e01090905030c0d031a1008070f141201030b0105 76
    0xa0100c4c0e4100c910103a19400340c90039818054080d2040b4200250144201400c100903c0184100319020f48607084446840145502c07e13445606800145590320107420005240d5a040c1c06520301d1040007e034480c0311105540f0f041d158201c2d003003103d00c0c90250351200b080400102c0780e40300b46006041ea6003404068005c4d12b032503901c81c02d0002c2e08000d00a098841c81d2000756030140d064030500d0492150520b5482c1c43e28108941c544000b84a0240800d050050390642480d004a000c102c981926000348640103040860002030072001c1d02c01d04070542c60344440030200e80301c0c00050501d02c14680002c6a08501450003c2c60200302d2440c42c0c040120034842800240c40407080c1c07504450081c03d0110301501c842c00c0c40d500798401c15903810010300c602c3c43c00c101c00759010307041070030704514107004103d40829030303414840a80d800250003c0001e0400c800501094021041c03040040b4030b44c64038110010303048005001c03d500c449132582e075110720000101700b080310201410b405081c064541007581c0a05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 519453210 1250 519451960 519451967
    0x1e0406170c131503030905030f010e0a0b041b0801090506010906060e01050702060d050117060108010207110108100f0b091f0207120f0c0902071b0303211407020303100e07 75
    0x49000141c401d0101c46105541064160400f40780d051180300c0e0b8980070f568a1802810101c0b46105d01402400381a03005030f80301c0810320528001c000c04201400c04400743c2e6a40d010b41d018001c0c42120301b100f450807400740c007051060b00c4501800d040d03000050980014145146000016071040c20940e040000501000e513100d040101158004c0c280307070340c603a0782c2407000a01c28090b1002c05501a0300d4880001894566552100503004458040c2c1d0b4240c0d80391100b803802c1c4d1244200103000e50b080228140c0c03642d4803038100f059000403c6001d160201e51500c5081550b01d1003030b40145d14079200801c40a03c1c61400021b29800c420703401c080707459407055002c3c0180d10b0707403064401e004040303c061619074241f06480f9920034071680e002c142c00d40c6440e103450f800002508440b42c165003c45101c0900722001101030301c00e4065982544680d00c03020040c44412128194900c07401a03d83d89030341c202150010031841030385c000d65868014544034601016a01c00d176484a03404012110308031418000e0b1a40c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 519454460 1250 519453210 519453223
    0x516201804050c0103020c0c0306070f0f0e1f050c0604050714010203090a091e020a0206101e0b0c10091101080f04080414010c050a0f020f0a0303050d0b0a051e040617 73
    0x30217003800750b125001100400d0901081801051300f40c0100f4080150380c035800307051040e280d20a030315003880c2800c140c00c04071140580309070800c0d0081085003448015201e0280041c3c200c00341c604e06180751010706001c450030100c4c240d80032033780e036840100240409054068100d8a03841d00b0310045040040990006d1100d99180c4140c1381c145940c0d0741951041c10104500d40b03031414168500350764981ca20780000307686010407566030f08010052500420503042c3c6d80b020302c00e02500d515505080c6801c0c18a038a0b02c47e440700011001500c1440104c00d5005103900803090524024a50b0f6040200c00303000145c0aa41c008040780001d03103c0d101000001b8411406031000d41f0441c00080d8140c000074401130f10400c1c0e01c94405009842160740302e608100c180c142c0c0304182c1c2c4c8280c1e40300505c844c4440034071641000900000340031079810b128024200d18107500880071000c0080100e00140c0d078035804903c4000c4030f0400d644900b10440e4102c3c0d40c03400c00d40544001021403000d441c40504000c1c1120303460b0716 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 519455710 1250 519454460 519454483
    0x4090c03081b0c01140d0e01141305060c0c0a142a1c020a03030315030c090c03060b04050612040c03020402280c0f0b06030a08030c0d061a0307051620180405 69
    0x5030740784c03204403903140250300030100348040d0702c50b070441410000e90100ac0e0b21480c000c22078013131007154005170590001001b030b81c03120380d000c0000344041c60481e030300c034400039408124080c1c452113422802000d00d8150b0b0f11420358840b40351003a1881ea41d0b03440900500a50060b040750020403240c0c4040d0050715200c07200f0003181d4051900042c0e00c9480341003143d18040d15030001e401700103c2c00000c100070300c0c941e001c00c6005c0342e944c80810001d540d402e100c3c0c00038080c41c03142c01e901900600041e890b4001c0f4200d881d6110340709000410300251207900003422a000104800a8140034901c80d400d0b2000c0217065000e61604c5090043c0c4005190750350616a0700c808500510602c0190081500c64408101d400450365201c080342c2d480e03180c8000e490449070420340c488410076003004000529003000000001c07000c40c058102d9855513680b01001d9450b507101401350650a40440090008150300300c0b103240000c030f0010034030616440090100040300003a540c0034407030100711a051000040c0c0000f46102d048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 519456960 1250 519455710 519455737
    0x109080708160215220e191821110705010c0f02030d081e1005040203100e010e06040e150f0601020a0501060b0c010e060708010504090c03081b0c0114 66
    0x42c54894080b5201040728007000390014410348003410f410600c9030103420b0004085901c10060b100c1510000d04201443c40f550074070480c04008100c0304004030360b000c0c0c040c104d19403001c9084040d42140a00280182c18180c4440500c12051105100200c5d04601c0c0211140741c400341040300c0071202620b4514a00c00c05041c09208507200b01040107a1555110594000b030a07038000500452000e08a24000c480200c07105c164505c003d40c41c0030b0003004060045500f1402c1c0c8120500341070901000b0351010b0504000070752030210000c0c404564070b0003e03000e480c1407200c0381d116007810ba0070300060f1107003560301040e280c0054150703159005400075900d9103e280996060f81d9502e884005030700300f400c00080030b007103075003450400f10303928144030300801da14139000000300200c1003030a840d261183d105948010000f2000d000401807803416400150780c690092140c1812196250717210081a400808c1c0101041c2d8502e0a42c10041c1d400c1c40751046110003070801081c42c4030302c142c0b1a103007441001e01402c40d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 519458210 1250 519456960 519456967
    0x2030406023007230d050d05090a0503030c0c0c0402090f040f24081513150228030b04020307140c0a080c1501060f09050d111906110109080708 63
    0x40c860708080e500920318400b1200ca55507400b5060420806a0b104048001002600340510088200040e40c0c20384003c165602400c004041e15500050b01003c2c018042d54402c00c0c0840d00070a800780000d41c01021a0402180d0310000e59003d40d0900c100c01d6a1144a07605c1449030765499180d12009440c0d0342421140029006c2c0c1408240005109150308855542d080b05401b40e806079130070f89050300b62141c42c421200c540c4c5140c00002c030b0b05541110551f5100090030a2080020008c40703502c0c1c505842c0f0000941060b904c0168186040600d1422102042248007050038281d014403440c003c1031411345040d4514501450094200d10020103140a106800160101411024000d9200f481c0e401400c1b1580c2c2c04012580554454045480c0c600320b035054000020f020780100f5400b10828515190080312038030703140420009140007a0b00f0b039040602004802c50b01d540c0e51810304090304a02102502d032506141b001800c0f01f0400b84e115449a141080130008141c0344010386030501d5128181d10358 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 519459460 1250 519458210 519458263
    0xa030c1e0606140414041a0a02071217060102010525230a080f0708070c030c02041b020d360902130302040b0607110405060a0305070f06020d0203040602 67
    0x40c8034404110180c1002c0c50000041105200040c1c0450522402c803400d00521100050000380301c5010b440041c441f043c0b03d06181a51041420f10590042d000740300103052032020388400000000c4030708241c0008500700c40c52203800c10403240154101000b071000b00028603104d10702c41c80c0c0d012a140c01c4042c51411a03c000211489030210501134814111400c3c00410320825541441d041035241c0008141c0502c0081c50903102c0205c258800c2c0010394990b10183c03034020080e80c40003e1300c4400d5080100034228030015850343d000710201c0308040514080c1c51a980d102c024104510301000004000c0340d0031031038071001224551810180340300d01ca5a075a000404051140708022688205030450012400100c2c000c0c0010115044a000307450900841c526501040340c1440781e001b00404011000015030b0040c1401c2c2d215952050700900000d940716120745840c0e180c200c4547c040c000301840f41c9000c1c04032030390500c402100003405000840c01d150802c41c0180d1100c1c00c0b0031400714203500c51b601004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 519460710 1250 519459460 519459503
    0x303090606190906080c031e0a02090c2203060e01020412120201060f08031306030603030f0818100f060e010321030f02030a02090307140a0b0c0c060f07050c030a030c 73
    0x40c1040c3c1810004260b84001080e2144000c408151203802140c403e110300b1441c0300c120724850310300100640b40302a2954200300840030080d00200b0001d6051024850005c0861b40000c0d0400d00c81619480c0301e8614a0124143e6111005004451340103010801149a02451842c0740c568040c602c5506603984d00802ca004011541c803e00d02900c0084000070210404001804040d0000c125030300490749910003542074034002d100040001d070000d561808414401c524072900001c4641d8614004d80e9107060b807901c0c10340c88005a00520b0760f15080700c00c0e000c000c0e1003498001d104d00f45a0311110361454032404070300840c2c0c09507c0031250b241e002c170680d400e00c0b90b400702c40c2603030b00c0a90031500c07030405d0b918200c000e4204915090007031150600116500306c13010780b02d800d81c0e0401008004514280101800e0035084982001c0c074031310a407502c3d03510716940d1001800b91010404082030301c0301c546050541c0351200d80000d41d07010b074002c800b0140c003080c9d10801d1824101d4115285400f0308451407140c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 519461960 1250 519460710 519460759
    0xf060711060c0109030c030f02010c0503151815010813111201061d06040c11030d0b0415060e180103030c1118010e100f21030c1e140303090606 63
    0x80403d504c2d2004190800da0852a8030200900aa665000b41d07010440203070708844c5507800c0100030420a200040070404043c42082d10224040d28028082c600f0681a80706580103491080176a00c40c05003001180d68401c080b10342c001880000d100b5540126240c0068406405003c02e0141505c8a8200301008094002c0401400350000e10350004030000340100400605503007091155082c01401450304d0312500e101e14180b41d040010f1481c3c840c0cdc150340c07003000b400c0941009800c142c43d440c2c109800440003840800410b61038452181640e0810200407004600c600b645100c012080f0050004c02d074403c100d41c882550001104035203400c0e042c00034600c080c0c5071924600120300040040750000c1c030480b10fa80128070480e01a00075940381c00e101124021580220608110102012200400d00c015081516402424001204410364503600c0030344003080300f9101809174102c02541006004108040000c03500c0e0b015504504144582c02d8440700045c0ca004d00c01e0381407000800501c481c03452103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 519463210 1250 519461960 519461977
    0x60f0509060406230c150f15061605030c010203010501093618140d030c021c03110310031a01140f130c0206010e0f060306071206030f0b090c0f06071106 67
    0x800e03885d040e00100c0c250b541c0408103540161843c4030401314440081c003c5006024240f0b50905001040e10081480342c0b03904564a0359004240d81911000490030900080591446510000da41d075030400c4000b5202003900e40c001101d1550941101058000b501200084940102c4102c2c1c0700510341013200c009030694000080400280340c00702003c00580b11022540001e111082d00c000610586041d0105c0d0050002180503810640e83c0c0840c40103000c4512600c403007141000110110441c9140141c1e420840d40050419203c0307c00348207100c24a0007140081036040c0c1002c0096040000e202e811001c0e01c00d02c0c901031030112942101c070342d40e140c214600c500f01a070030420031060079402c000d54601007803003296840030017040801c07445c180d0f916085118a002030002d04454440c400d003122200342d0300c1c4000e0445595010088001121200140741d1640a00b8065a00341081c0d600c0c00d040480c07292510703108400c0d49603000e000f9165041a42d0758580c0240c1004412541d14010400a1068214 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 519464460 1250 519463210 519463277
    0x1b0f1206190b2208030d0e07030c0e07080a020901120f09330603030c14120a0309050f060402031b060906070503071703070801050d050f0a060501060f0509060406 71
    0x2008100102e0140150040351030010802980c0703041c48010b90030ba002c05008400c442d400800100c04c0c800710f65003141b19000c4141044507412a030740d03126642030070360f26000403085d2101e4a00380711303645078050b460681041180b0405c510b000c41620020f000d804a240c1d009800a8507070b8081400f1101640c450b40480b608150080c0d403108149161700d00110442c0f0054090782c0c0c00c41c00c81c5041c00c002c0d100e034109481d4991113207000d1642c0d41d221342d00e1141e0503101581d614480d101502003400f8101c00980008003803900c0116900c900c0345000c1c0d080503d5030844106a034000710030007025a9000514081c410355402041200d000b541011840600c034040c8010f0304040000382c04002c103c00000142011170044011040f08440f2080220720341c8410385141c000114401d005014614200c00c2444a203440344048882070350700c4212540c1000000502176444503503840040204036001030700e040c2401490308e000d502c0c01004500260700e900a0707001d00420440003101d88286205503000240c1106440345 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 519465710 1250 519464460 519464509
    0xc09090f061f0902041406070516120b07030b0a03120912050c033d021204030905040b030a020607111c0807020319050d140f0703081b0f1206 62
    0x4040300500c00b01c45090400441c03004034002055240d900c03e850507140300d0b91a405c401c844003010403202d900824410345040c040c25806402c0d091010041d580140211407648002e01d2140c01c03d131054004c0106131405050505251594564070916000d0951fa40003101e030543e900008002c580c400c0c11034100e90481c03800800c128080c020b0002ea0022600c00441c12680c0c00052511818030350a41400e05138521001e0741d0507001070441c02462105440d00144005003005e011248e01e5070148811760b401d60100d80b10107000e000790700b8203005608100308241c008040c00d00e034503404100244610100549140b0407032106035401c2d0b13240405640d0a6080743c60f0300f404409182024002d561195004034424852b009072207003040c01d847d040191982e0400060b090b25986000c1c1990403030151b4800711030580341040b40f800c0d0301081e038000e49529400307aa43d0100b2844d00850340210320701005030040100d01c05220380c00105105404030f503183c8541126040b041d440b0480403d07441d8140081c143c1d0000010f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 519466960 1250 519465710 519465721
    0x708070602100501150804080c010906020a03020304020a05120c06180a03030210060905070509060d060504150302010e040e0a020d080c01050f1518130807080a0503070f0306080c09090f06 82
    0x80c81d0000c16608000c1000f699030303601e094011a42c0c00020100109200e000004d011072150005064240c800c0000410b15012607a00c4104990111007179902003030b40803052106500788001540c018207005d580786003104110403050384e0b03210030110080d4801c900020348502e4084d00c045100b1070100014020120300c03074682c68080d4942c5141c03c112a040c40c6081800a0410040d0003958040d107480c0c0c880c0d03032504050303400744000381e0300c1007940c8407400791074540025a80d1900e1003852401807080b0390300c0d04102c3c11031000525070400b56988510403030916441000b900f101003426022560f0483d060145101e05152480c101e000303440e685d0005500c0c1400304005491403106261164107244c140c3c050f044141800c00180321b0401c400c40340c000c45000e001491551096000c841a035000b1841c482c2041002d0fa10030b44a40d02c01c40c0800002a800f1081c4a00d140d042041c000d440c003020700301842a01d0411041139a41c0c0f00040600341305001d060301181c58400107200d030059005c0850155503017880d02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 519468210 1250 519466960 519466963
    0x2070e1305011d1f090305090103050406020c100b03160315092f0907020a0c030803091006080102040501030b0a0b090906061c1d0109030512041a01080c210d110708070602 75
    0x458046a504100340e042e580b14080d500c030304103c0546c15282e00b0704040e4000c00460080500a00449440307500704152030080c0b00410200c0310150001d032001c04d06030000c04c1490b003401c01030784040766602c80380700c0c091000a8810804101000102d01d000481411600380088210000c101d100016220000c80c40f146ca9500d0300046810351065070104c802e80c45000c812680d9940d048009400884000024400150100021600b02c6088400ca4100c00c001841c044126105944461510ba600090030003103540c06000308001d025003110307051300203458170040d41a02d20a4a04040c81055490006584d0b5641c00054580315450040340100f0701c0740d01c80d90302d4000d0000d500c400820401115100440b90814024004101c6d4582d5546040902502c901d583c810301c00345c0100c560076507006c02d4850080b5040b10690081801c4401400d21110310307010300c4180c0c50741c180e998404480c20711031001d200c1e800080b5034004001c07078a410700b030b4403429030320b036070708101d080d400c0a015805060b43c0064819070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 519469460 1250 519468210 519468223
    0x101d1203071e065f011403010b0a0312020102040e0117060a0203070f080405073f0803010302061803030318010e0309010c15140c0a020d02070e1305011d 67
    0x800c180803c00f16003401345090428002c018a4149844040d55a844184911082080604e240080c46542090324a01d0703515808807401440400201c1000410150f25140c4004016000541c001c0140404003004511412018000034008280c501040c50001d4402d50445004109000114915585491078402c81d80281020009a80710b1307200803404072002c0e8402c40323000d610302d0784401000d8000030809569485008109031110b018280000406292101c0002008051160200c10b00e00820f010144400e0344d030015001640116200100011640300c00c89042d80e8044417440d440ba03c1e030f9141d52806400340500542c0500000c801d000000342c3e8050808245e000b5000203202ca500d5003152690b807030142c2c0e00d0303243c00501240f200c00085940c4004642d150f082c03046001c22801c0c081a405071000000303032450701c0110400921428260350510107001c2340c0c440380c405401d145280070440c009005c400380c43c2501110a4820500c20010309603c03240070001007802c2d950200581e40d103210346490 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 519470710 1250 519469460 519469463
    0x7090306140c0915040902130f0f060914190305060712050603030702040908280e1e010503180106180b030f0d0302070f0f11101d1203071e 61
    0x141064007481000360308020440c41082c501c14810704004140040112200003c01007005810003044086800a0a40002d00e40118044150340d035031890642c041350412050b50202c0e154040e81407040c000c03140d100b00c412040b204c00721001c0141103050380000307804c0d500301f503950181f000300d002000081110205e050307841188151581660441320360780d0b020503150100d0320f01e079041d001000740f036005242c154410310b0076602400c00c003820300360900019026014001b40031031100003010300b402006944140c650b00202c000391880c90885550451022400c41c1c0110300d28180640070001607202180a41c040345400c0d180720007803015582c1d8140f0f691492041c0240446a64101041142d1034100055211807071700c3c000c0020a00c1e00d01420b411802500860760440703083d43d2000e00c1c48003183c440807007501c40314007030b040700b406d421381d605c0401c03202503450440801131121582c1c08000c0d4000b4903d20b9101c0040a5a045030350040400a10381188540e01000340078109080c00324201c1400514400d0041707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 519471960 1250 519470710 519470723
    0x2010c020f0c0109090e120c0c150a200f01022109011404300e12011a090a06170607020c04021602010e0310050a021218060f070203040905070903 64
    0x210519441d868050044001e400b0940e940c40402000d1700355800700706410b0200007a00c028000b600789940380b07070388001c548201941c010341201465203403044171404c14100300500b4030b182040564010348082c5882d10504442c0f2600304a40711947d40501030707030411881100c0210b540e10a03412414800b10001122041206144000a554054144118210390030120071160b002d079501d940703451820009100e034411040490189842036502d0307180c000c42551084c2c8402d01104141004c2c410200e00c2c1e10350500c01681490900c1085104071403100161100981e07000d41340d651161040310140c4040e0748041515655400845060600415000e0050020398240c440e0760341d0650401c0140c1c056102c0401c0706400c8040460015030250b10840740e0707540098203a800c01108003a0000485404544101c2d469400190b50780303801c40340c0340704030f03910042e410640d010391b41124007403603a1000002c101c010242080400f00f03119078000c0059030000c200071078042c042ca1034071000050507482c080c0700440e02c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 519473210 1250 519471960 519471973
    0x1060f0506040e18070510030e160b030a090302030903060901200c0601090b0102010b12010b0a090509030a0309081603090501080f0603120a0e03010603061406120d0806041b02010c02 80
    0xc5141840441c2d00325181c0b5801c845054490660703500021140ea01520000e2041000c0003489841d00f4200d0980c511716500c001440c5030801c24410704200e400301003440e0030400b60b4001d021007414078060300d40001e080c040006805405e03190592443c07185000d803690620030a4200045514150400c84c000605000300400c07610441d0300350380c00790040588030349142d04042c0042c03100e40110340c0480000401440042008000040800d16051004800c00000d9454550610090030071500c00c200504040c2c00030041483c11802d03403a124014400d0007030805442c0c0e0400e00030300240a054540c480048045c48040040c5440c001d040054203105042c045009240050b41d000208590301c0d2103000c010740602400b50482403103d09a034000e01d0544203014100d100441907490910814015510400001500c402281c6141c201503d0003406ca9106440403c009030010501144180722480141804845500e802d400036000d01540c551409000400004c07a4000700d50541103c9598103240d02a1102d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 519474460 1250 519473210 519473219
    0x1a070212130510020607020312070e0909010501080d0e010c110604030c062604030806330705070b0901023c01091208072007080d050c0c03030a12050403120e01060f 72
    0x2c59000444015000d80c10034421031600090030314074281c1c0030101d07241910100300030100140d53310800b0b82d80c840040e0364440052001c01420824191042181d0030b00070402400344000802e001d8002900500990804040c424a5200d071002d403400740d9808410b0780542600c8070802003ca0841c20b1002c51414000d941040e50300420301c00c0d441c0256017558a1004c20390340c0c0018400350482d18150f00c9801d580c80d90624244503004c00b4034851151300032082903611101418034502c1c12a4039004805016810041d4100c1030fa000a8000000c00340300028854000a148140702e2017008070411031034125154001c88102e05040d409007108900c25070404000c1c455400d012945010100d52107008140261411241e420000c820000c40150301d40c00c81d17408988845c940c5044c01440d440c804049007003c5010480c4080500c10700210920941c021420400c094100400c614141c194007174a10b40d6800101c1d05061040b0401c101c4e194800301c041c0200c036282500a402451a0300c541881c0e120341040114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 519475710 1250 519474460 519474463
    0x105070e1302130b040b0703090b130303030e0c03060a06030506100f17030705070b21040b0a0207110a0605031611060c091f09081e0c01080603070f0303081902071a07021213051002 79
    0x11440004a4061201207044dd5810780c0204281c005411940c801c02c0503d110580d0204221841510076040100c0c400d032451070554a8504054186c40c040f0010300c0341400010516100781080b0b58041103800031541603500d000b8258425801c0151003401904170104654007900020034040a4035035035803502080b403002280200d64141d40040003000c020021a41414090b00900051401014072414284100d00080c282d80525802180841c0001c0108862a5036001d403003186401d040c109000c1d41c220b443e40707c44d110b002c0200070070540040480c031142c1703644815440c6410010275000f41110a0a40d0101901d2440c0c0f600c640c00f0706105400c14602c032000b151030801200503503100107043c011080001590328120003081207805200310030300014050a2040c88e080150700948a200745410000350200010076010800d40c5a24010000c0c0c10005076100d044514241082d25aa0060389032010101d0500c11142454980b419003c41e07603540b00c141d403035000c40850340c4c1107801c855940a2030506a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 519476960 1250 519475710 519475717
    0x905040209031203061c0c0905130f03230d09140a020108040b180d1205011418150a090e010b03010c09140102070e07020f0105070e1302130b040b0703090b 68
    0x242d0542c1000307150100e425450300155030007a03c010059901c841c401034210703024840c124419512121440010400c60301706210344d0f6001540456018000c480c6502c0c0c035828003c0b1711900808205c22a034441c254003441c004040d400e5460042043d03552001c1140640c05002e24000c01d6882500440400954900000d4120410b40d4186c645080a680f90340311140109001400c00d003a100c044e00e404c1d080848107000c3c0d00140c2110f6150440007040c403240200031141c058008901c201c0c05000b50f4070301c9a85000603400a0800c043e99190300707a451400301030b0440504008203400100100001c034040c5503603005003038401130810013042000b4005007058280c032104401440490000001400840c4282074002940803040c01183e81041d80c50865004046088402d0001a00800d0200500f14070a01445401c0450740c64050664100b0100203143c00c4885260003032000d03400113420181444228500d00107142001140d500e45035551405000742d80044001c90018980040c08a94124a4800e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 519478210 1250 519476960 519476977
    0x1b020a090921090b1c020c03120f010605070f030936060b04260a0c09051302011409010215011509090911100309020a1502070801090213181a0709050402 67
    0x2000f5500d0310380b410094a640c402d0903246015204e061140702c4004083c0020030404e502d90300103503980d0000c0c13004030020900150180301364512903030041040c0359100d401e03030b500c040e00050703542c40c2b01d10140780030350301600207a00580c1441600c0d2002c03036103025003602050000c01090110031004044124101c2160080e014042208070180414000e201c0e00c05449001d10601803060f1000c00151200d46151621a800403510501480d10600c065203c500517544c10620082d05c0e45400089640060b04221200740141c081003400300700d10100b81c2c030802111844074400032001084e0358507590501a9044151404008580b818a00144003c058850340d218660000e00048540b2142c5040001820032500c81508150302e440700040541e8490030034138000e00500c1a401e84501184201904003c000c2c4c0c810000c5074581111003000d41c445120313101c0300c2410b440d800104208188298030341e4000301c0e0005404594903207001c0780004001107009004144a03115103c02030b5030303881007100368400c5034034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 519479460 1250 519478210 519478217
    0xc060a023a0c0e0d0f030212160309140d1704050a09090209010509010305060103021e0916020606040c0e09040303021c09020306010f0303200c040e010605090606030402101b020a090921 81
    0x8501c000304002113a50302c1ca5602c24810388d040c020410500280c02c0c0c10004149481c2003403ea0740c0002c140d0410740b00801000300032031401600b0548000590320311034440c1d01a1800114815607080242000c0407100604401002110080e803038052101c01486124000c13801880c04100216991500700c2401b4100c03584500140b0b926803e5609220050110400340031006c0b0904940a070155503c80049105180d0101e040c49100070380c0781c3c02403400c3c5001e045140074902d040d003000b41a9a016400310201041601c40144070340316858206c00a2098802c0c000d18a17411502c0d607601d24819801511340c1a000310200e0710142d0702c1c3c03c0043c500c80c0d075500c001008151520460480c1ea0900c5104804a45079641918800030513040400d05031640c4030501c45442e55614030034007451034000d081c0d13500954152607240c21880c3c03135804035501d5058482c8031800c0c0b1081704441a1403800040e421906030764050481540c0c503988106a034003810301c20f0411a0205203a5100585e42202c41e040169140c03143d50b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 519480710 1250 519479460 519479479
    0x81f020325120c0509130c0f0309020a08160906060905090403030e0106050303031003050f0c10110703020d110102060a111b0309062d0c060a023a0c0e 66
    0x200414001d0030151280c40a01c0001c82c1064059582881030060f107983c56100e140d40c50004c00d08010300f42c1c900c2c48501601c80e2810110291050744903940308450b942c203003000036004000d400007541004059002c032000d8071075444101d541030702d803034203000c06c136040034100b84a15902c03100c1c00c0d100040103000d45a00000d2110000300460301c0398201c83d0454442e80c0c000070f17449444d000800d0075030b401216040c0c0e203400303a4802002003203003c218000004005d00003900d0260000400940d6150b09011800c0401100780f160140c5034101b170007000c1c02541e000305841801040c40c90201c8022448031105405401068001025031050f4002c240b0f024100680f02844c14891000f02c180d4600400000c02c400d11040c00840d07402e0301c070b0b000100700c039100a04003203010046171b110a68a200e0903480c58080c000d0244100448601c001a03000c0d00032004032405070300c40c6c0c4d00d8182d00c001c0c02030507040401c1c900c8a143c03006040c4030351034541100b40700c50600203100b21200c080050316010742002020b45c0040010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 519481960 1250 519480710 519480751
    0x3120f0e061602090a02180a0b0702061b03031e15090109021b120304170705100f1e0506040c0e030616020c0603011403061b270a081f0203 61
    0x640080c91060040b500c40081c14419401069a4103401c6548052903903000901d107880c2210110151002503048072200020b9050505034480c5019a4078002e00854001c0b440c0003d1000402000b01c4c103540f4075080303070b80741d140c81c00740340840f03001e4441c82d40c0100d40c400e8086403950028000282100a000c1c002000c0c0e81d11f090b6020000354441c11039074001d05e200104046030000c05018089501d01c00c204075548074109410911002c0200280310308210307070200801c9001540205110880802c0c240000980d1040700f41120040d20380010300c0d29140d5222019003000d8a40e03a40071300c2c0640c10a8034100901811004145c4418440e101015810347c01000000c004092840d13511a0348035103403065511096103200400e4180e00207030481224100904ae03504914141046441d80c4800b4505c00b0b60a04006d800c05104544140320385a500070b1401d54145007c0c800703404a100c1114400351070001545d40d07410003140c80c0d00d07400c074208030a404500d09441c2001610700903030f070003122070f22440701452141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 519483210 1250 519481960 519481969
    0x3010b03160207210b07051207030905012307030c02190f08120103080c060915060d0203160611121809130f03090312020706090b1b060108030403120f0e 67
    0x900700814114403543e000420b40f103910404204602d00c41c507010494204943c074280c0d0915000030141010031006010140180b0801000190008654100040c0d58071b00d6040c01c0b0b025091600106003241c0f4400f00d40c10710368055800c00c5d4403c00f0203640820841d466100101e8441d05a44220444441d00088a1020840050401400300e21071280b8500d80032080060b40da004009a2080e05d02040200e88503056080c184101075101c4803907005000341007401d200c100c02148010b01a00d0103030b20450404c13021510300b045500e601c19045003202d4911584d07188010020102d291080340180501c14400035110000c40036502c1410f6010f09051710f05003c9005e0010403007005200c60048a8480c402401180502c1300380740c503560195030b07600d03071443c210b003400d11095030340b0702d6182c0466100140c200803181e0302051010035580d510b540c4554840281c00d100410701ca9540d4000d0b190702504000150003100000200100ca1103884003145034907040c007080e104017041c0b411607408203030b03414840303201460b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 519484460 1250 519483210 519483241
    0x30f060115051e0c070b0f0409050a020702040e030a1409030312060621040c0501210c0323010305070e01060503011202060403080703020a0605011a070204050c0919051503010b03 78
    0x2289001c0d41043c1d0b5104030300540001c00241541d00803800501003110b0301051000e20301601282c00303400d18000140c020300c2280e2040c2c0c03064070350940d40c0700c001c83c0018080c0e030110381442e50010010700000e80000c0c17082ea00c07580800b10b00c00100300b10075100080812807805503150000f004001d141450341000c910406140c0007058164451810492501080810701c1200080d4080b601c0d5503c0a20f00380c94000700940c1c098006070306100d051030318508490f078246462554001c982d000071510000c66175080d0090602c2e030581440a00d038504000f00002401c4600c241224051003c440c40c40d40e69000032507001000307024440014404100510966210364122452544044c140c60b01c1c00d540e03601c2c0c03910035402003401140140c11101e440028084507000342d6016024814600d02e8482c8200b80c2c9020f0381c0b26040303000780103d441e0700002c2c0f080c0344030009890480e0750140c0160b00c0c2107030408910348024050300490703110740003440904001d80b01c030341c040d00d0613180003c502c640745860b00640d07480000c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 519485710 1250 519484460 519484499
    0x30a0b09010e07350d1d0a0305100b0310060e0604060b21190603110f012105040812134110020f090a0801051003081c0504030518030f0601 61
    0x6009003c1c10303e100c010840c045c9107a40568800d05520510005031001040030b010141c403402d4003050520114502040601034403803401c8000070552414004a0b00300300c0340010301200c0a1414100054200b8144080c5210f00700c102c8040003065290030044401c1e004c0c0383e03d08180d000202c1c0d400c407a0b07400903152403030b0807859034200e61101e01941c0da0400180c400c107400446110044443c03d00407420448241c18104c0c000b401e01400058071501c4d2000b9101e40103040c0f05445842c0d60200e014025120115003e15420181020176850f0942c1d0115864031082e10488140f212850f1141001448a64001401c0000f100103000755124186070f468444187c0d0b491080c3c0d0040200103070700c1c000248001c00a00b450079442c2615604200100907501146900420503a4101820010712103158a03101054a61182072a81c1310070385860f8841e030841c885050388100510b8501480181500440503002c180103180f001c070b13901d160f0076040c561215041000c0a90681c070400052100705844030420041d0b5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 519486960 1250 519485710 519485789
    0x4140c130308032d09251508040b0a0216030e01030b10031d06010f0e09150703140c071101030c18030b1f06050f07060209030a0b09010e07 61
    0x54480e15584140c0d40281c80700012007003104020301840300d04e80e020f02450301070005030007082d02c0c15540b05602c07242e582010102000f46413074408603090482240c034001e04108892007607441c12551024002010968065402c13985900006400849500032500f01c41c0e0340d07101c84190700403e50b40030740b041003003002007906140d155950071f4050380303640a4010b4010210f82c0d010036901164480d14130005812414500d0540042c00188007a440c83c980040c05c41d000c0d025200f03134940e10700c09038604100c690440e0390581c81081081c0098254140c011601280a084000e05242c550354010b124030b1103200002442c080880490100a6010f9400002c0101d8681000013404940310150303121008240c004407111840007041c03001340700700b02c001420203e0341800c0108009080400107400c5020701a1102540800021782d00c1c20440c464043d503400ba071001d0102c0340340100b10f1401c9071034000300310340000d101d62809480344003050000880d0b034101c58004400c21004080880c5d114403007018003110030b555 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 519488210 1250 519486960 519486997
    0x809070b1801030f02160209011a1213240b010c02010e0405040c050a030b19062105030f03090a0311010b0a061202070c1203180e0a052505040801050604140c 69
    0x4540321317000401d2040080000310214000a20400c40c07403d2041e009480c4080b40ca43c1d0550181d164403080f40c1410100c48007170f01481c0d4848060b80d074640d600b548014428136a2030364822050700c2d404480400503034002410f121030402d8000441342c0102860000e030004030030485c50601403d00d64040c5800c0382c060049040c7d103e490300c0c04102690071580c421159000d5100c101b200140042ca104c1881942c220300501501d4a011b01408803000030042e82c1e00c041c02420b081c43c0800c1400c10807112680081d14115031607280520031561035100c2c4850030340c04614031803155054154184a903803e003007002450962031f5410540200d8030b40c0e01d81e040089600e039003046a100030031074024400004165850351034003e0450340c0b43c000c00c503903110b00c0301e00b5047c00c009006011001401d40d003903502060420300010039594400c1c041c0f01703c200d03a5104104801c4640702a0100d85e621000800645001400038095500c0d110203100450b6040c103440c1c010a03a088001c601b00c100303601c0041421075111929083c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 519489460 1250 519488210 519488231
    0x605070c080a02071412030405061803010f0509061305060112020a030b04060501170a02100e03100908040f081603061119031a010503070f051303080304060c0809070b180103 76
    0x2510341c00ba8800c1c1025a00c500d50801141c4101490061803242c01c1c0c8600c24180c0398580040d950740200e026491064170007084c410040c102080e88002c4111005000b4131101e00d5010745c8100500090342c442e10300740250380001d1070b10031517003001d001c41d16400430062820760307e4440b504100c1600316004990145802000102003411440f0450046008020009242d4540601707122900851400c5142c1a00001c40507400359403080c000c981d8030242410709034801c00c542c0000a041c9403c075094251050300d00315510051004e003901410a41d03000f24400c011198540001c3c40d030724403084103400ca811001c07140510000d1129000192000c1c17a40c001c0c14207240b00f04810b030018491203406800000d42d900302040c08090441d019038640c940030308200b882e6060003074000303240d4044030000b4000c0c0540060080d0a40c0485000f0308001d540142c000740c4c680c1403500c1c194001c0d002803007515000076812008640c00e28000300b000e00403659074032226854201c000b10948007184800c0ca41c1414035540c4c001092 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 519490710 1250 519489460 519489473
    0x807021e070302040f0605012a080a0e0301050a1a0303042907150c0f0509030c0d170a05130f0f06110102040f03050c03010c05030621420c03040605070c 67
    0x1404411751308030101302c05040c0000142507001c40403000c0b0780d420101d00e03c070003414184c00c82c0700011600041c005a94600701c0764290750049421a009070550700e031070200306403800150700c42c043d041920400090288051000c0503940e019501900c5400a100110080000c2c0d011100f50721020701c5260560510303000c2e03101d44150300c40540f00344605030340703d003400c0007100d900000043c1185a141070041c1410a200042580c60341011403a0340030300d81070750180e41481408080d00702142d15a1a00655441000f01c0040030354002a440d1202c2014030200800e90f400e403881c00505403800d00204408007890070000700e5141080350a45142c0d550308000c08690a600c10311150081c43c007072001010b40c8180d1906050840d1200d400030010001d0034414444665204041c8100e146414035076202554200c01d010703408c0094003101d141146112109891480c1607031094800d03814242646100200307034840c0c1c041004141200d268442150030800180010003580c4a03503000603130b40c0f9108120313882d141c0e0fa07507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 519491960 1250 519490710 519490721
    0x10b04090302150c03070f0e041b170109050f13110307060c020315060a09090501020c0304030f14010603030503060409050f0f1e070b07060c140f04150807021e07030204 74
    0x20703030068102200a20600584a1803650041d555944082c69480d200f00d00801c070f0501007049000300418880c400305203990340d410800c0307120b22010b0210080c070a01000907007140700300802c2c0407101c0a046c00005d600003981c481c0d0f52240004401c80c0381241c0d40c0401c02c17400704905c100211400aa044500007140d03c0401071341c00078204503180c20f06a0829401003624004605514a949014603030800c2042d89500704403030100c404901c40412040070b42d24250380079004454100d00365100224001052250000c845a01c0034000c0c1c10f80c05880c200d40a09078242d074043c1c000a00807650400228072981402e174854035400c0e000780142c41c2c0008a40c01a1400c20108004150060b032015424000d440791082490220a14040003806030a1034582150700c14080d10001a00701d65494400b210054052403410300b540d0029030a40b552060800c0c512241900180614000c03013441c003500f12400343c06182c65074000c40a80c0c0042ca40301c1040844e6100c00340300c808189019000b502000801a2110b0140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 519493210 1250 519491960 519491963
    0x4240e0604110915030c0c15010303031407052718060306101404020c0c1f1409090a0b0103060801142202060a0311040f0b07062f030405010b0409 64
    0x680d04003402084251042105a088080302c1088810700c20364031420501d050a0070071241d0740d183d80c1d4049a03040203010b10135081c000350041d01d840b0074684184190f01da059134441e44080000c0d40c04103114000c0f40c18101c40c10408a1010011080705402c048400140b404015104034030b8100340802041c0d501c184021611400c5c002801441010b2405011850744444219560303800e041c50107242501c007603001c0d06c98500036503000801d000c00c00810b0142040240005e0613004210141ca000e0003a20b00d42c0030250400951240006401e4881b04000c80380c06802c001d00c1102c0301d44450309940024100f8200f100c0c180b603a910000921140b00b8080c5c0828805c0384000442030346804803901c2c0e04900c7d90701501010003000898480140c0c0c403801a1086071403030786000a6804411291201213210b80d030005588080340c071200140403001100100600c62280e00c5c184100c020000c552101c0e200c00b02c07001c0391204006c2d003541102842007400ba540c0180140008607d0841800c042400c0b108400e40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 519494460 1250 519493210 519493229
    0x21002160b2a0a1104020c0a021309020928050c03010303030e25030605011a0708031e0f0403030e0c15070201020c130603021804020102030403020f01201b1c020424 72
    0x4018007070004d00c0c200d40020305000c0e00d06500c0c0c20b80d0303805000c2c0c0314030030346200038403402d90b0004880c00ca5455a020080081e4094540802c5080c40c4100501150790450b16010302d5107482d015240244c3c1d85c0c01001c0c06022501042400c1d0703400c55400703030058009443d168010f0f12a21030343c140e8448801810a1300310918070303400c00c000741c00c6041c4401620016002402ea070700da841c0c02c01c9192180c0200b2079070a640c100d0401c1307841c2d0703c0305800d42035044044041c800aa81f600000c1c0f200e60031503103403e13a014070b2007900c0130854070b24a81c804ca51036a01d4808826409042e1000380c1c00c203846201d0080c10014414170648240318684400643c000310044000482c81765583c0d000d00c02c5042004212011162103107034003001d86850342c0000d5984c4035502009018542d020640c0000c0c0c1d019503d411140302400395271000c9070b458401c84503540c10300600002c3c0c0401c10950014020b00f00f8180c52809003031710560580380340d9501d40070b000c098004402e0802e0310725503007c1c413000f2150300ba0b070f14030029001105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 519495710 1250 519494460 519494473
    0x50d0609231504021b07030302030a030c020606010e0111150405010209120a0b0a0c05120a1a062d090a170105150d0b09120409050103021002160b2a 65
    0x5404030480c00400c1040404400110a1080c0345a04050340510b00000b102c026036221070015200c0b00c200c04145001c0030700d109030307640030080607000702c040c1010084a50b801c02207010103540072641c900c425606c890205880d4040d684140d4890000c50801e449044200c400c054240e8200c000312840494055501c0d0358041002c101d1032030a5001e80310003910030704c024840f81645032a8030982420107010000515610b1100000c42c9010303804ae101c4108010320313110050b107000011070000e041072410805510704901842c40c82d170f240c95800d49031640804401a2540303026808940101a04443d20344e4440400344061400c9580300003001d4050251640001c40000301e80c04010b0079500060b09000307042034a01c0329200a40c450005400c03080d50402420b1400f62942d00005003040400e40004108003000240802c2d03107102c03a00032078100c134030948002200c3c4201c003d0880c0c80d046160100300e01c3d20400d01c0100318548a40c00902681114050f4030522515840001e50640c07815000c0c82c00c2507003251 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 519496960 1250 519495710 519495731
    0x130b0418031709070614091f0503060909010c0c02060702150403052b050d05040c0302090a06170d05030f09100207060522050303070f050c0105280605150307050d0609 73
    0xb2009140c2249850b00204038280c2003c9010304019882c00000c900008089154216603407002e455608040002e0b1a1010400341928000c0055000702c407000e0003110b690004c6030880702d052040f41d0166865660b945040e44844c3d0800800c1d901c0145e05980c031110002d9032802c1c0004603801003004504c031b40c000f044180403017010060100035a42c600b16003442d080d001030150f507400c40c04032030342800c0f1610700040c1582c03949813031098040940c0000e0b41004c860000c00c14800356652101c0259082c944a1200710080303014210303130300c01d40c0114010000710140081140ba048070310180b40c0107a10305055031850400c20700410202d80212409440c615120000d109243c40402c404503d940151055043c1880e41610360556034840901000c040244019042a19520900a0700e880d545440c00074040350500707048060710800301c0c218102242c41c200f440c1507403400440c4942c01c00c464028240f491314100c5e007940303154035800c005c1140082c03007810407a00591024910986002d03041c001070004540d043c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 519498210 1250 519496960 519496997
    0x80102041401110a050606010f12050109020409060e060d021903050d03020711120615011b060204030c060822030c1a10060309030207051507080a050301090f0902130b041803 76
    0xa007540d0013101c49000800d1022584c207611610030b00f840f201d0706500c0002118500c0200080201881c41d00700041228001a0010011900038120600040381c4556004180340d0043c0c03025035100403c0c2e04a5401030403c80a20b18407260000b5a0114107541d0340c450342d0824074042d89490010368009801030802440c601c40ba5803840050320b4200310700d03500003940e81e60b803540903088002c0510900101c9020380c0c4200c4d0b04801361101c10040752040303045480c1800203034205000c12116084140b20109006200380700680c842c0b200302d441008800c16078a40025018002803043c0c081190051844001c00e0003451000045002c1031f85261461604044600c034056464000b141010705000310040400e80c00100c070380a464080f520412481c0024030845082c2c403aa8800401000e03003c1075140760550800003940c12111040300601c9410a0401941d04850741c1c04c10080d4005d40c03090401c0556201e5511190621101510015a44d1400301a46549103051901140011030886810015120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 519499460 1250 519498210 519498227
    0x181302030613050c040b15070b010f0b0a020703030516170a020106080613020f18071701060306060c061e050901020a030b0306040506060d0819050903300d06080102041401 75
    0x42d5000b071210814842d0343c4158850840c4c03071455124030703103d81201e4481d075107050b543d168548680c60100e036590154908900428002d00c1681020055420001442d841d658103c8540218941c094017140b8117683e425078054010359802d980d1690008894800296402c2c0340144038003d5410064071003005105c024251420b03a00088405d070440418055a80f82001e10480701c554100c0c1c09040701113402c400309030f640701c0f00c03e03004442044803802d01000540000c0c1c400708000001002c403003543e1301c52206800703881441c0305101c0007400488031880400c403c1ea0203465654080ca0f4400e00a52180c1302d24429a202541c01e24590b9600090b12b01045400d44074401810781c0640c050312051500f41c8606441d540000d200c24011035044062200700407a52080303e440e000c44111003078a40000c580001d2154115060f864080e00ca080c0194040500c00c1c6082c00c0d40043c28407481c6202c404081040790030750400d01110500549515003c03440900a001601c0948811003081c0c01c000c65540c001080d100e03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 519500710 1250 519499460 519499471
    0x6090b0405102304020c0d0908060702030306010903060b0409020d06020d1802180702280b01320a08060f150604140118030605130b0106020309010c111813020306 71
    0x82108904000c8403c4115018644881250010309889420000320b0041e02c6103890300c2c035080c06080d00e47e040b010381202c41002070703c4003001214203a6a445001740d98a200035240c1e41c3c00315030001d2041000500c035810258030064003030004210440300c0d60118280b0100380c0c2044542503004520100244c100e403044d6804000c980340055035000c0381d6004a240c0000c030000c4074821582c0100041c0b4024004c010b4407141801d03040522440c886210550710341c40280401c02c603408041e031400002c1c20502085090403011303108a403e10001c0f000900e125004200e1101d0301d03001504900c0024070f0b644140700c002e1040c061004040102c1c034201d51f44030419400322007803510810040c842070103030810884c40705070640800c3c00c1001801d43c865051320300401c0644e000400d001d00f014100001c0400724108040d0f1070b072260740c00c181c90382d80b00d1405984900032140305500044041c900c59000c144402040c8155040c05852001c1026a0400300303e440035003220140300129140240d00c2c2103040409c88242d000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 519501960 1250 519500710 519500731
    0x9030702010c0b060103150f0f0b0c0316050f01020a0210110c03030118060e0403020a122a0212011b020f063c0a1406180c1c06090b0405 60
    0x2a02a40081e20707441e00050054010920000002e40c0c2e6402a4000081542c410b074442c116907550790440b52080d800c0e0300a072100c070030860000151400c0500280d400c151003000c003450500c3c5441c0c0001040714602c0304282c400e441760130f0320310090074002e200505c011511075003e0700c84c1480340401c91041e03500fa0002400c5001d000c03c0803642e1042c0120580b03042d203e0b441c89508aa1038444802d8015007510781048004e1110348090100301600000e03214402031203003183c1101e40b0424841903403041c0384084a032600f0780d07030720402e00e5141e004000100c09603440104603461081e1141e94650848003220000c43d990880e03400c003501c04540402180040705a4240100103e107440040c240c0a00804a0180094140f0b0040c4203002c01c124141c840000300d034503107031001c50706c1c082c040c00c009405049400040e0302e0010000c45c030503040503041680000541c14406946880e0318410f081c030f0394403a10250f030602c03240251a5100c10381030302445000740f00a01010a000d042101040101c0300c01920f1a95817 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 519503210 1250 519501960 519501967
    0x100e1e0703020105042916110103061802090d12030501052e03050c160302071d0405031218070303210209010e19050d0609110105030f0c21090f060903 66
    0x144e0740241141c00303840b81d0742c803810006440e015014000c203006020b104003449000c10011761010035494010f031043c0c001d008155030483c2c1040194112591030043d403100d034000b42e290070034031120b5030028925817038041c140072400e071010740300d403001409646103050010381c07210300401c19407410507108059030728040c040c521000413129001c200203038210340120038591035900041c18203000d401030f202402c00000310301c500c1480503c0c00039101c04084c01032000c00000302c94008410620420781500c0760780e1140c011442c09042c0d012410305140002c081c0c0d090101540c0c1d000c1c0d401041400254000c41c840c0d142d00115000f20801801180b95010341c1c421014414410b0901036a40a03c504400410680c2d03070322401c80b41108940b0703a003100d84c2c00c00c980011044042c141003181c5948002d480e240a074031100400741c2d00100443c1c0c0c500c401c1c0c6003a500200712101240020403100c0085c108900c1c9583c0100c000456041d10300c00b90102101c6054050700401308072540c940b0280111a03010a04002451a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 519504460 1250 519503210 519503213
    0x608060702151609050d060b12030a0203090607080f18090705123402060603010609020301050108010303120f0f02070c0503070803120405100608101401060917100e1e0703 75
    0x842d00010500e00c40d46091005054030240240c010300c4c0038000c05421050070310001d08144011704081c0d0382d01c83c0115925007000b001608081306807031010007113501071440d040120003088982c0c0c11003c4282d40c490f20800c4107400e07080c941c500404840122a400d00c05000203c4c0811150040c010702c401c003440800c00086002148540ea0a035200c40055020024070398500080d40d4130008035859201c40131001c0d905402c06a40006034503104e04002c40082c0240e03919140440300742d000030b21030035010541440c011700000e40140c80c00c0c0443c03c00c500d800546c03040700038160b000b501c4408102044e516800580395040c04110034044010f00b0066005080c0c25107442031903a03480c403405401c0024601d80c0f20104003004014044222031000c00001401225200c1808503201d03403000300950480b038508020590707402016081141240c98540b54004030503e0007145148a255110000903c2e018085035403880550a100701159124000014140480703d02032058000441c07030303405000e50344001f00800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 519505710 1250 519504460 519504493
    0x601062304091802040c0905150a02120d240302040f1401120302031905030906010603060f030311010e0d0509030c010504030206070f14030a02030a080a020c1b030309130608060702 79
    0x20100d600c00741000071603042410660440d159802c800940c06800c020340d0070f040c87d030700003126001d940c030450b2411a06030100a00054501c0703030850b100b000d80c1107030b0a070b401240d1201020f49020622548040759501003900ca8408500d11600c80c1d8007100d1081a0520940c28284180002c140d9851020841e2025180400601100501c2402d015007044e03210030081601c20300540300c0c07a0b074078182c6c1c2102c50f5400801c040c2080d0800c45e55401241708000c00000c80750712038002e0104881c842c961018203941152400c81d141105141703103400d03e40d2102c0c2c2e00c071112407042007603998a07404d030368510b51525404400c060900d84441d12581c10490280070610140e03071100105e03100958020340d5140d001c04240ba0800c0c02c41c40c2c1c00c4001140c2d02002c150b0428941c0c002c001031141420036038415000e580da84100c04205d0284040c1d01049504c44070024003121606644048820002400c69062030f0819001813021401c5d04a44103c1a40b140d03c01c100c1440b04111207900300c03000f40040c0040540e100f010700c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 519506960 1250 519505710 519505717
    0x151909050a260c0601080d02070e07050f041e05010f022107110603040302010203250c0b071b030e04110306090415060905070c030e22020306041d06010623 68
    0x42c11a1050340b0100c8108152054280c020188080c2683c0d260040301200741d44609003407003036500e1402012025856144003141b6501035274080314035100c1c6a01e442104490f550450002034090220420021824190040340514a240316002407440c081c10040010315a22240401e07106641c0180c0c071002d07041d00c041807e800c1402e0a1504d0a071264aa401c00c000072b003100790000707504448000180000d156042d001140b260200200c0000002d0040b90401c00d000b5100e0612000a091010510000b8a01d03c03030f00c0e5040029840c11199440f0307001414114144076a000314081035800301202e5940c141b130700540b1124107149010754114a4014007040310400300400c0101019420300400060001ea64071007000b42084400c02c102a2900240c003500d00100c840040c3c0120b0b0b124403c5c05018981461b1029040710f043c1203a2141600000200c0c001e074201800c2250302685845805c1615481184000d112500e2a8020f00c4030394940704010305001c84065140313101c2e020b1501c00f10f45c41003400045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 519508210 1250 519506960 519506963
    0x302160807120503130806040b090a03082415070615290c070e01080c0916030b0409020d26040f05011b060608030d0f0e07030201030e030408151909050a 67
    0x140c03210b510b10b8078500b188903131035080e80890484200426414000203009204500c03504109000d2b840302e0400d580c2d1280d4124004000800e2540040c045400c0740c10705103c0c40c105451440b01e01d95101000540340c12140e0020a26036602140031400d0000e0b5001e0440170880e640c44001c05c0600b4000052a607003082181406503018800030341304060300400403140e0024194007901c86075611600c408242a00030300c2982d82c0da210f60048441030b4900000c4240c0142100000c0070b018000402c0160050892404010360040e0354000c180c0250306c5041421218501c2000b80d84802e4103c044080c4100510b8908a000c15509120522203c400c000c00076090310780900340072054254243c0d480300080d03a800802040b190400314001813464000018191a0080d9582440300c090000681c80403603010320b55402c882e034003d030400c002650007503202c82c401203219001da07031600e612018858948480f818003411009a580100050300300d90103140024100b9200e0309004003000ea48441c0c2e0343d00c25003030b030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 519509460 1250 519508210 519508229
    0x11060304150c02060411010503060a091107050a1406160206040305070c082401080a0f23060f0a0605090103020904110a05121b040b0901090b060d02030a090302160807 73
    0x450180501e610032541d0070160548148440c02c06240000d48440701507500310f40c103007141d450744c014a60160303003504c2c030544002d001c81c80300b54580680d0300d01034004c801c0031112840c030410a060200c0c6060010b90180e50003036802c40130000107c0c210900d401c030000d18101e281c2031496914004994007291064220760540f400039203905003400d24107040540e952203455144195008501d1040720f424104802c0158034900c000d140e03a0380c100030358507101c20010082000f90441007460018690101100300d03954003140e10002d0510135205603280c001d0940f00d03420840007541c00c00c60341d034a090060b01d02410043d0707201c003540c2d4559400715040e00805000289200d0380c1032050030702601d80070070450040000400b10000010703910308094a40d1000c1c6160210300e000e0711171152283c1413a000d65100c0f1000504a030507035a00c2e05075100001c0c00303805507190b48210b040140c420389250a001035030052100034800107401c0c10a19010380f610801d00042200d80c054000c08020b24030700410a60129200300c003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 519510710 1250 519509460 519509467
    0x312060a030f061509180506090319120b0604030804170a0f06050601020f07120b0609011410020102090402210718230607060203090f03120c070609060f2301031106 72
    0x21944c0065005540011318070300d20344400d1511660740c11941ca5000c1e80907105451254550001307a03900c0c0d01c10a60146004c000c3e10301c0700d101da10300c6400c1d0f00c100940304c4000042c2134580440000e0050b8420340c000c1d940030201041c207101c02d0b440280b01203c12410300004202103080d079921000840c090160180c00c107036a6a000601e40d9000303224981800340d520080d0f8031030741d031108001c0800f1390748000300341d8800c0c480344009801c03401c10f205081d05030307141040551420300100c0100400d4000c100000c004554090045003c59210f5002030039001e41d40800000e0030034042004040f140030001c20341410410750045251f6400110303880c050551b0345252443e401c0050303100038401000700038081c117501b10000060210a00c01c0c10b074080d50140a24000343c408510941c180b07296203028001001c0307002d03038200000c912a0380c15600106400c5100311004284035559403500350844164440d904005500c5a06111585880c1100000301d00f100e1404010254150303114000c54502c4000e0396401600c001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 519511960 1250 519510710 519510731
    0x1a010f09050907030b1c12030e0105130f050708030c0a030807030915110403080708040303090608040c23030d0903060b0a0f2105060406060503071d07080403031b020312060a030f06 79
    0x1003618030603050b600151000d2110b07031402d1f0b5400e150000140002a20309129242211418050580a102c01d40e902c42d40f400250740300d90100c04c0c00c101e81214a445035078000540e82c10180040d16903003035010041c210302d11f06803e016000780c0005149a081500d00368003000010408180c0c43c500c00d040007000030781c4404110079600c0920403508080c260640101c0c1410401400d6002801524402d82e075001045654542c140c40788034041d10000c265801c4440280b1840c0c4101c491205041511914000809100d2012074140b600402040c40050b0801d6018001d1144d01e000303140f91120240da40107455071410071444400e02d03c500400c3e003d0b8402982540e407420300c40e400c0c07440c2c1c5508002560030702d0a007460000c0040281c0d10070319009010710381c070010704080751048240191000b0a5200300313030380d01d5000450b038120005108400341940d0b54a048103d100c2103080c40c07121446500216a03035500740900c02d0140c0c10080c809032041220341e5040c40007481c1d007441c2d0072445a10200c08610300140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 519513210 1250 519511960 519511969
    0xb0102060f090a0507293a0f0b0324040b1b07030503100512100203090705061303060b03122a030d020a11010c32030a02120703050103020307060e12011a010f09050907030b 75
    0x14140016081c184907200c204640301d40d00981042900f0ad04a075440f02c4000c0003103040c040c4568105150442d140001030203c1c060941d416400700d004080502e0506820040301c0b5550032040050340000e50210401c21444a41c0200501800c011241500490030034400c0c55515a0310680030b01015802102240b44c41004204e02001790000804c03094640340701004070301440c0c07610f00c020b85815041ca0f0b0b00e0302e0b1604010540044c5144e00d6600f051802e9040d110080d00140134450b00300303201462902c40301480c0ca0500161100c400f5800d000f607035412400340001c01c62500007000d8519a45410700119903a17410101501d440700350071180b100c85c0f002246082940c507800c041c40d1400082d00000700485054507900800c0c007071040802141c0c942e1110740c011002c41e80d0900000350140e04c500821b220302c2d070164619001e00d1000030400506038002c4044142504c400441c0341c952010310000c061301c2036801c40b03082511151240f400c0d11100d0b240000061902c3c2016108000385079681805100036280c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 519514460 1250 519513210 519513307
    0x319060512031c02030408040e06030a0615060e060405060a08061314010e130b0103080c01020f1909052d01030605031f0605040b0102060f090a050729 66
    0x80003006074400340220340c0501d80729030003a010381c4030383c038610a40d00b9640700d100d1080d6401190031070759075410507007003006525800c0760240403aa0300d44200a04000000e000303010383d80d40c03200f000d921101107600e0500054040050342c0c2c42e15204d15404e200a100648943c1c0c04e588a40049103400f8040b900e8050108041300c0000100d00e03030070750402e585501103281c3c0041d00341c101c42000021020954904814000e030700140c2c10b0040c80800f5000c010400304a482000e04061607202000502d4254003400d540c22560003003808041304106141d610042c241c1110740400100001e48400000c40c0c440e02941c1402ea1a110303850405544420040e0b1071039100390300c12006050302804841d101c0c0001c45030100641c20904004034000c0c01c1c02404503150400e4000c0c980030b4001a001440961680c07801100c0488008015807043c1c0308840510011460801c094401000600043c540c0210100301c1a200707240d850104075207181c0102702825685d6044003070035404000707000200102d11801c4542480144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 519515710 1250 519514460 519514469
    0xc0f0f0c15031a0409080a0c02060d02041e0918030305041e261306050f09100c1707021008040c09050a0227010c0b0c0d02030f090c0301060308031906 66
    0x41d641c1c0724454541580c4440e4901400c00e41690903120f07500200016a15441401082c4050034000c00c2000d034025004086220b1000b008942000c4c41d040d11101283c000340c0c000956010600190304200d02107060410141c00e20007000d215050503c2ea40b03285014a50b88000c081595802c000341c140708030700c2101c00e040046074000804e11803071400d000101b88800d4443d465411f04150380b060564080004031507400e822440e180c0c0c100c2e0326141e000d54403600024110700300c009040005800c0b40e03450300c0c0b202c042d04000e0b032150756070440641011410041144120f0342000d0080080b180076076604041c644a103101072030050015030b1580b03040c95080e803159104912807820042800507810142c0c001d0480494500c251586039070348000020b10b9243c401c00ca1501041c000c0803040041b414002109a202c003500c080f040c0340c1142c0506041c12680100c8103001460010320900c05c042d0020304c00e11403101821030081c890f00b421921514075038403000d010104040c4074040380310070741ca407160403a10090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 519516960 1250 519515710 519515729
    0x2240c060411010215090d0e13060303030e160b090f0103150f1a130e07050f07030203120a020a1d0d050708030301030204150807060507020d121d010c0f0f0c 69
    0x40c10549049620b1904628080e400b60040e020103c030600002c2c80c9207445003808a00509050303109440558030301c02d45c003403035039001183c1443c800c2c0c0700f40d030742d014400045100703503000200c0d810080030345410314051011141c0b100d000407804001040c0b00c002611701c1804200c417007030181401c40c801a401000000700001c40c01030b904134005a00c00041ca144c2085815100c41045c984140003504c240c2c03485003506600c9440e048050901a0350440c01c009540180709003821481c0100042c0c2201003504080310440043e4400a0041c036625202c90f0f10f150001c1410b1825801d1660000c00030b030240b501e40303440d0019620402800e030001c5d5503411240507840e4000098905c01a11a4411504c0e03500034003069000f14200040e080c0911201016001280c80315000b80140d2410544e0444142d800500c041c1d03485100380c450031000c1017201c114a482c20135140c86076250024100800c4c0881560001c9050500c1040c011900100301c0c038038189516154001c40d545041070302e078980792145032042d803c0032641 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 519518210 1250 519516960 519516973
    0x17030441210604020906030d05031f030510050a06050d05030306190909050106030203010b010207080a080c1515031002130b03090307060501080d080105090c1b010609020d0609140402240c 82
    0x800100b00c25000f03038001d0320084081e503500405d055075203030b01c078a1004c0050303070820000340341c82c4034082c80389015000c130501e001d04560b50340c94051030b1580c1d2841c001d8260f55141c007441a5050076204480041c50b0a03104601441959112242c0700c4c00b0080c00c983c00780345849244800390300305090800140c20501c800b04840c3e103180c02c1880c002c12080c04124007a610f8111848a10343c0005075103000c5a04000041022012a69445c02e07a604014911142403003898a0001050035000d4540d10804042c0c0100820300c0f00d8400700f500d49079216001000007403040240003003a14210720000f0035216000f809541d281c4030000e00d14030350b00c00c507400500194135080000c108290301040103014248940d5039201e15903200c900b004006507013a03410180d42c0c14208420714005104100782028080b116000040140da540240c006076403040130b211541d0740d075a0a0a00c0040001e10403032201c1c8288401d00401e40c1307415400b14254800d040300300420103121414159504050008940c40f0f481014159200c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 519519460 1250 519518210 519518269
    0x60510020106031b03111212030a090201170c160503070b09030a1101020903060f040320060712180305071509080405090105030f2517030441 62
    0x2440b907400100c1d1140072014081010501c02c01040040c0d036088032000c402d803a81c6001b08041c032800e01880b021750b4001e02924050019062000c0c6124201011010607107400d10700c001071401005900c641100d000741c505005128000c0d8040d80c80010020b000d07140b000d00d645c20014594085c65a0003841c9204000c00c201c0c265401202420b14011180ca8030025140141040c030b00380e000d105420b0744c03d50311250000b42c01d44640c40466400901178207021036120002401c40f445203545030a00350203540894148200d86034400e610002c08455036804004e01040c426100100f218140006810001d0114041044c015030020042c8444401602001000068a003035005604648941d0344222003800000545007004514a00140e111501030400c1001c1c903030301c1407001e075001d103104030610700c3c1a080851030700c660060540181a901c0004c1d515146440740520401034007403401f50303520020059801c402d04081c00f01c1c0368101c06004e040c02045014001007146820b02042d00a103d0700c20003945503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 519520710 1250 519519460 519519463
    0x70e0a050a14041503030f051803010528020a090e04020a0e010e0a0c0903110915040f02031504090210030915060605120a1107060b0a030f0818031f020d06051002 71
    0x401c1c1c1c02d064600f481514140d00710b809901d5041c1c4030150214107070044208550b44a0401000715000074504080d8150900340030a08580c0d0848440c40702524600074a08007002c1c0c14112002e13006488001d61524000202c002d00b0032059210b011500501840030400315650306d03c0900180c44800c150003265a0b5a13000d50078039100a880d0070740300a14180c000c4145034440c103015000d07290426800941030444a0034001e01c2000106540d02035101500000c585556601461100f0441d1032005a160b0515600941c0f1034104600300724130030380c41c2c110340ca0010784070141c3c4084002c40033f040004a4102c18204200403400c07510a0309401c625000c0c0c04207100f608080a0200c034142074807070009aa840041210884500820102e8507400a200b282c0010300c04c5c0d0058079030600e01a042c0003005071f4a80d0340009032880c510301141d0340c10000c40c500203400302107566100f4071f02003103008080c102c1e031403c050040d1950f2140d101c603016400013804030005040e40c00180082101504200701c2004031075009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 519521960 1250 519520710 519520739
    0xc0a150309290114012607030b15070c090c09030b04050c032e060e0604180b010b040312020d08040228060f0e030106140616060f0603030801080a0b070e0a050a 70
    0x2115009414480c90001d03510446090300002e43c004005801307032410b0b000d18405c01d00700901c0ca0041680f101403041c14ad4503125240c2101d2110049150744660451500c1009100e458125201480c43e041000c000c0d142c0c050307c0c04045a4009480005d40d807120304001e410013000700440740e01031040b00b0b00180c402050340c80800030600700380b20300520704580c4d05d03007076041d140a480303003984401c000b001040951a150f0301006041031000c21070764090072241e94212003010264420380b401000800c00300b052080c4101002201c0484d0b03c00f03000e100079141000740c041140a0b2029002e000f83c00f0580d821030703514041a04c00f204c2007007400b05e82e2990790500140001d40d100703142d17400641d1010040e03400b1700f0140510400e450035140700070242c078401c00038409076030002400c03201e0b5504990340f05070104046110712034080841d20b00c0841c1c1c2d5400c50401410f500d00c1a0700c2403803294842c8001d00c021909080c040c0760010743d07078600314680212800000d01d141c040b63700065440031511800144035400807006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 519523210 1250 519521960 519521969
    0xe03040302120a030c031412010f1d01080a110f1309150908161b0803070605010e01061d0102030c0f06040204050f06150f27030c0a1503092901 63
    0x541c00020301d80503960344580010b10004c1c00b00b030b091055680003d004840c40e03041c1d50251030700e4600b03204401002c000409421f038407281b41152160020301001c1c11001c5c5065050b64009940e003801d5140900c2039a46000c4040094481a80200000b40341e035148090410f95440080900c2024940100030a00074503031500d00b246c144140615140c1b010700c035802103041c5240c00a010750304000d0109110034800c0c0f02180e040f5072090314001503e100d8080701d002000602103e100840e2500414601081104c81c113030400240000c1e480010044c0304d038090940314181c040d2480707101603c141600107078510700507030350101c503e4003440c1360701c24000e08009902449203000320340500003a1900e031600005c2150a1304d01603004890280400c514540306070003071411282c0000c09501c2e003e004100c1c01800b50200b0110750805c0c0180c044945189410011003201020480f80c20540314039003910208590716000c291824541c552a604062040045013038074008121b0041900d85500a0105003140b07009015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 519524460 1250 519523210 519523219
    0x12020412050607090e100501050306040b0a080303011a03010b030703090212121c091e1109070f0f0e011d01090902030103140d0309020123070c060917010905030712050c010e03040302 80
    0xc00241c5900706224503000321b48a0405400e55810704004407141ea10080c0602d802544881d0102030a03201d02940c1001403900402840e140d506000c0e10b500d001141e0300b01484000c609000504c800401c90b41200d402800c00e050029000c1d0700e40c8040b4603040d1140600000c02e0241c03107100700640c10264000c0441822042e00c06c0740c1d20358030301c44180445490a40141260850301c882d100202070504800200d9400742a8880341e0410313050004951030310844004000880c0014041000350b040390a00c00a4095800c0c1044a41c0807400020005424801030a07800c1c2c00e00001070300d990340030720703290742c080c2a200500395521b42c1c481c2460443d070020103d0104492003141e1482c0755541c031a1040740306095059441c000702d20700c4801c0d1403140250a1201400039082004110001070b46a541c040040c6100c2d20b50010041c17408695a18619424080c9141340c0d050056003c0000e80210884800303640c4000d00b0b10017416000c1c030845050007802c00200541d8a46016048000e10000107402140e01c2101e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 519525710 1250 519524460 519524477
    0x50a0b01090b0706091707112d040507050d050c0909010509070c06051008010f060510020d021213080a08071b0b0d0504021f0c05071e0612020412050607 67
    0x90044407240103522400c441042c0502802001075219000601d50500030075001364040c0150501c84115480300308100d46400100e007654419007061441000c041c00d140d001e58110010001401e00701c034000c60302c45445240d503800011242d0740503500b51031110302c86c00c00c100309904e060307038910140c0da10020311903201c1e6070000f00010b036074030f004000f1610940c03003075944100010380392391020701829000d007171100e0319140c41501061005c0300f40300303d00a1f9501c045020901d20319010038402ca00101c86888011074102518080c3c07c2d6400007800d03040100f85415050b501d40444c01210401d40c07091b080500503001e07049041c0140721a81c00a4100305000c2c81d004c400790080c00c591000044c4072841548030018051100c040d94800546c4041e40c17090000d0b09410210348028403220000c0100c06e01c0c40042031480d41150148081048507001a0602c10014010100326150400703c80c5158450b400802035640c210344118509034041d580100003c00e455a43e0041900d0324a40300e007803c4908500007003005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 519526960 1250 519525710 519525731
    0x213080709061406070f03020c1509090a0606050901111e030d0b010513031113020310080f16051504030813080d0315060f050906120403021203041e020d0501050109050a 74
    0x84200c0f102c514000309401d00d458400c0d5203107115070207030380c0b010b030300350700444183c48110340340c222031256202010720b0015a5007d1010412420703040207040c030060949840c000b0300c00e00c1d8000c03003122800f4900342080e940e0038200c1d040161402208181180c10041441203c0d000050000301920a41c0d508903030a210100105004550034012006808050148207100b00046201140040d1050710090b00700c045503441c0c050614260703030080e5110130108910490410041070140140d4180b490600081d1225461244120b801c41038140115489010301c84852560b5180740402c80c0c0c02140d010888503110b0726410044903c0610511a00401d40101c8100d00f030200d100e0b04c51800c0a0030200f0401043c503003004000c840349180c0c0100013007030000410040300e0030750343e0401400d848802c0c081c403039010b4545850000c0c02e041ca01c007004080d855051080c0000030740c6002c078152075680e20300364018030500180005032418290103000ba0040d440c000000c80c014130a81c010a1050545000a00861864 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 519528210 1250 519526960 519526979
    0x90210140703080a1401080c01020706091802161502121e0103030e03070816080d050c06060603040f08190906091404050a140a050406290112021308070906 68
    0x50014100c0112080000c0400280110159074000300c01303450000c1d45440482c80110700301c1013070b0404183c960051103003401941e410029600038046910b020400c07186042d446034503544144034240764013900461000d00c1c51818105140c9207580200701100589110600000294001e0040035018440800012061140c1480b81d01542e00c01081007aa03603813864804848a18088602a070306d40904a00000c00010400201051442c03038100c04903418a0300341c9083c54154206042c806004060080c141c001001140055102c0c00030f0300c5007640d0350f4035890710504a80310090002d000c032002051030000c510303486550f00305915280d103036406c41648946007910a81224810700200181500d6450380b1790405401c410b802946d880008103419030651061164010201c83c80f032100741d9104100024424130f4098036490411000301411810440c28031034401d500140025814003804040250f1030350f440f030b4109c4041c200c0410445803c9030710b880d121500d0b60300d54480c070307000f42d82800d01c0421540c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 519529460 1250 519528210 519528227
    0x1902040915060306050c09221503150e0106052206120b1b1c0902130518060105040b01120b010c05100207030216060207060c0c0f09020306010f03090503030601050706020409020706090210 82
    0x200204880b042d010500d14440004016074204030078191a48480e1051780c402c07015100156110f00070010160001c4800b6032f048680a1401000981c1080c100300f0850300d40c4000c18801c580320b05016080c0c590700c2c0034244060006548103400001501e007e100922900c0310119005010126041c69420388503010100310b400b4041c40005c20b41c40c1011401401c500f1503200c4c0b0080c1d4405400d045442d82e006454800300e680c100c8501b036001010034601c6407245400e02c40a4090f100c01c4078100415901c050001700300e42120f2500240c07075035403024030344010f82c000c2440550480e4080d0450740e442c506c0042020107500404000c8025204892170340b02500505040318007030b41c140c0e43c010a81c6514184084035501158501075500c1100d4110118599104040390b1014128a96002d030392401c0c0b84000604491151040c1030400d854400341c880010700220440b070300000c2c00d18000d03841303902c0c50034401e00901c1a6840315289520004101c005c01c1720981050420a008039040c100d00900e00c0000d590f0840d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 519530710 1250 519529460 519529477
    0x1605040b0108040213020d0902060a0c1406040b040803090f102403022407080a0918050721141e0f0103050a020103090602071b03170a021902040915060306050c 70
    0x10500800e094135200d195020780301400901f00d002c00c040d8900e4000c03038480c0d07001c60030000000b01013984081c2070000340c0380401120881e207030080425103080e444590328000040c200515035400040415914203040100600008040b0203030381c1c901c51210311050080205a140c6d1610410207a000c01160702e0780510b010803247c01402680014400d0308680200c1038012050048010303043c40078001003070740381000d0000c0c0551501d540c3da0060034800a0310100c1d1200c054003600d6402c10080101050303200c107144480386c81442c1c040720320304000000701014109001b40c41e400302118034100040076032498a6003e44000c0c04241042030b0700e0301040716800c54400d00001c0c2541e8000200e84005503c2940301c540310300d0146400508000d130690303c12645074501c40003990306102c8160188140245207024050043d05100d031245001d03035400e800f0f5100c0d01c80c240014120880e0021440940d02c482c2c2003400c1950b80710941c0e0458420211000b4001e040a020585000740740100062050415404880140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 519531960 1250 519530710 519530719
    0x103110a0b0d0b21030702010e041a010f0210020a02011a01030903020a11061606020d05160207030f080c01020a0216090c08061908030c0a1119180e1605040b01080402 73
    0x200384542c9031014150f40418241c1002114589180050050664004441e60280510b039513103910300004018442e0b00003034a200760720b0400024102003848400f41e41c4860207080080b112488450240d04000c0e4a800c192161b5000207185041c8079810351004034805155001400780b60401c0c00110b04683c1d49060003005a4001000100411400c00c450954024004c00c00c5141c0340b440c092540090819103402c0340d031361341c0214441002c5491402074507030010982e5440440c001100d00f000f50b80d1129031001911003041040614140500c24040b50f8150148074001d6503551510b1030002e507600c0f00661050701490681d80301041001c903a0140700104401076a0b241850780741c88c400c104c100b10302a5409401d40c8940a40090049400d00181120000c40400340c00d2500303150a003485030200c0300d221030f0301c12090604400440d20309418024280e40e01c105040c0c92034030000842c50003d2840c050134001368407602e500098101d4041c0c1092055900580d4103025000c0d002c00152208441a00c009500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 519533210 1250 519531960 519531967
    0xa120507210b150d080313080406080601170f13020105070b0f010509090a031202090105120702010f0b09060915030f010e070303120b0108061003060f03080714070b07081b060a050103110a0b 83
    0xb04042c00301842d08051221202c0c145421f040c1d071202d01c2c83c1c4c015400700c404a030300482005529a00f1181d01038400c084032070f41c50203030300e04241942007014000f06103c0600e2003000c8442d0569103d5415a03019503031004649880d03052003494201505c40c2449094403c10768840010109140412606074060741a12040b1603202c1400710000a03401032002241000790030f006500701c42510803105030041703a0f41c2d0000200040c60f000340368240c0d0510120580a50242d809004054030f540311042c1d0b002c0c81031580315a840040d00006420102c0200a04010750b080241103c040306021610b00103d82c030989a182107103a10900200503607030740c0b25089002c240500c0005002d820302201d4120552900e00d40001e00548403031941005054542042d106a40041540001c10465040d4001c60003080d000926440d4540080e0f800180300c1c1c00401003c4100c04501c800084450111140c000c040c0c0301c0c10303106d0f145044004803004140900c4296940302860480c0702f050300300080c10720240c03041554400e28 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 519534460 1250 519533210 519533213
    0x7031806051503030a1718012a05070c0509070905060301060e090f0f0601080403140408210705030d09050102040510080901060f06120e0c0d0510050f060a120507210b150d 75
    0x7589140200351400d00700040304441f032582020b110701c01d544918220b601e01d100107803803122901708190480240500004104110111710741c50406402c0f02c0c822545840c141d40c4540d411100541142d22140e0007500120011454a81100c00811003030015516841241d44a10080400c40303130a0381e00a42d00c4202c0d4003c2800355101e200d980d988540a800c0101c2c440001400e01a0302d9445640003103855003042e03c80041003000c643c01c900d0704484240807907040c250207407035190300c1e40314800b42180b4050743c41d2401d004101081d015600104401800c240401000040240100c1411251141103500e0f080010034408441340b0803200750342241d0340f1221701e509042c0c280340040c24034107111221480b4441001180d80d8660710140300c0d16105a015182403821850b183d41603d80107401c902211070090100059500d4111f0103030203d84404003040580c0101e400e00714185020343c1c100d92104441100b5a5081038600403520350040d00c11350700c0c031000d640d40a843c0c2d10444d0030000c1c41c9902c141803840800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 519535710 1250 519534460 519534497
    0xb0c030f06040b1f0f08090d020607081f060918090302030a030e0a0c0b1b0118290408130b070807082a0d0801080a020f0907031806051503030a 63
    0x2844140c0107400d1307074901085807110070700000c040140d84000600e00103145030300300d0344544000c0d00f11403410010722017064120b00103511203100520180403c0b055900244040320003031040c21810400316075940c895038aa59004042078070034086c2011020402044a030005428402e00b030f10035400d94003940c10925800e400710064100c9800200140c42284241c101142142c58074400078a507416070550b65190444c5c000b482c030948031030100e00c1e6905d420301180c4601046601c1c001d85641c41810740600e84565044001c1c007103003609000c01240c900700700308800c00c40404000c00c4070742c618801604030785e56075900010051141880091002400b409000001074060024201407180710080440140098031801107001414410012035031007010101413080c0c000084e203015120035806041840712503000308100b04500c000c864010032071200090012417080e1b022013034000032044024080c4180d0305002c000b60400b40c51f000044080300c610940c052400204071440f0325501d4842426a4a4001400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 519536960 1250 519535710 519535721
    0x1e0a1b020f04020d0902060f07030201050f1b03130b0f010f1202030304051306050619030506040e030a120204080a030c051209130b0301020904050c03070806102001090204180b0c030f0604 82
    0x203181c01031700e40c110240180c0c0c40d80054417400006aa0441c0c440c461810000d003035079409415044c0e51084a414030003070582003c03250403001543c45200303541c2e031244019002070703120461014100d140340505100000c24400310841c1282c041c80000d07036045840300d0800310304840c11030000b945a8010003040009007031100718900c2003a0622800070ba826a2030020a100fa4064020103c1415054684100c11340d05489195003040060340c04002c96a240000d49580b8491017103008180203003104841c8884c0c6490301210301811421061310388854007441e014100051185089680340603032051841014820f40c11b507548c00c60020304088541150503c0c9400801988201c00d07003554080001020301c0e259401600d00030724000b04420380d24580700300010321205000d440340c2d00c18400c080040c0e23400d0780c0c0210304e2a40070394100d20300d45103100710603100c600501440c01c00a402a05182500445c243c10b94540d0456a018025206860381e0700700707252140b40b200300c604042880c034003070120b004c41c200356010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 519538210 1250 519536960 519536977
    0x3011d0a0f020a0c15020702010507061d010e210f030c130f060801031406070e01050c0c09040804030c0f05030718020d060b040626040609081e0a1b020f0402 69
    0x100901c01c07100d454240d0b404000c1c100c004c21100c00300030081040880d502c02c0d022034100011424500b240d0f0000701284550032015210a440300316030149071003036002401c59100070000801290b0440d04001d034866011013000782a01c6001d00d40c2c640d444000e40122092210841c990900d15903036075409086940100e8001d44658010050100e0b4082c50b611404014005a0312100040e61552904080341c0790150417010603900503000740b11840c0d4000d18555107039442401d00a4440400403603540c03510412002c4a0740c005910001c0c401440030400c0107205580c0134884115100d9100e40038080b03542001d104050300740c1d00405040000d400e41c0007a0b0701c10302810400c05031401e07800d502d01d03c05840d02c47d00107094003640082c0c10001c55070010503414121110514150900c03c4045200e141c0100c020b001525854031454042c0030400103804580c11005402e00380700c80032201441c41c89441d0840f82500c4c012443d424002c54101c4200b28451410390b50042041892101400038880a5041a1003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 519539460 1250 519538210 519538231
    0x30102070215031906060309060b010c11091e0c070201170906011a22080c0a0b0d05070908060702010213060905100e01020c060a020a0506010515032404050106170c03011d 75
    0x4c1c20b0500243c14050306000704030a940204d20007119081881c1200c034410b0500b41442411003090001500700044e009103800704030341400887c1c0d6694031306860001c0101d80042410504010018403403040c04c09407a41600070ba803500070312030406540d44000c0000703603185030703181e0302a40040020240c4495840000403030a0038240c1400c41e10b1540e00c03590381c841e8403180d614080381c05041c040103034100300317180c614101128201080ca01d850708007540362180081c01c0c60500e07214000111001e01880081d00203211900c110380040c0380c000e600034000c0d0000321205107803107403422000400b03074480e0440e501500c4000300705685090032a0403d0b5551002c80c920b42d8150300581d055004107945020140c81007243c5500a4050140715160041c01c1140503081903100c1c2c65402c0402443c034401e402500c3d403181d0083c2c8400d54841c80c0f0b204a4041c084407175109039110341070070004959140e0011201e6001106d2207840001e1b44c403900c0c00f01250740000d00801c100401000d040408200d41940c0541d04003990b046c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 519540710 1250 519539460 519539491
    0x5040905040b0a0509011e110405060a09152a0f0203030d0606020f0d020c0613030606090204080f0d05091e1005090109080c0f040203041506060e0f03010207021503 72
    0x9841015a00c003107405076090705821080004403100c41c0030f240c0c0d0041e00b01c0001c00001100851305d1094401904103002c000e85d446481c5211310940d40112005004010314540c1c40d0000ca410003020400f0a004104440b0441300132152454085c1c4003604841b010f042c0d40b0020803014a060030603001c890041030ba02840880e031000c1c0540c6040c002040342034541c2d1004924182055806881c01c3e8003400220465806156801c815590104000c00e041300102d480c15580c0b15110158201c20030305803c0540590b2070a4800200c0d0540313a0700600880ba403400036951015220080390380c440a9040b21507011070401c00c10703900d407450046008d940400c01c01c04403008810003c401718111a5020203684089840014203807080d40c0c00c600c2c103c00604401d00182148010034002c43c022244409000c0d028507000b01c04a010400100140340452201410402802d80c2d00c0c0c1009003820590f08206002d59820300b584070280c201030003161100c0d078000e4403018020801c0d03482680123034001800c2026006020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 519541960 1250 519540710 519540719
    0xe0f09131a07091d0f041b0b1921021b01020c030d142a04080a0c030201080709080c09070e0a090b01121407110708010629070816030504 60
    0xa84039151010141c4840d010903281028015002505030f0300841c190b079100103042c3c410b1080100005522030350000110740251610310709900030440d2104020040ca541140c00b095014014024000a078500040c4c80180303803100c0e0080c1c9580303840c1d80c1c1c40e40c60002c070810034042e0300100390011b206422041303440c02c400120806086007203030490900c0304c0e1560800a22441845036034011844409100f408614042c10078480800c00000c0c88076100c00f010348101c103402401104502518004d011000035104103084278902600845001e001c00c901143c0400040703502c040c8211010819030350541e000300340c51400c51040048516000388000c08116a84010104a488a4401c40010800900085104404000050b013a52128480c514090b840c00c600c035100d0505800c0c0281d0411060300f03144a0038011f540480e4200500b40e00990069800e000c1e0010302480100c0500000309010382c0304803004983e46c64100309910800700094a11241486610715656101000d4007010784281440b41c6001e03601c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 519543210 1250 519541960 519541973
    0x2030c100902130b060a080a0902060f07060c020105132019181a1c06060807050405010503070b120c070c0303091805040309351c0e0f0913 61
    0x490510031151615107822408500340880c1800020f02e241800303208590b5441c0c00300d0b05c9802444001020041000042800780325258400d000e40c1d90007405580e96868103e40d0340c4100c1c2c1c011801121313020b06d1700400b03a01c3c4a1040c400e10740a001c944100c1c4c0c3c0d140309962501d80d04110000c00365030800044559075404c1c0c0d0384480c5100000b283d8010045095460150342c0000000320704e0490003d1820003e8004101c201c241c141d10102c0011503002d0a65407400005050f40b070b12204000700014a400c8000c504104c00044610407514116030601482c0e8840e000c0c10380340c0d2014848c4100f650030074480140d0300b080c05142c06610540c03104a07141080c0c40c84d110140c04001a0b4029004110040d105200d00c0400c60022081c144901405000a0426039001055907070180702c2e00c07550040000308031324010440031071320310841c80502c00c1403950288840c2d11078958800440b14458462402905c0c15598061460034860840c010f180031203c8002e0300c01c0c09403085000701104215001500d500c0c0000301c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 519544460 1250 519543210 519543223
    0x303061809052416030b030109080912031e0c0a1e020a06030209150c0102160b0610021209091305030a090512030c0a0807020a2601110c1c02030c 64
    0x1100007003140d59840c00d00c0c0d41444100b000fa01680041d582281d00c609015102254200300e26403541d40c03002000c69000c8009003420460a85c0c19400d0a55260070701099401500d0741113412035800e071442211080070307a9030f481a0702c0300d10094009606511f040303010050140c4064802d510a40c1c1b14000155134809a01d0300c0c2c0641c4140c6101d01541c0c0c101036003410300d91a006000542411441c00d00c1daa000200c0342000d00b81103d076516000500041051029015034082c101880244402046c0d0f604d0071421007001100c0060045454084074800c85100082c000c0c0c071001004411841c200041c000c0c4240900000c2c4010f032032014141d518800110100020002021650f130780c04402170908040100c0300000c0c0070888081c1d130083c80b41104008000c01c40c0b4407081c0d4003215603a6591454800302d0f0194060f68445242080000030810b40c0c4001d100c910400602010000c200252600b5080c0140e806030481e804500d60050ba9504040e007141008140e112180340112405c15502a0402d4503010303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 519545710 1250 519544460 519544499
    0x601270902030f072409060c0b220501061a03070503070c0f0b0106020f060603030c031c0b0604061101110315010503040302070333020403120815040221090106030803060d030306 78
    0x1014085030820101a2543c50103034200c952526030381e01454004c0041c0200c100050150240b2790343c5010507140301070030180505644a00c49031502030307404e81c10402d000b0b140c54443c0074101520964143d04010031201120b2143e003864132141d040d5140e000e8112000a91124100d8440300c0c1030304040c0c080346c00406090f0003001241d0092003a041044101402c1c07a4002e0f0126020390b00038010209038a2000c0b040e22001c2c950003a10110b4240040400c401802a1030441504024009000304403298404000c8484e0548a0001d101000e4001d10011640c80100e550117400302007032481403469031241c4011030308140a407040f1a55103441e500c0300e2070081070140c0b604401d6080841d0450461f00b00e0b1542001e00c50140c1d8003141000d10715240c192404204411842c00c006503900003404001051100012548020300304545071400d09201e55214000103006880b40f4810b68002411108140a014103680e0710018040c00d5440380030510020140c0d0348803c03070505444000101d40e54640140340b10104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 519546960 1250 519545710 519545729
    0x304060c182301050913050106090e1504180c1517010f0e060112050103051b1c02060d02090915040c050a0206010b09060c030a0305090601270902030f07 67
    0x218060031014200d01a5101d0441109038080c4040080c0c08802d8054690b224a01d94512409001140122002e104a5100c2584200000c00b0b444210290398000c90580d40ca9483e1196040d44505410200f040708840120f800d10031480f4880d06820300307801c180001e6102c40c0f412881c441c46641c4d41030302e012540c1c00c00f01d08510001444201e1541c400c00420324440c02e10f460390459411300750002c5904c0207034002c0d403200030000000700b201da920880710288400500c0e00200419612480c04076124071102090000348041c40c0f07000702091038201314079420000c07031200824014403d80c2c203020042d0001580e00b85200da003032055911646510341150b02c0b0340c0b040c0c0b00e64018400c82d401000200d41d901c64481081220078040301c0c0038180c00003121815625004c5015031100c10880000391241300e030401250b40c2d400042800301c4020381503041a4050140081503510984c0c881c12120940340d8041c1000082c1182d0725501e202154081d070218001070b001038266542d40c1c146000d176514011169201700c080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 519548210 1250 519546960 519546971
    0x406050f090c0d080d090b061f0206130f05070f06120c020c041d010e0f01050a0623150412050c100210090507030b130c06031404060f0f1107030905060403020604230303030406 77
    0x686084005003040d038118891309d0070302c0e20f0f09820003035030340000815106440451088036410320140d4912802816408000c4940360791b1036400c50015801c00b8400c040105400e50609030a440b214000d414084841c0e40c000e000110ba400700308806000d400c80ca5000407000d50004428101c400e0041c403540c010418028005061100f502a08452000380505202440e000041c06292034941a03034203a14070303145000044444c6140010041c1c100d207544003c006078006400601210702d00245403440e40241c0a541c0e941c01c604050144042c5e19008140058002c00d060042466581d40000c0c506401102224a065100c0d55030005800b41603d10000e42d0905508200c100078040b4080c8014000c6807500741311803060710390b50b1000c01d40301800040c900c588a050302c2d20f0b030b8101507000444800600300b0602c00d4914010b09180175030700144080d00001d2499601103800c0c00d1000071034046a90140c400b5142038034080107401c0074103d00207030414480802032048000d80e02000918065401441c00059 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 519549460 1250 519548210 519548221
    0x15040b0a32060f06030f09010e0106030b0618010b04090f0906090308010f12020d0b07032901030c05031918050d0806040e0105040302060604020c120309060406050f090c0d080d090b 79
    0x1c9071100501e254418102e44902000c191078840c141d0350131082010000aa6440303280c0d001d40034205088928100d036203015000000d2180100c1c00c00d0058800b91880c1c503100500d11351203138508009005111005000304010007030140c440d4440030726002c0c16600015404840d94800d010780c1d200b00002e400141c003d50050180b45d030901c14100040c0b00413011109400c0265020554040d640728010302814103540010741064000e4100d208138186682c901403401214064149084000c4801070b0b000a14020f00707058542d0203441128081c1650b4203005010707201854054000d40350004421103041904404a400140c0401c2074a007401c2054a40250600d086014081100d180000c1144d03181c0c1400c0c21300001c40e4010440030b4103d1400c0e2000341c1d030341c4007510f469403600b4543c4c8000b542e4903100008100c1c0c4c614011480d5030260b840740406201c5510cd1b06c94403011000c050354216501c0d005a0518642e41c40c1c036014110301d0510541019040c12483e8034600f080f2031031054243c0d840d00b0603004108 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 519550710 1250 519549460 519549551
    0x1080606010f1b08040b0316030b010504030506011a1317011802010c06050a0b0d03030912021203010603020a1209080c0f071206090f0807030c050c0315040b0a 70
    0x1a800642841c040c41200c82c8041c1c001d14003caa51005100c030f04448024005100300c4034103d5020f001e8402d6015940c4c00c06d030082c5004104403091101c006483c09101c51482c0d8802e004550883e500940100403690820f0b0708840292500c410421040504000c1e060542d10602e10100c001c03c3c540036210b05111640c200d4a0965101d4040369200566400e40200180e030800808500c0340d4101d0300000e000d5807000c60b07a00052080c0d4075119400b400740c40c0c00c00101a4960402602e00c0d1048544008154482105998a1030b00d804010703001d8005200503c902c030f2081c1c0c0a8540c18216142240400c128500040d040740c00d824416106d201d00050310410b00c0504014034071880c5440300082015034985010070700c000481010083c446a1207840203c280060b404000340110b81181407596124402c0c540900480400d610880e09801203110307510640c5804546000c80c10030b208030b08201a62150b9034008806c0000b801c0010066032a0012590aa4504131080814000410840541562481c0c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 519551960 1250 519550710 519550723
    0x60702190305030c070224130506090f1005090a060522150c060f0c050403050f030301120b04140703030513050909100e071d0709050d020d23070e0108 66
    0x44084040c080010742d208007101c0d030084945400a0b2200310510001d0500c4130710403918035021919028111900000000810211080c0211014a1039985043c410240190391005600402c1102040c50900700090401c00c030300b482e440c059203071041032000035003d4466600300c0c0000903404078002158210510b091122217425181001d02030b45008101e0b2008048052201c0411904031000c02c10400309070088000800c0c040010700400c29000801401c50308188815603840c41a4042560421400300480e0305845200001c1c008680c0c1d0b0751190362070900003420490307102c507100c0c00700d02c1400070600442d0003942c070a43d18a0f50b251504240a0010445500070510440c0e001081c415030310000a029514403994200203d04c01c0011115141840c1c0b040d4010141b9818800240304968441060184124a6900d5000c25a51240c0a0044003121032200a404c50a40020500400c100a44440052800003081c10704110411030b103a00b42030003948005d0140e48481d0041c0200001480403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 519553210 1250 519551960 519551983
    0xe0609090a0b010311010c05010f05090d08091504110d0303050a0f0c02031909150302040911030c1c0605030307060905010e0307030c081c020708030624270909060702 73
    0xc0c411000700303480d440d0502006200c01030446081407a43d000070f0340110f21441c8001c1c5c11400030042d50009042d41e502808044603140703042d000d2107c01d0207809002c0c0710014082c410900c010084a017883e1701c50b059120f0090b02c1070312912181d6580c0034190340e4507100c214140703110759000310703440c103007160f041042d00c4000202c4403895007040b04411744907900001b61804440001ca50460a04030301000f500c1050040d0481c0a14106030000441c00f80e4041e0010011144045002c01c1000044228200c050100361a2141840401c010402c0c180c0d400710210020100405000036949603100c0000340f541e400000c04580c139a40b12032070541800001e102d9a00d1115107580558036000995900801001f402c46000706010004546280700c0c601215900c5626400358070219902c41880c1049405030304200d075083e2081908010001c40007180b4a0b001102251403000282010021890310800c8002d03000b1241c040d0507520b881403116910305400d070717020700e8010f00039000500740350074000d0404440c00c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 519554460 1250 519553210 519553213
    0x91110021f05160c0c030b1312030204050114090a0f06091e0509070c03032309010e0d121e111e0c06061210090311010b0409080d180605010e060909 65
    0xc2111030000a441802001c0c824584100355041c44d150844c5884179070340018140c40005030401c01d0100949043c14011070059544d404499905041102a841180985400501c03003c2d4982e044004200c0a811000401052300c0a00764035140b00f0301b1001c015511074800201c80202c00c100e4840700c521101c00c04034101c0070440e0b0150801e00450001c41c8050302440c1009041111002814440c0c1e01610a0a10140c001448040048104a480f28050f12480070301e5284c401801c842d08000103a00303400c1039598460140c0f4041c00c0b01e0a00040610341203a43c00c40d0503201409982c0c0352a03100e40303542c08040c0c03003030603407200d0301100703072503d040450f461009240d4000c0002801036480020710982c06a0110f96401c2c1d1404180700d00c505003c0c0415181c40301509000c120420150085010003012100c00c0003003010040c0041007000307440011401400c10341c410480305020340c1c2640c201100c40318407981e40e0750702070a6690f0b0712006c85000740d11041c552800300c018007407140380202045800510100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 519555710 1250 519554460 519554471
    0x6050708061212160f14031305030d08060111010b0d050106030308090a0309150e03030a02010c0e22050a020f0a030906141e06130e0106030b0702061603091110021f 72
    0x80c03003d0403445910740c00b03165446041d4548003005000741002000660141c0c1c0c00c2c01d001803212200e40d03240c2003072101c441c04111200003c519828002820074408540b556000440d44400740195500711051401c40a55522070b0030700c1d805502c0d280c1891030100e10490002410f94650309000b0329280000d8002c0070b05420494002c008079a102000506903079030f40001c0024101109400e6030100b2100320425050b000c0403a00300000f0740c040d4842c0304103d42035240c03071040b241d01a01708a4001504840708204080800c051140c1140581c00315903c0703c94540014608103d18402c14500e81002d0705c2031001075210711004c401c01071f56000c0d80d0600c200748408038100781420140c1e003801600d4018501c03128684400002e000341d4805013401001c0020307003820044003014030400d6028202e80d020503a0b10202c00340106461501c000b440d2032140c807000704000e00228030400c00701c018224596064508031303142c0c1c0c4ad640481e511a91060022000354004000856240d42c03440c2c203002c0300446e101d18061914 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 519556960 1250 519555710 519555733
    0x140601080103150603060519060803090105070323160c0e2217040b09030717151801050c0d05070e1c030903060216050f0d1b0f060507080612 62
    0xc0011415254040003284045442080d03450081c4501d6002500e1a420082401506d6003081b10041030311002d000107108a503104d900b595a2481040c1c0e1070340c0010700401240011900c40c000380c40b44001c820520002c240d4402e02401030542119101c1e20701030081c00403401c00c201c0c0030010b54008040c40f42d080b400c00d28111600032141000c0700ca194003805020034850f0b0030001011007460311000d09102c402c5e10380d03440d084040000e40000500074044d208040021a1403050340a02640048400009003081964400c603500d10200281161609080c0707440a412025420f0164510448411410b00c4c0c907101d600b1100425920003400520502c03a101d20032030400c0e1289460280c94640c010002c0300d1f406038074641251841074950000e000c062000c59583c400034411448546d0541c0581c0c00c07a0364200f01c00e13403402c0c1c554040140350408a0462084500d1249104400310790143c0203010301502d84495448000035204201e501c40005644207040048a1504c4c26443e81d0981e5804000c040340c540d20b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 519558210 1250 519556960 519556967
    0x90403020f16063e010606020f0a080d090f0b130b0f040512030709080f0709060f080a060f0b060d060503070f03030504171c050909130302060a0509071205030c01140601 74
    0x2040021880a001d0070320703140308041010a02c2070319004841e02004913808401c507500130403030390160b43e005005a103603480d22080006142881d50340c000341980d24191554000200901041c10202c0700b11403900510f2003c00c0c9078119403440341d481074a41d40d01042040c503010304480c43c0240b0b5184003180600612020641c002000c581d03402d61000110382d2515280029291404941e120010303d12420031443d54207200031a00d001140c141c1e1b0002d1100540303506580c5400c1c0e80c24081c81015500c159513074000300d00b441d04410b0503801c03180d200040380082040031983c42c0c0e202001500e186138031030703100f00400e050070091600140041943c6801041c2143d400510b00e11880c89026030030788882c841d02e0b242480070301c42400d5840b60400900001a1419400b801c11742040609500c1380c00c8500020b106510104801104540d0550182a081d601c0d206154000c1030050100380507403141010100d00070300301c42c21103501c1c1409000155251b4414214a600391094800d1010104540d03000f441070a982 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 519559460 1250 519558210 519558227
    0x90706031a0d020a12031e030b010f270e0f010e0c16080408030301030b070e040b0a0302011d030304090e0f07062a12050901020d080f060d060b090403020f1606 70
    0x80342c001464078a40d00005803190500d0308039189013041c0003140010036400c510302084911003031031003524042c11004250f049503c007119903800b20b0400c43e4008016403241c0d000356024858040c1c803203d0025a4041c16031424195082002c120055030180a80424203c00350750040c0742c00d02c40080145805142298940200219020111210b0003814200304240302600c000d40140c1d002c498480d07a59041481c0724280c25540754003c550501d103d0340d0541001d0007441d14615002c1c01525a0324556401190380a00301006821410410411100c0c507075001d2004100510040d0004922501c05907900c17410b003411440c09144da944051800c0140c1034020f8121000528900d10101c0301402741c2d07102005017207074203a0091490144900c20170359260440d020f0203020400380c1c2114100b4070303ea6800d4801000c150b41d980c4180c6101000103200d40381207442d01d440c06100f1600800d403c201e180118045810950741107025800c00403400b11002400c004c40d40601c804515216007161400e00007411540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 519560710 1250 519559460 519559511
    0x9060103200105070b040803041403091509030c040e03041814010302062a07030b0a091a07050c0a0501090605061807050a0c1208070311090618031f0509070603 70
    0x100042a480e0050f07004205a944441d0021800b43c0203103054500f46c0c20b203a0049508580164000021400c1c08074004203450075104080c00801d0300d55021041100c190300800c03a1a541441507034038503030311500c5034003420000107080ba000b0360301c2e18100580107070501501c403290700c452407811030700411703441c07001c2c0e01241145d8056400642e248044040c0c8001510203130010541c0c44c0722104040342040b070014a480407a80100615100d43d103d00e900402907506060014100049460150342c032203e640345d446070080c8035802d02c2480c0c4498422802c1c1041c40d03006054415940d00c81c3c0c00010300295004031075104104031140502c801c0484807002c00d43c0e40161001c820018040340c10300c030381401030301d804142907008030300e0328210b0401110003800c4690844040002a051590500321443c01e001969110180242070768100804c42190886c524404001f0580c548101380350441c0d020000c00881202c900c040201080924048494901e00b040c1903102e101090700c0c101e0f41101e52054484140c02c900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 519561960 1250 519560710 519560753
    0x20102090609120c0a030c082103150621060a0b12010306050601030902090f06150c0a11190b040611060601080f090a020a0914060d03090e09010204180c0809060103 72
    0x2e03c60b0140b018a484811403001c2c0c2c008401c401d01100b801070310154001102d40440c11988040030740850300804003404812030360031050500200b010009a60110300213254050401410300d03104400c1c5171540082012000e1107880000103024090901030240c0d00a4480180300c1c80c5011442a090240c3c40300502c005000b183d07640021404d50ba05c01d400c000c104d01d40040c50010703141070010001044c260103403061803041c428035034000070641202c07003552000100d04001d0b290044807915025110441c21300c5099000341c40d08510481c0b20341a01152010b0040e80c1040c0d902d460504c13001a007a01d000301c0071641107900504c02c00c503840e07921030780c102c0d0311448402070b6006580f540086c8920b08188210000d501669045020450207038581c804003100b0752010101010743c4600003404003c000c001c00241c000f50588801f4005007074021031554001c04000c0c0018582035581c019000001c0a046250b0f41864480700d4090301d03203500c040c00c03a41020b031190281045525642c0c1d81c0991085109010100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 519563210 1250 519561960 519561979
    0x1120c03031101110a0f17061323100303021002040b030c0a03020d0c020309130506030a02040207031704050a02181003141f02221503051314010507020607020102090609 74
    0x298642900301c03000042080013410348805841001030003040b010800320340002c1c1d021242d4602c520840320041e006507006401d1111940c01c08540380041c00e18200b20000d620281c4042e40000307c004107415200340d00e84441041c040d811454001e0904200c00094180e10340103201c1400740e940044203d90300031a403404540d03a5241c104c00184c019008024041250600e4035488040c1c0030f801000400d01c0e030740308607501ca64028031008058201c5a0585a9642642c80413181600600f0141e00034190103005c1d0a0803c43c0445811401410402c200c40c02c5407a43c11031008501142400801c0408103079940b003102c4030b03234034014107010842c0d40385100203880b41d218507503459888ad8052040640c00040f03440c1030401c1040d44d400f628041c0d440141d00c040031084680740840920307940c1d01038a050310155009103514240c0035004401500b005001e80d00c05003103a255081c009410210000c103001070185c000700f05850010b80103810410020528070035139004000001c05981c0b10350840307100c01d40846d03607044d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 519564460 1250 519563210 519563237
    0xa050a180b0d0e1c120c0c140a29070c060f020c28120503060307091b1107060509062809030507090b0a140d080d06060801120c0303 58
    0x5020029400749a40a0000400c1e07440c45050340c000a84424401c03007259151200400803240101c800041c0e4000601a0307280c10101000b19080b82c90124010325140d80040400e4031510305800c482c0911246681c000c3d90303000100f0441a01c01c42c4c0c02e0030403080c40c108501205100c5940310340020404000c00c901d5085000402001ba8481c1d840300e40032400c21901ea080090b890361750f42040061820142c204000340a040d4041d08250011042c2c1c0040960380000c6600301c155410741000d801d840e418043c6040100385084188640700e102881148100700c0f0108002c40684010030301c40341089a44c002c0c0c0c0c0c0c107121140d001800c9810b00d08081d035141c1e40d6030120b2651040c940784510541810407502e601200d2010350311402000a990140058800c200d980d004c800d0222511070300000d80110500d00104988412801034404401c40645901c4a40300c0d0380d03482000540c0303c40080308140f81c0d100700c144160b5600025041c05440718045281d5103e140b07440c0c440000382688001400c1000c500320104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 519565710 1250 519564460 519564497
    0x50a05100f0c060e0c210316060e03030406061d16140705160f080c090103020d02031c03023609041b06090306050c090a0314150109020408120a050a 65
    0x800b56000601002110300001c1c20903114500c01c6015840340700032281c01c0340042c0700c1d02020383d24011500001d514107480c1810014106550304401d940156840c682c40820300000e000442c8150712441002074400c0c240754040d0a245034040002c01550b101104104140305040d055800b601d035281410070961201c002548881d12a140b0010714a02604140320300000c8286180d4081d03d03520701c1f5104020340c4401c0000c0d914519403804940c4002c980004001505003038400c141d015001401f50380b404440d5000c0d00300b607401c10300e000100290340014080000a600e550aa03121036603011130481e00180307c02841d0014084440040c41003404a01050811402030440d0f0110540b0035801401281da4500140107140140310544400381804001000c522161b070850f1220304008000c0c8000a0643d122407610441d41c4101109603c1000410b201903401000424024044040d001d603030303282000b1095050807001d141c060b070b0201003440506000d5820200351404043c05183c072156803800f404040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 519566960 1250 519565710 519565727
    0x70507052103130510050c060105060703030e010e100606031a041112010603091e0b1801020903030f04030231020306041e050f0603070f06030b0a081c0306050a05100f 73
    0x381124440020000389200583c0f0b044003c0342c1d0211890740c414040d6003015956886011580c6086801100050055280450240c05401d0007840c00140d01d100c031098950848464103212000f5601c4444c0101c4040b800c0c0c041c00c0302605243c50107104e15240220146100c000b2020310074802c03610b0340d6065401400078800d403608840c94814000e81541d5504014008240c2d0b41c00c140c2d603040d62404c6c080c103460404c5846101595201900c1013440e962440124400340340e43d10700001c00d54080044881556040010780100d40103d58129940d41c5540304102c0131042544019074100455900d5401c036040c0c0c2c1d02141c501261001004d6506d55807440000d008120480c015107000703040d020307480c1003004640e00c12845507100c0800d00e0102e468010406685540e40d120780b2512906c1c810303082c010300c3c3c0f10b601301090756000a0101041c3d075440d004000e013440c4030b186c8040103901c0009104003025a050080070000c20080d07510310380781d9081402084014150510080600c4040b05010400920078103d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 519568210 1250 519566960 519567019
    0x906040f050c12090601031208041103011d06090706090510021c050711090f0604021806032802070507031e140c0a1d06040b1207030510060b07050705 66
    0x2004a442c1c0b00c039010480e030300052a0404070260f0b1a00060f0000000550a03040ea03800c403c0710449464090302c12240502e00030803c5440d000400392050080c0c500b401241003040801e24501d4070300d05007010f80f80c03400000520089036503212883c10415541c01c42801c01c15104240ca00340c44141c20086d040c0c2c54041c615000b0280d4403103111003a41502e40c8800500300b40c03482101c40403100003800c81081050b035000d540c00b030710b01504840414070b54940380d401400315076103c3e0130f01c48d038074418100094002c0d0411112811071550b010700e40240384c0755182140c00360f80f855030000c505105a54840701e03500d0f106804000c041951400e02403022190000b616503041d5440100f074008110031502c500d4031010340c0104180900c85200010030094040050000811941c0720b12404690341c03036081001600425085031340100e42e00b1600d03480e984092180d10003440c02040140b12201100510008803035082d44122003200e820b02c411030005002003031103800c80d84d040314160700408040a0381c44651910354034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 519569460 1250 519568210 519568241
    0x100c18181a4203072606042705030d06081f0906060803070c080606030d080f15101d060f1e0c0304060804020f0a0b040306020a0215070c050601150e090604 68
    0x110b000002d0104008510880f42991031302113508103414170300418000448840002440080010158109540a8081c00503890012411006c076082c014030380200301c00303082e00c10f030300002550080303d10380780188402001c0f000c00400030003200203074407211100440c41201ea07454448407440c0501440f82c00500141c500315058a43d960740c1440d040c80d0340710b0729115035000c90060b54000783e80d0703140c0440c5000c0503039110744450308555a410500000c24030020010030f25200081c0041056495841c50a140c1c01d115845074400e08010b069840b100103800515a88910300c20070005560080107810b40c1d10044001803000d07040c1d010902d81e031003503003e000a903490b00d11010400041d005d60049072280038500aa40c002a041400ba051002c420b0290140201c0c0740d40812003000092800ea005040d802614815a408214060307001c00320301d041614010009118a60194140a0240801401000034011a000f0b032194070001800e043c034003954141c1304080e41030015481f910b680c4c100d84800010140d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 519570710 1250 519569460 519569569
    0x804031214060a0609060c03030b060d02120117010203070e0f0f060c0a0c0503010203010b070b0a0908031503010c18050d21050a021204030302100c18181a 68
    0xa00000740c1d004540561041c020038100294950050003190300740c0d403907562034503d60790040c0c84c1903020f08804500190408003c20444440500c2071000d400090700790400c4885c03a5141c03404030b2070610201a0760495a034410000e0200013500b003880424240c0090315030b42c0d0440441d10020f000c481c40780c0c40d2243c100c6400598180d6a00d00452010480342c4a03030402602c1d240c58206140c00c0340005d000b84190410100078101c085040d04c040715500c00d61502c3c021035031541603910030301d580d0000d680702e00900a5140c1c151150749400e004108620001e0f2500c003007a1103100680541400062141c1070003084061500024003000b02c6503900115041e44031080c49030031080c2d00828650103031089000501a0f02245902100381c20119802c03a90158004c103075000000401c0390040c000e1005400601041c2c02007041c0030390125610750020f1001e1114040d00440e483c00001c10b403594612442003000c440103824110b6a940e0110340d1040300380d00005606281e80c0d8a81a00c900300d002190541040d180303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 519571960 1250 519570710 519570731
    0x60f030708010203161d0427060227090a0b0102010605060711010e0105031e150310062306070b0604180501091b0305031b1f09020a0e040c0608040312 66
    0x150020350180000717881d074085050381000d003102d0700080d031116200e210940c00400200c03480e064000400c40447d080900078942101c90b41800c3c4040c3c40c01c42145c2c0740c0d40101d541c3c0544c0350b018000c2c03850051003882a00d407100801d8001218800010001040c3c80c0d56005c00118591003588000f01030500078160542e00c014a0410340ea9110186140500061048030f4140c4076511503002d880c001e0603071161000d856035600b40006094200100680f200000f104a0a49aa0f8040200c07030120f40400704001171660500300c0002d070f0f680740c251241c80c02201705040704c0704545034039045500041d045003001d203a90b1109000200039001c1030301804040081c103210881404010b522410910f0720440a4244064503d0742450405030140300240640e001406500b2068900c02903241841c0e10000175103120120f02d000c2007403140e50f0180102c01051f0350300300140450411040e1039010b4002e8841c40c1d00c40d80b034595540d45a02c2640d000c0c103030401030b40401003401c05004071400d0300800003a94042c081c3c0100c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 519573210 1250 519571960 519571963
    0x50d0201031d2406010507020108180c0a2402030c21041a0406020c010806090114012304060305010b09091b040b1c0b040c02070506070c1d01061701081005060f030708 73
    0x40031424100c001c032083c049a4598007031400c45031001c0e41a110042c55648490039803403481d00e100080300136400352290401140d901d010095001e0010003100b01d89056501d011145c03100352000541080d5442000f5880c0402400500b01c2a00b040004000301c184510701c05c0d02e10304d40940e5201040e0300c4045802e415050103100040c1058400070760880d5000d000c00001150000f006407255500003000c00010b21002100c2d51302c648400c801810070700110b20a0001d88104580c58441e00480240081024400c4581c14001ea5004200c50b19401d4105640c3e0b03c0000c86080f005015050300511421b107150703142c01600140ca000307103888460b030394449041e2080ea108049100b80d001c054507181503005500c6192038030070224880d140b82e0003051040d04000038808030b5403041c1c0050f0f50380c12400500140f60210039804c041c29801e2400a22030a526205010700450003500005044000031360042c03152a40000f50351a5502e00400e01082940314100030030300e550a40c00505030103001c3c07048041841341c3d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 519574460 1250 519573210 519573253
    0xe0312041101080a06030f0209180a03080105030c010c020604090506030703081206011b0b011719060e0f071802090402070f110111032a010e0d020a1209050d0201031d 73
    0x2420703243e01d80c990f51105080c2040326560700000b000c980e03c1540c007001604001c05010351100f451066210091402c0054610740038611070b00300d001804040042c000f5060900c0001141c40b020700f4a009030000700d900103401401039016031402c156480c0000b801d0303550304100c1d000c02590400c818a80e50480b01c1c00c2c11110070b20480d00c0d5400700742800b08003e0000c6002018401c4580c12540300f0901e87d003001009066000d0b9413440d03101030311031860743c41d02c0740e00700400460140f84108000100200d001d884503060401c103c490040e00d40100e00200200d802c0c00000395200c004500005aa465031900014003d0240784000b0701031034052410310003000803844e20082c80d2182600c44020422007440c00c00c2e0b8a10885100c084081c1075020494010700103030f00d04540d25402c0c0c0c0300100b0340d01103c5014900d400120380c00c16005902c03400c10101441006013150680103441e01c4c0204481e410030700407800e40d40703c20400038105507644003101d86155a10007401d440440010644010890000d01c81d5410700b1f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 519575710 1250 519574460 519574493
    0x9010c0f0b0f06060304020d0312200405100e1c021809030a091e12060905010e0a030f05130510021e030a121a0d060204031a071206060e040e031204 65
    0x42c1d03850b01040651500405a9102d554020001c0c0e00d095030700c2d54115010410300d070201040c5920b038980f80140203c0c004034840d28141902100b03880e20315140030411202040066101480b2840c0c100342c0203074848025409041c5c0040740c1d07540c41e0714214400310365270381e1440c0803401e03c3c8100c4809002c0c03801c0022005142404059488440d03d5072500b000706e0710540b42c20504105004c154504106100c14951505641030250304000b80c2900e1544480c2d082d504040080300564002120705802c02d500301246071541c400703034607005051075403424400c49206014081c0b90f00c149401074540b21464400c0000c0c00002c03c1000005070710103080240741d03699400030b0041b840420050030294400f00e4851044241000c00101400354841c4030b04140703e4420300d00070041e01e00c0d50702084040042020840c0042c401700c1301110018043c0303880032000b02614441d20112100d942400e0080142e140c0c441201031401c0c4007128001400d6030010003003440d6115102c440190b02861104010501c25015410b94440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 519576960 1250 519575710 519575731
    0xd060f0b030c13120b0603240a0e0f0a0f02010f1b080711330f0912030c010c091a1306080703090c030f02090c0c060103031d03061f0501110c0609010c0f0b 68
    0x862003680c0000c03a00c0020104448084001c0d400117501c0c1340276400404070300d0007400030b42e41c007074280d10f002a00b000d030000000d03502065900400c40440d41d1002c1811400b50381441c00c400703d40c402001a00c041d42d922440070f0281180860300b0700600901d0410304001c04001801ca1704c0703000da0494480c1d0b5003800ca80098100540036040320910300c1001c82220074000122442030301e4144498200407034a07003a0070203078055220034000e100750f90009200301030f030f80c8a041d111040340500d88100303807442c88500b810b201c0d8130f50802e0081001440407100c114094a0030707418903511070342e2043d05c11030041400c50406030011038401c0001080c405245924000d49000b1f42c0c82081035999000318003502d111306014464507500003001000402d00c155040190748220460803004110f0540c0001e1808034187d502d1180251155a109841520010b507640245000e0030071000c951004e000d100d803110300c00c282c0b1a0080b18000f43e46034080c2c0c8103554601c401039105005d8400d19a160904000e00001120360b02c1c2d99 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 519578210 1250 519576960 519576973
    0xa060507030c0c06180507091a0d0302030304030c020613170105180601060c210e012c010509030c04230f1027050c0d060f0b030c13120b0603 62
    0x241482030007400c01c03001c2c403529240003a1589030b07078040050201c0c00192813000f58000040c0c0c001001484102c0003050508000f051400d03030445050035041011040901c00d8507044040e4002a4001c4140e030f40c401d8060030400c0407408a80040b0300144076074186480940188130010690841113000120340c022042e00030003040c1c0d552045510a0200440b22440c01c0d1300a60040055520130490361813840d100704404901e0707002414201c0c0e00149501055804150416000c031819684843c00ea060501003400c0004100d1258582d80742c040014a56031f810800001580c0c040354900304014003c45030060020044031000130418000c03e900c02c24800e01c400d61441c00700710000312415105010350802c14450380924581a0302900084a0b686002c4000c0c3d07055110a0300d04600e0301c1458458001c507040702d9a00d18405403d607040304c405803c4100e4803180100140702824000081c0d0303501918620b641541c601001d1000e00c1e4640c040d40c004001655140c070702c907041115421100e07000d124207030204e130003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 519579460 1250 519578210 519578221
    0x201060302031618140f0c0c07061e2f15010303080402120a03020606121c0e0102010e01050c0301050103020a050403050d090e06040e1506010c02090405060f1f050904230a0605 77
    0x262001203c03c840005e0300a408203403d4040c40c0d06860b00184420a40e502e0300a0341050f0700d0600a0035440b40780883c0866a2071003400102005118001e4203602c0c0109000f101e401200301e018405252900d40e101c921144042016010000250100c85c0303850501e1040d0b0b900d20300100300080c00c139000c90003003401c1c1c0f150211046000502d08451036140d00a441d19035945000e0240202e0460304110480c8201203c000011280806107890a62240d0b21130300c80c0180071001909488038504088040d038580010020745051800c16281521400d20f0050b9840c054a681281c10340103940000d0168054050304030302e915000000c20044440d0050915140d84d99001000b0450744116032411642c1c000541c60b03043d9079000e500143c2d00040504111208100035000b05035026001c0724200e815610180902902440c220481548041900100c861080c0004080c3d03d011009203c2e10340950302c90400f01d000c02c0303240d0410740d2030040750300c040302800880d512034199954844103040d9070051900001c80e6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 519580710 1250 519579460 519579509
    0x50a0902090f0d0302060109021606140a1109030a1205040f0816090c020d140f040603091401060f0306091a13060c090518040c120f0605060108010f0e0702010603020316 74
    0x20103d90150050b100a0307203000a480b01075407151991503040516034500e0000204144110741d82c40c52192003880d141c0c03620603036200071039402d40401044120706000c203190301c1c0e400240d001520b55000c05200d50b54003140405440e580204c0d000b01308014206080802c4041e80001d081d0660714000d18200003c0340d03154002000c48000c503000d0f1006070044500f085403107004000344804092040740643c54440b80204545080c1c00c00c3d0044400a43c0350200642070002d083c0065060410500081009624202e20301c0c44a411a2100802c80d5031201d01e801300307021f02121424640404101140083d2610966046d45145480822a0418507105544110311703c82c0c0d400406441e8040c200441c4a4030a00e0000c8054100130f104031a04900781e900030076a9560380072881d580511601a5045018083c82e104059580042203681044078400c010024008640000310496414000e18502600d034800128054141c0350006505480759034420013550a04581039021580300c0c01e50904030504203480e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 519581960 1250 519580710 519580729
    0x10302120a09020d0c06030207142407020f060f09150603060105060c0f01090b01261009030324150302210718080c090c0918070504050a0902090f 64
    0x240003584980016040340216031058054500080080034298581e82c0c400d80c640c2c925402040002e41c021408108001c04607440125203500341014104102d100c2200d010800d00d19012101c0004181010034a864003e0050102c0040c0660035101136192007420640445010360319410207100d40b031904401c811540740080d00031480140581826440e01d01085015000640541c22038001c0140e0070708013580034480c02070400d1045644100300e61424000011000f100300c0f2074001d13a800081c00c03044808000c1440104c80700c0c01403001800810506003100140250305030065510690803040d4040302c510304070340e01201c1580403510141150200100e0680c0035900c5540300b0720100104420905032080b100560200c018501400013001c1480303801d40e415001d0b8000350aa80020380c050629040c00851254000600c0a29500c1d2107400000701c5c9140d000c00030030403424058180815002841441110300521005003201007058445054a0003948107108640c4503c001030841e9100d4184410751 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 519583210 1250 519581960 519581977
    0x12160f0810060e1203040806070e0d050613060e06070c05061008030706110c100207021c0f0f11130b120a200607060f140601050423060d050f070806010302 68
    0x9089590345044010b40300500c001c20f059a000703015072006507200b2010006000104010401071034070341080d01d0003420000d0400300326401404004040004603c0000c0c0c82c0b42c00243d46140c50307001c07001d107051150042450010941c03540c0a04000c0c4100d00d607202c4c0c0b0345030b240380c0a0810f0320380d19182c400c0084060303041d40c410300c1426081404454080b03111a405101e0024450200c1741c50310740080401810554548100300b030040e400b081c074400350309103c1808103a11101d41890202031480d9151040c404850340700080504001c070b4450020010200017081c000b400280405a590407107500d0100904a0611458050018034040030242c4100241d080981078024410007000c90913030300e104c541000c016008a41180e001c0114200194041c480d210f0200c08090300016451104142c00c00310000150800381040000e101c10f2051102650b28900c007040000800783c40341000c80e0124010780501503812440c2d40c9490100000303040349400c0385100d41680d0b135811195680303880040d802c80c000c6580 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519584460 1250 519583210 519583231
    0x30105030a02130f060b041514030a023402030f19020603040f08071a06030d0914030109020901080312072a110d141b03060604020304020612160f08 65
    0x8018015080084420200301c800c1d010204140c50300150801c11740340c183d40f200404480028003004900c01600820410035401d160070020071456860303c00c00c0c2c0c0409040300200c80e0307001840030500707001c1003d004184080f1510740d101c01010584c000d030381009421703400d0b8064042d400044440340800f003150200600c12210131002e5030603a4003480010340000340100d030306204601c0c110010481940180903014454101064168134030011000649000307441603000f42e10107840d2184a07600484008180c174000000c1038002c0a0f40c0c0b0019000d4207142c0c40203500141c1960020500c0d100c040024015455000040700c0e003902d070400103c032445803000307050140400720307128800f010364942002880e03180500120309440c2203280004901d402c10304411214582101048105001c052018003618071000114040300d0705032001203a224640107101510556000000030215600c0740d042d944481440709a03541c251902202d00c0e1844038160f04500d002c100c03031174405420148030f118002d204d902c2012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 519585710 1250 519584460 519584473
    0xf0e011103160e0d0b160f03051e0a0b06030a0f0501050105120a0510090e060906070c02030318041d0102030a1a1309140109061b02011506050a02100e030306011403010503 75
    0xc084581c0f501d001546548109108510804130301542d400900800074100355811a5041c80000303024012602c1040e001c2c582814204800c40010001c80e02d801210341448501503529000400018034034844055403050000c01070003119803d80e8002d2284004102c8200802d90f210001500c844c003a00002d41d0a004401e00001e070b140169810003a00001d0100400440c6078941d0840c1040d5419040c0088075030703002c00300700807820f4420044d41d50090401c1c02c00f04101901d44d00420f407a480303401051071244003001e08102c3c5603283ca07808004901c4182074140c00c0c08400b0014a07010398415940043c05a0804054015602d800441ca50950700000c1c540030f600c4899080034130141495030001d0b00d07140521140301c8402c0304203000b95050385100324400140702c8490012500c1401d214000d500441e072400786200e400b000f5044804e020384505d0700b000c1c2d844d04001402240303000f5229900c00103007414010004103600700080030f9805004240c8906c004500707028811040d82c00240f00e1143e0550104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 519586960 1250 519585710 519585751
    0x14010b040b1e160203070b030105060d020927181902010e0109031e030201051308160507051305090118020f0f0d060501120510020301050a060e030307060f0e011103 72
    0x40c008008001210648032102c5070903861100d41c1e500721020004460612410760421440d080c00801c0141540d621114219418840481c031140108841a40860381c00a1840701581d00d00c800703041286001110100c1501c54407403220140001a50000b281c4171480d0440d41c0281004200404a903200d1030300d410008600da0011125410000d1034141400346450b408808034140900084a030254800c0c0800508054034000742110f0b0014083d00c80c18100d04141070002d890a000c4503d2070102140c0c02d2102420381c00c20034249401540510390100c1e04181c202170303801e81c0e034001e10310800d00200200b00c213078058100c3c41d18018a41d40e00941c081840b00599a00d403507e4401c410039185d000d0000603411880345c1e24101120000e8002d8500109242004410400c0420041c040d020510006600303551414002c1000d603013a80c011030003801107a0b210004c1a8800700141e035901a0045d505001e081300b090b13480f500401d900491405203500f0000c20f1104031240c5000c0343c0c014003040c161038420740c2c010b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 519588210 1250 519586960 519586979
    0x80402060702090a0b1e01090e0c0306090711160609080a0203100c03020405370b0901030f0207020d0f030e04140a090204020f0a210c080402010c020f04091514010b04 73
    0x140034100a40d90b17000044415143c1500400303141001300c01c52091010348400152070404254094005c404203842003000010b01c000c15030f90400400d403a8115580c481880070f076216810110700540741c2c441c000080507043c0f440c1101c0c00444001e038480c00d00b002c1e101c082c405d0705c0300044d50b13000e90154005402200880156403010411024a240060620741c8513000590b02901c488d05d440d05c80d20350b511246600e0380d01000c500c0b000d600d2007030201642615002c0d83e5403660240c4c8400c14181a031319090784126641e590112442181e000300f0313000b0041700c075241841420040340c0302900052078520308403005041030b100d01c00800c40f501c1c0200550b6170f903c52401c4050030094030200d801c1902405000e0100c9185000380000c40440c0c0c81d4001074500300505003010030004820f5030841410a0803c5408980001c400b680094080c41c00400754002c1e400490b0f00703403841c9448260000e2410242000340085107844501043c6154014000c4a05e001e00d20080d045003801412656503040001300001c00b072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 519589460 1250 519588210 519588229
    0x41103010510080a0e0a03030e16031713120f060b01021609090c030804030812060a03031205060109080304090b0f03070e0708100305010c1d09221b06020d0f080402060702 75
    0xa40c58081082c10261340041d042200030300c002c402007a207410090300c0344080ae20100b051f05050b920301184451440d2500301000d1220355a0f500f0303404000419401c00050a20040040c107000190780c0301300fa20901c0c0038802c15a109000341c4100c0d03c1c04100d0703240d13984081485004410226526058241440c007078500030702e05c0c2c00c02194400c0c5844400000994040007410007140110041500c802140320a40d2420303c006242901c03941078403c0030300020743c00600000801c1300010f03000a4036900d490050710307550f2070750701300c00c4080c80007240015124a146d00709041a44c4140d80181c07412901c08181561038045000f1843c40d10b581c5000604002c0c41500c80980c0100c01d007041103801952911902d0844040c403420000050120303418280b560100e9260241214042d1800c100d1843c00b1075000f0031034411a403410000101c00e00240b0305021440074030007883e02d103110351124143c0d0342c0e00d000ba590740b81e803901d03420100f50084549075895014280c1d07140300720f4002c1e0140d8540700b03099081081e03c12 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 519590710 1250 519589460 519589471
    0x71b0e15040902150a1b02130b01020109060e01150501030e06010b1e040e040b180d050c0304051807031b1b08041203090e100609051203160c0504110301051008 70
    0x640c1d03400c882d0007503600c0e08107032003400c00d0580050b07544074108000107014104000b44544030040d41a580030060b140c04003861400104102c000403041c125a0040303025048800300680324a0074200300b074010800641c07109940c0390703003e04204245079454006505441c0d04016840b4a50071448c010004082004002c20400c028031400460f60b00c110b051342400781d0841e4204074210003030340c0300300030400000f14051500300d2507042d40c0b801c500d1300d103140859459008210f80402c0020114101c1e051040400980b40680001420142c0d5000154070311203200300700300c2d09000020700b80342c040102201054140c9420404643c0c5844440126881580249800410485880e00c08110000341003a80c1c2c2a510f01d420302c207035030704141c241c0b404280c005000f9014000d42c503d001542c2080141c50741050740d05c070480d102902c02564099807100302034114092800010840a11000180f0400132a002030200342c50048030208000b80c2d03613551015040c0000d004040d0130000f0329100f00780b01030003410341c00c0e03001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 519591960 1250 519590710 519590719
    0xf0c020f0109030213020a020d1e110c030124050d0308040f030e060705010c14090a060804170301081c03091e0203012009180c030c0a020309090c071b0e15 68
    0x20b0b0341e076001c45c1d90342600c407000e480074560100310360301515414803050103541b40d10b1800410601c06a01c252084000c0c04450a041c40340d0102981c007012010300004d81400f02c010000c00c0144040040b1000f00007850460f0112003003103074000301c1c6520342010701c0e00c841505941c0300d56240c0d85d640d842c204400d581e41410f5017400100c0050102c1a0395000c01040190711038070010450400c40c603c007070140e0401c420f881162050a2007800030725201c899182003218041e00d46404070b919142401104000352882841805400000100c0e411100207003244405681c8a9022040f1408003001c42c00c0b00c40f07030040101120480c0f00c0231002081402c03070a800050004000043e5030700e200c1041014005800d6000c01d0703074030001c03c60026034607061070315000c1a04c0b01364900c40585814260740380c0621004058201c005008100e1000642c401c1060b6440313010f002d8992901418a00120080341d049010100c0f07920500d107011010043d1841314010460760040c0d4082c003640c075100c0c0ca5484080b2017140d4644c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 519593210 1250 519591960 519591977
    0x806070f02210d0f060302090a020a030e070617010b0712050a05091e0415030203070b13030b090a0605150a090e0f190c051c02100c050f06010e070f0c020f01 69
    0xc0c440d4107a00505030621420105694808201d5a1000d13203400c2c012002c05280740c482d00b040503895407501c00d58010701100006036070b580da00400750001d0420114004c018800c0a1011a000d174102c034414101d2219514004c1c1701382c3e610b04120035507101d4804010f007030514219860101c02d00400152110003064200700382002c01c04000300e6000703454120301c2d544242e0f020b040c044e400c1c18140b1501c2d00500d05024060b401c1d07070543d002f00b56154603a208102c8011800070320514a20b0b850400403015590040000c07015040c04480c40340c0e50351070050103941c504d07e4180400c4050203801c455080c1950b003c2d011446003490400d1000092940c620045503501907281d200120040070700400c034054071841116a01c3c0c1031541481100d1101903044680070721554134120b100c54200c0c0015801c00c81e2304907680c04903a0b110a0049801444001c8010081c0c8203004240346405404500d29059071080c0c0c0120781c03aa9640c8401b200c00d81e4a007080038010900700e803a82000f50400d59a2040c41d040181006440e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 519594460 1250 519593210 519593233
    0x40201202a0907090e180303040210210605040507030501032012030412151e05251214070905010804060b060703212711040e0d030b0603010806070f02 66
    0x380b10702c044079000d0026031184400c0c0a51381c61200f03466000280058010641c1c500074810310354911000e48041d102c0c582e009050040148030b0803641110b02441c8c1c1c1915585003080180741d015040302d000300d61180381800006441c6612070f11846048a40020403012025000d9802c60036420039601c005400c40d61000700d2501d0301c20704100410080030351020035800c040c0c807800c1080c1003280c94001541142d09000500e0b55650111104003050009490005015150424a403460b110303052090241a203103403485c0c1c10041c2d0801c903c00a2512214828052000381404000c0c22501c06c450140129507003400500c0310b544039240641d0b000f4801c1c14002260051080007601c10341040c1d000320001a07000000d0804400c1009c500c8400c0d1440364400d100b00e5840240c052400056800f0410701400c4581242091100291544a10090182003040200719017492280c80d100781c03e50000109061007074a880d5030600d00200c078102c1e1040e001500440c2c89002c030498520131031181070811403203045810329 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 519595710 1250 519594460 519594469
    0xe0105090a05120f09130f2d0e06070c0606081b13050c03040210170415060605030c22080303010f09060b0315040507021204090203040201202a 63
    0x103004a0a0500401c501c084034604945081908100d00781d6200307051100d13050500a51060300c0003800c0480740f10030038074110b01c1244001d00750214207a003943c2c03d0503030814407102d043c0d00346d500c1c107600d60701402c84085100c4884802e684421803220f499070b000318001045140304414040303034503210300c4010603119510b0030301a1410555950241d858403c1c0e16511125140200001182000c1000203004901d860400612140001440079000d01d03031010308440315920403005030441e005003440b00712003803e0600307110080d048540c64244089142440100c0e10300c1c00b810549100380301450003e031601401d160380c210000b100190344c108a0310340c690080b4921100b0302c05140600000800340c25a01c1c40c1c4029801075540c5907105051480041042c401040401201c001d0030000a44011034152590a81280391281c0b200e1210040c07000030a0100748407030507400950045000340e90382d41200214a042c10055070721a903456109610003012002052317a09001c0d242c24190000031084d0715410741c4040b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 519596960 1250 519595710 519595721
    0x20010227060d1b0206060a1203050a0324061b020a030f051c0503090105010e0c0304060e0313030c05030607080708151c0503030f070f050a080c0705070b030405071413020309010e01 79
    0x1003203891820780186480c039604015159100320121140c80340c0ea0308d09004891031000c803010250800038001084510103029412480c2c2c82c0002e40000c0c2c903210303000d5042d80c0824442d03006038000514195801c03188044d01000f8107168540013400c00d00200d14694a20f0096040000215801d001c0ea0410350001d182c00030543c0048061525001c1d680d00d0050659421075505800c01103052440c0c10620000701c40d00415280d01035403000c8009112210441e5061541c01412400c00e0703902c40c0035402100b00308201601c10115007040d030440d0403d40300d451040d00c0209003103c00400280c140740c0002c03203401d180c80040c03050130000351000148010703001202520650001c41512268000002d2100c84010302100c142d22036014684007804a0030140020864458080ea00040054400100d05442c5940c42120760b00ca0380270044501050396061a03509503001140e06441038020b550700000d0781d40518a5240c8504401060114907400003a207001c0250000b502c00c0c0fa2a640c0c1d0f505181003900c09101e00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 519598210 1250 519596960 519596981
    0xb040b070305240a0314062a0720120a05011506050712051e0309061509071d06040f0f060f0507030c0f14010b030d03110a230a20010227060d 62
    0x83c01c01e514141d09104449084100b511078440001c43c90302100c050200b040e0351000b85e0240040a4880002b9408500c0411441c01d455101064043c250542308000a94480072403003034000b4030030b0a84200d04c08040d82250720494022803401c10013200000c1e90030302085007107417140c140103080c400000e0842c0c040188841c400c00c0b060100105229906008002095114885100f03c441400f040701c00300f940502e003c2c00c150240501003021418040354504003020780c1c01c0c0948844e480703641d00c0ca11080b01136200e20440700321004040b0b0109066201e800142401041500c0700703898904556422500c0e1051107900b03442e007520240c080b90000c0c840e8032620482d41d1140340081681c018000c01c0500380320540416030245860046c3c002095001c00e01640c500c05c2c00c0b407c10710f480c0307102030350210540105025641c94031b900028120f6240344e0001d41251200410503500c2900100b00c4500c1e41c200d205065101407583d6500f40000c8a8112071070a071f0342c0004000e8005810a00160040c009480b0303041107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 519599460 1250 519598210 519598213
    0x70903030e0d1205030603010902150702190308120703020d09060f0c020309090408030915160e0105211510030b10090b0f07080f03040b040b070305240a0314 69
    0x100140356000d100903829490480d51000008a07654a0300c00d468080b150b0f207010f110000c1300003522a50290300c2041c070240c0103010800c00481c06100e4403017561054100728403904100641d00c024405003400c03681503d030301188552034582c01c0524110a00d0004003d141003540811010300980c8480c0030b2445a030b40b2900010450f010202034083c10b0b40c0846c0f440008640c42030016030361035a1121600d0f038100760800e154690325102c11002d5800c05121040c0301c110441318209001c007800d10501c00c000e0103000c82d5202900b41c44050b004403200e224410322450300e6441e030604043c911480030f100d26081503180780c2012518245402260842200c550700c0300110f03607200c001d00f42d03034140300d2480b080120051904c190258240307608100d00b4020700070352180d12000070030702404102000c82200c0329040c1c0c09990036241d2034a407a000d00c003c0412602241c06820f1003006c00c10f514003078000d042c003c0c00c1e49800742483c800c0070300b240300a8a2a01c124658400101100000860070f102d4800d08034850460 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 519600710 1250 519599460 519599477
    0x2150411041407090602010c050f0708090a0303120b0d030f112e0509031e0a0504120b0a0e01050403050301061b0f0b1807050a09050604020712030c35071707 69
    0x107030080c01441c0650300c20800d40e4109a07a42480389d07400402c5590720349120300b04030780321341540c2000700d1940100e541d295003001110030302005040d041000da403909000b4020501401121a0503c40896411003004000c600c4100e40c0b12500c60041d08812280400c200c111201199010f035814051094035251540e007521000310b13000d000b000e81c01566030204da0301000307501c2c4c8040401c1106585601010401c8080c2004c03444400c298403481c121001002c0030003a46840c4207131800e0912880ca81503c40c4080035182c515070550130030040c0a41d611a42d01350f1940c40c2540e19180d4150340b2004001c6001008000c032a0000340001c2c07010400c0341225000700342c01c0742ca40c071380703103a01e880030a202c89071014075540000c0d4104415500c1d43e45e134600b82c2c2c40f80c2001241d29280d500108029004040e03008040c4d000c0750100c50806940740d070082105804668403002001c280d40c0072800744007039030000b02c601380d0011f000c966034040b1000c42203138020070b0510300401d064540c00780c0070a11071020740303000c400500f480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 519601960 1250 519600710 519600721
    0x50103030e1201050103020913080c0109060f06060e010c06020d0b030f030307030b03030423120f0604050d050403020312070f081b070501050a02060a0f0e150604050f07021504110414 80
    0x15101e101030640c414000304130550450300004c9091100800611001c5c4003101034004000001d001c1c0d501c0000014000e000d048200c0c50030030f000d03282101d04100c15034600000081e8281c401d603200c801d411410b0312181540b50b03942d280e142c043d50103640f0030348040f51030f40c105100945041080c071251400c40406147c483c102000d0050a648110455501c00d81c41844180401c03d954040c41c280901c1581c0c0c2525244614030220f0511407040840394054014001c4450700c0c1d100202c0c10030320680c4540d0070354003005a0480141c600f40500e01010350164009406550450f40c030340e009001e078034000d00d41c045900c6002c0d80c6004240e401400c84860f00d02902c00c0b81648840d080001c0d2024010908050b41001c100d050029a10071009010b0381301542c560038409102c202030782c0140300044541042d0b1f0701524a048400703040c0c84082e00d6250140f407070308001640e195504010340d8002d65980d400781c25000000c5103a080300140240099802c500f078440c911490b5552840346c45c0205411026200152420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 519603210 1250 519601960 519601969
    0x703090503010e1c110a170a110d02120c030405090916300218010807061803030e1905090f0906070305090c0d0609080a0309020307060309020102150901020706050103030e 75
    0x1409008042031303000d08280c030716141030070815031180d450713902d0a904120702503e540d070f103043c040300b0014080e14404403003c2600c03080a402441d01a5181d11151500c403122405c2d0366903800207180403401604268030f0841c001e45801c00400707001c0c6802003240c0c103240e11000081c4c43d0403020748091842d940405100e910300901c07654500c0040c44840141c1c150a41610f0320702e0160513428051510703429140940d00f04566070040600c0400201d10204a125a140c03a00196100000d01030017021800d408001a0104c610102034410b07a64190f0718102e5128008051010440c0280c8041102d001e02070380100e12510f60300c4100384039291100e4040e000e030515482e524240440508503000705400c0508100f0782c2d06000503108001071003034910442d926040d0074000024201410001c102c071200088030703000f056243d004500a28000c03820754405036a602400da044a0307400724020701603004140640e03061049034401d154407911690016103031200d0b40e5a468111a826041280455641fa480000b141003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 519604316 1106 519603210 519603221
    0x2130504030f09052409010908120306100c021e13020301090b010e0a150302030406230403030615170c070b0f06010807032903010b06070309050301 65
    0x625240c014550400700c200b04001031419100803500d8034080105602c080d0b40440311091103000c0040074141ca421015000303041c0103410340000790000050080440c1c4032a402c0300a5901d251403010801d40200c460941010440c0c4c032510180183c4030200003198509069100000031560000041c810b0700f0b00841e03034402640040000900c0400740c4d00203035a03110091300c1e0700010034803070001e2204c200324505c03400092001c2130180948070b0303000f98000c5411070b02466000c00d89000c030b46200d04c09076203000c60084941101104200901d45d0501c10303031001d000c03080e050520901c0307a400010039491042a00451034800303c00480c0c48410b24801b21504664040440c46440c6414540c070300c4001c8044403140d001c00c040702d001030302c1c5500c20320542103450903050071103000e40031908031261150010640309402d0346d84d0303210143c00c540c1c0fa00040e00a0510950b1246c4544d42014181070079103c = true := by decide +kernel

theorem cover : BRFrame.Cov 519424460 519604316 := by
  have h0 := BRFrame.cov_init 519424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 519424460 ≤ n) (h2 : n < 519604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
