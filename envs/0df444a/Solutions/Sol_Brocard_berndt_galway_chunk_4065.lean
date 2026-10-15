-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:28:21.105913+00:00
-- url     : https://prove2.me/submissions/fe919a08-ea7d-4c97-9206-165846a9fb8c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 730935251 ≤ n < 731115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 730936501 1250 730935251 730935287
    0x6080102070b0c0f0d02090a030b09011416120209030a1202031213080a03050a232d2206091a16020a020f0604080a0f03021002131203140a 61
    0xc61025810402681d0204003900000c5240049040b45d4070041e40040c10003680045030660040005104800020320030002c40000140b155002040e00c2d40b520009844d41c01e80320b03052110005003d601c00e403841c42e1054009005a901c22041d03022038940700704841c1c043c048110240400011560120040c030600405440700c0e40300791901405001620300c1c6c06030080c5030100400c420040d0900940125a100000b1000044c0e12500800d00344e00c3c034030740c842c101c56502c07242d42c041054404040e00c0203980316624010811381c5460000361380e0301d41400a05048070300601c0030108081c401091041c03d205a030710503001c2c000003481d8681311140038452003c0803005450140007816a410075110a140704210382c1c000c1c2415001c9400b0700c104000c100301d095802c81000c03c40440c0c40541004000c00b014440c3c05140808082030500905003251403040080782401086601c041c14082d1650030181e40c24540440c100f900c251800b660346941134184c0200b8070b000818001c130300f1900601c0f103802c03406000f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 730937751 1250 730936501 730936523
    0x6050d0e0c09100e160e220203010f17030a0c140c030706050a1e0813141c1101021603050a02010f1401150c0503030703024e0709170304090608010207 66
    0xf134500321102c0d84480349400002c203a030741591582d1800c03a440c1c240e0510107246010282d41c1d030000d464142c0e27009811108440712608010400d001100306589000003c05025504151005000410300c0d255880c000d041070401d6607150360504024400006c00d80e00c000c04591801e60303140409403841c6c04c01c10801e4046804d0507403800141c0b200074250040703840d490b075803084a503030741408008112803400300030380e082d413800b80011074548010048844406080264081f000000c81d00090910740385180c1c81a503a401070141101c411198007800b0b601139858240203441d00f030400001c82c014100414a076148c6030070724128040882d001c010300303416503a20748280c0c0f05280c010002a01c1e52000c002c0d005020740c0c02080000c41c020b205c1d40c041e203603003000d4010100c01c10001c03044034400c88100d00322440884041c46040da00444440c480440c190400340250740d40d6141c502001b501241c2c1c2ca106400d13465071a4000040c200307100f442281d01410803403108002e003903248c00784c0c98001e4011080c02c48030305e1503070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 730939001 1250 730937751 730937761
    0x8040f0f080c1c11150708090703050712020f1c0807060b0310060302130c05030a1109060307030f1a010519110109050a0c06020f060a02070c030c03080c01110406050d0e0c09100e 78
    0x2c910341c80450300c8645c1032001da841d190800c07180000024400001801200000300c00107109000324001041c059810101c0c0012a004024220410130840c900c03402c06079103800004640300f80c10384803050b005515282c680e400c038100b84010b004500302191741030007050031080304426664000001d032030081d01c01004001e00c9005200c1240c01030003d00300800c00038000245111826046031036160b0000421506051980d03020034540c0d0019126440032a488990207030008507d84540640c508400125100c035510b841c001800c61301c15010701404504c0a004c2c8503030080d00422030140000c22090003045503680b64100b90f525112240d50032070b510480c078540001c5e05480022000880384151000d0805900c50486140c0254040401180c0b8000c0d4420004081294020343c44000d5009526540e0390301c039402c246c142100c000c0840071940f500103200900034a035104040c0c58088100007130000304c4d4a40e040701c0a03d09161350001c0c0d176200e10300c1010007141d001d40c004050120340d12555002256114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 730940251 1250 730939001 730939003
    0x251103010e0a0605040507051512070f05030105010e04060f08071d150607051507080910050c0306040905100504111008060f100e10021c08040f0f080c1c11 68
    0x11031186a0724039031000c0c08203000304145500041d042031049007150411a6030340c1c00704d0010b644005454070b0412010913075120488589010540c4881a46068000c00410420140007401b0602540d8100003125480c98440c0d1125400180604a00c0344c0b0805543d40d81d000c0c0c1d956a40721405074282100e0300d1362001040c0c4070b003441c403e4000c4682038075542c070001c000d03000c1c4011600600420f646502c01d01d949401403450311821103000d40100e07616030f021458040318062629004a802261691034030040107400910501030b40c0e0012421540070401c80d24500304240303449002111450004d151500b48010004000310485044c1d500361544400c00c1c07411801a603504a080705c615410a41441c94000c0f640b500c62280041581d950600c1c440c28000c4101042200400d02c44ca0b5003d0381c442103a40718a50081460341c50000004e01e0440c040f40342c981c1c0d0340540b104240c0ea006004080984402c003c2082e4001038510b01001d0800711408048109901c89c10f2241140400340030406400d403074402004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 730941501 1250 730940251 730940261
    0x1020106140307030605071e08011412150a02091314090a110409032604060e0d020a080d090b07090504060b03070e09041b08061501050c0703031425110301 68
    0x10000d0183c4400c034655103d6030040c2c10000c0c0420200310740141917101c0580034104907140c03158a65251103013903040c02001000111098034142c414a000c081c4143c00c10300006903110034507030368100e000654071035403448000390046d200750640c031006054280074010030951080b02100385003078809036161100804c1302c0c2c8a000941c40982a0003108089401d9820103402086c0228031915041c11080d03001d0119903484110f10940b424070748000ea050005010050155840c03501e0658043c0c480c01400c120081e41e10300c14000010840c2e1400b0a65090f003041a50283d9440c1d07401c00ca08451514208a0082603180da40c0134691189161400124500200e402500d00c0380401d40c84001b640340f522000c11020900040c0111030904014401d01d15145050768500024844000201002d0410382c07a075500c4001c00b14606410480240804916204009000790071207405050804203520207010717420302845600e07201401c0c1e01d046200018410100d44c49121014001e424019903001ca000415080e0741c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 730942751 1250 730941501 730941539
    0xc030e151c200a0912060506040b09060f0123040e01091406100806120304080a02090105031b0114090901121401060f15050903120a0206010e090607111906060501020106 74
    0x41846640d8840200000c001031040001c5402c1488a00d580d465241700054a00f08044500306d0b1601c0c01c1c443c1608060050704d4903900100c4280c8400d280810100c1c1c1440e0302c00a00c2410009014445001d4034074102c0f2410100740421856039545407a43c003403441c1c0400030310580300700c41d1803e02464103801c00c4400f01401607000402c0c0300201d42645400b201c10013400b070407140d4441c0d0500141c140b00d4a042004200030205c0c18080d040d010300e07c0c0100807084a05034885402500b1907201c905584e503101c0c480b04110502400c150383c1003160b4403402c4d49203006580c0e000ea00a042c3c18000700315524095000344405119140341000741d10400f45071400e950481c840d10300c00342402182805610015000398a02255500c0e100c0d0030501d000b00000d00e04030344622031031051903000803e503611503414021540901038141c0b00950b02e0030410001643c50f80d00520074420040c004001581d079100c28400020f402901607005c038407040c01030070050010050340c03003024095840c1c1040060441e0b13605005240e10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 730944001 1250 730942751 730942781
    0xd02121e07080a0b12010903020d0e0301060f0927030512150d24140906090d0e040f11360a050907020a0803040602030f15030a030c030e151c 62
    0x41c3e03c8401126001d4105210030503400380a480654455800c24421604600d000750300034048007142a002504805001d1003450107641029401d11038043d00e034601d0400c03a83c0140c00040c40300c5031503519030b00c2c040101c200d8640b50055034412400f4142c0c03183c003911070004c2c0d80100302303403d03168075040a088400c07000e50b583d0095000090540484c40c0b1080342c6025010121500c00c204518007074040846d01d10f1840304406248440a00032284020001c880d07022640600030104c01c5254030002c1c0c45030711400801c3d407080c0c0e2110321a40640b1800e400c41110000c0d49007200d9152306d65000d00d012143d00c00c0000260034420f0000e0f180346a41041020111080702234003400b0035070305160138001c031924003c02c00c0003980b1038520f0040c0058403260095105a014000050b140d040c250140702010002501c600350a0201c010000525540403440510055040c01e008864082d54601550b8054081c8203082c1d021080c01c00f1501c3d0104081c0090184810342c080111100c14420184400c03540d40201c0c15002d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 730945251 1250 730944001 730944017
    0x108070801031e030915050d15050d0b0c041502010f0515010c0308040c0f060909060803032517071205160f1209050d030e01150e06040c050d02121e07 66
    0x80040f018503042075000745070052100d0380312154504511030b4541417000144002510142c998024840c11140520744244070294506d0940000d10002000c0005845002c0120200e089040b07030a04803030051512041c481034641c1d00c45006802041d0700849001003a00703050004003001e4403c0004c142c031142c142c6a403111030116450490340084020030440c3c4100300b20f0002b0032140c98805040d40141065568901282d052180d100c0565602e03a014840760340c824018400e04400c4904101c001111701d500e0b0b401000c40c10035048403103807100710214207400b64072400d000700d0507403140301500900105001440039803504040802c2c40032030540710030000b512603102c08510398840c800046071000c12400c013040301500da40701d0a003030641864003500425611500045214028041d8070444101c00c4003800b0780a20300000041102001041144a80c0e903d100381640d050080c802da90034906c40300000c5440b562071240d920741990054a4103000c10703018130100d4003000300c903100340c0c1d01c1442582d80b9121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730946501 1250 730945251 730945283
    0x518010b030718090f140d0201111806130306020c0c01020a172218050708070c0615030b040b0403081308092403091f0c0207031203090b0c09010807080103 68
    0x21042c04030514124070b244c3c507801c40c4004a0112103071900c11a0094440c9141242c00d4445145040c030100941001c0d07904148111784c03014840410750f0484c41c030048855030504003420001d8000c0c424800e403140d660300012401302c01c3c020309078023808004e04600102d818250001e1f005a984824120004041c4004d044025101303048000244c9074001011198600100140c003000702504999042411000726000c010100c0d0032070760099503044032860500c12642d0504080050a00c0b81800010b0902500c030314044012140c10814440199001450301c1064205442d00d4900d0040c2900c0580000c0d0340c0c440410034060178404071540b142c3c2d000110600e050301c1001440741507000e81c1ca4491044060811150b801014140194402c0d01c2038030103044030a84014241003656400707600803079018601248040003d400050780015030350080c0c2d85910500e002c0c1000c8001e0070000c10000c10b68480c400c24411040e2071800a09510402600c400007c1d83d01c0810440d0015024070024118030182c102070300e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 730947751 1250 730946501 730946519
    0x302040b06090901410a0e010b030f0705040807080a110604120b0a02070206180a080309103e0d0c020d061a091e060405010305120c070e0a0518010b0307 67
    0x9040000182e072000c6810351044441030207541d2081000c5c04450380140c0114180c646400284058482c80c41c2079038a80d414258000d42c1800000d0100103005007040220705414007e1094130300078040c4008607103502e80c50b1401c0f00d0f11a8031444044504404001503c2120b01c5c001055605481840c4084408103100361684103107907001405000c841a400c2180402584030f440041000c0d401100703a0a45a420000c00c2c80722041541c4d2000e07407180c0082c400e02c000f55890010b0241d59404c1031908180189070015110000c01c0711940a0b140ba9020100309004040d050301d2502c10603000b0b000341d860a112140d410354144a21680081d882194050726a0008903140d0128101c0406115003040698030100414072100058541000b80f80d605801d82c0e10b000c01d1400401c2e81b0000542d000d0065501d541d907016a0386c205a410044410000f241030304500c1c10421072500141076010300007049082003070008008000603580c100300280300080200e0300d04814000e0054000c4090002c06a0740c0c5040c1d120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 730949001 1250 730947751 730947779
    0x1821070f121502120a06030b2406090a050d0c030b090303090a0308040302012c010b031c030e19061b030c1e03020417031b06101503020f0a03060302040b06090901 71
    0x402141d401d003c0c0c41310004000210030b1089a450382c0010740c2c203085042c15079071404002c0085668204200940107208414100e64483c410140d6040b03071505000c100243c01d64500703400c0503030440d1150008900b40550051032030220303805612070500d01e8030780c1c502498903403008031283c0c0c140b6449002c604001034402c00080341d00502901c000501d94081500d603080042d000244005001520723110500088400c0c4211301d0340400c1100201071110140e45600c0c40c1d08001441081031543d25018240d40751024840718458800610340d070025100c0ca4a401401400d03241c070041d298a440c60074005c141c070f0280c4034010444410b6203a495002498892003500c2c0350000c1e400c4010990240000982900e9140500c1c4840034800301554a6500302c500021000c265910502c0550744601c2c24007201c14000300b03201040c0d40c1094042c1c02e10300c0000c40242e000e48a2607540e00480c042c00182c41e4004c0354103502010680f44200c5051010885600400c20940583c00c0c90b076901c0040d11004010300c1d0619101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 730950251 1250 730949001 730949033
    0x1060f0206011a040b2b060317071e05060403030506060f03240a030c03050d03020724090b0106020d0e03032a0f06010b07030905040516051821070f12 66
    0x61502d000d0f103070061100c5e560041c400c9890042d08819070103e0a03002422801707444104000100580b503d1611450100780c0c02034000400c07400c0006100b014004144915002c000280015010552251a002e550360344100c6085c0d000a01c0d0001049513458070008844107a410507000d281903444000c0304216000010203030700d18800d40e5051610150710b9248048001394080e2004010703842c40d5040c0765040030b0701c8400c144105031041040304009008490307070340b0144200010030054012825031040040c80594009020a6101800000c0950740020b2144c03020142d07650b4100c800811074185680c0b800340d1000090201d00044c2c0b138030a000b054410b41d40c2c1265155045941144d58480000d003005000c0c1c0208107003180005000040c0350700402c03900028038050f9020485460050102400c00c0070044041c400c20200148001a1a407464203401d1a540010104007035401482c01058190450081003a004d0050341e50015000d1911441e1804642801655060a100716652200b03a0751083d15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 730951501 1250 730950251 730950299
    0x608190c11160608060d24020d0204030b010501030b01080f0601110316080a08090c0d0305310602010e030c0d0f05130f1d0601020d180b070807060501060f020601 71
    0x2910188a0410040c03501c54480004880b01c0341d0f41480c40050040c4001859140140c28403503032000012064111412003412890108100341102d038100c40283c41381828581c902c030b0001c9808030031b00003000c1d4468100c8100f40c83c104152510f441c0151074008080f20500301c2507141c180050b165500170780c2010540c0c400402660715008020320001c507810310440003034070070725408110300d03031000e030013045040d0442042d038000d0880703c042c1c0e0006608040f034801c00800300600402d400d00305420600d0a03c01c0c25500302030381e8138058030490b01101e00001c1485040015170a0600c0d986000c10040115015100030310090503900c01061000d691101034001901c0401c04204500c511084050600e10082e08407140d01d5219280b4000e030b68076540d0b0084028461460003502403140daa03030005052148803e050034540c540c0c40d51030300b044910162030b500404030f514000910000f000f0b045c50080030b540e841043c081000e40d8076010225903000c4a00b6034040581e00c2880184101c810322580884102c103a50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 730952751 1250 730951501 730951517
    0x30e1002210a020c150301180204080312060a050f0d0204050c09030a030e01020d140a1d06040e0a05010e06010503010303031e240b0a050706021b0619060608190c 71
    0x1103810038044600100701d400074404102c40c101e0690500c41880781d03040c2102c10341c512040c40303d00703907120b440306202d82ca0014260910b664280344040c2c05071002004003005884e240c00a004000e0b0301014122140c030b00c41c80c070505000c1103516140142c1c210300703000900303040061401503091100502000c0c000c3e401c40901800300180640d41004032603209071107552030fa40013101d4a030001e4a80801f54809005001c1581c0400740c020710b4000c151081c1540a02d080c40810141070300c01300001070503080c041c0d00400001030106000b010804098064003421000b08201c5e0303a60700c6040c04107001034038100d00081c4200300400109205e03402c0f0007400010703807081e40e080c02c1c0c884016034121007509d980c50103483c07489820342c0c4004007040c5a51008084820710b441c501b501d0648002c080344500c0703600400c150b41c049001956407046507a0844050081411540581008642d0310110000465402c0c151402c000d0042a60741c0325200ca58010030440308408000640300a041c2e0144c100320b403020082140c81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 730954001 1250 730952751 730952773
    0xd0902190305030705011802090f06010903060f060515071e17040914090a022b050706090510020102180114120c030709080a080a030e1e0c100309030e1002 68
    0x1900d1264011032003180159582c20607480c125003542c15926101031000c81115803440544c40c0d0140d0203601201d45120144e0991f1102d00680d189900c9410252400d03203000810026001c2aa00500aa0340c04840c84a10705420300e03a5050103202c2c400300101400315809040d4846020355a00740c291034032420b802070b00f0070411012555690401d038040480d03517882e591003108040b65000c02681100164001d00000038003600801d181c94164140a0100e801039848039865000c85c0c01a183c9490f4131100355049140d0341c0c05e000b003043c0d40c54085c075840782c000f07000d40300c003600e00500c201d420440f0050440b0f10f11542e81e000641f00c1200500000d807601008201c482c903400c000030003c030301c502ca54000f255200d040c80b940060403040e0b00d0700318030580d6100000c4500403e07003000c25074801801360b140114245000300499030400d8070304195440808034102e6070101d482d90204034914003540c2520443c60b52000f640c011810384000c800094003040c0c11074140141030428880f50564103440740111540400300c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 730955251 1250 730954001 730954039
    0x1a0712090b070f08100e0702100203040f110604061202030c0c01020d06090b0301140402041505030703030f030c052d0f0a030510060309230a08121015050d0902 70
    0x20500807200d85000a040050b4103401103445528042d0703600c1c000b1805e1030304694001c4180ea0340c0c002c003030030305c1543c0001440441c420071006440000100d4150740b139080034642a80c00707040745401210341c007203c0074408049041c00340945044464550700c070314180003c0c61852009600240080c4001d51041000941d41302e000d0004100403172208800181c16841d000700c6c4001c8401c0107000d0b070f200e82d05140302441d1184504e140160040d804480000d03030803046c1c1020380300d2010141d20240c4c1501075020b00009154004c1090103400d40b60340c5080c4140d4654401c11529481940d22070340210f1100c40c035096070f840c440110760b940c8040070428140340001c1440b410500f40c010045140c000b80c1c6807410000c0c5101d134070100200424842c02c0600c607030445070341c0d10300074440800e01810700c18001200c120941c0008102d100b0000381c002d80115030b64119071584081e4440100c0d2451002400e26000040e455600f5440c1011102a962010f00700000903c41c90007901c08800184e0780544d01c6480406140301c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 730956501 1250 730955251 730955261
    0x30e01050d061e061107030204150e13150603030f08040201120e0f070b030105060403020603090102090904080a1112030711010b10020718020711130f24050d1a0712 72
    0xa404805000c05040f0041015110890f400860400290707400c0c2c008a20800290001900e604440c042101b50a50081d1920b80780304e80c0c0302d0040b0a9205040c890281407080ea03002006c0d010325006141d180030325010388140c410320f100080002d001c448002241c0c900c2021150381062052420014030480c680e25181504c5920b01a864075401001c0c46200303410f4100030900040241b20155401c540c54003001034698092444080d0050100100046803004c0a40c1280c0c907516004009020504150504030250f80083e20480041035045c2d520400b248000105c004080012442c5145182e48040301201c1c030f068540c1c0144000d64984010b41c503260744900c208100d610280c1d00801045103010a040c00303000e4101d80780040948100801004613649120281c041d21050318180d0941d204610920300810304242c075680703040e190180c0d030b00001036143c900700c0070402d04a8814888030344074010443d1038240c2c907000070011107280b45042c2e4203100501e00940d0002440c00c110418184d140c1e100000d0751 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 730957751 1250 730956501 730956509
    0x1020c011a030c120c19150c021516031209020d0b061f02060103020d030e060a230f0d05130209090a061805030d0905070914190203070507030e01050d06 67
    0x16031020000700d080c01c000114080030111100152420b8180c080c68813079074a400524040e0030203920044448510000e00d02c0101b90244200c0c82240c200500180031b01e00c030480c00c0344184901d01020b04001000c105840413078a102e0310040003800540e80c156004082d048250400c1ca032903c590402590b1100c40c00b99515000e601c0c103907500c0c0b41c0001041140d541422041000d00b02405c1d280d00c41070340c006411815640e0584000104a09505080c0d9185005410340c6a000d80c001411450700c680c0100304540948050180070801144808150345900a0482c8800310420900001c542240f25420589c3c000c1500510307200b40b101c2c640c0100720a09011940b8151590100e6040002c006a40c881c0400b00211200100030019803070fa510b944030b1090845140c80e003900c8015102c2801000d101c80342c010b0038101ca08001212200c0400044100c4c1141e4110f00c045e05003101c008d41c4d100301c1c02103a220700c42c01d9803a05d142030219641990310968022001d81080024804250280441e1285401030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 730959001 1250 730957751 730957781
    0x1c090510030e0c100c030f20010c020106051e0d061b0507150506090402010305070311040801090213060b0316090317190c020603010611030d09030507020901091107110301020c01 78
    0x440000b101842c0080701040700d40600b018040301c01a0a03400400c01943c190f05280000004071111011101d40141c039402404440d005200444c0b901c00550041c41c101c5002e8000b800303160368a8040280d0308003039000040c0410b040301201d21413454001b42d5407510510400300010400d107104000b14190860b01d420034007080e80002c80e4020b1020100b4001d8030f840f052070007480b4520340708000c02c0316854090002818591120f0106000c68080d80000800300417404043d521145c1d43d521050180240381e1069000d2500d80e480b8224203d258029181559002003c1c035103140c40c1c02c3c440321054001d40c1d60390410061040b10100c0041d0400b007242030328000f40c0c00340e5a110039401e0607800d480c0e003480e41803c05000b01a0b50308001a1a00350507681114290b090480114451030019400c4d4441c8031124000c0500d0118500c04160b0040e01915000d4001d07200c100c0c1c0740e030f03c0d03108440845060081c90a004a030034094440042c5a070724404000110180015080c4035a40c03601a0940f0529010080a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 730960251 1250 730959001 730959011
    0xc01180504023006090a02040303020c01050307050c0604150606020c0a0302010c031701180b01020606030d12060b03040602040e010f081b010c06090c0509070203120f0601050912010c0e121c09051003 87
    0x1246801c03a8580d406c0080180c0840c5420b01d903940c0650380304244403026060000100001c1d0300035000d20103036600c02102105a510903d000e10b00ba010440d0103540e036034803251401c500490098400101c00b5101c03200030703011082c8c481c00c6400644100411400480030404845074501080f14404d410301d000700301d00806440801500074983d01030310800e4203d00d0440d80500b040120710355000a1940d1904840d08103120407034068181827010300990f4101c803a00300000418041001215401403040f210382480c1c003a10750b43c84070a05407101c4d05070b101f8941c017648001b90511503643c000c4c0e25001082c0050424490342941340c3d40e880c01f9035a54903c180c070848040d00e020440e50411403002c9503c60700c2c41c030181d4544421040c00060a030005803440e01c52030a007200141059010300100c07600c00a0042c814031200110419035400707001a41c1c600c1c1c2c0020800340e600480e03800d00402100755a41d0320b41c00742951110749800d2607051142c0d0a0f8140810010090009564881b0301e21542e0500341945c011039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 730961501 1250 730960251 730960261
    0x90302010f2c03100204030506060909010b011202180a1206060906180504060f0222061403040813090606120b060705070312050903030a09080c011805040230 69
    0x9400e060510301444951428482103404056110802c5400500c4008541190b0340220345000f9401c280442d072548000380220600400140d8107108a10440b45054541e861505490036658440d51407400700784a51008400c2c80329640184c03400c91a101a6181d50b2020540010703c2482c0341d03400102c070b240c1103001d0a4284602c82c001e01019040118ac10b00105181c08010041c03e0084000941c44680d41c1c0d012508200a5400104c1401d060034025500c0d96411542681240500514030031950f46100c80000e81c14002c19410310005c030050612804c0d96515252611164412400044214180701002c00e150203948a80006801141e84d1014250f050151000450f00c03104405813064000340314810000f40f000330890156a0710071000040c521150109440390b0185088281e0b040c01b001c00c2204209902280d28801c4a042800306e0300d841480c0c000668118100340186000c40220030001d01c85410281c00900c415903000952200e440c035400c400c81c04c81c40d042103e11160310101c0003841 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 730962751 1250 730961501 730961507
    0x61201170a1a010e0f06091501020f06041112010902030d050711031c170411060702130203160905060a0e04110c0f010b03070f120b1009090309030b0a0b180a0603080a09030201 77
    0x6602010b02c0101c5130742406c004000800880000740107203c400c01e185244d0015900c02e00c8480c410b81c03252012200141014074201d1900991016414041c008980720700c40307050014066400c016401401070409070861220441d0140d006e5107050700e110748041040040c40d01c1c104070b0b1403410181c15411070000b14030074100400d4800e43c1858840380d100d0000600c40810030484038040504412201b4a03550801440481c4490011642e0030b10950f01c040100144104000400c85040401c2e5640000e9151220308009981c080e5114080008088508416060403d6030040d004200911407290078610040da40030f1801d203042424440c541d441c0c01d005c06103420100540070182c04000071801145080c03000007600c9032490600a04408140b60108001d2141070602a02401c0f00390700030322144529042c05041900741d407008455051441b00029240c00291241d0200000010458800000345800421940030080d204c2c00b8a10f40c1c0e00d000000007003d2100400c41110181c442c074415074550700000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 730964001 1250 730962751 730962779
    0x405010b03072106060f0f06090902030f060907030609020f120f011a16060e0a1a01051e0301020918010608010f030b010e040c0801051e06061201170a1a01 68
    0x189000b0340c48803a041c0302c40c0000050211100e6404480d00c506a00700b420004041c007141e42c44050030800041020a00b000101c1030041a100c8946a43e40300541d0f0715030b41c43c100d100443d100706a00030307401c011800c54544540c0d410340110f00c528010400c40d855201d414101d90110000380101e81d8006941d82504645208855000e00983d100791071662400c403106807040c0086040020040d0002140c8074003031a0038101548103174002104001034882c400400342e842440000995000341600c00d0105d40201901600781a40c3c0060904610480309500308000000100d242c158555000e01444850751102d2081924042081d500019294586880544a040181c125904a141529040c4003060500b00303007030704482c400d80b54440f80d9500d0b403c05104150041d0040d0075207500309010b0007690148554b8502c00004c030790400c134109446590810005101d6804045043c250241c0100615020700d450007014402c000140c1e08441e1040ea00d504c000c1c0b40d00f40d1010f400480000040c030a050f02c5500c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 730965251 1250 730964001 730964021
    0xe0f0406080a0209040c0e0115030b1e12070b0c0313062627030c010606090e0f0c0c0d03050f070e220e010e06040203010e12070b040f020d0b040501 65
    0x104005003410004020b44604107040080c0c001c0321044003180800200020740802030403104454000c6503110b013540306101d14081c20010010f81004610a21480c045101c0c072004168081801070001051050000144170145991824014881e0001b0000d903500010f02009982c00c0203195075040d410101440c41030030f5005101044080c9582c0c0d0740581541c001170400e0481550380024907500c040d445d041035090a8640382074050140c840080c01940000a0881c0402280003801695156401210b02801d40d01c1107600c005240808100c0400001d80c80c1a00010301c0c4804030f2500000101c0c5910381240f20342e02d080000d54502c100a00960746000003600700080d032800c00603c202001c00101600e080c08000d0343c01d000c0c0c0c803440c0040b00146a0050354a280f0420080c8807450121011a842c0e4030211800e0b800f03542803980e1002100e40c04201c0e500040029602141442c009440d46000784800034402c440039103110741c8170703405656800c10583e0482c0c45040803940350f02d03042c6022401d58244800b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 730966501 1250 730965251 730965259
    0x30f0f0c250e0402120f01060f0b07170a0327020102011a030312150a0303030504110901230103020f030405030a090f0b0a050f041208041a040608040f11040c0e0f 71
    0x303141010303100c0500100440b03411000389111030310395000141e82181d03043c6201e5000c0c40341001000004e8011340180307040b600c107500020481750351084ca0180c1449116001400c20b41040c0c40b140494040c50050b006e503083c540760005001c00308200900041030b450741011042c000c0344a04100f15a824003c84003d4154040700c2c0849180d003a000c01d07507902601c81c1031282010201c0004080d88050700c1307660b050340b1000f4846c002160741c0703040c080c000342000c3d00c05036551210751009108030700700702c00c2640c12256102070300c1e82c00f114000d0002d80305d40a80c0305414100740c0c007040071001d09040740015501450280c405180c3d102000040505281c403150b2008580c03083d0840708001440c0781d40b041e1070729002d59050295641d1452140c4800501c40d07900a04410300f16608004c09200092001c0e0056400710110082003001181e103091003030003140308100009411100040024945005100c0d03903070303c076103140e40c54041c400000078151014600c805c1e002540c180303440030b0b00c0d01e000d00070030000310340544e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 730967751 1250 730966501 730966543
    0xc1c1e120509060405102705130506013005190c0207031106070c170c090a020c190203010f110c0111070503121306050406020a0314060d0212030f0f0c 66
    0x408101d282c0901d02c01c184c459220f032000e001b00c4601800307001c1c0032a2190307070700c0741100100280c0d00050080940901d80c0607041a11942c4c1c0b581e0814440c0341d006886c140c440203000c0b00381c0503000c081100b124030000070007401c0307045800600d1f61078040c283c0a14a9024080074820483d22000211207400c444201158003000f02080880d0034084040240802925540e6807840c4506008501d00321a60003503c842c84400301c0b060040b00c01240e0300e08141e10441d4042103030346a501601c026806818825070322504012001d201d885160510380780440c0c400790000c00d544031880d08060444022005000203c4000101000009400e2081034001050310b5041802d140c015101c4d5036070b13401014440c00071640100041001c1d0000c440312504e0180c1d120f0001e10891074580761080c040c0d0030801c0300c1307000f2030300b000c0405030004080851180300c1c600240840b070040030307070790200a00a2541001c18240f40402c201d81c12450103481c000f0030000a2100c00c0b1039079260080c02183c40c2c107000d1030701c44030740f08401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 730969001 1250 730967751 730967767
    0x301031e0b0a0b0607020307090b092a1606050403030c0801060f1409120708031c06031a07030b18011509061d0103020d020406110106080303090c1c1e1205 68
    0x21204890b000700c81c4120000e007090400010030841c1c89240000b940c94892500c002580c10703116000100f1104040c2d88034000c03602c1d5003d045070140242540d44000b0310781101c16843c1008000046c10a003800000d03440754525994a40703608a840a8406600003034a5100901c1e045402142c2d10b270051a06150551418010300401450f031b00581b40324010340c41c0300082100c446d41e14820f841c0300c00c408940980c0e40481c1d0b00c402587e940d900124040c0500c80135241c07007004c00d06d81480761030704a81e000b240b007280c1d036181440891071003540100034105059642e139142c0115110012600401800c1084681c940e504143c0769841c22400003040400b0480c3c198400c0c41926403280d0144042c070031540d00c0d40c000320081c40041e0080d001d012014000144085000500c190b4060050400d20900d4002004a19210405251244005c440100291344207410a00c26414080c003c100310100d91311351002680c0b000d83e2400201c3d8203160101110440c56428201401403210000740500314038144a4540095 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 730970251 1250 730969001 730969013
    0x50d03200901030e122106040b0915010c150b01030e0c010c0f060e15220206040506070203030c0706050a08010e01030b012d08070911040308090616050a080301031e 72
    0x81c5404035030405803034100c20b18a280c000c0005120002d20440c20580710004a20646242c0e54a01d2001c02e407007034640003180c1e00c0c0c1450b128828140c0005002e6000b15a183d0a252200145072440c950410415500780c80c081600c101d810f03401881500380c04980030710150001003daa440d800c40418a420100e140d140b580e070045000b0ba001c652107011200341201a042442c02401c80d0301e0054840e0080d034041103234182d580c072403007441865108407030805a6144000003440b2551803100a4100343c0c101300c24400e91926801a240031032000b0f040341c0c42e00c041c00c0315590078170301c0c940d105c0350204030003003020b24280350440e1285000d00080c091301115580741d9120106a01c80601c9403201040c80c9142420f2405e0001c4007483e9442d10441c1d100005540d110005642ca0000c0d119018032540342078005000c0d1072601040360226078200010b507040c11482c8080102070f40c45001c44482012001d42d9600010300c0c1030241e01c5005000307104540c0c580d8518282510072186140140903141c400026440004d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 730971501 1250 730970251 730970257
    0xf090f0b030105010e010c08030906040210020a0506010b1c1418030a1b110d030905030f191b0302130209150307020d030c020c06040e0405011b050a0c08040e04050d0320 74
    0x20007440c103418425503003001642c840c503a1f0390b8080c0c000c0c0c1000080002e164000180980a94803d03180d69288644000040761140c84040e4000c0258216200401584800300050449880010440189642a10a004100e03407101c910380841d24020003c0180c00000304000d151810340700e001651503d006814010010762101c00c0020104c180c50501c541800705c491042900b003100079010024400e440e04018021006900c40c485c4680b29104800d40c074820041030b042103c3ea4001e8036030018005581e2500c0b0300d0500d40010141000c6003841c0003015035144003900600711101c480c0144d4443ca000140700294407483d861001543c810014810920b40c0040c4420440046140000700d042140c40d080f4202036030070724142d511585c0440c004c60301046100e1080d000e94490700082081c2e080103081c0044451765089a0400704409118000d007080c09295a842268030800c91103203007640b50100700c921180c3c02c0d0ba080da92580084109001d42d9058820280341e00a410500c1041495828811650348 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 730972751 1250 730971501 730971509
    0x11202130504061b0804060c03020c0a02060c0f1203090f01020307090605031b0d0e06130c030201050d060f09140603160b0a030e011103040c0b0c070e060d02040c0f090f0b0301 77
    0x280e81d841c009018080b0b240d1003050203042c8070300040b03269010040d0040400100350f03000d4a07020318002106014038024402c40d82c0e4542a00041c1080460540811807241c0008100c1c404500881c0d00c103410003013040c040110b0106440c0301c100e841e4140001540d1525440305811034a5a104005105c009a045244034007140c10728a81165260b5540328000702c01910340030828690324007c00d00c810a1003064010101d0007108200321049542c45030100d4001054142010708407251410f0140055403242c001043c0e83e030080f5001203010b680d100c0c015001c1000c0341e400b04c9102d95403007944025015140d403a45800c00c0c0c0450007030800482e248442511840c01e40309500c03c90100003100e800c1140203070842c2005c140a40020002100a03071503074130165100b2141240d400000110100e011805a019a007445180da001404514144480f80760300c00306c0585110751044540c000040180d80b98000c0f0b0301c2c036503c81e40d924000300100100c0a09962050f40004400a240780ca040c00b98021308400c1e03c0c111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 730974001 1250 730972751 730972789
    0x1e060303021e0c0d06020712082413050403090e040c06093c05033007050a0b18101406040603030e06030a0204050a090501141c0b06010212180405011202 67
    0x44401450245e000b40b10b441c0004084544215021080641044445120740c00c10030065145902c00502c403c040810070380300c41c0e401152000300e0500186540d10059104e40300f130401100d8140c03183c600080104080300d085031400ca4031042400100d80c07121070800241a0500800380024019184881d0040c010240d1100c0800740d61035a260301c0303007101001000380405020740b162400c5400103904460140600b400300a140346400080840420701280c80c1c40350001c0280400d10340a548500d4450405000c94030ba03a13221030360703030f4000e5501071003500202c403104440098030380c8504003075001141000f8000c602c10f45c5041410400319400601814440c601100c04c81c2c0d9991303030b000c0024024062500030580141850300041600300300e980c0304a0599507040c0e07007880718144000810020141c40060a111320952036000d000003180442007540000050060701d200708210030200b5030307503003007011241c1d503a4a04400f03da83c1400d00d1301c1618003410315424041c1000c5419000305d058401c82d250781c50340c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 730975251 1250 730974001 730974019
    0xf040902011b080d1e11040806010b0d150603090c06030e0304030602071716030908030405210c090c041a0f1c0e0a1203140f0612011e060303021e0c 65
    0xb00f00a420455184204000042020041c505004c2c181e501c602011070690501d042210504034003680e00390350031144804020109a801c0c8441d4440070b4001c41d08480300c803501c0d40031105001c9c118506130b401400d5141d800042c19086410509000056a800038040c50720b00040f9a0304903801004841c01e59400c00c0000d61b8406603031a01c09a01c0d580c2c503444005480001ca0640f400701220441c0c0b46107a400b0f50303908504c1315165100117880f8032540c81140e6001141600040e505010780048401000c2c02c0401c3d521103280304c0300407916119003150203002202c4000f0f01440100070000f1090b072045102c12025084c1841d020451b9840d100c0c010140c2000c600d40351840d4907603045504001e981c0250748040c0c03031a1284502e403a54001c03519291900c042070034284003000d89a0007000c03da100701d01040001d4501c2e03e0315800e1105841d0322982e038900740e549403481d80c0c501101f090a043c804c00b1040c46c000511519609000b82400401b03000c90081c4d041c0c20344000840c02d0001107a0200003001c8801105c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 730976501 1250 730975251 730975253
    0x80619030c0611160605090a0f150e0d050a0c1d1306150f0801050727090b0f0d08070303112107112a040b01020a0f0303090b04050703020f040902011b 66
    0x120f41141341001c1c0709421814a80440d03a603500c140a05440d41098909940f410384030320201c0407161060080b42c81c03222240081c02070807442004040c0070000c01510490b05452181c0b01c0c1c9007000560380040d10b0000340300d01c0c10040b1481c942c00410034020309801c941c025003050382d407001c08003003151400740125440b42041034102c0340c1c580091009100d480201811282c0c1c448920b070103014102c0e8a0302c0400c90080c0c07051901980202984a803218034406915160305240c10746c0c00405105a005810005c9441040c80540307504030010b4207203004081c8182c071518146401003d543d5072000c000700350f01c0c0a1000d00503004a001140552642c0c00b444422156181407040b500c02c1040000540a41301d880d00000103019600c03080680007400c0700d807507011905201d091005985003551101d0040c0d00c10134210000c241d00038040c0d03001c7c42c807918010074100442d880380c10b0a17003419903007a2000e80080604000b1407800b03c00061406200f03135002e200d01c2c1c107940c002078040500c101000300006007140c0404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 730977751 1250 730976501 730976503
    0x3050f1605030d2f0d08090c090103030516050c0409050307051902130b13020a030c0f08010605071713060f02060106140d051302030d030605010908010515010f030f0c080619030c0611 80
    0x2840c1c00040c58221012080c005000502801c42540c1a547da4094130f0f0f49841030303060840b003050580390503440380c81c074040c40502040c0c825000d50405651a00900f540e13414140c4e1b441c000e2510351350107900110b03203c0304075080c0941030a0100a03040c000170400c0400600503200c000201c460001c1c12140007031a0380030340001c1688500c140c4140b0151510008020544a825902240c0d40018690302c20401c1e0070208002e40e48040e00703024190102d0401e010440007e502981b10a041490280e209420718440300000d04092505170025808a0351044505510350b604000190040c4101e14108050011100c01041c9a101e6a040078141c02e4075000043c040d440c154241d104403d90103800c6502c2c0410810000303004040ea03004140c0010000f4000249001c81400b402c0c2c0a0070b68000c8842907541448010b560403a544034035403040c1a180d084100c01100c030340c0301e4001e02e0074181d116070038640b4080003000f44501c80180701540d1241620014004a100c1221003030503500d0034148072002045a8181e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 730979001 1250 730977751 730977827
    0x9140120100c11011401061202091f0302031803031014180f090d050306031504021801060909061e05060f070b0103050c120706020607050304020a03050f1605030d 71
    0x616420500c101d040103074454a0fa4500001e41002001510181035070f44010900c00c3c425480040c0700c40500d503008841a900a0101b100020000ca0036642c000c00e448018440145140300425804010010192801000160308c0c03801c43d00a5895490a04603180d010b070300341e009580014008400c0341015444550301007603880e140251118140c40c1c5640021044c590803030310302c050b50203696561280c0c00d026209503402814001d029005150400640c048104001002641c2c00b28222510319514140c044113207000e00241c1d55480322190412080000356400c0364810090b101c1c0c20007400c215100f00b48040750907101c04941c4155104080d505c49801070240700d00c0501040144000042006800a921954400b080da480608a20300a0780661500d1561003144056041000007a10140c850f44c02580d2091009060040b2981c0343c4d00d0301c0e898044000c01040c86070344004603240c007a20000d041a00103080890041060070000040240702c280d4441180406414140480d11040384100207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 730980251 1250 730979001 730979023
    0x302030f1806030a1a0604140f21030703080f06010519020c04150f09020f03010e22050a02032a01030b0a0e040803010e100302090f06010c2109140120 66
    0x2e203407241880d03150500240810140c1d000c5040c44c42200c00030505040050354201c40d840200d03001702c2d000e0541804550b4064000807507100c6602010755004074924076030440a1880003001310b85404652070068544000a401e010380d18998100300144d5a900c40c04a0f010002070706140204003500200903440d00c00c6c4035041a600505015031480840d804040903021111841d00f01840550f4483c4004c00300c1c4078000c525200000100300500c403010703951403680e03004640f40e144a0030041040c0c0000002403480f06003110641c000500e8501503180c04c001280c15040350800150004030b0086010440462058449040c9910382408d40c03c0d03a40c48a9444008108207100c0004c0ca140034a81551a98001d0040c044120100c001080c0c2c4054500c0051081d40d601810034080750300c0303003021483c00c841c0043c0210704004102042200007142503003c0ba440c590045103050f01084040d1010b00704d05076940041c249900045005240d40e0780c800c0150200c040a0012030540c0d40308044103e0401c1181c0752 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 730981501 1250 730980251 730980259
    0x161a0c07030b0c0706060b09060a0c0f020415090b010f08070315030f06020316030e03040506091f0906030c0813110d0b01082112190605041404110306040302030f18 72
    0x100300500f0010b01002000d10510490007001040d4951400c1089030003001e14580d0002418004102014002c0c0c49540a0300c1c0a0000c1e000d94100c61740c00201a9a1450304c030304004081d0758801c0084500c940102140b910090801c0621091485001030075110024000350801d5110700000c512080c3d160300e5800a5904200350340604066030a020020f0740c01a180b41d8104000340640203807940c07203441000310085103600950f00d41880c0c0720801c511078001c0380c001e03540040c041d506074106032410b80b0b1850740090340340c80396040d55290010290858001c0400c64081c080ba48003040800488818403200c0280e00840451441030450040f400981c0907030801046640a2000400e1002303000a6203c040780d009040703600384445544040082c0d0182c407400d0264070340020041030103049401c0701842d000e5601d000001c0d030981c0c1c07000040d0070389509642d503143e0340b4600740610003030080d00c000700e40c10b030300f4150000e000504065400075600e115680940e5001c81000c1a00703941580c5c80305000302003c4c4020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 730982751 1250 730981501 730981523
    0x1c0213030501180203071d0a0b0a05060a121805060c031b030a060510050a021b0312040b0d0b060f0f0d0b0916020d02010c0f120b09010b0705161a0c0703 67
    0x1402035000100f40c0c1030241c0c0300e03105000c000034000007003100f250b5000c211011a403c030790b26a01c0e500f80280c100700c1c6645d135003d07044180105003516200e010700424545569808152a2140161012680340d103500c4000d00d18600305135000700e41c0000740e00b43c0201311005125501da8502ca98901101070f94004194111000001d220700e200c0d640d080361095640441c3c4000c02d0324030500e41919107104003600c09002da00084410410324001c010384041070503001d030070f07039600c500c6c1c6894000c2c583c0d00a8000700c00b13125000c114507025103240e00c1050540d10098480e00d203030001400240702d060107041015601c182c2c000440c40843d9041d82c000092103003001d40100c0060030603107010451100d6002d00200144205c09034100068814011104808403544076030002100c8400d048400d48455031104441c02e850700320701c20441d21001c130568000d0481040f0f41e82c8400c5249081410101c3c4280106040000440c040c0010b4800403100001c84860078001690341280080040c2020010f501c0545159050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 730984001 1250 730982751 730982771
    0xf2102031e07021503010e0925090b030f030a050a0914010c0f1e0c091a0a1401050f040806040221030f0c16080f0d09030f24020406030c030507051c0213030501 70
    0x100c2c9007e0f0089034880180c070f8100f100005800302415017040d107486e07801000700c41000094120703030145540c00d0010f0306440105c1112480a4656070151034040002500003a81c501d40950001c04100501007214045956411581c0020010b050005000d004a503540c42008100060000c06d0000c540c030309580c0e41502c01103810200301c1c200b024801c0f401c1c600c0c10405074842c69400c60002215030038005003c4188181003149103070894507001c3c000c40c140901040307141c01646d5807901800060028000501a03458144140008090320b1a030603000c180c10b2440c001201c480c003005031f07480150844510f544480104440b07a18008100600c00407040d404103020405e110017240c200c881c502140308480e81c5001d403800442c0c035040b10b031002418403031030886910f002801c4951100000c000d40c601410b07204003901200300032644283c2c01003000c00d5507980c0818407650140141031b4451614141142016011866019000359090107101703d20740c00141411081d0f008171504000d150800001c1001c100340b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 730985251 1250 730984001 730984019
    0xa0306060c2112091208070305060d120e03160302010e0a0e060402181c0c0503070303120b030c120f06010f12110301240e010806090312070c0f2102031e0702150301 72
    0x4118440e00000c5801b400508054085d00601d802510060401c0340780c0c0303c5d0342c4c69154041445075208004c10410a40f1501c45a5042000003800b07011170a448140d0b920f10700c009416030700c9010015024106540d402c02c940500703100102d912a00a580141e919400c402165580c41d4041c140d0316130000640c3c04902e200034615024100c031070f00c5645421410394444003011b40e40c1c442480000c00040b10031801004d0744140350003a0205540140c21145200c1c0058000746800032104441160f80d4400b40c1021004201082598010001944031281d80d074148249003034492010303503014100c0c40070144c402036151004d41c41415549142410012806a14002484036090758882d005000b50302c0c000100744230380081102401030b80b0550040d03260400c0440e14090101c4014407490910072404800d0f00480c40c01d41c41c4050845c842c081c04800f12404003244d01164240c89080000c6600a005400c40c5e0704010714441c65000100c10040d407940c0390340c0700203051800304581c50b0850440200c000612411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 730986501 1250 730985251 730985273
    0x3190308090c03010b0f01050d110304050d08070921031719111201051c050709051e010509060118210b0901021c050c1b030a0306060c211209 62
    0x5140030355080e01c202030105820399042800907036200c1c6c02d45082003120360080c0014540c0c3c03c20400c0c08614611604c00100158104540c2500d42e90010103844e801c0503800314100b6030002c460f09041aa40341030400c200310f09441240d4a246004000c0300c0340c024103025401c01c0004a480300052145403612030310050b0740842d4035014000c0142450310f03459180c0c60010503604c85640704090710036603030719180801c24a8000d600c444041802100e030b86402040c41402201c01070180200d0224080c01c0c040d442110102015031040c035007456040061040b60388500c0e80c5e41d000002440d01c44e000000c0105410060980307540203500540d084680e06c925a01120440500301d800781c001d4041d103039555640d16090707100d0a1a07400014410090743d0120003a550b000c240c000040b1442107003000e001047c0e003801da5542c130b10580d4591303201003101c038280b95060041c0e002625440c5000c6011181c1d44d1f8581c00c1407a04804408620303060041c46040c0d081c811500c00718401c900302000e000a030703a2781c142101404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 730987751 1250 730986501 730986511
    0x302070f091109010c0c0305060a02091c0c06120216050a03030e060708012702120105040614011d030c10090608100303020a0b07090f03050705090f07080a090203190308 74
    0x1050000d00054400000c2c414545251116440186001d80036401141d00b1401d02204403441c140700c0310040040340c42040140e21520074181e00590b144149400c01480c00c8500091404286084d10300000050360601e498007100d20b1070400160310400b1807148801703801003405450748050505403010a02c02c0c000f4000003080c2c040e403010000002041c0480f51680ea017103a8140110301d055004005520310f0901d8501040e940d044ca25aa2a1103510040144c1c3c1c0880e0521804080d10801484103140521a81d40108003d80c0030314500d913801400a4100030f68801e5034596040036010700c0b122601d00303110380e0000744001402650000509a0b010740030101c1c50140c107000412043c00500d00c09a20b00244003580d405800900c0601e555903150007031100010440e80800116180002d4081e02000001005d94031030006030424034108010311101c2c60008103409041001e02c4140141d0740c0d0000c0d00c41d50010380714000800c80c440c4c18000b19140004035000f0b81c1251000d509400181903100c01400c1c01a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 730989001 1250 730987751 730987769
    0x62e0302160b06100801030b070503270c0406050f150903030f031e01050d0308040f050705150705060610090e072606030f070e0118110f07050639070b04030207 70
    0x1403280034805c07180c03000240801000304e400725001c1940c280c052400b450780403184084101c0c0d815a40044004003000345c2c0f00003c00c981c040a040c030400e2a20b40950809070a040d0340a1103003500c1c401c00140c0b07000d8410200c00940d24002076140d5180c0741030080755000b0601d448400e5403414810401602110000700d1100300f645668004591441c200200f030b4a21501541c401489480c1e640394480600c03040c0344100c0d0280f0a142001a16860720f032059040000d08074240c64a502e11410030b05d007800401000d0501c1203081c80243d411f8507400080e941c0c1952171030451350742150f4460300207840700c1c0c006100d03c01e00b5040d01110054618801c0d81180e00ca48000d0b82540c41025810000d1359960b01c440c01b43c0e100e444410030040c0b0204070903005da1441390740300e00c03000b2401c0c2c107000d800c18a103030340400602a5001d80010b04441880000c000c03081d004900009a80d581e00c9906000c4410260740c07a15040111011204845040ca08401551603141d00120029a50f00740f514019680b41001d00c00d00b070702 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 730990251 1250 730989001 730989019
    0x80d050f071d060703031a04050414121309021b0124050f0d0303020307170a1a0901030507060513090f0c0305070201020c031b1507020312062e0302160b06 68
    0x928800d410780c15000c00a000c050030301380c1c59a010b4001d446083e101560b024591000d021b0799588600500d80a03d000c0e20032500d4441c0605c500c07500f0508095413420320003a08125004000000c43c14840031a82500e00c01600d0320102c0b041d10300754262130a5080615802c0042c020b40c0420010710705000000c5003000c202105a841c0107108040b040c1101d401d5100300320044100109000750011988018586001e1000d01441042c0141c01e4105488072b901c41d55581404580100004085204662088559803c250b1442c0e641640d2410140544810081c012034040820b041030071024018140b11001404001d040c480020020050300c9a03520009043c203022501241c010301c200c5000c3c03492200614503100c1c040124000c085440c020381c01d11031203030140d20719081307102c42c0b1850f02442140d4050b694403844c0c0820741d5441000030700400d1290203505110111030400d9224083c0042c803800c40d061010484e00810b50003401460b10ba0500d60346816100310400a000004621900d4100c0720191 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 730991501 1250 730990251 730990277
    0x14132415050f03060f0a1d0a14010905060c071b03031101110915070503040518010f0e16030509100c09050102151b180301090f030e0102010c050f07080d050f07 70
    0x18108000b000ca883e05a0414400b04009400b1301060940c00200500041640c4007003421680e440e10013400c0400f4031f0780150341611f00b0410154224040d001d0114020f100d49561070b217600e40c5500e00a00b0f00e20904070000382070030401041011803828040000b2003000e03131036507904019001c3c1142c20000d0401354608070301080780b00c500c50182e980524018100081d0768229009002d0694840304060340c4600c818400000c2e0390f941e145c4403840550408001c03070210751400d40340c040b0003400c81d040710003120f6411003082504134100049200040c0c55240108042c0c8483e01023305081c80004588095030034001e807401002d40000042c821108213a007151020390f103112414425100c142d44640c00206c0d4a9100d56003542c16602a007203c1c0e01c03000c1082507815600000030300b1200c04e0402101c443c0d40300d514100602d80c01c0803000c10601400c0c0020b104c41c11030b05400400354400d420040e421440c1c0440e20078140f10a00d07050f50034820080e0420801801d1082c2150310580040341c1e850006168156454 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 730992751 1250 730991501 730991509
    0x50c010f021c050a120c0806040f02070803040602041d0c250b04080c0d020616032c07050405070e010f14040e0109050f0c0a09091802030303040606031202011413241505 74
    0x41b00750f810701eaa6400042c0c030381004000180c10501c0390b00304200d809010440108440c1001540642e100c4c0000695a03442d00000941200038803080b004504145404c014000041c03608581440441c082c905800c50056003100180c0c1e82c8440d4081d11134100ba5040008200c136000041103e41c90b044115412600b0707007402240c2d01c80d4211852000285215540c0000c140280c101d13007241940400d00812414401c0d0040d9441e60b81a00440800d5114130010000c1c2d041910560390841041e00d4400884850280081d00a2544264000c104807402d010341c551040c001c0c05440c0984041250028203594820350716001d13040544560000c03801d002d01083c6022211400c840a54885d45c85000c415403410800d4002802c1c5294469101e02002d000300005a80600c000c42c8140c0c0b00718400100542141480c80c507c01e01d400245041da0300d44404172081d0440f68050560180086040302c111050398604924841c91a21203400c10325020100d8004203180da8021080d01081c0709000b504080c1e45500304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 730994001 1250 730992751 730992761
    0x6010e0a0f1211090a09030305060f010e131d0a0b01060918020c0717031c05010803091e0a330905060c070503030a03020d0e0703050c010f021c050a12 66
    0x6036020103000c0d5002c21060b0411078060034954003d070140302400c3c0c184008500c101404440101e081c0f603441490b4410182c141c82040e801000640700c10070004820000a851181e124900706c0c420700c0048900c1c81018126004107100318910001c044507545800b0302d49660791000300c412601d1076500c000101c0d0651089501d102210010a0032200740252660a1f0009500648034580540900031021802d0032071101d440c42c0e010700d01c2000355034440c80920082080c45000400044440c01c1c0b00c0104150080017054903050369040350486d074100d504022880d0001c0350a1505030304140b0011000407a044041140c10030356190704e5081c449a1042441c01041a04518860012452041c014440c5042c400b01501060419404070750034651900006031454025405c1000000e80020f603100d0242400c0c0900401061044001d250f91400c580e40c007a22103c041c96403034100700c1c43c94a8110558420001c0c24694210781300f0000c42d0482010b40100035134032035402c48000c249171445a11285850b8480c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 730995251 1250 730994001 730994009
    0x1e0c05091509041103070b040914010609090b0d0c150206070c020a090903050702040614010216081b011b03030501090b030307020d11012309030708031207080a1e0506010e0a 76
    0x9450120241c000b000b10b51000640166098211300c900d090240d20100000d40250151005c0a9244c605d0a80b07104160343d40d1100c0c48403030608403001080031a4000840200f603d00d805c0010032010040c2c40032a88480811102510340840e544000412140b0304d0201c8010612583c02d45010b81d40390401501c4003640c6400094002501140401002c0c2c001d510005296109140c090300c0c11765260005401d032036058010011510007440088199030301007010b0201d5100020658200c2850002080d84030b8441c00c2c04050103040050241050307030b03c650384c1010500d2400c24441000d81c01402c000b4001c003002d00402443c2c510b0200151168070b03000042d60800303a40201061540300b01030342c50f03804528410700e810781407240110b11841407192071030213868a44410794040c0d80740d008c0c900815151285036844490103030410820b0180300041071807966480651418074508640781c040510b00100020000e014001240c00d075a48a4084141c010600030f0009903144851a100d003410490aa011445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 730996501 1250 730995251 730995271
    0x60605190b0f130e0405010e06012702030705070219080c0402030f07030903020c0a08061e0c25150c030f06050109050f0a170601030b07050a0914030106031e0c0509 72
    0x344218000c4002c020012001a10940c040316661001203088401d010b64080310709075150b50603508000c83c204030709401008100c01040040440d80380071014520180041c002300c0303800000103244075015808854215038081d107402402405021200d6022135640a841ca04c1c0c051a121030220f407038507000340c82c01030140f58261142ca48030301c401a0005c1004400440a5000d1520044003990710403291030001c00c2c80c0c0b005006d0714600700d03c1c08900455501c0f44802103100704414480e0081c9614243c555031002543c01d14505d002850b07a940c0250111034000b4000c3c3d2008002c1d000c80e40349500401c10ad20920f40307081c44066100c0ba82c190a960140c000c00d40000c0d44048208414504090789003112000170b4501c428498441100b10519143c07070508103200c0e440500104104a490390110780c1c044140d181503401c00d400150001d140100c3d40c8a103200c9070440b044500310380d65082d803004000f5580049000c0c801c03086d03a0420924209060000c0e1880185280002807d08002d40c1980c40703401685 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 730997751 1250 730996501 730996507
    0x2d041a0c131410030b03010b15090a05120c1e130c0e03120d091b060903021017070f1808010b0a0e01030503031807090c0503160e10110c0607060605190b 67
    0xf2800c0b001880c407640c8482c0d241d0340b901440c66080d140c100501840d0030701981101d40d074580b11030034040c2c5010b10740e00c5913000d45210b0722000200785020a00040f0b01504489401e1200c08078020307038840c074140020150f4009606182401c01c550306030b01001e181689134031024a68541c40b02050b40750010b4501c4500024003c100034030582c0116840741481c40e100703214014845060b10143d26105d04181c102c0400304004407002d10941c43c1810790f484840907079142414114040d8108102144800f91508051022001c11442c85034001d0441d081d80e44003001248460701e55410702d5501a00301210780354000c080080010481070340e11515241aa90071400443c60354a0f241c0380e503030031820f41580c10400e0f0f01900c003001c1b5007050319000d40301146049585070f07512410141200041052203d054806001050b50341102d1902e030b059a110700040c4504010402c001d0302120107041c0504210010350020001a041781001041c3d4040415610184c0795400d000500c038403070010790b903a24042c0880b101014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 730999001 1250 730997751 730997779
    0x30303051003080f0c070e0417070819021b03070f1401030e030a0206010e01090c120504020604090908030406050c030903190201060f030f02092d041a0c1314 69
    0x280c00607038100904201c20340d0850b41c2d0303880b807600d144c01c420680d5560040c0010807100d101e00c00c00c14180a001e0102000d4081e09081d95a0800f0030800000020540303400704201040c81494000e5400e60140800d003c41780b480c134454020f490b426000b5101e01820901c3d0490919802e000880d00240e804429103049150304295441e002c8200c4505060304054507041c903201c21500c1400030303203100051500200495410a60041d4042d80141c1282428174642450072520350b0384000502c0315110b0000000850b40c44a0010031001d00c00c0f5000503a08a0505004504100340800210f02c070f00d0107000100031580740c21b82c039008644415a080b9020b40d00902c100628903061000094002d01180000503100d90307248100d1840b03014503030050790030315143e01280c01542461103907968080d1f942c41d0102110a0b500302c008941d20000045034600c070712600c00080030070194400d560001c000c230807444201440c16250034401d55200001c00200016001d000054041c180c1c00391000301c0d440288060130400304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 731000251 1250 730999001 730999007
    0x7050405090705030a0c0905070c02012c0306010602101d1c090e07030902011e050a051b030c0a1203092102420402090402060a111203010f060e0a0303 66
    0x15003850164050080d00145984e000c10590160510866141810340d14084100e401c560703008200c24240001c90300d001c00141c1e4400495001d81d510020307488440c100c2c0300d4030011030100000110780c01d44075050000c29030301c1e0001030500721a030403e03a060092045080c400c0c100d64250415154090740130b064807070081010141480b18895841ca804040e0595800c01d141c62940140d90400c0401e0b0f40304203800c19940e1148000844140c140726800b1b600e555400700401c03d00c514001c5400304000440d0031440a003910718410100072820007100c4c1c4800e142404a1780f120350400303044500c0fa40c5a81001c00090181c061088015044081845e1082000c800d0200c802e602401d002d08500400c42d1114001c0e10014002c41c0c0400445ca505c004103000c170b64030410554120b92031176000b503c40c90400005a69035084139601c139505490090301e0320b00181e4280d403243c040300e100c8800d900414510480086481e405541240c880d80c0c020081c0b580c0e03494003920517a0700080c403c0d03000f12401078180301282c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 731001501 1250 731000251 731000261
    0x270806060f0d0b040317060402030f16051e1b06040302030706020f0403050a0b180c090a0b1f080402041b05030403231b0f160315020717030f18070504 66
    0x14010303290105442c00e90b07a6000b200c1d10b08450031000315094990001407001460320482d800041941e007185141090350341c014921400510300c100844401e4001405035100f0410f45404400100255101440c001052801908520982c00d54807a919208907050403001450034007458050700998a13004141d16000065071110000c1c00c03014604020010005108102c0340c000304d802034002040c1400c2440b0942c03614001502c55401c00c0c0d005003205491603981c0c6584c00d800c0f0000c0c0400084102c0e0200c00307d240789185a001d01c1e1510061050344181c83d0708400000e2007144200e07010401103240454501070040d601c030401c00060002c0c000200000d000d5101c1d074030504d048448820f0001c81c02c0d210503410b9400304040c0240001450450740302c07070300104440da44910741e08010f415075020300c043c044d4050080784070160140c85802c1d020003250145d58111740709250041c45203c01d039170040601044941c030689945920380715940005203007081e402050b1501181550242441c980f03003004000143c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 731002751 1250 731001501 731001529
    0x1090c03060c231b0d021f14090601080d0c0b040807020d0210120f0608031e1c0b0f041a04020c0304050d1101091a040303120e07030327080606 63
    0x40241802c1c840401128003595858400aa08950390844005006003926001c5044030060f17001c01e2007007000b160086107695520344620080c11500c044c00c41c0309030251400d011401ca100c00140144036011001160890684034400e0844800720b507004011940000006e40c080c1401009401040014801030002c00c03000d8001041d00c0202c28003600050340303440c14044098082480010403480400040c014002c1600700040304105851801964603105d03c507075560f9403a00c0c00c111200c18030b507086c1502941e88050740714091040c0d040143c4910001000e05c440711038415142d0241c1c042241c50300c0e001d903400044541c001d0900102ca05007d12000c1d40140300540100d0106001c00300322a110491905083d50180b1081262000ca000001d0705030481c54200c10801d41c800c800c1586200100d00c1102c003102d81c90301e000520f011500f4030300b10042245c800124440d00606c180001411b0740080303603030100c0e800c1e40c240054803d12020074030b0300004948a59040354010200003090740c0b501198015150b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 731004001 1250 731002751 731002757
    0x6100f1e05120a050109060e04020a1e0f0608010f150903030e03070308160c0f03030503063a03110f100906020f0f130509071b0503040504151701090c03060c 69
    0x204a444071542005501150201c201513503079001000011105c0c055503004090000c00d81400d03042540200324003812034040d42e484280d40640c0c00d6943da0603035042c0b40003400701c101c5000c4416105c000090060000784918107489000d40d01c0840c00814101021000c0d076010340b50844d900d441c56a0070380b140b84003c6001079041c042c2290000c0400d000c103006040000c0d008200004441007458000c041c21029005030080c28010b040134000079410400f2250880f0044400010060708501e0030045a2608070264180c01c100d411400e00d103200b90a101e0312094440e4440e990001ca00c1444c1d682d81c1c0c0303004002180b240e88920725240c000c10903940016541802150301500d804c42c50050300049a00104a0700c0c160040042c03941c100340750720308a59010341400ca525034400e00304500020440e21200250b068204911804c5100b0807404104a400802002d0000e0210f40c40400104141d80ea40c3c0c0724a40300411030b040d1004400320306204080700198001150351419040d521164000e20151170040c0038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 731005251 1250 731004001 731004007
    0x60e040203090d12110a02010f06060903030912081b030702280e0406060b0f0a18030803060603090709111806030103230a021c150b0307090e03070609060506100f1e05 73
    0x2258031282d0060141b400b5540011403040d0144110508491080e4804c208000000c0700c14400682d0200803c001c6440f4440340c0420703440d030f5040c502641e00c103a00c03481e001c0750901ca500003100f070f402001400003107000711140f13002007018189000d81031218203ca070f405802a41c00a210002078041000d4025006203c0010115120300342d01d120703070b40b280a0000e01100c01103642001e6951001c0141d08654042c02c66000e8907185a4070385855000113481c13188900380100c001041940c040000e24010081948203002a0a4145950000b40e2091070701030078180c110f00401410382030100407241200e070b001445000d002c09107290300c034242c41c4818290b6180e0040307210318005603032100201100500d410300c150000314064906182072106007080889114213168419029940200c1d01c0011100511004116105c1441c006419071090020040c07030a46012a070303605004842d4040c0b4484e21013510342c90300300c121120080c1c800d58641421940000c19420342400c0300443d1003100050961282041c1e42 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 731006501 1250 731005251 731005271
    0x3020d060803040510140a0c031107180c020703050d0c020a080f060708180c12010209121501050102122d070b06090a021c05100803070c060e040203090d12 68
    0x151103080d4031945140d44046420710040c517104051100480440c10890411500710740da4440d107006207030102c0d061156592540c41494080c03079401000c0c00c51b280655407056144c0d10745400d68414113440c03c82c0146842209c5054600004112060700d070031034002c012601901c08112805554180200c2c0c00814a40c00040e80b03240030018000411001d0001d000e8601e0108801054580010400810000b66803030341d0540042c081035250f600389003503034206041684183d80c140680b08648901307401c413184885040c040d80300442e100e003900300a01d284290320707641c3c1d50049a651110b034052100c01c4100700300202441403103806c9952f2000c0c0c2001c0d0f846a124200401d031f0317120f401850059843c00c410030700f000748a1403d0000d03a9400150043c0850804202451011010382c2180c102e03d880c5503076101040140840380d04203001400d02c2401c4960300d040a10300b02d520f4100030700c00c000124480e0060000c4502d420b009481c41428540010700c0064170102d01114001b00c2d000012844a40c0c82213034103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 731007751 1250 731006501 731006527
    0x1707050703051b090606070f21020a0506010605040b0d050a060b0a051308030c07180905120a0318021e0103140115020f1615092103080f060f100302 65
    0x800442c0a034000d00b4080181c94403c3c0480140f04030000d2080c0035031001c101207681ca2a051f80c102c00c0c0c1000400380e542c1b8551404081440c41d1200c2045601c40102c06250002d9000850146e02d900c070300155402a41c1ea00340940e11070186000c0d440ca0444107000c0038030b43c0f42480d80000c0c0d001070034200c0440c1b040d80c0c0303058640c40f0b07900040308840040c0d00003414410f00d6482132801d500810140c401146408401c0e1903281d10b0301401c2c010300c4030b2001c170b10b8100e00c20f40c01e040d0810561150408255080c0d0031080000c1c1540703900c840c59000c042810040d241c0060f02c000354074184950f0b000b50021810780b541d48403801103500080c603401d05150f0385241d1003500c1c15440c10441e028003c0895422050203014002914008010391605184e90100008400c8548000c00352012a1a422008021210740850582e8904616044001e00c0300d0205007110840c511035440c0000c0306c3c025250b0b115140c644584526080000f1245190043c01480d40d4400b01d042003000900e419a592400604101828040c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 731009001 1250 731007751 731007763
    0x7030c08041220060a0c0203211312050a1401020d1a010909110405010e060f0d020d06050d050a030807050d1a040b06030403080c0325020d020d05090607170705 70
    0x1286148181200410800c00115101204400c415200e601543c00e0400012101c3c403514049504100d000c6c8211000c40d2410030004c9c0d9042c011840e01c0ea07810750b1b03c900f52541a0002170b005003c6403070703079503000462902c914079101145070000007a02c03d605081c2c80c0e2014501d54242e617500bc0f590b08002c54629005148103080e1070744038a2040c2000c1d942c82e500010004142500004e41c1240703030601092a0200c03180807502250380070309000440758040d00000348030b405608010500803000040608402e031080d40104840c2c640148100940c58490081c0300380d038061101c0040031503206000c4013003c20b000703020a0f41c4c8500c940c64003d20304850508440c09581442c0a02a0740c81c03d02013070111180342034000e0380d008c00f009448080c11441c2c0358400606610010b0024113910500101241c10f00880c10100001405d00c259021162a50030714000d603580070200b034030b01c0140100c2d41b0342c02219100e042100d403401030081c01603051150b03985a06255920340c861071b1003a06420000d40c00006d0080c051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 731010251 1250 731009001 731009009
    0xc0c01090f02010809030f0d05040206040e16031a01050a12022a070504180b09100207030804050601050102010e03250c0305071403240411121f0c050301050607030c0804 74
    0x10460104600c0050981c4c3c2014040710715942050104607030b03080c19807094038000c0207000000700c0e00f5146c1e400403810b94400c1c0c0e00003610503120070041040e0f0b480382c0400c03645841c03d40d40d001c000c851243d844d81061503580c090858000ada0400c00113940901c1640c0c465800407036940300502d00320300e40c3d03440e48049401d900c0303401d40304c101d1003a81e80c0d41c51801d01400d401402c0039076061083c80a075041e5090b92400c1c0706d0303000300288a41400305d55004420070100c0044405014110b68904103828040c2010038110f408440340d210300d80c0081025407041c06880d1506007003070700030760074403034a00352400ea0483c0400d040c10404201108030000316003000310140046001d08050091103091196400740c4210348002d0724042d0f880a2250380d02098051020703189000c107251a08490b440e18500f0304071005200400c02d034001e4a070010040c070700d0380104d406540200101c020030030000d4401c0701c0a0560f0f10601556003c118140010022800e02e5002028603501ca46800030410303075030303070b448042507005900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 731011501 1250 731010251 731010263
    0x150e0703060303020c04020c33010f0e240f0d080f040f06051303060207020d02030a0827150310030501020a0f110604050a060b0f03060c090102010b010f170c0c0109 72
    0x2001490f80512840031485d50a0354258900b400c0e50381d10540c2c54103030306064550500c5090282e401710f0102602c503001c00c040c1d84e05184983d65688051b04a00ca614000c00d560240350001203809203852018220009500d45840b604180f007020030401480e40007403455810007803400d0b800001135080002050a010080380290319030703007498611400e1070a541c00030b00511004000041c0c00d50309002107041201c1c1d010101603550056880807030203030070f00e00b04002c0d014400c9540030010030955070047e00c44440885a241098403e5021401d014901091403903007001c0f05a001c9201c51040c2801141d11003103c001c007416860340c03903503800d00f203901142880700026000921100c03007940c0020144180144800204007508142d1902e82e1100384445000701026038400c51160a5110541500d0090788010252652031600704180c007042e9002540440c015468500403d6081d802009254580a200c1e80e8002c0741c04150340340c200341020060080350b00080140010000e03540300340600036010b40700d42 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 731012751 1250 731011501 731011511
    0x3080d2d0b280303110a0305030c0904020f1c0f180f08090a030c14010503011805150402040311040b04110412051c020d0906050c0c060f04080a0c080d0203040e0604150e0703 76
    0x420020201d2035034805d421119042000d01d0310100b603100040c2c1e900008031080284d40c602014001800030304c0b80e885210600c440104001a00004401c4a4940005c40040a02c01100f4020000040b5901d140030010f207102c064108502042c6a4480290f1051241c041d2a00c0e00d0b20300300000d003c584055104a070390a00b00c0c0340c14007280440d031820f040881001e090840c1954140150100585598110000c0540d07441c40000d0841e1100a5503070100980604110760315905c1c0e040c02024004900c003140c0c050750500702003505500b024404c10b0a4103050b003002d03034241402e01008903904100c1040c203540e0f600c1418224501103600c00413034148101d0503001400c0c10300c0750400162514495600680902100348000c070284600414804107551080b0b55880c0d032001025204001402150886a807500c500c40d20303041007041c0c0010400503111100d00f1a4207002d1a0790040765a84514092403150601c01c1001c0340c030714100760b001825501d00140302c80d00c2e41e80e1110011350040c2030840d119400207450b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 731014001 1250 731012751 731012753
    0x31703040507060e0609040515040617010b0d020d15091a06120a02031f0e01021306110105060a05120c090a0f150b1e120103080d2d0b2803 61
    0x108007580080006041044d000b030f6410300020b9060003481e01c81d034000c0d5200e100180709044511460150110002c0c0100011900d80702c820203120104000c83c01250301e0002800003510b0003800c0ca21442e68001e20981c0071f040c80f6940d0460420740300c5107880c01152a214034034005460115821008041d9a00c0c4017850301e80307181005030b000f100c082690503d401200080000d43c402041e4040d580c06a1000c0c2c80100003e0341004004280e250001c2c3c0c450752000c5440d1181845080e055811110680d8441c2403100c0c801d80b41c2822a801918240d41c40341c00742ca420400d0341013000c555035142c4030740010b036925400d040d80071880690046400009981d036403000340b12484068414a0041440303500202403030350a140200da941e20070310090f040c546041035100c4a010394414100c2e600000343d0348820b0142e5a4a1074080c040381c1210400d0400e403820241e10340f0340800c11640c0703406542030840d9a00079103042414484010494103d040390000360440907120000e051102140f03aa040c3c103000d18cc156499 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 731015251 1250 731014001 731014003
    0xc020309040c170a2c06090d021605041805010c0c03180e13050f12040305060f090303130309051005120a02070209040b060f13020d1104180f060317030405 68
    0x14011503002d000c800003d4002c030290604081d0391009420000040b0740403041054143d1030080415044802c00119032501580c0c40403e0031402030440000301d40707101c075a042042c0d07110b100009203900c3e01c101c0300320100007034901354010755000300b4200501181d0b10a81c1e107030a03003950022010f400124080c44c15900405038040e07840000b80d9480d25010302c071f85d0300309840301000040c050124080c8018081c1c001050050034062003480404074800c4a00b1300322201900b02d0142c0051000703485602a03135000801000d08014500e00c5607200c100514a196241202e80346d0b00203440d00281c040064005020485446400d602000341c4496101c0a03250303050700240402c2d07288005c110721b0b551360040c015500107888402c1082d401643c00710311a2510303074401c004103507e51001c411050340b04454110090580d101e59000b4903820342e0f50107082c07200c40c030b02525000aa200724418043d05010340380c00c00a1302002030340b109096042023040411515035a845054808600740e01142000d10300200740f204000c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 731016501 1250 731015251 731015261
    0x108031308281403040821092b082a070b070b190603030f0315030302060c2b0605011119080d2003010f060816140d0c02030904 56
    0x500100200b03800d4100341d02050001c40350380c1d2100300d041d541038104010410300018003400318072103d08507622244d03507081040e41c0d0a44680d440c203044010121355050751844030115030224001400c0c1415090105924a11303120750300c1d4240601d403000c081c4140000f04084020b103001503400490111410403c241d41d904c41a0700d00c125100c41c0c0c0060000c225801d0520103550f4002d03001541d0381c189944100c42440e902c09080a000101894140d001c420141c0204015803991003980e8108486200307800c2c0111002c0c0e25001c0a030240e03012400041004103400020110710051003c0645640c05d505078005581440112240000b0785900050009582c007a2242171000e503480d00401501c0074017002c280304407502c039002030103e642c00a4901d20b00704c0c241d00010262a20712100c1b00b1081c800c40b0304031031550001e01501d03500c841c1c0004001038541c4185a01030040f03001c040d039442c00f1201d44009490080384075a648424803400d0107004013000a9114002551072503070091a0341e0303800502040200c0d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 731017751 1250 731016501 731016509
    0xc0105030a0b120f10290d08041e0b0c100f060906030804080d0203030f06100c020306040b0a0b04020a080604020703030605060a02060108060705030c0a030515060d1409151311040501080313 83
    0x2529000b89606e401540c00304403d1740c04282c421180004051502041b14074440c044064410f107800640010b07590305540e41c2860708030a030b00a0b00e6403140c603600c159001d4171404100032899406003071210000004c80d0302100030605035034030002d50702e56500c144c9010744110754019a048040881e00300031504007401810f00c00030720342c03000e10300d10f1800314cc8518139228040c2ca5140511605050700b840f150190b0009040d1540050444119150074602000d113030b0700842e0502a1942050300701106402d02c0d00990700b1002d120340711078199a50751070a100007508400b80c1902015210300300001c160315183c0007010040074a0340500540e604144046152010140c10541001000c200300051404480255031280009140101d000c0d02c4101c41001001010b680f082e9101d0000034105a1280c8664098109448551801d801f641c0d902c1c078100b510f442c10103c910740d003115540c0000d1a5190302a4040032814411900c490034400041c002c24120f580903005401103a00000b17440340740d4440340180034018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 731019001 1250 731017751 731017783
    0x30e0d020d0f0806180c0c010e0309130207151103091c050f13080601270b0a03081b0a030509091006050a03020d0e1c08010b0405030c0105030a0b120f 66
    0x640031000244034560006901c420444600045519a80d45008030706125800d5481c2c101141010150408a6403087c020181150311b0002007800c03803100802640c1800ca0300500450000381008007850103513004d49022100480b070403080003401c605d03900c90b010fa100d100c0c00500361a4a0402c0d42d00d4500801861400d01400d4420344803050f255101c030488074a0001c91000340d4440e2000541d040c400d81854000b10500e01404001007542805000d000034101078003400407003292482c1e6070a2085640c4900102d4001462030000d05c0810701c403000410b59401204900604a98111741050410780c00d140c00320006000020b5029440c41d000740300b1904a80042d80190166103081781c00362442c810284008181074000c201c285100b040e95000a0380c607402c400a03552007401001b80d0381c80110705002c01c000815110800401c1c070314a0700d8160307403d690b40074000706850900580195425000201600c601c140c0358210300c00c680d103c0c40150071108034048002c25281d100b103c0c0d41c2e400c040e05400e100c0e0031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 731020251 1250 731019001 731019013
    0x2070e0901020903070320030639040b0c1510030b150f011b0b0a02030103050f160b030415090b04030914030a38090105060d0f0b06040b030d030e0d02 66
    0xb07a13903808a40c0804882c2d12490001c06414500c0303d5015194403c0381084e85401290100b147c0748405100103e000004500221101050400094400c0001d900000d0326040305101c280003a1441500a00050a8101c221004140140c0044003141002c507500c00d00d204080d1410420020807100c0550001c0b440d043c008114508080400c03101410040d6030f41c100048a569864041d00c0e0308035030307202142c0080d581016850818030002c043d50082c40304035060310800e2254001c908021607007101c442c000407500000d691a08442003030b140c002070001e076004c7d412040c40d407010800314030903800800e1040d04105c0345490181405028904c0960000e1b8520560b03910315160b40d5404140045156401101c0e41203401c40a04518260214010f0800e03070b440d0000c0720b103495401075000c120f104d03030340e000001e02080e136031082400340c01542d06400404000d815111780c0d001581450406920030805400080c00c803204500107480c107100c141d687c1001c00e944d400c203602c15030740c1404044006c90345c0c2d000805c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 731021501 1250 731020251 731020267
    0x210c0102070f060806090a0b06070f110d0302060f04080d050118060e271c020a11010c02060d020d09022805040e0d05160c09050915090712030504050306040302070e090102 75
    0x4c01e200c0014441c501c00c007600310000c0d407420200e034407540b2003040280c03065844107100e03e09814a40380d02c1d0390a407000c400200d502c1a4a142100000d8501caa06a0141072144c82d103d00100080f807001d041101d12107814000040c0228851142500810480480c01c21745400408807a04a800982000341c01421315400c10045c84803400c400a840c1e07540e07920107044500150708980c103000b1070030500644074120921001e1708c5079001882c80c030100c0c0260b1b40b0740c01c205800740054400155111009400a0f010300c079011406000d5806030280b00e80c6a180454403403541d07030000c2d40703049400c25910081d0300385400542c07074100064525409048151030811110030b5032544075503241e01036403002007040b20008104c410403010a00000716603600500380c2e01216124000c03180502004c40318010b051242c1402020201d103503441e00c9019000007005041c10768180081e1280c2104012800c0d01408002c110004094400b040721511407402036014040d0b6506120b0702c07060501000e065441c007a8010f00c5010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 731022751 1250 731021501 731021507
    0x1b01051018290307050406060302070510020a020d0e03150c030711030f0d020906070804080a03140909270f011b1404060e040603051e01051608040b0402210c0102070f06 74
    0x228141d0403001c2030b4201d0086000001e0324011054100980040c281340000407041d800d41c001c0e007442c0d84032b4400e403415084020a50303801c030b020710000f81c401a481503120b07840c1103000e0202c01e0117519028080c0d640b140001c0318a213250310b0707080d144811003201c00800c0129155100c0c11880b1414030307030801382d85004138102001400d4090928a8548180d0014015160f595040100d82c0b0181c0e220a00315155a941c03010a40c9541e0a940c06402044140c0440f010101299045485001d0000e0003003803d43c641c0a02000d0403103044403030704a440c1800e00d04003103e040c1003109921118410b000416004514600c03160240b069810304404e00210100442e68004e00c0000c4c4c0d0240c034201e14003e41c0d2030500038009800303070096510243c03c83c051383c1092031101240c142c03918a07002c1c2e504024050340c0c903010a84002141c040044800040d01000490700041032054400e4201e40018030f04403240b01c0c0f00d600000049020700c0c1141159201a941c0c18855070107004180c014041905a640c480d460100c010b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 731024001 1250 731022751 731022791
    0x61213140d082d090102071b0302061215040207080717091e0a1d070206061c030e131503150507090b070507080f03120105030a171b01051018 62
    0x300e0908103407485820303900340c0310500c03c0510408400c6808aa800d15028241c001c1d030020205441d1994025040c203204020b95050034112540580030354904203010691004403000909910605081c1e50003004a540c0c803400030303001c030030b0191041954459243c50441d403904003c200c4e2000b891010301102c1d403581d5480810001b00340000c0c18450724200c100700000d500401c01d8104a0510b210344c50143d56014110001c0e82c45020305400725401034036000108100404607c4101e030740441103852403400a44550981044c0b410054a0000d0030b03104200c0170743c15501c44095003800002402d00410074001521843c1954042c442000c021909210600030800321250041e1700d5110700000d500c0040000400c4440d000301720303000641c0c2d10910065055610307070707200030f100c8410584190008203071854089401a60380380d0018890901007040b012241c0b0320342100c03180c403401e10040e4900e80030800c400c4c042ca92040300007240f404075003418501c182c240c09015022000d08240340605030044480040b5a03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 731025251 1250 731024001 731024011
    0x605041a0d03020c03161d0103020f1e062b0e0601050411070b0702030901020d09050303030a0c12020a05071208090c090c040801020f07060c210b061213140d08 70
    0x141180c40c94260605920704081000380c1c94061044030580f0110744180100c6c00c0607180c5000360005a07088074540c1429100c002e0002951288481092062520300801110341c109008817080700094040400501c0d030350840c1400d04403055004c0c52005003500e00c01c0e4000141000700a0821222049414082e0340300014092140116580c00c59000b08071a6034040d1044140d12148d13513159403800000007916900203000150140c4910101e48200701c0c01501003609a65003d0025803e40c1d0b01d40140d0340c054083d60150000340b100b0034650705013285080c0020a0b03040c14503202d20340d4450741c1d8074000640c180660580301c1004164401d2201c0e5480108000b01d1301c01c000c40e91800141c80b20000420f0724410742c1d00100003503200040b844908101140900101802040300300060a1010742c1524200b00011040450418003800d90a120049500c0b61b0071305d000c00b901d410704207444803a84002090b415100341300c1640744800f803202002410a10582080c3c40b143c0034004071040e64801810545001d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 731026501 1250 731025251 731025259
    0x2604050a1a040f081c0e0d020f190b0a0902060a0519030203040f060c0216081b122a04090605151903080c0a2315010b090103200a0e040605041a 63
    0x8030380903a0201c20440c041c2d60b80300c480040104100c6c6c076140300c0d500c0300c2903100c15015002d001d841c206c80b01c0d40410b580000c484041440c409540c0c5c1d699880b404203100900c088510359440c2c42450258407890044c040c41d400a031981503403242114603401e0b4844984d2102020107004001300310000e20030b001c40041303195000070007158209182c10700364106411056041600680c03020700040a0400203881c0602541d01c50183c812900d2101c280035800c806030111000c1903124480071a1840e0303e00102080449101030000101000d00c000179081d94813103101601d10589800900c0800c000c0402c10101205d0122042d041c101c0c2d003110b002004814510024040400100d0f1130080b00800b0301600c5120b80d0302c1100e110303d00d0120303241c0c005800d40c801c40c0500b09101d540c50410500780c5020130765059130110560b10313081080c1c00c0c1c0118050b145034045000c2000000c802007141c040e140000c0c25008030f0b2616014111250a4184022112a070744480d11030b41c100a109544810030012480d5140310541e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 731027751 1250 731026501 731026507
    0xe0a0312120b12070603111908090c030105041419050619060f080319020105010501081302192c1302060729060a0e0601020d2604050a1a040f08 63
    0x200c0304006101c03440c00d8542007020783d4103030903958070042484401c0d01c066480801c1440104411816140120070708600205d1505890803406409025650341c0328200038110b5618001c810301081c00d484058030111140d00b200c0100c0c041d040f13014000c40d41c829200003804601e0031201d49030303180d0b01c50f00a072003411480890b42620346410000c1c1c011801a0010403070201d00156290720f855602d42c40400e00c1c0c410101c0c004c001c000600d00c10b003d40c134101c540c16074a146040c0c90ba07680700450014440d500300d80c00320710182060260f400c2e610b8448020130400401c5409558421400c0900d010111000101002041c0c00c00606130301d80c41401000310f806840c1c00381c43d140686041e0b0591410030792444d100c075002d00a1100031440b00b91543e84208002d42d6a15000c0c1d07680c125503040c4003c242c0749075000d80c00103039044100701d02c544000780c46a10400c103400c0d81440701c0c1010040b00c00c81a41c0944054100302c4008041c40003100c0c43c0744240055040702001443d160720b07104c0080903181e82c003d141580c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 731029001 1250 731027751 731027777
    0x1020c0109030b1308070b06030c0603130809010e190e090129010c0803010b070c0b07030503060f01090915030c24140405180a110a2f0a0b01060e0a0312 67
    0x1c1030031a055803010b220ba944006c2400c1595240744100c804510030312401c06e529000f0704244050b2801000364011882c40400c003666080c00c56000004010304000d190007191965598100e105086000b18001c151840740c02e0159106901400402d03005c0141c1c10111030086480d02c0300e511881c000980b0b420000d041c0b05440040711032000b034090190031481c0100000c500310f440c0c0310040001d1071080014040140d9910f00380c11207805451006004070f031083c00051070a00704501c040091180c140b41104005449466000884411684000840d40d0144060082041d00a100000741c560283c55650403030b0701a208110041ca02c05064081006940590f003854a1402c1900c0c06000003e00322140c685024004585c641000c41c1d407204064107040180d20803070001d00c00c80b07110b12644d03520000e1101c0078440c28151030031803003090820796840e4550300c81000c00510286c0780061050b5100302c0c0c0e0f5450000001c0c090102500b90605c07458101d0070410006e81400381e03483c01c201c4a41403800410804e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 731030251 1250 731029001 731029021
    0x2040248030d0b21030a1e0f0302070f020307090f0506190b07050109051009060c140405040902030f060703090506090d02060622060f062303040204050c07060c02030304030e01020c0109030b 83
    0x1415040b00a195411850804c000030003001074445e0310141e40e19980c01040041c121f81400c00d081c0b007a076001c40c4640007150500d5119400030000c040c0100f8040c9606452070340400c2c40c1c000d4942c0320042d055a5059041c84060050281c1c6800203011158041c20710004030b44140c00c42c480d445014008540001d42c030041140030741104020a0304001500c45045d071500c0400c0240c080400c0440e255441c150300400707468020601e9080070003618140505003030810341448001c2c540c121040e0380c1440380c40e01e002c0c0740304020404148141c085650224081c40306190040c0346c104040d250907004d4000c400d4240e1880e030b0018029a1143e011541c00740a09070741044520000103500184074911704000c404a040691320403981c040310307020b0b907401c1c4000102900803d896000980c1c0302c034941401704049800b600c1d02d0740000742c00a4140004600c3c215696403840200d03000ca051100140e0004030400050542028039044900400c1c00688010a40540001c141c1d10702400010018451040172030701d0088 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 731031501 1250 731030251 731030269
    0x40c02120c010c0e0402120121050304230303040b030402040504020609030109030e0108010618140a0806011d010e0f0a0e0f031215030a0c03030c02040248030d0b 71
    0x20034103504664541e08049002c0c06410710302010380200d12140042c0d1000d080c81d108881050a5900050042e81d0804001041d003040d100c69186510307031503503030074004510b00348002c00051020350046031344003100e070a5130403050713144401180c40394005200c02c100395a541001c0720f40c0164100c030b0000b500c1e034403440010b0081c0140540283c0662a1059403010103030494409510320f1000d0320341d840b145c2c0c0d030362004464800310403941a10903080c0c0b04003001144a01250303405003000c000c5c20684210340794941c8a02d412401d9221000103081c0f8240e08802d9a6100102400b6108501d0206d0301464446203403009120f0242c0b60550b16540c444040e10282414030001c0000c00d2000c066961740d0500c031200e0140100c080d6505a00c020b250070280c00c0a00d40020001411035010740d44400040c6140c81c140c41d0080202d0090b82c1041e020040c000030070401c6940c4400b2201c207403404049480101c0c87c5074801800c80c0900c1030805292981d81c81414000109441c0000c0f851400401c54450080204030441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 731032751 1250 731031501 731031523
    0xf03030f0f0c0305040203060a0501081f021e0d0f05070c0b0414010c0e18071e030b0d0f030f020a0c12030c020409030807020f03120109020d1808090a0e0c0306040c02 73
    0x5280c60385072034802d6816048103000d240200c003164840d45620b20000220741c1c01b84127a05c5a640031100301d20459a9050b240400700024000060814000c400152461100082c101076954400a070340700c9500401d22810310701410400041102d0318110304098603442c40440050502ca1150000404005c1c2260600092400c0b40d0000d000c40c2c1c04200c4041c2c80040c91011140c407481c0402c10500e104000032401c148500710a82d5400004464014120701d1525004804003c06840f00906421a2110f02d8802480781c0305260703034440b00115082c01480b521b20b0703406d41006c6403c28280a400310f00c60f48650410364000a011122269070b516040d1410030015000a41040c2840c10751400e068000003100c0c4107642c20340a4480d00240c40d002c50fa22486004120088100000018442074070103501038299000c01c0c06001400d40403070520000b81005080c401c072107103480051512643c6c249042c9903802007034207800800481c10580000c0740305000c000e00742806296520000388002d44204080c0d5000c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 731034001 1250 731032751 731032781
    0x501030e011e060f081216021206010e06041b0819180b09070e0103030f05160212071406040602030d05040807140102122203080423010b09090102070f03030f 69
    0x8111020202c0c00380c0900e03c100440c5000d070ba80f0000b030000011402501800e1000c12861802c110f40001c04108800c02c6016604400301c041c0c05550340c40c0401800740039100324000c441c09454200c0810068076580f0740707100f1350704910400c5d907140c00d600074464581044070340c000c081050341c100360f02c01c005100700700081c03c4005c00303140c410050040301d404681c0210815819070b2001500c0da0242e000c4c44c40203210040004440c21036440d0003e1183e00a081c080c084601d8010705e00010f82c0000706000010101e404854010103010041607043e00c842c0c00c078000066034075505151030300102a40300c0c060783e945429a551039900103410095000c04444815a000c246403515990303086400c0c1c001c1d0013040301070f1150031041c00420000d0400844444103441c0750f0600380070a00d81c560b4203e0754005c0182048980c80c3e0282641d505d00400b00c011812840003000c0005030b03a41c050020414202c0001d400c84403141d00c100904804614030b03042128020b501400d0100d41031100d00c0c200d00042103208070030900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 731035251 1250 731034001 731034041
    0x209100c151503110a0612020c0109020406240e01020d030f0e0619060602010908042303120a0e1507080f0405030a080706050f091c03150f05011e0503010501030e01 72
    0x1d4095450b8004050701d00902214500f0b8030740304184001200301e80a885c001c100c1a50481d18400007a4000340980c00707aa04c000b15410f051540880c054603011341221020080c611414050380d540055000e1404c0418a13229219600890010313403980c1200e0001410103803103900c0413070f01100a03007142071040c0c0c05508545151405c00c1c01011a0344000074509201403c00c00c00198042c030500071510050b4214000038503182c0350400042104620050700c42142800042481403981c1c188040054001c1681282d9620110719000070640c00c00c04503100d21502c0540d50781e038254040c5806503403d45510a0003681c1e20742c62100c0c0c4181c103004907444140e141c851070a0b03a90810140202a104942c49545c01380225101c0b00300107240040200c5400c2500d134800220380c0541c1d0071916501c50318030344c1070400060024101c4451a0b0442498000003ea0388100008200d49c2d40d00680d0b103032030000004030004096500401c010900e11040c0304d1681015215a000f0144403020340c004204082003468842c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 731036501 1250 731035251 731035271
    0x90206251401110a11150103080415081608180712061a01020c0103020906120a150803030705030718080604120207050105090a09020a0c050316060f0209100c15 70
    0x440c0400092003200c20a003040540381003000140102c2400182d01c8000c5402c00e000298101c4801500c1081030486104441010040e0558424801e020b5030280070030b00c1c1c5e6541031207071540e50307074201c03a40c403c04002d8039108014001100013007103001032542e8031300180103880f0240794201102406000c1c12460107104400240705000d0095101518440e020030700c050100006842d85000d190304005000d80c0080a80340d0320f961090340184031010000b8081400d07c111000c11100d1044116400d403c2c13650782d00c0706810070f201140b4151005200c81002145140f80a02d0020950b020291895090140341000d0351800300c42303081d83c80060101c2c2e0003150310038505810444112001e802201003d40030b592404981c551080048444a0001620401c0c0840c5403a030300e80029404062007208110315a03502100117002800245141c9548031101401c10110b400d0a4003103900b16038107600c0315481004048110b031a5001c1203007580d50541442c142c1f242d01070a01848405049a50f2224540303845072400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 731037751 1250 731036501 731036557
    0x703110c1b19230a230d030e12070801060902090f150d0b061204080d150f061d030d0504031e21031506020a0507050618060c10140a0506040908090103090206 69
    0x1903c981200c1403030308080ea02c0c4c9000e126041d840b10a000c1e0010348c859041201c541480910720640844000458404a59a9030a1b50071640700350001d20b40c503071b00040c0795106450f0039800702c0141b460880f250f00b081c0d08074010724030080c812408421f00c1c50b5104c00c0f00e40b509030340d604144c8400503181181c0041c94038140c0b600c05a42c0e4051440d0340b5050b0300d481c40d000311a9814010740010382c3c01c07101c1304038002c5042c20302c2540c640483c0a41c102030010b840e1108050354605100919004803203440d4140c03502c0c25460041c034002409c1c4021800750030380c1003122001c10320b03040d0b103240003009202655130800d480c420210f01802a080d44001c8284260400040d141d074000351192880c3e01078029586181e444a003040070500c1a100c49500183c100c80c500310a61510400030083c2412410403a184401d1680d0008142e60703000c842c41000a10100400400c12114021103600c084100d5003040941d40503a125190303405045802c3d41007568400c2c0c7d40b0210344502c1f08070381c00e628111000301000c0b040e0070228 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 731039001 1250 731037751 731037779
    0x14010b220f0303210501150c0f051510150210020304290106260a0b1f02030a030b0102010b011e05120a050405010c081b030703110c1b19230a 62
    0x1058405040d54484d28840c49607200c0c1c5816501c1c00340e013442402038600300885944820400585e00c0740482190b00c00054000c0140c0c0d4441c232000a1a50650f1400c0004242d00e032034a41e0150340c101c0c0d446c650a4428035404a600c1c100b040041000680b01d41b92400d000550340c80700c561600c881000f00116099161141c405a8100c3c0c85c0d564401c080c0ca096143d1007202d501c5030005200c848e82c2c2c91404210380003042c5d00400c3c41c441c0007410082c0002c8a804612078103100d0740003d080560030004150300682c0c0c1c0b50155521542d001e000900c122904080001d090380b0b06a611100280d0381c140d030380c002aa21980c101c8940c0c50810403403441904000100200819007610121130319881c00354180c10990040d2031041c811100000032141e034180f421503003002540b006100c14109a55504810900c0d82070780d0141031a644402e005003c50751404980c0c0011b0300030082803a21816807007401c4009205008001415169440719165886405145041345c0c000c070f004001c2d510011088020640b031403c1e01d50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 731040251 1250 731039001 731039027
    0x603020306061005090f030a1505150604031505100b070c15090b070b0901150e091005100501051b030309031c060f0302060901110d020309010314010b220f0303 70
    0x141e8080303458440c200007580300040b01e02008030700240002c0c450382c944406000407202024040d9040c0035416030340c1c1c05900c0f5414201070382441c0c1e200144880c20543c8000b02040340d00c152503041c81c180c155201c944802d201da14031b07100c1c80341c0c0304c0000034269a01d03828010300400c20001100d861340014076010710032100c03e0045100350080b0400e0b0a00040c8214000e6040701c011781007043c41d00308244c843e900c2c594001403244c001e564841d140300c0c1d85115000703e130400034100b40c0e00d84812410440011401c0a407208940740b034490034601030110050f210349401e812942c090a0040c0d89019807041480455803641840d12103000c048204450410040300804a050702e001c4101000320440200c0c00486003039000c0c5900c1d1910025090005080081c02851001014100325104a185003584ea181210456040c0b00603003000c2400755055070180109c0c82151041d8819004642c10b000c222016400750026140d030761020003d076a1101d013500747c07045010b0007400c0104030754580c80b03040c00b5004c0d80301401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 731041501 1250 731040251 731040253
    0x6010c0c060f080c090d0305070c120f030806040903091415040609060f0306030302100f020c0f070603110423010c14070f0530030d180614070e06030711060a06030203 73
    0x45156943d4130403103042201c01000365101820a032411501c6d600919821554120059008514000100b44640805202d0307103103002444041c2ca40184030000c003602260045052000c1800001c2d0080c1030f90040d2451004070214060440002446000c007000007140d80c500000b170003280f6164000406015912035840710002041041412021101c1d40d11001d001038100f0302c418038286040f0b42010400d1a1035100c0507040010a42900d400c024424154048617884010304001c1150107005d840203120a0700d020ae42440c0c50411900f00d1440140c3d415880003103030004d0808660700a0030b40c14651600450719100307040300b01c561640d858002d800f41c00141d04401c0e5001503280b80a0091a01200d54858034002c1c46440b10785e401440a0041d40401003400b081c088d01c1d07504100c81c4580012694401006c40c0c209406090030b100b240c880b04544100e002030341c5e0030028019000701050016007010346107a40c1d2a91180004c8443c94000c2e5541c2c00180070f01d109100c0f00b01141d030021403c1e203000b10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 731042751 1250 731041501 731041517
    0x30c030402030f19170405180103020102160b04090903020f03030709060e06030c0d050a02210f1b030112030c061407021c120e010b041d0d02010612080306010c0c060f 73
    0x10070a03558078900460610f5a20040051003000204140c904006817640e104c0c2c144d01381501c60002072403c0c0f20080318800042e80f9840100107540c0d041103005102c0da0742c1c4c800c1c16009424441040c400d4401c1380188420703261600d00039001c01d8400c1103103000070280142580d44078105424010020f80d464414800003074100d5040d03c000c3e1510200303c0e401040c0016070326241142e03841c1d8035000b4041c001c0c4090000c82c2d0a100440100c0d4201c041d11001c0e64450006400c03503e0885604900c00f0343c050b010281543c9051f0880202001e0328042382c2c15560f11007801903c12009181c1201d8076a04150001d10740c40c02d086004130200128501c1d079010301e0040d02130b1000c180003071100c6003050541c2e018410004940050400c18500598444401e403440100045941d010071004601500d00d60079062403a40f503040c0802008034410301c840c40a9200303910091110500c0c119240e03070106110700d40500a980d0000104419a014010031a1700a61002c85402055030f9084040d00040ca07022a44021070620 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 731044001 1250 731042751 731042773
    0xf0d0b07020d170a05041103010618051509010b03040f060609020c010b030f060105120127021806010c1e0606140a12260d020c07050a0b03071403060d08030c03040203 73
    0xb601c604007a070400d40103020240d84c0341c2d00e641d4060100604103960407a004807842d02141c80030301801c4003400c02d07405d010882c8e920105a03401102c00040415000340712522004039079a49000c45581142c0455150790b84030f0b00c590600c8007019202e060021302082c81e0060000d1890100e802900030201820005c019135001041855150507005d141e4060a401c03940050000340746c040d0558405050010000650702c40c00303046410141d28001c01d05000003910400842140f0300740c5010844100074900c0115242446c41c0060000d50400000030156070714107400d17620202a101c0c40d0550700d60450428001103584800c2c0204005d1401290390046442c0c04000c2850000090303601c0c040303640080d000f800aa00c5542040082074040300100014208000c40340da008428005000b4810448018200380e07403400040151050301c66000c550f64074018400c0040c69078004004044020070050384903030725a54900090f040700060700d402030030700740b0120a03c9130195544016501c282c0c030a404844007400c2c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 731045251 1250 731044001 731044007
    0x111c030306050f06090a03120c050f0106032102031903020705060412090b09030a06020f071a070917031603030b0d0c03021c0f0f06111b120f0f090f0d0b07020d 70
    0x7514401c176030840700148003000010000b110b01e030b203e100e2520b040e000d222020358845040c00e101e109103003066074554000f402030004080050002c40310300c01361401062103244000e9100c3c0a041103003204052102e010503038460291f01103404003680401a28103518040c601b0360644c000345400000001c051540100d401002c0c101100c4038800020f0003080940c1c181c1d41c84101070340c40213800e4110010148040d1000450718410610030207a4043c0344e058a14002800030060b102550103e4030000c00c1240840c070320741c400b108603001500c083e20603a08150b034a040c240d010304200810a904050311029013400c0c449211030740016684200c50b064001b41c0d028400b9480100b808901500001c6001003c2d070010b04035000403408a84611000b041410206081c10030541102c03150500e902d006500d6820014002e10103a130181d0080440c46080a1004507245928010112103152002d80001c0705445980e41e119420012103000b0002001100103207050295030310140c0e480310140c825545d072a0003042c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 731046501 1250 731045251 731045257
    0x5060907151b02040f060602030705120304020d0f03090b0f0a0210020310180f060e0433020a0509030601140a06140910170a051e0603030304111c030306050f06 70
    0x102560303100d41c200d10160282c891070210500481e84240d4036551180c2503d01401120018520b0303401a40c1c658081e410041c0c10b101c1e442c0103403400c40300104101310050755503412014130720360484c00d6240311140d9803406446800f0b803504001914400443d81c0301b03900e8168002020790125076400d4504806c000c181c11016401b0641d102c00e0ba100b4685801d000000380000c40d01c2c24078822010100f08041c118050a04803400c6811507900b88219070200024059a6200c1c0701e03020b010f4119003044c0c0c82d51060640c132111400234090122a40018850b901d140c85039094520303d00004040c1c44103960f55a0701c101c0404004403803035009041002c800a80380e40070300010140f151000f20b82601c0d10f24401e00300302010178882d80b92006d1207130312425007003c0c5491000551040f02c0028000501d42051b0001c2e09001011201d081c01d940c2c441e000304503607520f0200c241c0390001d41c030107803203d00507041d800000c82c0d203000c4488210301031300001a8242455410b8101c0d0040300c0c800d580c0700d07541c006c000701488420300c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 731047751 1250 731046501 731046539
    0xf080307150519090c0311091e060a0e0c0304120f0206060f04111c0e0705030c0402030a06150216051e09070212040e01080c0105030708010303111905060907 69
    0xd04420780214040c0a03004142d002d816549071414802d1902403a8044600f254400d8840089a40d024170030006c100e040000c0340c0e481101d003841140b408910702400804502003c0c030300c100343c88004c10083d8032030400c8000684100380585640d4542082d000c44142c208450070351f41c0f00c5442445030b00680c05071000d5160104164081c0845d035480030107222100110f00c00482c1c0141c0d903251818069600d180141483c241228140180070460755400300c259a8200458034544e08203040c20081650001007800c1626411b41d03003d07071a6998501480010b000d583e0007100c000c45403130355080c01d095001c03c00e001c0ca1181c00310031150440d20f601c10312050603c14040c0d442d02e102c1804002c6014904039001c20380c01445131040301c0050045400000c0140c22590020800b442540d00502aa90301484404c400ca80c003031910324114500301c1001800700006100140a1146813146032121010922071180d5040c0c510501c8202c4641170302d40103603a52422628903e85004031840400c40c29070f808011010740e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 731049001 1250 731047751 731047763
    0x8150a05180c12090c04140919020409060c11010e060712200d0614030102030c090613050d030c0506150105040b13080a050109050d051201090906021606060f080307 72
    0x1015050040100c9504042d0200c14410300a1040095441004100500c941016005040e02200c100c0c01d102c16550481000010710401d8805c00149100010b003040c0c1c030900d140102c44040c025800400d000700f0010710003401040c10000074800040d0020164040301c0100002041415426030340349403180002c0d1b855000203080c092404403c2c0c0c00d6500080030f11000c800e161101060414005011940000e40c201401c50300c1c2c000400c6002915812038800c081c040d4000d52941c6420390004082d0b01c40c840f89a03115920100d0900c0c0342c0d10041c1e04a801503c400742194070b1958071418081c0060f00a560100c44a12610000500c0021390602420601006031205401c081c240802e017441600004560001e0420503040002c1400040116480e840e0281c000080c5940150a0a0b07081070000310300f940a004040104125948082607140c3c111034541000003214100d40c64943c01134030a0400400a05110203012810701540380d01c0a42220401641f15450715590ec1c481070b00c0f8040c102010f004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 731050251 1250 731049001 731049019
    0x1300b0105060f0909160f050906090d050703061109040e030a0206220512180a0315050a092108010504090203151b43121e08150a05 58
    0x25820264080c1c2840070300742d0411810700122070003240c0700741170440750700c1c070080e020751840710160317070070668104d0314140300e16005251044840114401d40b0900005902403007454011a09201c1c5c01e0150038042c5500401c140a20201c1c0d2155540fa90003a21980f4403643c5400c03481181c45c50004211400d0301c40c81d801034546940d0f61054148a0b40c1f682c01411154016840c0282c0012418843c0360004c0b9500c0030781c0c0e5280c104008a8034100c1c1582c142180c05181c0c121030510204140c0071480c440da00400310082000e80d103840a60024260801009080748842c0d0342c583e060540c04544010000441e035900c24441e80d035081000180c410b000e5001c0e40581103000e000041e044242d020983c00400c41800c245034002d09c014051440d440090006040c0451540d003c81130403080481180c00a001c80340030200026003100102140d107040c8000b05039111406841060500860340ca20dc50701010000303603a4048007900140c441002282c000c1640c4003c000700d01032510f020000b01d070035030b40b0103808805 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 731051501 1250 731050251 731050259
    0x703031e020307260f04020f0d08120f0709170102131203030507030612020d020a1a0406020f0a02011d0406030c15030f060806011a07050610061e02100c051201300b01 73
    0x581c5150203003050782c00001c234106160b243c1d240e040401e1440b47c0304000060399002d40a100403200140641020f45811028040c4030b4115440b40011040c1d0300380f030110039440b9083c210036600910404003086c4905024810004205a80c501c0504201d801703600c06010307a41d648902201100d14500800c190602c1d140031810150030500e46448080344068055210b01c1d45501441c03030707800217442d40801c282000150500c403455060010421080c04180180205e10455001070001c0811200e02891841c03d1081c00d5850768494101400a40e008210b440805443d040204210b840350303845035010a040000c100700d19040781c440d80c400c40741044003800c0580d00f440c50816602c100240481c130b000d941403001c000860030900c412402405c2c2000403031002480d0006c0942005070310405039203041ca80c2c403480344440b60081403200310003546100000c0d580004c56815201801403600c0d503200c4148030b800101c1e082941c4000b1031080080c4400966400328800340310314070301c01c0001d8024402004800104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 731052751 1250 731051501 731051521
    0x1d06030115091a0301080f06010308090f01030b09040b011401050315011b080d0204030605070e0d420b120703060b040b04140109050c07030c02060703031e02030726 72
    0x10450182c6003080e400390b80c03410b1a1410040c103980d10000c1040010040129000c100054001061000040c18040d0300d1070b1030f04049400307005401402400c84580c000c1c0103a01c00e62140740c1d20075006108264034109400e0050a516090080c064001d481074030091143d809031007940e2140054443c0400c45410003401110320483c0e2454080428490034035450009801c40c02903c80001c0400005803102d2840c10305405a40018104806102100d0700c09039480d121050340081c041d4000c407404200c0700300405040405511200070726580140041d4031140300800c20700d44059100c42940520901014004100d0401812000990168001e001c01c0002903141d401401c00411f00420008041080d4004241a5203181e84401f0341448801e0040c0306aa40070b124050b04400c00801d035508003140f036980913246c68540340029100b9a404900d110400d4421b4103d0b01e0a100d0520007071300560b20700004c04010f500300303451010110749017050450445c80c44052030260f107841c0d114a4402a03c0e03640d040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 731054001 1250 731052751 731052779
    0x70201090f2d081c0b01230405120f16060f0e041d15070e0a05090a09060c0c1103060403081303031d070509060319021306030b0c04061d060301 63
    0x50440d80e005041508281800500305150b54040c1c0061640c0390b80c18078080744c403c0f0b0300184c03002d8440d1401c01d140c030090f40d100070001c90f0210108040c40402d440021005040d0089034845580520000121030302d841c00420300c400b079807510001f211100c80062803c600b080c0c0d200d0146400080c1c440d6480c2011520599000d00b80600c060800038209988941503490149078505111a80e4440c9540c5011304404003001c0f41e006000b442d00035a00c400d224000780600d6801e1140d80d02c01c902c40c1022903e12150307030b80308144050784540c003008072030032070344014200c01c20319030041c0e4210703503440d10091107406d01281c2e052003260f041d0b03101d0307109994421b00c0c180c02d0004a07405504065451000040200b188000030358002c00c900010241c051800c0c2c108100e96100400103070103900f00d030a8804482050309460000c16a040710032244001039151400c00400c001c0e440035101304010000d0150104016001704242c54559803500c010421180c0c032100c3d00380c3e00c9403906410400800040065040708030b20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 731055251 1250 731054001 731054033
    0x40305160501021c03140408030103231c051611130c0e151606020310050301060b0414010c0b010b120a0504110f061c02031501180b090406080a0605060108070201090f 73
    0x10000c0c0c0580005501b9455a201711400c4490303090020040c400d01c1046a0f00104080c0c4250010340d0448a01a125448601118607070f0031140b40101707d20001409a0300340ca500d40c45c0440c8016072040e041c245001407417483c0350820b0242c0c103588243c2500e21103501602e081e4a8151716064103c0681d1014050a4000036a950803e11001e004000c007400d1030f21420010580520409a146e0a00015842c044142c2d640040d00c40e80c5050001c024407003406080d102150400c0001d83c82251800005036030000c0b451034000c129109600000c50710302d010802802c0c3c640c5522200d881c0c9990f5031082079040300c00c203a0300030740100c0c0000c0c6c3e440420f203002ca49204440d18007400060500e0303018040a20143d0204080034009600807003000042a200707238041f40003d009280c0000ca030500b160658948040303601880200840028104100752a9504494001c02525045800c000c426003000401004140c490380e001803041e1005c21941c92050040d5403c10342c100b00d01100e00226a55141c03940000025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 731056501 1250 731055251 731055257
    0x21009030b0f191a0a0b04060903080903031c0f0f0603150c02030d0c02010501080606041e050403020a0206030109020a1d062718041a070e040c0905030d0302040305160501021c 77
    0x20f080705040680d405040c0c0d40c00840802d0103000154141001110300084d00b140d07180e030805100c10003070316610010002c1100c0e081048a40d07030b185180c002c60300790320030302c0d00100101000418801c3d01c0806940704900381c0f650b259041240020307180a070400c0e070703510f40707c0901703a0020350000000074101c542c801100c3c2c0724a401128038005480c000b007010341c4c448402e0200507075500c00040100c03903000c0c001ca90b40840121420000300844401001008050000d6400c00582d81c1d40042e00f014001c01400101980040c501a04e035030351002c4050107036129103681000200c0c1044150039460f0010f0100e02007040003400b0f541010710450745801c291507400300a0088210b0f0400365809030b101c00d580d03410f0540a50015003498170303180c104a55011003030301445150f80c541804010034150f101d4050860ba20084402040000c0e4400044603141800c2d0021903042c0039034107014003c5a09036004100301c91040042d5140c0602e0a064540403021078800d290160b0406007020419800e46110300b074403058542 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 731057751 1250 731056501 731056531
    0x1a09040203070c150c0809010903050703140c0304090209030c01110601180906050108030a0f090509070c021908030d1409071a0408060405031b1b0405090111031003021009030b0f 78
    0x103180e26a841134034095030000f80341d44030040350481d64081c41180c1c0c400d807242c0080c001c112440d50020002c1c0324245000c0c04010102503510010058001101c1000305240e048070f03119a141c0810000039802082d4481c40b80c801c10080400ca0f5005041e00714142c40c590002e800541e00e01800c56030705008241c032041d034180c2c0d52884c0c1000115148100c90103040c2801c01152140f61012000d00440d14100c844410b015a9140c208860b80d03461410960000107458603010f038942500c0825a0507510030f5281205129030600860318200000180012001c20901404003e80c0d62111a000542c01d8a840131142c220071818440c5901d542e04450a4989291006240c07568400450741001003d07a400c407117507000040c004001018525409911320f000101034a05102d03001c40c1c0c3d84201d403c01281e2030040740c60b03e001a008400c20362040410300100d0342245d9807031910703082c219460300480c00704a20800443d000221aa80b1032442c1205036544203900301c0d0b55846010450f60014001001c07000002c00d18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 731059001 1250 731057751 731057753
    0x6031f09050a0b0609071806030b01050d09060c1b0b0c070203030c07080102070b010b0406081803160c0510050c0a03051c09060212070219150b06040b0409061a09040203070c 76
    0xc0144520381800360f89952001d04004007040f41d12000a0b210004104148608001044c00c0403805402c54105081c00078000c0c40002c01030301e80d0300845000c4242c06240c10301e1038082c84441d802c08600c1d11032507503603401072a2644032000907070a0103040150000300c4038800500341201903001046003a0008045a04042d44045214540101c2d43c008080c545d401090003403c2104030701d180b44c05406000d00160400c0e0401d44002d00c241d070b00174011194010ba501d030242c6091418421103882101d00c09080494a0741401c201140152520030140515008501c401241d4800c505584652810740b000e0f00b03c41c2030b1a20304407034540055803040040f0b99108070402d07251445126901c0854400c010158890132100702180106134010070601c155000409200782c0804a0407840e0b100c9540100885101e4415840c1140140142060035070400c000144c0422114800000361045440c2051306014050b2200110184024a003490301e92040050004420b10b18060f0003442d485015450092080206 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 731060251 1250 731059001 731059003
    0x7110603072c15040f060f0f23040f03020f040507080606070501020d020319290411041505070c06180905072304080714130b030f0303040308060a050906031f0905 71
    0x310542441c3c515a00040800000e08900341c0c40c401000182010080101c0c40540070b45a030104440d000104105042c0100042244a02c06881062130302002519070740c03101145039030f40d2118082070780702e6080307100c680b6880c4c64103001d1540718005554030041c00b9200d050034440d854200303c01c110b13010354082c8100d90342a9414400b461281080d03280c2c214000001000000480701da01c0c2901c00da00c07800285102d4080b02000441508190944001907615a03009100c16035001e29080102500401081d40b4002c1e81e021000c0c0407554098102c52420799902c0307205485982c0c100103181e040745401141080811065482a50b0000340c50030020040074007000c0b803442c4034010b414040f000c014041414060200100300840c00341c10103c000d0134100307088030300245108031a60110241a5121801401a500d0500c050b4000c4044502124ac4a0400c0d28028000c403904450690083c411804005032904e400c4122902429005d000380004845180c523000400d0840440440e00e561030700f0141e800240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 731061501 1250 731060251 731060269
    0xe06031014040b090a030806060d0204030606030c0501080f070f0f030902040e25051318120302041e0e150111070602100f091502090a030209090307110603072c 70
    0x811074032018254585850400e522100180115980380d008450075000030350400501ca03000300040740c0d05512094003040c207401030701c21508000c0c001424890000100300c9001c80c0141030300e000741c0b1031f00325035035901c0020f5020000c203d8030340700045c0c2a803040001040c000c0703800e0506140545008182002180c01090980f04440c85840c0b01d036010010b00c44040f0300c0000040031000311484034122140ca0b01e0001034506882d000c00c10240c0c1d698041c541c402d4081028003000e650b91040d02034204241640c1c0103170094005115003680c000d02c040c0701c103a10041c026466070a5448040c0f008245444504230942401c141035103541c180900ea055000240703000b003003541d0051605500820f418164a00d041c0d040d111000301074034215080c07035003080000e0fa10403151030707c80805500058950704140c0002d5495903141c0d1000c0c0d04120380c00240040410080003c04007980103e40c4958814510f000303000b245d200031620700d0006110f07461440c00c00d0344524104080592f1740409809070148000010303003052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 731062751 1250 731061501 731061521
    0x13050319030624090e0703090b160f02010c091412060f0712090807083901060806040c0b0a05090402030408120906071b1118091903140c1603080901020c0a0b040e060310 74
    0x510080d981c5582552111589840c0c50907403009021104403b14054407407a124001d00c000b0036000d0002d482640c440c0c180c1458800c2482d000c81d200c905240107420841d01050f00c0000c001074105200e40e000b0354290040f51119540101141d14005142e101c0304800c5d0005642038280b00200709004c10081780a081c07040c020080307007032590345000760400c00030308403a21507020300810b400c82010403000c20001c1030f04104403003039050003c1d9030703545501d0100e91501c9004511075200e4404424001800000805842c164030480340c003000d40c0c1c41e02c035403061b600c44003224460002800401d070101c490405007031070505540302d11106c240c0c504000001501c02c6004220181c9401c00c40010405000c804020003010040308020b03172440600c05444c01090b0044101402c03403c0b05c0c001a0a002d1420100552804135030500400b114103a02d07460841407507400750324958014401c03003074007d01900c2c10380c0c0104112410780c034481c1d1030310f46052064091b40384014112075040c003170114000007007001409100544 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 731064001 1250 731062751 731062771
    0x14030a02342d08070504150f0608010e0705120703020c0c04020d2004181805060901140a0608031603090e2a070b13050319030624090e0703090b 63
    0x10280c9003042d102205840c844000c1d07019001820031441c3d4000c51403c2c25100c0584000c544044d01420244610fa8143d000d0350308243d0035040010420750043c140380c1038421002502c001c42d1588171080303c1070f0151080d560000c600040100301101d0180c1d0003080003880c03031410f58980c480100c0005040341c1100c1100710340143c44094a0503159104017540c11441840e10740705051a04000810301c0c410b41c080030600c03016954503d162880342e20702044040503039003c41100c13454a08002000e000e013040146040000300010040f41d01c2d000540180415078a00900460502c803203000d581e030110000010590030312210040119546c1c803443c140c24403444541e040000801c0c60f05a84503038501e1940c440c1e010724401848404006500c4840e529041203010034a0741d010511400c2203410740c807c40b4020f4041c240310a8100e40080d03010b4100f2030071180c0420200a0103914449000756204040203005c0005101c44001d0200c4d030b040c00102c03038000d00715241c001101c004070f81d10400520f00a031809001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 731065251 1250 731064001 731064029
    0x1111e0102091c0308130503190c020f0102010605010e190b2a0a020a05090402040b060d0b030c270705041e0e10030503030112050a0501021614030a0234 67
    0x80350403c5151100060100c18500c109000140c8000703090200c0a0130042c3c90074010071116040c03280070001e0350600300c400741965918222071030b00502721020b080c17401c1740a80752142c4014010b40c0103200c0c0030100d81d0107840d03c0c9200d00040080290401e10040c42c0c90106d41182c0700032554500e25005401000c0c0801c10580300c640304001a00c0c0000f00c0e42c8580080f503840b2060100c01600d40840010440c1c4055410140c04e440c0d520000b00030307040c01243d10b9000342c00860401c11490054110301c40010054040d00c0300e141e80001480480e6000f82c07031180341e5109044031a8088c443d54103c142c0d1118603440d0040c01c01c0d03101c1d00e00603d80c903409450703020711400c040d8042c48002c0000e0040c64004d0042c0c1403403c500c91969403419140d000500c24012809003250181d0140441840002202079201008551f10350342c003c16a0034070741c00306a046d2140f055107803000c0344000c0d00104480b00400160000c107014100c400340306070540102c2250410f01070f40301c100a10616807010821002d0020300c1d40701c0070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 731066501 1250 731065251 731065267
    0x20703030206091606110f0d0306051507050a0f1e08070b010608040309030305030a0b0613030c051806040b0121050f0a020f0f030c1b0309090c0a080601111e0102 71
    0xc9440c501503c0f403020b9400c41010290744600403c00c1000321510f9092030805691a02107403030900201c105450183d002c0c01045201c01541940728a007500c4d000c540c4c00450f092251501c0b0003a014105000304141e01c41074152011400d146490074000d842491100b0110358a88424078040c205020221420325010841908000103210038a002d01010300c1c00c0c1e41140703041d407801803881d4010300c009410700c807001010801c0b1700110341060152800c01f400740c5039201018200d51503104000d03c8107840d00000840301040c0e519000e8048492404114550b00803a00c6590400c40289490315066040c8100640400315500c0c48071200901480c0d100c400152a10b05100000ea1036a002000c89004034410044000003030702c1401919400e15581e0726a9403030f0758500d045003030340b8481d0014845001304030300075403268801c000000f84034031801590311000948030407504070418040c0c0340c41e160104200400244d580d503c03880101040700f944400322f07141010340841103210301440000c03040e22039400142c0d0746 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 731067751 1250 731066501 731066503
    0x50703020a09090c12030215040309080102040b09190e0a0c09031a0a050106090812090301150e04030e04060f14041506090602150103212601030209060a03080a03150906060207030302 80
    0x4801003040200c141200800751b03034001d4640500d8000055142d0b09580424203051041c400302025000410003150341d503845640d0440103400103180648070303180b089001c01412a44e004d0b80c0c02118000008031601d920b40c1c500c880040d20340e0401181c10480f07048400408660442c410900c00102000514202d0a000b1252002c2c4d0b03c058020a092100840c002c101d401d01c00200b80c03801c100c6d040c000545404c01d810010b4058100c24014001c9904a14000f14800c103801801a0065202c2d03100c0d210121038000070b0200703030344546c840d107403842190718001c2150301d0206455112510008000190180307802d54032241c0c003035564000f1800507405038400e000081d0100400c2e91401e003003488616040d03143d0f03583d105040000040d900b05907403e091a0041d4203026100c0c2c8003942d0031000030304005500c00583c0c3c401d004000d100580c8143c0300c48001c40e141b41001131250050b039400c400d0840c90301052403016006400e400444041012005000084100c21031040c02c000e0102030303010784155441c6042c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 731069001 1250 731067751 731067773
    0x60905090601020d27031a071d06040302040218040f0b10020a1112030d050a0519090b240a0308210115080c040b1206030f0313030f050703020a0909 65
    0x2410366001420034802c40380c000c0c07081052481204140710005c0584001541c0c0105140d00042c52070503080410251204000941e0b4814640b6550302c0c054118649062100340c181e81e00140e400c00c038208000d00260400d50004c000b10540a4080b58048641501040440300111880301d10310f41d403007030609114908024901101c0205100031304021880d40c82d145800b04481c00540d1040341e141e1858041e400050054540507641c06004000324a4107003006400350000f02d0703145000b9400c0c880b0f4486c03000c4603403088611983d000710300100c2c650760b218202003a244040300c080c102841d640524a485039207070306a000c081c51042581f0f5484003400003101c032240003500f1044907100c4020b00140481c007420280b41c00211000e1418501e1a11043d5900c0303601e10941d00500000b090021740b005c038040c900301c0c0040c0108410380488a0503180409071980303d004150b0381e5a07101140240030004550140440d40300d0a002c4c00550f841d482d5aa400204004010303846000341c1600c0c0c2d070122007885490a02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 731070251 1250 731069001 731069011
    0x14010f032c0106060e0906041551030c0201020c1f050c091e060702040501091409070b040b0903151f050a03020907031a030706021621031101020f0406090509 69
    0x20040102c0f101d03c00044286c00014040c40c0503e0b919101d440f4a0f5068050f01001132811541d008400d00d5140c0c2003c951407031900610584451a00209010000308800703e208a4035001c1c4e140508280700e00c0407005070805109440856409000380d151204003803081d40d21603c2d07002034050a008805aa0310107641d001400106144000c0c007641c6120340b5030440104684001803c200482c401c0d03072000480a020f20100a50001d14100000c145a4060352000100d02150000702d0303429546d031803402c2d9030744415000f641ca0103507051004100c600c0310580944400903008040e90300580050b00d000c406518100c0c0c043d400c05500200f0080f0103500b100144016000c26981329a1b0282513070041441084046e240031700705a42c45c001c0e151142465000c046a07010014203a44200c0e070703203040007591400c1b428015103021300c64110000d4a6604c0600c03a0290120703c1a800d02803c1e400d8500780d80b4254521245892035400700100e4458000442c0100041c28094031880000c60820041c02110040108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 731071501 1250 731070251 731070257
    0x13140d1103031b25060506030616050412030c0807080415020102210c1e0301051801030209040f0507090204150908010e0709020912121803060114010f032c010606 71
    0x305102c449095034040356049940010080c2c0da454500e0b403000310884460074100c807040b04c01101001088003d0304440e000b024200c003120505d45551034064140140b9441190119004000402c24040e21810303202216002e4180b010404209032940d84e0540c0c018001100d03215000203050001400f90400382040350141d01c02103090004810394200c80c8194441d03038004504100300020000c0d4440e800710382404442010f8480c4c25170f8521103907502e81e0403c1c001d25115000803954600c101c00c00303030b80d043d0480740c0080c124010703501c5588800f0b00ca8003030a107058503240510303400852201e0017400104003c4c03400418181e841c0340490001403502005801c000816418100c0500e8242c00000380401920400a00140e82c0c11032200003d000f20304002c1079260704d000744e11003444500e000001814505440c0032042100a20201c00c064503600c09015811003100508141d64417544507a002e604d401d00300307040c0003d68401d4084da003400d10b052102c09000c414607165181503018000e010303041c02400d041c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 731072751 1250 731071501 731071507
    0x1208090601030b0424020c150703090506061507020907080712020f0315041e05060f030313171914460204050c0c0d08150913140d1103 59
    0x951402249903003c1c1018045e04008481c5c07a00c544050440c4078411031044d281195940701e940181e5440e00c6005681c4008400048002000c06000b40111100d156000c030141c41c440d070301c2d20304120300701156409055603600300b2b200040052f121605404e014081d151980c4c2480e10744900000c1c8180c00c9001072212160060004d10300c3e400045056035085401c07014030000900b880d070046001010414540001c0d49540390700024006c007994421401040207865a48000004009041c1d4070b200d15031001d629590300d40d000704003440d055841050010300c2c50040c0d0308401460301d0341c42000d4400c81d6040e100e114145c0c400013510b40301003203c005011500301c0340c401010718070500401c401049021905014901301004e2001c40c0e021047c1048499006208000a0801052201040d00400840d0455225001071710300030a0040130708620034002d1500030800341d01e40b8002e10204038400b030050054800c0d40044200040d0302c040d00b1001c880030f02402400003509a040080c00c0b044011030f21542d0750020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 731074001 1250 731072751 731072753
    0x3020d0b151b15160e0303030a0605040e0c182503020a020606030d140c0106080708071a0c0304031e02030a14012009040e030c03040f030201081e010302120c0d120809060103 76
    0x52116036004c0782504000c11034203810801541d0030342900c0c8455515000000800c58151002e41c81070701921000c0d01c04000451800404555030201c02d000540d001c296801c04025054001948561200c4403501c2000e802880c103406082c02d890110f010404170390003040c01900355a0401c00a5130081e001c500919202145071000713040c0368581c80107a0181080000c40d05110310007500110000e0000c1d01c221101150740b9054035403940b40301d016141ca03924030140524000055502038440c0e110b1000003542c5010314560314480700304d003852003000036003100651040c0503036030602c00307079940500030440480b82d00d024004c0780b42100c0c0c1109408000c00c040003607618a0f029070006443c01d400b01550700180d1000402c2c909407640c083d1000701181880300140110314004856007810840e40301b070721904125100c924040700c08101c8140c0c02c2d4403000700c00c0010005803600c0030160b040c1d8410f81d001d42e1440002400440e51220380c6e041c0c1504c180000b02288404150310501c00c941c082180409800d00d5411 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 731075251 1250 731074001 731074033
    0x50f04140109050615120708100b0f0306010c0203010c02100b040218040b0d02030d09060906140316090b0a0804020a0f0503060c0d06171b010e0105070303020d0b151b 73
    0x1800b610101070303580ca000880a0702d0300002e1448091040c0035480e01d940d120075a000250404031000e05c00940349801054000f009a120032055400c0301705442d04104505120210a03040101602d040115640842015850a1188103c5401c02c4d902900c01028101c20040c01c0d42c40341b00c00d05014610400c170307800d038403c0c1d251000b001a24080320b0126140c0b15940001d42d100a82c000069414028042801c10310758110204000300ca410791650442541d45280c1070780d003a1480c020b00c40140300c0400001e65a070140d030602d42c464850605021080715114401000c05400440303010000c10403a400307110551400355500300040c80d01109004071503007490042500e07044050902c201549000c200c58094017a50303000320020784000d84021160700348540b24140d481101a103190302c0c40c000c60104e5105544514407040c856070b4180c4070180b80c001241d804070b000794080484c07500d1465036a11010501e6a402c01a400881d20603000c207611032465032204440b40c0c1319001184038541c0504076007a0700000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 731076501 1250 731075251 731075291
    0x50307050f040b0409060e060f0c130e190606090504060b04060c0215091e01036f0803040509040605060303070b072f100c0c150204050f04 61
    0x10203842c0421449803400103e0003034502080002c207814100906d494019000040c0c6902c0740074218a44e91880c0c03902d1070b1200d00c500c2148003000701520441030901c0300d040000b2001e07400845400c030740341007010070b1000e01c41200c030940c102c0d20009856140030443e41c9014018000030b05115450b240c54180380440240402014a00090141c0014441d159403800e80c401510b0802501500042100c3d81e0b1030140c5400b260b8030201c5e2404640707800d044a010041d241c004c607188095101d00d0b55003514850000c000d24403c400c05651421441d14100e44044441c40ca103001e001090001e160100110350604110405103904640c0490740180020401580e9214003140c101da048100013415032501d00119096104009020300348210203414080140c0e40b00d281d02c0c900c2220364464500001d104552500b4007600c00001c00303583c1d4080d0032000840c11055224004115003400c00f422a100c0d00d541701d288058980c1c0205468540c00303c0d08000c00c2c02d0400503100150005c440801000d185c1180142c2214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 731077751 1250 731076501 731076529
    0x24060f06030c051903230415050a02070203010e030405010206070512073603020a05030c210114010e011d0601020a0b041b0308030405011808070303110405060f031005030705 76
    0x340e1250645008903006100301d6130300c403013050640303006a840004003501a00030401000c1a030300e60f4401506540050380d0425000b694801503602d000c0040102c1d501c0907080142402c031b0850750030030489005a40034411508070041910155448600c1d16001a0070085c0c01461001802020056030150541e4404000e600c90618104148030210309a5a4030f07812504030b1010139076000803015540807200304915102107038400c550a480c007613100d13003c0c181c50320303d8089001d40001b1440040010724400c804080c200350610b500005164120812214551600381d01c4080c80c8811400184615240c1c280c0703140c8072004603015450305081c041c0000f581c8682e43c150180041c551000450308100140d250f00d04003410011b6419005c503101d013840c43d010761040d80c080b10036600c0d091002c9402550f6001003c501c5402589a80c240142c5840540191107445039044071080b0800c008559030b035031400588200198030780f9458503840c2c40c4d8980c9083d984642c100c1e61103940704201c200300395a03c0c02c3c0c0400ca00c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 731079001 1250 731077751 731077757
    0xb1219062103180803090a090612020405060411071410050103030912030e1e010915050403080a050906030a020304020414040203101d120702011b1104022524060f06 72
    0x19440d81022607900140c210400d011446000d400582d21000001030701080b581103c2c40c90500313030b9601100c1d0842741c140c030403907112500158040e4003501e050740c0b081750f0080d0b01804c042642c07440300c14a12055404004200d640c01c0750b160b0a100310080800000004010843c2c08201e654150785001d04600d42c14031070000854a4003905000709482100507400440014001c443c004032190118203807600d481c5461800640303030030000120740d039800800410312465501e8140ca0541140c403801566480b01311b1800600c4001c1000d145240c0368000218400c02c04881d0058a0381080d1041100f07666004081c25101c410306014040565030200d00260015041380001604e0204048800c80c600c049031503030324041c0100780d2082c04c0d80c1422402010340078402d0380c441036442c808003d14115000c000710042e1008104a10003041820103900406a06803c42c0000c0d80c41c000c920546407940c00380c0c135000c070303004900c0e5806003400100b0784080f0f00f0381c0c04501e075041c001942001c0010001481d20300c0740b4010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 731080251 1250 731079001 731079059
    0x1d041110021009030834140724050a050411060c0f03130f0803130302040903050d1b0e03010b01270308030403020607120b0f040b0a0b121906 62
    0xc10740204000b120b41108a20305200e03a00a81c00c000e0a004400c844910189100100d0240152910740c8880d4130350708046001d41151000110854449515101e9800500c0c41081090f01182200e07442081e0351030803035a40103100c050000500180c03480a010700b06040d080c04107000001d0303c4c0a0302d80003814410f80c0e590340c0b1401c102e07007881d1400a6004c40740b20180070015252400c20342c00da881106a8680f551080d001d65603508005d0360324071034407900e0038168011780300500c0149040d4200090840c000e10380503081101c611400400c40307550f24405401030300e2640450400c2034014107601818201140204041281d880018020364841000069110310060000a410000031742e04005543c00c0180251a03203007a1601a60708d0308145d441002080014010342d01f245002d002c1c04030545005000c0c04416005001880007074401042540d5105500381d80c049104043c41014040f1030058601650050521048417550310079410320040d0f2945c20000180000ca000081501c81c051441620040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 731081501 1250 731080251 731080279
    0x1030b150a0504020f030402180118020c0c06030702010c08010503010510030f140102070302060121022209140c01090519060f0e060d06030213090b0703180f0b011d0411 74
    0x8045480c68000b107034060f2005c20031414860b881009184283c0c801e4401c5000d4114107000702ca5880002d115482002c1c2c06400700300e04202442d0054110a01090215040008240c00241454104480403001030303641e22200303000e869002041c103004103019002044a401c110b9114504d446260102030851482c0b080c4080402003051011128401124000c54488605240c0291101800e10907200c1c0000d650103013907031000a0b03603d00040c00390700500c0c40c03044e00030845a0040c5800d04001c030750030144d03603505200085101445407450034050079000d00450310042002504011098011a004002030b1440c4040820308009000c2a1215810840040b04071824216030401907952035a030007901c0407a00c4502c00c0310a4005009803442190058001e005007041001198a2000003a050b500080c0204441e42c0c000d501c07064000840c000d200300d1051540d01c900500381c120140c1191040f015400410075440c031100b581c60200154000d0407040c0c209601c0e4580c5414210300164428601c00780000c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 731082751 1250 731081501 731081509
    0x9140609031002070605160f05030f060d0516081203060a05151e0d1103040b0f0612030c06090111070b01091a0418020102010b042a02070819060c030501030b15 70
    0x4090b80301c0100103665072050b528044001e894103030f0b48070586900d05180d0224050041d00b0014040c110303079031541d041d603075038444001c041c6402034020342d0807188450a00002c04c0d810712090a680101d10001609a032070000c41078500f000c10095090b1400d020310a0086aa0743d180390902100c900320342400b00070340103020b545110720840d12010f5100817151081e00040c0d0145000e40008490590100089100c03000c0305005072104031801007070840c05000250080390030319002900101c01809001100100c50f049a156500141d89941242c1c881c004010350003d007401400101c80f07440d0601c90900507265070b5a981844180101c18aa586a4145410301390ba041d604208606000f8014072001211490007003c0d0362000c4800c2e07005500344030b84480c0d5030600d8003132080b82007403c580302103410300d01d0800a812072210907401001c5014000c03001407880e004120350000040500394085040038240350002c1210f0821440c18241070800d4010008100311240300f03513103d4108442d0f0080900844002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 731084001 1250 731082751 731082763
    0x103110706020d0e160608060405011212110a0803010e010f0608151519020c06130e1302041b0207050d0c090209030f06090307060f02030c0306060c01200a030c0914060903 75
    0x4130139148503184800c1904500d030710855049801e203803a90002d41c0c4510040c001614001d0103030540c00c0480910702000120510760349508680c0c0741c54a200d4032501e000302941004d03205a0140d880500200043c002c80203200186030040c050440d41c40403940c940034024103001d0004001c0c1910a1810810312400e40300c1200200386413003000721582e61151340014608041401e004840014480d024005800d8100f400031903601510210850444900d0b0036030003010218024564202c1b42d05803010900161114050100521b80705610034141c41c5003480001c3c6056455070100e48184610f21030203022a074550145803d0780c580d0800075075a5402500402c1c5004180c402c4c10025101d000d0400261210100181c00094803c1d002400000c081c41b50400c02c1e4041070300e180860500400c00b280c0c1a15000009010a0a1130030002c0303660800c0d000b4511848400c504030822985002985c003101c558107106007a0402d4650820010315414241480d400c5401500c4e8213004040000311b1010f00d640030061 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 731085251 1250 731084001 731084021
    0x50f01080a090219030b090d023301241b03110a0b0f0702160e060409020d06020f0901081311100c060e0109030315080a0305030c0c1b030c0103110706020d 68
    0x8a146038000d0f4080d44003404600e80710079201021b00d107002c1004c00701d003c9000108101d0681c003c01c00c01c0c005649041104030781c845401000b40506408095482d1240d03002402000d005510303c10303440b034500000f140c000610702c500080050f0780b080b40a074200d20200c0d104942d501450161141a8210140340c907001c825003002e4002c0300c0c4081080f21107104000c6240c42508a6800c0e114022403a902c10484290305000e21100c801d030120014a03181025488a000039000901031440002242c4815080340d001c0c08102c48060400a4440c13041d58121a01c15044042d9403501c0c14164134a4452881c080c60507000503118188030722400500500c503000314826650000c008206100e1001607044c000c2c075854404030f020034100002803145008950140c01200d0009014001da8501503404448944c002000981680001d020460030194100449100640e018240700d46000c01e0004051070450203081c614105400d02460362003a40c4028190f424103984a0340160300c62411280f0f0034041e02e5803030385c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 731086501 1250 731085251 731085259
    0x30a020319050f0108121611150403030305060307120213050a020d0c1e0804050d0e01050409110a030516052a0d0c15060608012303030412020316050f01080a0902 71
    0x144180c04405040844c1214011011260200c2401d800320109000307200c0f00400000c0062010380c041640040300500d100d0004111050741002100c000c035464215820030f40001e0340d10000c01c0f025041c1000140098040b1910344084441c2550025202821031304100113203544807000f0444a80054040c0e40c10246641401e0000e1106140c004080102068451a00009810311125018080c42c0014001c42d04680600345880d0105025142610407000341c50401c40c041100144003a8180315070300000c411903011503601d04110030014140c1d50301800850f07681008503002904c258216003251b5860f0310084100050700301e6405040040c101c0300b01c00c080b0b81c3c011000144681c40d40105090311943c8104c3d08a075083d18917007864412200d50b0702600700800c0182005000451007620044e012500c0f110360a03000c4c03554240464115042580000030900746092400114a82440f039140e5590040314007442640c1341c000046d02c080c042e541407034144079119001c100100c41540040070840c1d0054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 731087751 1250 731086501 731086511
    0x319020c072111330f040303110f012d060e0a0c1b0209010b030a0e1f06050312030408091f1d010215010312020309040614040e0a08030a020319 63
    0x100c0e6110360321907840100c407801d1000c02d800b903c5141c041001c50301400c03080140c20103060150f440c10b42102c0c60b00103010242e0b4040c04629800840400100040c5110b039440c810180500906680b070403144040045d202e0b41010310740c541784c80b483c46035944c180380310813411150342a40b10001c1d0000c08240e0440e00f181d0500310204024415650021104060280e5450035100c40042150107441e0b5800700003580404034800402c940401400a560400003200c800214204140000c03031412400f001c1300002046145400c0f488150030f0700c20701c4000c00d401d03030141c4407041c2e841013488603920005000925591000c01d030503504d03484820300803500100c030301e000281701c002075100a40b03980c00620290009603a0000b0b050305551002c901034128401d00514002e2507425903840c0e10b03441c0429042c40c402c510081c00740c80646d540c1c40c05408002c010760318140d5a00425070083c401a1a80903000d00c4d04c0703038024081400042d400300200d0f54480700100d40140c41c0d4031a0444000c40300314802030401c01074104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 731089001 1250 731087751 731087789
    0x190611160503130f03080f07030509100c05070503070e0c07061d071e240e100512090d080412090b030708090c150a050c0a0804061e050319020c07 64
    0x1000101001404604016070316460340700039007060302004160010074850007a5000c8028068448c05100b82083c60502d451400801c2c040b1140c51049c84c00203800725984d600b405024070461001e082d080c2c014054941c18000004c1e01c08001403c0301590300c0340064100d043c0b16487e4003503901001501002d5004d401d903285115075588080c002e07141c00c0e00080c40c640c0e0024610340c0c03040046036915041c00031a00c0500090007502c414485d01c040602001c804205e00d1a9038108111001481d20780301e4a03100c842011030300f040708000500000155101c079041e02101500442c1031940244e01c9500c1240b8800c0744e80044818049030740c081e00c004080070040c000f0098121a01c1c030710070142001101c260166480811001d81e000905481668204001303c01d10140b040b401000c4070503030b0a0449800014a0342c0c0c0b0045070707000e07070700040001e00c000300d84007841c902c81a5541042c3e08203150203070660070845042001ea03c0c1d01c100750940f05a0009400250702c2c0b050000400400c500b0511350351051328 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 731090251 1250 731089001 731089003
    0x501080601090506040902011409041509090506130c05190e010b03041e02100302070602070506090c1c08030a1e05090123150f030f0a120306081906111605 68
    0x400c2c010954a103083c0400502141800d02c44c004c50150160b4542c00c2a008a240d4621258441d46042d60401d4441596002c5280000105001072001d0100041ca00301281000d5003007041c0a0640e42d5203041e40301440c408601c2c80b10081c01616002c03252061a4014076501d146c00044a6001e07130f003e850b48200010b00c2e81245c4001c2d40c815401400d41641c41e40700f00600c0940b00500c08002540702c3d040d800d6524925200e0742c06040a02d00c0f40720010302d040610780342c07989840006c1740e20041d00e50002421001d9410304124100807415041004900891036a80e006183e002c01030002100e175544107101c140c0343381014000c111208100600b00202d040c40300845011345189203241c240c40307462200481000d069840001e1281c4600c6003403085d03044540040061070380c8514055070f41403060321b40002035404248250284103101e80c1c0c0018101445100281c240e590607440b1080075048500c10b00d81545601c9281000c0590150001403c20041c0d1003482c5507001c0d120030302c2515410559040d081003c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 731091501 1250 731090251 731090263
    0xa02030c010609060302010f0f02070e090f1c20100207030c120c0204050114010e040218030d1115041a1b120a050c07080403030c0305041701020912030a0219080409050108 75
    0x1000780c0c4c03810048c0d80440c60544100411340d0220005a02030142041080550440c8541200380882075603039032640000314a00e000011030a060996800a103403403d0a60070146034100d600e20700c01c080c030008020950700c46d03c444031170710000303021900004d4200c01c1510504240304080da001440501148200340300510302440e0000803030040c0d03c0c01c00045500c01d03003032a840008000503580d00c06a054103809000c06074000903403000700080e4401101100381e500f0302605401402540e55008180c2c14504110310700344400311810300d5420311038103100100d030724241c0c1c2184100010582920310384805100c03a00300f21500d0341800300440f012460b0740020201c04410b034020405000e05010b2512400201c107000d00c964800140300300c00030042080000d00401740741c0e0245003e401d10904142d60b40ca00382d1105503e0602651040e540003500e05054a80318054200044117900114103041c0d440ca0080d50700d805007000d4444a000c681201d40030010300358112409440d290b00306203d2569200cdd04243c0d202 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 731092751 1250 731091501 731091503
    0x2b021c0506070203090d150e030a020a1101080c0a03021602150904061508070c0305040e0103150509060709051e031501030b280c020109170c070f1a0a02030c0106090603 74
    0xc00740a01050225200100703960054400501d070f100b1552142d07031011555109407d01498035500c8038541d510180043c409015480c2c0c50750064500d80c1024501020040c40c0d6028080c140801da009000a40c440304d410f503490300d04241001640c0d411a08403801d5440d44171070b4020f50210b85000e00d40e144841000180c55000002d54084c0403c42e125546441000f450480d030f02c00040c00c4a000420031445400c0b2400e1040c0682012403038643c0740d22404e40c15107401d030411768100403100d0b40082d90305510310407941e00c02c405030007030301c80350070450001000c40c1c10070302c101031140c5102e640c424410700c0d080100a0700305070010700320744400002c141c1c0c130171620340c00b40300c00e076052141c040c0020f078009980d050200b601ca880a20380030404444450081c000c01041e28208115940e498000d400128116041c28000c2c3c00c03040655201c811152105107808142e070004441c01071181030400000603c2c0e0414489600b004072020740300c0c0702c8243c0c00c9280d8090802c204002d517080a80000300007031300d64840c02c00e403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 731094001 1250 731092751 731092753
    0x30509040608071503020304020a030b0f25020c061312060e0c0607030503160c0b072a0305040306050c270a06030c05070f1e110a12022b021c05 63
    0x3569514403143d151101440341d14441005840311624491081d0300a65000d403000380f01d40b00082d241c1d03c07581c030070001c201d58501d007907040e001c10710075025029440b9004501400081507002030305100001c4d180c0e0214030013a8040c50b004100340c241c00c4000c503080000f80a410f08050489159428404060841450f0040c914025403250900505000c070840301114bc044d103c5a241d900c0b450540001002501c07a88410801c0103412080014103040406d80075600c513554160350400d03407500701d20201c10b4003c0390f500709004c0040d071000000e400400b5070b012603401020001d0103079074484081f0b405201d18003920f8511401d001c44003504d5004101d0365414908191340e10031300c9a4860005804640c0c8a50611010071420301442d00010b02c03001b00704c4a40b41c82441c213182d804030481e0502c5d010041840c0300711601c92190910058070306000c0c0f00360004109090240704041c8013034000c922511800300d010f03409443d411116141c007400300d811140341c0c02c0c4d001d8004072600c100d4500b01300004100c440102c8139 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 731095251 1250 731094001 731094011
    0x12060b0d24080a08070507150509040c030506031515030a0c080111091305040510051005040b0a050a0317040518010302040b0a08100b01200105010609090203070e09070e030a03050904 80
    0x10215507032803005980e80c0d0300080845940c1c03070300c6100898121510468852040107408100d88005000381d0b80908a80e8581d145c0b03c8220b482000103886003c10b440d004c1524040820140c0d64000840c054004404046a07000362a400c40303c81c40e413400300034100d40600c9229482020406031170085011115203100070410319000c40f01350302c0c0c03e02c11988900d502407000d1191041601890b130102d500944600101c4a59480302c80707040d0705488088031450350303180c0c3c020820000d42c00d10b030040e07440040c8100c804d03280d6941090005540c401c3c0e81e010103001e140f04001c0e46e07a6490040021900540f100408140440a140503040110750003404128012414542d108c0c46c24100841c2e1030090340d81036006015003d0902c40104001d014180c610341c100144917040d9980307486490101b50307901000d4400480e9543c14040e01030005810795001c2c2d605144100200901c1c90341c445c004aa407944202d54209080d15028030884405a400c0700d1640e05020302c0c451203003016001002041090015942440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 731096501 1250 731095251 731095301
    0x1b121201080106080d0e0123092704080a09030f0503031602060403120e01181208061507030804033606020c0a03152a02120306010f12060b0d 62
    0x2c26a0140d10843c030590707114641401c8864000c6a607106020340601d8408240301e160910803480c3c1c0002c0081801c0e42d140007031014081d00b07080031908011706c100340c20510707222001001140f60751070081002d031020101207002d503060707481203400b500150b4000000100616031401c040340c0340c0d4010781c1c01085060640600d030302d01070700100713015100740d4241d04c59081081d124070b04d4001030405051026030a551f82c280c0106110743c0707038030700707070740c12800b03481c4091070310000b001e014250020203818140701d000b0f5480000b4200d11071b0021280c8259051402c80c1c40381c0c43d41d240070b40d100c0102c842c02001c1600c40c0100c802004400315603031105ca4a0007a0b1044005540e40c41c00d90712030301141301541e0403141c8640144040303111003e04165046008800181403015184107060144c14504010104000225510080c0c0c0d0704105400700a03400542441c07860409100281240012003102c109000508810041e0f08609502c9100145500800d544c0d03600140b000c00802418000850044014003840c564 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 731097751 1250 731096501 731096503
    0x6061c02090102010f2a02030d06060201020d050705070816150507032408070308090307050a030c0603050c04121412030a140108060f2217030402040f09050c061b12120108 75
    0x2070b101a4400f000c0c2c1b56006040c21415044000d0005c03020191310040100d210b243d00c0701d200342d1000b42010342c001a03d9000c507082c0c42003030f60000303030070a0100001440354001142c8240210f80582030503003422290f00c5542d1422202079081220344903c0103140900300410990981c2203585c41d030610fa03101021041e40106105207040d481d0017044680c0d44000800e000040c1c414009058261004084441442c1c3c1c51001603200c00704c50300119140014644100241d4ac2c0500820740c1040400d0151401c040c280440c0315181101c0c0c0c400582545080100d10718500790910050150f42c207000404d81d40c900e01344080d80c000d0f1001040c50148480740e000000340e00070010895500480200798004101c1d01c13500c00240000c4081010352880184540f250b80000e0b03215107a02d1a070301000d480309034a070300c0e007030042004031203000e0120040c0340e00b8502a6030000c2e00118030340b4400381044403000c1c0ca03540070201c01120b140014004c00c405100790031010122004000103403034140d4405003030700c06503a01c0b86065 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 731099001 1250 731097751 731097761
    0xd050a0c1212082401140a030e06220f1a010902040f050619140f0703170604020c06072304030c090b010507120c03120218010f050405090c0306061c02090102010f 71
    0x40300e100c10558004c1c0ca451a0342000820030707070014501060420b010b01c1c5040c00c80c0d07105c2d20700d140110f82e40d50341001c104a014020203920030440307505100c0e0482015403450a50f080d200006010815881e031500030003485d4055174002684a8803042c000790385680c6083c2c020b5215015200200c507081c440000c41e031400100315880c5002203400b400b90891420020340d0400d00c0c002c01100c08010502c0307901e9502044401400c0b40780d0081c0d070f906000c0031440c680c85001c2034003c0c28a0b07000e640100001e078640200002c40e140c0108052414180360501c0d111031012010400c03940f0209010006400800d1040c170041c1141070b151251000c01400d03c01d140195035a1081507001054101c0d140c03c65000a07000344102e032802406800c01c0c02000e00c22405000c101c0c0c5c0045142106940980080d0b482542d00c540c00c103a61a0302810840c1c601401c210000303451800003003210b80700f214008000340b0992244020748900c548107046900a0b54041240d00d406900040c403468015031900443e542014814041c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 731100251 1250 731099001 731099011
    0x60115050f0c010e031305040513050d12061203020105090c011106040807110a030f0c0f0f17010f02030115030b0f060702010f020703051b1f0504050d050a0c121208 72
    0x1541e2500300d10008007106a000b584207084030355070700c100e072004480081c030051950482001c115a00b290520741040200d407000340280d03140010400d50000002d00005001c04100d16608140c9603219548210a018000316044550311040014810b810517405401a03800303040c1401c1928440e80c00310004650400c81c01d9100c03004d03a401240071502013218200101406400740c02c90112411500010824200740750f0300c00c41d0000c10700701000c0c4c280240c5801003009000030340200c01100c6d15241e403007a08140c4034041d01280b103101c0c902d1003072000425400104000c1c12103200350f442c3e40c5e482141070b166504000118006c2400e140e250f103a145880700d00008906001043c0302c3c1418055001100c9145048279404294400c2e00d201002044d010016030000001c08142c880c0e1191a003000d000141d0520024061000482c19000b81c04540040c02d0f60700741d600584050240d03c5142c2049413429400310005041c1c5602c0301804200b800c4011000603140340512310b140d0485186040c1201c24480841d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 731101501 1250 731100251 731100257
    0x70308061915141305120d0801050114040f080106060206012c1306060806070f0915081f0b030402150903060106080a02040e010b07020a050915040932060115 69
    0x402d0003640c04628000100901d1407900403401d4101d0741d4800d8595216040a402141c100c05040045c3e00d00f015010020b503001c10003901a00148050240840d00103004850600003101d4030664201c83c03407000e1350010035039100500c00341d607550500c6500900582c001c03080180602d0300049600d200386091501031f4034440e00482072000054100041c0f00d440504100700810720040d202c0c02003800c60007224050074181002d086941401c107805813807001c10741290f60034003409910070407080f820b44120001800007420011815034404240c82000c66079406001ca480c00120400b00f80305000030302551040c0d109a803004032200000d4003948160040d0480d05078513601100041c40304c144540201c94000d0310507034002d402c158845403603501d0350b40300741c1000700c6140d070220304181945000c4030020300030042506c00c44105c8c1000225154201c4020003964007441d1940d0314102008200c0018480d600d0b000428055907806102c0024403e00f50a00041c505125140001c1050071120504161014040e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 731102751 1250 731101501 731101549
    0x5040501050607240222080c01030b03190809031c0905060403120309050c1003091a19050c07020d030224070e1309050316050f03210a1b030207030806 66
    0x244014130040b00155003034400d00d4007031210482084000b03040c2c522043e443ca103070801c1d00b0f00740b00d210740c60710f1240f401c0356040600b8615031011640340414103109404100e05206102486402c01500a20031106100d400d44600c0900710745401034682042c0070070807595109403901d0340c1c5800b04000c600843c0000b40c03a0042c9241030801660080e40302501c0b09104170166114018042d0001e510f003000120365601081e00d42800200300100c00f101482c4081c1da03602810290b0134404009507031441150868a4419929004156402ca194040d01c3c485640144407000780e21903458000d40319642054410301c00110b141c10b501e0400303500c070302846c45030303441d95240b0241c24402e07010410410009041c0c0d2001542e2031102c03201055051000301902c050003204000720207040d1a18500e80302030320010881d540c106029600c6086a11040e02100f40c695580c6802161540e042008c02000d1481c82210461072501e00903043e43e4254000d001c610b4000c0c0c5600d086690340005110700f00e0311400d40c168043c1908 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 731104001 1250 731102751 731102783
    0xf06060405120f030c070801050a0e0a12090302040f0f0e0a02010e0d0c08010203270607020703022b120e09040c05190f030305070b01050f0f090a2405040501050607 72
    0x2c2920a1080342e0701d981169061100c000348141140e212038204a05074102c1e207818010780b02d090080c82d0700910b441200304034456000c0070560f240c16210030002c0404031103003144508c0c80d01c03401c0c2e503001a54008104201c100344400c2d030f0400809142c3d22425483c0d040003103580b0b071681c01040034254160180c640014008110f0204066031100a50807109030a41c0e400103e0910000d2000c1c44c45880095421441400314600c000111407070b0740150b05055000c44100650103a002c1140300440790305450500b2606445411000324200d4552224001591049101c0500001681a030342340740036030b10340c09107050444041c0b02f000c002c21540038014409c1e9541c01c00113810f043c0148800c09002403c490801501c440000d01548800e910503800248085a00c0085c0040c07055403500411042355005080d0358400e0201d03100032543c4692900c19001080003030382d59809074010b8804413240320400f0030501401c50405400000310b00415004920f46400031449040000c201d8040c40d8000e90988400781c01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 731105251 1250 731104001 731104009
    0x30b0f040f0e010e07080708030429121303080603010b09010302150c0a030c0303050708090d140c1504050c030f1b0307050d080309060c2a1203100e0f06060405 70
    0x4081102500ca5911200202c06220a11034041424024000f501500385001c1e5514540300640d085032241d0380040108000184103c410400300401d031061070184150010143e18150048141c40185850450100880010070000450070b6500c40d0701d801016445803000d040c22201104929a00541048c0042c80035103400082d9400b0240c00c194958074081c0355074543d81c145090750b68120081410b4121a008154141c025294490b00c00c1c5000c01e901c0c070300302404503980e8031400b00130010701c5203000c1318120300407040c0c1c100c503051030300107044405050b0082071024800c901210203861600a140042d1003615011559003c400c10540080c22950117101070030410351420190b840e03251060400004240d10740410345800c4c02e015902680e1603182c251140ca0801c04014201c00c500607040241c00c210b00b500c603110310303800f982c000d1000400e0221103000320303e00f03e42e2100d4a00d00d04000f2040003801d00c849515a42a200301c568451216260007020003134500d41521032641c13041e0180824012814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 731106501 1250 731105251 731105261
    0x51c0b0609062a0102130312032004090e010203100302091503061e0f010302060f0a030b03032208070b030112031b060f0c051207050306030708010f05070e01030b0f04 73
    0x9004054a00e0002000000703080ca610800000081c90300c0a10f5484503000240c4142015415110081d841c1603056104402d42404501005080c05440700d20412040d11039805203480241c4c00d00022403508200381940c1c9640c20a2248000a07800c0c400c60044240040c02a24000d169400740102541e056508004c09140010800602108101e1940d0110f42c2c0410102c1e0142c1d96080104c0c18080380c0705140e000070b0900400448004c0011001040141c6501c400c6500c402054214252030f01c000b448118094400341290a60520012504031780e001c40507103c1c100e803c50b0320065411a141e440281e503484810a03c10215443c0050004211880e2900c800b65030003882860103820b46400840000b08030443e03d28103480e00b41ea00c4900410080080c82070203c0400e070307400c0403818005038a8503040c3c1076070300602d0481040b5010011544644003000700b00040c0064034001c2c8105420320189070002c0400305d442400050048000700362950227441113003070440002e480240100ba29809210143c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 731107751 1250 731106501 731106521
    0x20a080909070c1208070e09190c0c061104090c080f04020609040e011401180e030708070c030f03080901060f242601152607020c0d030509040507051c 66
    0x101c0b846024600190b604c000c020302464464039050f0b0b50b810005001020342010301141c0d0301070390b850818045203180390300c0c0f5104583c107104000300e0195015041104c81300703486c80f001000c0c24108012251401e00c5903000d001a01c80403427040015214602045613040400e5031014254003041c070201c3c002d0700340f8000820000700050404103a40384c0c40807001f030840d1101501c005100c3c800d20010701845041d201c4188002410540510828115800c0c0310b41702d08c50a00000c00c210400510102040000742807040195003000000390380b06254180a040c000017102d100c1c2955203400c2d40864980454040ca405803030549505d0242032641d10340301c080d1035400400f00400d10481300d11400e2180805070101010301000f44110040b545045001420940d4486002e01849801200e1200180505003c60341d0302e10502c100d0300050b122050240c3c1841e0000c01ca80c0c0e04143c4205d41d00081c035030031100602c22940144d40800c07891383c031140210f5140c054210100004902051101c00c40003031500400544 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 731109001 1250 731107751 731107757
    0xa14031314030a1e0606141003022203152d0518061008010b090f160306120b070206070804030225090e06061009050d0b0a0b1e0f01020a08090907 64
    0x2c024180c81d08600040e801da07103a40c1c1002c002a2a13420440c150184100801012140101007010701000a0352030410501c07000400d940450602e1125817414049072140405400c001c415548900b0999007000c60410361001c1c00d81002c0030602c0b0511a41c0c2c0306d034912580b851615550741c050a00100140002030000c11401c1010031350f8464904082c05098094120b480c5003e10943c5860441802c0d0341526214a100d100100e082207034100048840b20b500c503504075403840340d40e0b90385034040e40109101c0d0003c202403c510400c031410001100c012a000710f01c55021242d0940d95030004464646007141c0c0240160051207000c0720141070304154100e81000c0d804008540c5440c1d040316000c0ba00c04006460b099880700307081c09040e0400400710f850b681d12626000d03040c2814070303001c00d032201d160240c020a110404030000d180351402e40d2058008035802801c080d04a0b500303074000010300040d0804540700c3c1941c030074000c0e110360000440c00641680506081d003440501e40c01c00c82450b900174060024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 731110251 1250 731109001 731109013
    0x52a1b03130b030601030c081302040b01120609140a0b030a080d060b0c2805071802040e13030801081501031101020703050304030503180f01171b0a020a1403131403 72
    0x8031104818000001c0c2c11021003507616407a1038000107050754138074210700c0e05002241c01032207200ca24000c40418104d4050750085100640240100c903000b0708228a14a41c07482c04001149508054004980c5020004420303072003612081072013011510740d4003102b6416400303182c0d050000303105c010103401628400000024071940d141c601030501e030b100d1007211345550442d5144c4a5074a1010340a03205c80d41128000c030401d06001c0c0e881075a505414000c1c20303141d2220204007080a405d0740c0442c3c0107081450100035003401d01080401d94020f07209400c40102c2d80c44000403030710080014039980c49001614081074240d00e1a21a88120384881c8282c03411401907400200104070104004e1008510a100956480308003490705e18003a03c010808510614110f144080c00d40c7e80504103140805249441c90403685890300d44010440c030703051481c03500d0000030441c4001d0365008030354500d10714040d511100304420701c42d0350240c482c41214201e017141142043d05200710070305451042407151010741101c0e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 731111501 1250 731110251 731110267
    0x1602012109111306060503044805100504050f040f0203040f060b01080c1207090302040606050a080a050103170309150f190e1009030e04060306052a1b03 67
    0x3070318090403050b00d000c1e076580d240d1551400d098a04201400d8005000c1044a003810303401000d51001402c0601856560920707902d030041125040040300501d0021021055400da50310f5101c00c0001c0c0344410001001d8030f0002d4103017452002510108440d6035030310f192504200800116803140030705141c01660364040e403c02180144001c501880c050400f20342c03500f40d103250250642d0000606141040300303400034031440600304c5c41521500c0c1c50f01030001c505680c40e901c2c111071300c0344154006503100e802c02c18000394154008004103100640755480c00b08941d241c00c950b60540c0d8083c072000740b0980c006000b00e459843d406014541042d810002c1d00c3d14040100785441078180f0903030344516051201000c4c8031400e120b40361070313843c44640ba120074018131141c011a076844000c509004240a40c644040008142c49005503e2030224001c2c400c0009030340344c0c20704100401e0111482d0a115410503075404001e2000d4002414080c06011810f2078001b0006c140004084210240381c0f51b8402031014030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 731112751 1250 731111501 731111567
    0x80c060106030b10021b060c0c150d0f090809010806060f0301091a1f080601020a05060937030f05042103082d0c040f0602031e160201 59
    0x6008001e42c0c0c2e40800c3e92141d4104200ca50314030803a0400c1554420000c03440048002d0f5081e081e401800c40e0796540755a01c5541c3d40d03081c810f4403000150f1141070300c101c5450044c4a031000d000101003e81e003c0020450044a00040303800700c00029200308002d004280040d8800d0003001c1d4010b0014002c142405816460b1500b2a00203800603104240c84200c240d00107800b03814040f000020841c0c1103200c26180105e98400190441221380030041740d81d000600320f134000c000e5661031643c81030072140e01d454031003503568965000303d440228540c810441c910341c0030710406050b0074020600b08400c01840603541d0039540c02c0701d0804c804003889030a2000003a59200e2046a000e009001400c41c00440d140e494018036101004001c0e0020700c0e02c250114507244003001351814408103d030303c46913064a40b0310b03000525008a40c03004d6140780c0152000300303090358088003804d014403106000081e403a6251078404024015599a603005c080c1d491203103c055072140c65441c00880c04034900d1184041c1c612404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 731114001 1250 731112751 731112763
    0x3140a05070509030d09031a0415110f0f0301050910050112020c07030c0801020a120515010c05010b090106020d090b07240e0111090a050307080c1e040903090314071a07080c 76
    0x104045401b8600c10400c1c081082d01070070629001c2401c0c91214070341980e070707007030000b814a0310300000c1da9540c130a0741240394401301100c64982810114544488030030b00c080300a07078000d000740c5014a909601107031102004d0040101900c005850320b002030140009681c1c02900400c40c8100d4a105003800003000c20340d000c18400144c00140005640c039040400040c0c9425181040b110341c144c601010046e00401049030039020318424a000262040d01d0300349280540122000c0750f87c002811000090035a800156400030001c0750f46804042980d00c00e2414414040c8500117800b40521071b0011034082c004480c000d1071014100320000c5c031603d5110744a800c4170b1034820007400a00c230008000e210341c600380c8072420040c10101c0c010444130b403d0190198035207512004150190070440084c000010b0100c800d4408042c000d0301c2000905124180140001d40e46d200903111a60545076141000d0741c089045400d80720342910980300148409515600369011100c00d5403001c81c203001b4001141024825 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 731115107 1106 731114001 731114023
    0xd0f11090103150b0d0623070302070203030717070507060e0f0409020f01140f1305040b0d0b04031407050304090606140a0801061d030109050d08010603140a0507050903 74
    0x494101211494024016030801001c8074020103400c101000040a41d407d050340c035216010103130200d20a540019416800800804012840c3c0640303520300e1000d040700f007c0c80c05c0c801d900e0f8176041c20110b81012000506c00c08100104d841d000701815064141114204a0804158001118854507054180c144900d216a2503100c4c1285400da0b0402c3c1d10104802d60b6071074403440801e0302c102039030080500c103d281038104201030030990381600d082a4032aa01c10200d0b00d0b00c0d1400d840c507503203a45000140c05010401080050f00500c007400c0106520200442c040341858000361802030719000410508400340a60864907900058540c111809810202c10101003a101c1c000d514900080d4070f9059070034000c946040020018505541000d6640c03003402d542d1321417074114141c940511818a0301d8401e01c01242c45220b81c1d81c046500303e05682440c0e880c0100c0000440d0500b400401 = true := by decide +kernel

theorem cover : BRFrame.Cov 730935251 731115107 := by
  have h0 := BRFrame.cov_init 730935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 730935251 ≤ n) (h2 : n < 731115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
