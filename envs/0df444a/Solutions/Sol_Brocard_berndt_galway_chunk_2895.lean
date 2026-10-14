-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2895
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:23.073136+00:00
-- url     : https://prove2.me/submissions/93fa948e-5bef-415d-b16d-c455c6abdd4d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 520503597 ≤ n < 520683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 520504847 1250 520503597 520503617
    0xa050c0f033004020f01351005011d040f02450d020f120f030403061a0d03111c0c0b0109020304030203160f082a0c030705090c0d0203040f0501140412 66
    0x1e042d2003511202260300c0b221f0b02c10240d00d140c0400d014801c0039a4140004100140300003420340c42559800c08041c0044a05010703c00034504200c001c001c2d02001e816015028059005030072009607404d0400090714080d45641003c1c0c0844c052160a2601188070303141c9140700040050303d900410080c4176a068841202281d0040c00080c00e01c83d04030700c2c45415114554017100044400700240089a120f0401440a4292021400b2100391040400c1307811108c40d11140010a11507540310314869000f0043c4c82d04140c02814001031170201c4141d820214450602c141308011030640540c0c018604044114114100303590029100d00c58164804c80010f0003032104400e00a80280a420040c0d000c0c03401e950307460600c002c807071b06110511800407070071741c00e070032001c4400a0116981d5101c04009001d8100c071410007040065a03034028018110806041c41180401d940034070045000e18025040c2c04001030951403c5801d48550140034070001d400780052200007001d85e080700d090030f106410880084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 520506097 1250 520504847 520504877
    0x71a0403080714060415050a050609160c0b0c0a02070801050105030309061c2306010e3007031410020f0f390c010c080a050c0f033004020f01 62
    0x1544100380d6603c00c41c0104020b210410000240c2d0381d0b0919400300062065650b17020844045900899a10f50040410400140491000e185174403601100b42000c2c00d40442c1034454221500d41100ca504d40e000000641da5001c58040000d40700030080c4200921881d810302c40400d480340500e82e0110700540c8046800050030f1041c0e00350006030500b155040003184c010030000242140c14a1440c404e070800c02c008a40300394821411601c0d0154003800f1074081ca40d00b05070103000100015201030440095848001d8100400e020040085010310305005e11850786061041c280000452445081c0b4030402060041c61480da0944495007810446503460f0703001d1440304e65141d0a40241d01300400300f080c40030190344104030143e0400103180c4044404d4100380300015a9a8140c0701c8000d0418107052255800f0a80704000408824801d1030940d6100700000320101c0c81c0da0401c070600081440042110042d41c416852811b2014a1524100e001802c02d50003050000c40b143d001c0904101c410b0400b1050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 520507347 1250 520506097 520506113
    0x71704081813090c06030e0c09061c0203160501090e1005130905150114030304062021041d011503050408040506041e05010c0302031b07120b09071a04030807 69
    0x1c40045420602c01c50310f151030710b01184105405603002080c50a482c4440c0703040c00240d402d44091000c1c250141640382c1c01c0c00c11046e102ca51030166425102d0a4044005842c103200200c850014034124503500e40c140800545600c889801460940312003c08001064040902050841e8015254200604548900c0d0b0000d088803201c040c1140c443da09844000c5c01f21240034904943d50700c64001c00c07481f500020140c692003144034a00001d00c00e08451240d0302e4002e6501791000c1152000c41e46811044180384031000403003016080c0d10040801c08000883c0d418100810082e6000e520341215810000d11030001400140c0f031108040e92040003c0400203110211006414010f200c547c03619070710743c3d800e0040c81840381c240c4004101c041703000031154007a8a1000c1c9166058000c1d6040c020740c2410000c061200d880b0ba442e01d44203840c4005000c8040c4e008070700720903008100c1a100303490402c2040d0701d080700b5980120a0001c20120b480b09044141082c0d406803607110582555403000c504046c95 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 520508597 1250 520507347 520507369
    0xe030a0308040f170904060515040603020c01060905090a0b01080106030b0a0e0c060c010606091a040b070f080706020c0d0807090b0d02091801060f08090a031b05060f0717040818 78
    0xa1030750b1896180c0010f41c912130103401086802c0342e0601c0382540352003d002e40000b100c121914040000d11081c884207020340c020302508901880000f0702c80d80e5604640092755010340d01e85403942c000041c403a060114082802d07016240200080c02500c0c41c560f60340440300300041c4514110341d55504100300f0600d0502000890a03801480d0a84503c0c2c0120228000c05840c495900800c00001c400074003100d030b510764000d80e003811290b203504052510410340c1403940321110071150004108480d00024600c10041c0864502440005131560075400d0418902040e0b41070b1a818040190100040c03075032b00c000d801702661443c0702116205c0d903005403518080c0c09079040b21640011400c00d003055114060042c5412205181d6802d444d0502004041c0c602010940b001d02007500280f007000080790207030140c01900b5815100e401410304240e16a203051200590381045140c000d8003e010b1902d03444100c007000203402c903c56068030309041e61408071074400c46c03145039119100440455034640c0e600001d01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 520509847 1250 520508597 520508603
    0x110c0105040b06130515010302090a1a0702040f0b100f03140903190801060c0318030b040b090d0215010915080d230703021009140712060c0e030a0308040f 68
    0x400315060615000102900031202c507405030710b034089800322100c3c060248500450450701d12080030b004c141d0044010350f001c00c0541e40c1200020384005032517071884200055045030400929100e039403070b204110545520700702c503c081c5800d080c040c60b803543d184050350001d04c0c19410410721840241005401034a511000140c115010350200b0192042c04001441c44c1441d541800381039501d003a5003030700c82507401e000c0d81c4001000c0f0100100002c0c02a46041c00840070503124030701c010342d80d0b0380c2c8900c00282140c048809001d04424080c503070703001700b01e180300075502030000c0c09055250004580d0b40b4a0148510009561160911000c004507520864003805501083e0384c82e1100a1a0140c0349030700001d0118000c1c41243d0140342c039102c4081c01d230b03030040340e040c0d001d4905d524019204001070702c3c50400c16114541019607240d8981130400c10b50009101c10a961800c80c90281419001c981d030901801c4203200c41d502007900c095070045a0700c8002d6a15040421060f01c6904100d0310a05401c9001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 520511097 1250 520509847 520509851
    0x9060f0307181a01090305250e011401020105060a180207021c050601060e060a09150e0310090b0c0c060c0a020a06090b0105091303020304060e060d0c0305041403090306060103110c01 80
    0x182c0203400c8190031102101941441d011180500e000045910094920001c2e0880c1c0058035440e0b4020110241401140010002c1c404815100c801c0c140800000b80e200603030381c0c03011004904d541d58081c000c03140c1c0460100ca22016442c40c10514000441c070302a41c215a60358001004002c5641e6003d007010b0811441400c2c0c00889050b2a05558540b02801100c000c1a82c2d68050101440e1102c101c41c084810341c2e031307924134042c43e00394803c9501800001200c2403000e05250410151010071411890301c280810101d81981d480c14800c2c0c42403c090924181c1c6a020420784144100c0051010340004040c4a9682c0c0d406542ea4128108014001c2c000c01203403d1882c80001e1250448002e8180d03001191102400d4948031303044d4685041a40d801005a002440200101401141ca00803080c80c064255490701340d9040070300c01102ca0704518100440d80d174134148800c4c00b1304108100200820030004520b4004040b0009039500c0e0003c10031410151200079004c142000381f0143d42c500340c049402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 520512347 1250 520511097 520511129
    0x303011e09060605070204022a0d0f02010e0304031118131101052d040801020c010516090b030609040311060709092f1e0301090e1b09060f0307 63
    0xa264884210448000140002400480e51407164032941d012501c45440300c91800c001c66080c00041e404c280054800040c107142c038030b80919899100c5414480c40760001c0e108002010501a115515030342c0c07514210fa161018042c0c194070000120741c141ca4000058031380003580b41c1300203948000b907085409181d4802105010a400c40000d5094030107200c1e0300c180007803010860044510340101c8000c11410103c91100190600700d8070403c480c03600743c003942c280c5019186c14010742079900030346101109a41d10000c1100201d51000b0405034445c01d0316003803089518081d07490038140005000c4901c12404200414101405140c801030412241002d44116280082024114036000d104a0040a0070484070a1040160080b80e50101920324243c032141901c0e2541702045421042403804003140e00c030040811040100c01540c02003540b0400070400e0340343c4030405800e1a00b0311552402d4010b9002c4c0c4510310742d42c0c030704050354041400d5407105d08034501400007c0c03401040f5400b6240c80001108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 520513597 1250 520512347 520512359
    0x40b0c1308070911072102010e1518150a0203060301061805100509060307030b1e1008480a090c09050604030c03150212010e06010f02011a010f02010905030301 70
    0x40e88008a0f10a2042040400c500600c6040c644c450140001c00ca25019407446a6043e00400410b0800809200010f043c2164103400c03460035014139011f02c0400710300c04c104090912083c0743d50140c8240b22011b082c8a6020b424450440c0303a0280c4810191a0007000141301070301e0035404007008000c203191210050142d01d031070000030304042d00c00c080039221105e0042454100711381030030301802c400f60090982900c0c0d51a1800c0303150024013440320000594107407400e003240f0b100009000d044140041e03811a440e00046502d494a481c4009081003000b4a03443c103000c2200c072443d140d03149618130444d0540c041580904000b510b0310701d010b81c49a5414400300c0c02002e654401c41d4054240e40f15542c0258491040204da8007503480f00415600e180c100500004298407003c0b000031070b41440140c2006640c80c21031070721030003d803c407451021400c02040210360340958500207a005a0008000140c0c4065541d071303040c403c0c450000d050100c8440103000180c400d5214880060b04501625241c1d40c681c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 520514847 1250 520513597 520513603
    0x6030b011a033103111905030d02091512060306070c020f1e0301110d060b04030f061d071202040f0203100302370f0611190f02040f050601030513030206040b0c1308 72
    0x1160441340c40c406c2c0190214141c07880c043c0712a02d140c02100560030017501c1c1107544040e51007900310641014103101d0384100411400090150401c038a12038041305d1a110003494a0311200505010410480080600142c1c0b200c0117040341c62901500e1b104018101307104d040350340b01d0f02e4550241c0c040d1711f45020014490411030291101500035201400200d80d9802140346c64090390001602c811302d01c0e4140c40006045601002d802882d0030080800460b064003410f08140440d8000c041c0e91444440020452529200d00c140c1410401c2d01142541068510f5100d00513840c00004d000740740300050303545803040007e00d008110b0820f6900400002802c9002246242d00340b081e01d031a4094484041003035070052010341d88844040b001043c0b503603007000b075104156a89a00c00d456080c1109101c1001d6195030045900e03030740c1c1e500f1001c1924284007000601b02c4030000c0142c044031114402c0940040d0740451030782c0c0c00c9904085411035070f07110304d42c88800382d10491480d4410724864440004181d4008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 520516097 1250 520514847 520514867
    0xf0c0b1303060c02030403230a080f04140405040f0204110f072003060903031906030209070807090e012d09090510060b090603010b0705120d06030b011a033103 70
    0x141d0010b1118a03a2402c1c00c4e0394030b000341e000040800e140d414503200b051042c0f80b5030001a00780e501c1107420002d4140c440c10030a03071020321110b01030030000a0070b00000c007000207030303111103101580c3c204010725060701d501c0341c00c80e0ac0d4840244100c1e151605005502201c1054034a414008103545586400e10300d054645560300b29000c0e10000072580754442d0758034000c1092803240c1501c801440c035644c2c0700020b59070820500c640c1002030507a40c0c6004009a10341c940b956218107506d0311804554144098041e01c081d43c1d40d840352884401c40d0740144104880c24a1011185104581c000b0004440c0c09034221100020742110200500e0440e00c1c41c248103000a080340c080a24a804021150b11444c0100451080b48205a0080380800040190340140d100400c3c1c0c10b4003800540b010030328181c1040c41e0681c00b201004000701c2d126441802401100d4541314018507280480c06c40b1103d540725883e0b46804000c00820800200701d460402c035446c00c4042c09221a1069040d0454240390f10307020f00401341d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 520517347 1250 520516097 520516103
    0xa18090203100c05030609100b0f090906030a380c070b070801081b010309121805010c020a03020411130306050a0c080609040213112808040f0f0c0b1303 67
    0xa0b10356802c404060354880c00040740760030342d941860f503a03880307003400a00407019041e5502180079000000780f00c600b01c0f0141c0301c00b5101420a6907108061403c0150700307072024120358420741181100d480007030400340041041040c9001d8600b001c1d00034215141015810801c8209110401020409841c014600074590240318562480e6661200e9208030740301c0d072090184d48220350150301109804140d401e45040504014500454010007540d00c100301210411211070209181041c180b80c07079803982d90765502400003840c008007485225000a200c2004900c0064090f0366685080c030b42400640003250b030810305002c08038081d03a45e203182002c000c0404590001001e460902c10001c018403503400c0303600510000300300c042140c07125020083e41c8851040f19205a035a50b1a0760802c0b0000e6070050301c0b000781c070114246000107038605030840d8810114600010000c1c1c600820000230303500001a004c45400000d44180d441c000e04c3c01408018107034200d0051160b0110f00043c400d24504501d6080e130748 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 520518597 1250 520517347 520517353
    0x2413030c09050c030f01090911031b01140c03160809191a0c0307120207090c0917030a02060a0908120a09050708031c020306030a1a0901051003030f05090a18090203 72
    0x9074152034002075004c00c0d2440d0312254883c0004020800e041c1d0088404507014000021000c0c140000107440c15041c0d041268482c10b141c103650510b0341e0070280c420900300c500090b580c134020020001c26268400d00c00090365011f030990312401804200e8081d128111009000304501280c9400b42e4401944548101800340504540d2424101e181006a40001c0b003240021400d24289950307140c1c0508042d8419030861056200006052600c0c3c080e2000c040d86d50740702d201c00d960500500800c000c020321100c0c01d5680c01085841c481039400521103600507801d0100190b03c0700c40c1c1c541007003140b14991000c0e104aa0b83c1d02401104101a480802d50380c3c03140c4226001d80c1ea4440d006600c90203028141c03a440d0003403008000704e000041d00195403048000b03055802c40e52141d40c1d03d10b0300d41c0360054180b001e030b02c9900401512841c2482100d03002003008110003d040d00e0f55400620750380000d900c01c0300300300c030100e1100d44a84800040001800601501d08842480c020618008020301c10050b8801d02c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 520519847 1250 520518597 520518601
    0x140604030503150a05010e101206090b0f0303030402011704030504030615080d170a1d01111903110901030e2b1205040803010e0613050403090e01060e2413030c0905 72
    0x454613200d00c3c0c2c100da80c1a112103a40b003070b5010400940107448030320340d130510007030b1043ca48180d122480303040c0c054000c0f6403000425014400a100800300c1050901d8003a80c001c00c288005030784c024003a04180e07200c0700072103011a80c8601d0103d5150056a00091810741008038410010703104001c00301c16141080d04031250b032a00c3d0075089035803518502840f0008050300c404034006208a4101c00e07030504103100480c5000211126182c21101500c030045005840405e00c2d405070f6826801c2d03525403128508c0c01f407251082d013030001115032081038400d90500d99506000851042d06002c5084000440000d0701c00001e525810b03440503122624011001600d03402507408041040d125070780c000c60b0000c0d0102d0071a800e09002d0b090000303000d0300700c69100b8000010030000961074011244182e200b07a031801801d40c07401514070b07207045040c0c001009020006c20942081c1e02c6071039050400000360704020f034202c11600390940f600c3c40b412801800912051501105212100c50044221040804108865 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 520521097 1250 520519847 520519849
    0x703180305060f0f07080106030b0f19050f0603090601050108041112060a20031909080d091b0b03061e1507200102030703142803050108161214060403050315 69
    0x2131390b0f08548820224a2003801408194800d41c007812040c4406080710800c188090002440045813010381c0301d091081070010300c450b003480320139000000420340b012401d5050016143d0388032001405668108038041c0d001030f051140a00391240d8070362014090b0907210100c2106a40c44000c1100c1810503542400c0062000c00c801c1c004115916043c0000a411038440401b110317420a41c001c20320100a444110700c0d0081b0f842d04000300b1244e40c04010008408801e85400d081d100d1210007075008240065a0410115401d601203070b520800c2294801c60002030301c0c1506100400d00c419290b006820306180f4116090410010f1850300d0213004d851050500c1050f000800c0c010319491580160007e104000000740210300400107803080034045070a1940c1150000044448203056500d107408410035020071581612885014006d00c402414800780d541a940c200c80390703584500390200d01481781d040b0501030442c05c5102c0806040c41507490905107824002d200303400a445005490754404540c07049 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 520522347 1250 520521097 520521121
    0x20a11012a0c020a091506170c0a031d0d0f0905040509190804050301050c21070e1002030904020d0506030708150a020319090503130b04030c0504020703180305060f 72
    0x1144404080040e07420309420216a42c1890381d4040340c0080415801082c00300c0340e40142c3e910b0b41030540010500354503042c5c000b00605040d04641003451121820300c200c44501000716180000b00e802c000c0355400c4d81840800c40050040b6000300b40e07000d0380ca5000600b0340e0018a8810420441d40c941e02c40503165000c05c400c540054600d988036034880064041c406401841c0c01a0342c074058212181000d5880020a00755041220000c01018000600e51413040c0c0030701e461101c0c052080c3d44801c40380f40118028107583d00c6080a14800d211200f41502c07954404c1048459081019000750b4803042c04140a101a184c01e4402c9071280c000c084011903a41d1300040e030907203080e551241070181d540f1109175220095201a1030b0006201078820200001b14440c000e03040c046205400440d40c507000820030200e00c1c0e4440e04007103d0707540100400c202141844140100750342c802c0f180149e4455082c5015200b99003080700ca803992401c49613001040c8074010402a01c00c48801c0144420303682c0303082007408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 520523597 1250 520522347 520522391
    0x61c05100f1a120f070605071a0609010b0904021303150c02030c06071206080a03090305070909021509040603140607030b0111061803040f0e1902070c0e0402040609020a1101 76
    0x80b02da4030b01d95200c02e03182c800c19040e034100c004802d903030341c2c94100e4154600f4a00035401240200d2000a13506041051090440c000c19100c0d1707035684082e040100000f5103040043c07140c000c01403004100c400e91036a469048800310a0313090215482e86550340f81c24040b10350f10f0700c08404000d1030001c3d003518060011085840c3c15081c9405401a641c41003415118030945451142503103a45803400303d0b402c4420080558407501035250310b103140f85180340003031030100d80303400c944000c5040078599001070b1241c40c0941d000c03c600c0780c100307910b89100b0800314008003043e03030000e81701cac441074040a5505040425964000d01c3c8131b60701800030107006001503801c042410310041c216801000010400300008102100d0842c0e42d000b43c030700d466501c140b030500e000c0039500144402c19483d014000700e410b1305203030b02d84005034184040d4203082c1d05071641c11071381c081c920500c02800000000541103544561054010702103a1804540354036520b0340c000c10003100d12005100540c607003121801c1c0c1d441c1e8080055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 520524847 1250 520523597 520523621
    0x10204030b01030f050111040e060f1f27030305190219021e04020f0c0c0f01020a03050a09120c03021c23010f09110a240503061c05100f 60
    0x942035919540d134440305031301c81c4034082e180fa568807441c404080c610200180000c06a15080300300030b0400800b0000305901c00740a40344200107900000e40b0300c04035a410303400c4025150422181040c120514000503100d101c0d80b0310002e500c3c10340c1c007008058100700940036242e00000c040d144182c0c000810307030b0340b15080d190b00504560b008030b22600501d420500101c50b5188031070f4080c440c48062010606a810415001c00c41000c003192002e40c180c0b007000780e48090310040b0380b0b00046041280010351a210b10341000350400c040015071202c0ca1707001d21096002170007092809000c07210359040060400341030340404c0f481450020301c190600d604071208940c80c40d81081001002d90140403106185807030180e5480d001c1c0d503d9a80300c01820001b4800c0c044603600950703000305410312402c1040003140d00f980003106110300c007030006881d6181c80c000d040c440d8582824001c0c0c1d41d484c0c080018040017420710181d5080203191855104004020900418441190506001a890540c5004207441040c5440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 520526097 1250 520524847 520524863
    0x9030c0e090c150d1d0c010c02100c020a03051207150b0a090b042408010e0f070504050601090510110d090b070b060f060304030f0f0906020d11032703010e01020403 72
    0x1446030f103010560842d04040c207002d0f144c54100c2c400d00200070b44500b134560f0748000600003940016098140814103240c1300910300b600b0140301035400030b100c9503010814081008401610701c0c1c01c40d120f002e02840655007003000c6525418403c43c030000c0a40c41450100c880c1c2c481609005c6000c2c0e4903000301c06103800e0052a2440003030400380500000d0105510207648151292400345003544c80d03a03519a10902100041520705041c1340041d402d440703220051100b103a20064100c0398414000c5803150503160700b10340200d40d68850700d004850354401238205a43c4000b0300b00a00901c1a009a05440d00142210030b440f05101000c00568240380603115002c0121000c000780e10002da84441c400d0381c05403009051410310701d400303008115070390030850701240829900c00c0035502040d001400c48074621001d00d0000c07040341c14282c009449051481d03580f000d0000c8107040d5003900e03600b8000d48400f400121109509a41d08482d5500302c1020094914025440c00e80c0c001134a047c18021602a00e4120b422 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 520527347 1250 520526097 520526113
    0x524060603181009060209030d0503102912060102070b0a140d0603050d110c0a030c17011b1706102003040305070e011701050403080a020f070c0609030c0e09 69
    0x1d0740641c00c280340e07146842e010f50018100741c809240b05542019009800060f250340365007042c54641000b907021001800300610400100304052594501074030001b1260300d900b4000f444203040310101000d02a90780802c046100d54481842c1c1083d148500c009908550041b03a54a00e011014850125844000f6040c0c0c1c824881450761000207005900d802c000c0010080e907a07860b680e04005640c15420000f03843c01d094883c0c10002009500080700c0104e030410314151941e0385415401000380b140e003045913100b2440800f020800c3d8440240c041c0b12404008850000600041400c041c1680340c00907407a000c2d0120725641880c180c0442c0c161415101e210700e46180c1c0b4020020040c0010142c000c40c4810000440016001d000c02e0f8010300c000303840344d101541071080103407820003100e0103138520303a03d01020000400d5100504581200d07552800590301c00b43c035600f000280c4104c800203856128400310000e000c0b07070710000000072240101c545628542d1903850000009806550303d02c0a0340c04040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 520528597 1250 520527347 520527361
    0x1023060f0d030e120a05160b0a03050a090212030a171e130609032a0f03142101140604080c210f010614030a030504090e0c030303040524060603 63
    0x1d11480030b0203410401c6860010b0000902c09202c00301120249401000300401041000c0103a031985409500116040504200202c4414040c0e4029501096114004601800c40590210f42065000381c425001140c071403903400c1da01e03400f490b1580000382104104540350151038420501940410604003240614080020040c0c40042e0540c101c0784580c09164000952512540360124482d0301d440c408550350703801c60391500c940b00103c0c000d21041d0300b40c0307540002c0404544220807989410242c0301c80201c9c0b4555a920300804010a1048580981c0d004010041e64070480c100c808240d210000b40d105441400700e60f00552060104a0b07102503d07524103441e210900741c901c00010301380010302c841869015460841d240001c4541a5591501444001156103110b02a1441a00101500e80352594001c08a119510401e81026034420b0800c802650520004000c1c00000301125204e0604d41070040d101d00042f4624480c00004011203600c09031304900300d40c41800000c0c261030865a98007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 520529847 1250 520528597 520528609
    0xa06060f180b0714030d060317030c19020f10020301050a050406050306011202041503061e0516142217011b05030405070905011d091c0c050f1023060f 66
    0x34800c1321018100c003180c00001c030042001d00501074003560042511451414107402802c050030301d43c0c440b40010401c028109540f04111a0940b01c8810701c160728030702021040f424241c1d0701d402d0400600808104680786501d40d009181a10f40c2280c020003610703030702c10410040340c440340700340c5425411001c01000f084910441e444401800a80081003a80c0c100600c00b00318500364000b00d4029588100c0280c0604003042051215060311204010608014902c1c3e20400c10307040ca0201040300418601034503c105030150340481400015541c1c0903461070f040d03828000c40d40d001e80f44c400900e4141e00e2850113014098150480410044e442c030310341040700111013540c0020425907861044c0600081c082207075120316030080030349080041d020010355070403041490010380303980c099a0081580303030043d40212114041c0701c109030a04103103c82c158941282030160020310408940243e05103071841808540000680705085224040300046ea00c2104895420641d4201d0f00306144501c49003040c01c2c81 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 520531097 1250 520529847 520529857
    0xc040515010809210301090b0909070510090801092d0c0308030402010c1202060601020f0a02151303060c2d12020f040e0c1206030609120a030f050a06060f180b 70
    0x2582c1540c2a042c401d801341201e00409034207405494000100400c0184030f60b115032031804078100c50810050521001c12550b03047c00d401042d208000312014100d01e0340c058013928008180b518001d01150340d041c180148080414030451032849102c20300d401070198000041d4000aa10202030002282952560a0244c00090080381808658803030000454446560401301c4007407a070040c100c1746041000241008003040c03180401d07070b0007844641c0041e55403450081d40e0506c2000c0f200d44480040380d91070b910340d90701c0d440509420328080781c0b030415990200c0d0041d2007060310203219005103400150b24554881c52024400043e40111b04c3c00018034044d001440c0300f248010400e42042e03103800b031421001c2c1c4103903030703058140e13000051910504401045840d40050114058081c41c54812441503c41101001c4400300020008000081d20b010754040d800380b2003082e204214626010101100402c880d00440ac0070518000101644078801c0c0d4902c00c0c000d0301c0d0040700800514100d60b4145941203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 520532347 1250 520531097 520531111
    0xb07061e0e0f0d0903051b04020913090201180608160908100f0f050405150c16030e0411031006120615120b0a0b07021003060b0406110c0405150108 65
    0x2403800c0d00c04004124050046110311440241602100891006242980007600340051041c1c000082001c034001060640341210f01e0f04040250307490890006000303104010b20030f6806031400e2501100c80606030b0003000154401e880d800c3c81090031100b2100040b110b44990700005042500150400e00100800e0780d501c102c0c1c3c18071b035600c1a150007a40303003014a0b00d443d0300711495883c80f041c1c01441150080f490030700f400c0030080203282041d40b034007521001104200300d05006440046506950074108407003011111007948025060f80745401031962650001c1c0c94031031030600b008a031001c0d442d10304503402120621304412060745004410349546c0b510b2041401155034942d00001c104444031000507042e101c1d5503d41c00b40c0140c00e0400c1007240d00451145028003043c42d020303c441142c0c901220101d40d0100c07204000c000030f01c1d00c01c6000d01b603590401d90502c01c011070b002903001d4200290100c0d18510b030044e00c9100c000c84c018442129421100c6041a4135110740018843d4010362155400c060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 520533597 1250 520532347 520532381
    0x17120a091406090c0103110406020c1005040503011803080906010f05010c0c0918030f0809100b190303030e0f0f03040e041a07090321080402270c07020405060a0b0706 73
    0x1003030500281002800c588558035600035413025080740da4984a10000000d4443c226810079040ca44001d40d00c0c00300001c464002c043c2400c106030141e0150341030714014907009000380003d941d02096102034551050301103010914070170100e0400003010402034140d5030400c0703174400c1d0f0364a440011102c40c4500d03c0182c3e4410040000030030102400d0103103041404600c1c14120700f40e103151800800301314042c80030748104a843c0b0103004200402007051b00412515203800301d40211006c0004011682c56200b9401c6040b8401c000010580c05402c00c03141041500306840c0180041401683c555840e1842c0d1400360300104018051034101ea04000e800900403842c07144282e0010085451a010541d07044000c00c100d41000c02c100403038060104070103d8015814900000070345c0380a07103807440281000340b061400c914522a01204500d0003203080110640044940c207081e07081c43c03900e0f400280244e0086050100080081c1001280c1c036080f6070038002c40703914011860300c446000f4414504145c003421 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 520534847 1250 520533597 520533623
    0x70506150114041203091706150112020a1701051002060a0f06050a171b09070f0e060f0304021201061a070201030b060c0609010614130504060b090108070317120a09 72
    0x1d240b00c070103400a00a4202c600262090508020705103e08907881809003030581003200080d044049000f80d000490348222911000c00503005862580d40c204061070740c280301042105141e0703440702e0082c0102c5018119455030341d0320b403424089151003008284004d6405000802e841403c680e00044281c0b00c0910001103007074443c07000980d85441036006d00030303401c0024130b810b105840610051505c281c0780d170401c903818441c2d03002043d050400104407030140070020106004d02801a650b103c00058001d0090350342d04807500b11011990800d5909038021020300845031205d080500c20907098914179845020b031882009201c0030780303511100040381011f484030500001d689802d009400410f07980d8029084601c2c0c203450650844105600480c401001170717422188a44601000310320001c41c070304001c2415076480c00c144014241505645400c6041c1c0382c000500c180c0d001c90410141c0f40310b4012811454080b10300d0002501072583e485001040180104203106600e034040b02906214000810040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 520536097 1250 520534847 520534877
    0x1501201207060f18112b050f01020a020f0c030a0201170a0209060a030506030c0f010f030f02040f030c030c0b0403110405060d050a05010617060f31050a02010909020705061501 77
    0x34070b10b034104442c01c045680910604021291768492569142070310050351140000303030f00100015804042c240040c46d1041c6800c01d005040c007007014100381000003595113060104000b581c0358100038641c0c081e4054000c2841c114500801c06011168050f555950000140b0300b1450f007611001d424030101e04c0d030030441d9520680b41d08019190b0b00d0842e403400600380c5000404d00d4109a40c940809200b0740034a102c1d8030886c1e8100303407004444840c5190004280c01e0f0341c454140244141c0e00030341e008040800b8000100700c400903458043c2c0e807140060103020365403210391921f640a00e0000600c5a0341e0031a8040040c01e159020581c00000100f80320021211501c0300e0b2308040750751034103860740d9460385410b0002c140c2020240000941d007074000c00e90f5117072803050b0f11074051015000000741d1150f01203a0030039040301d529058076000c0e14860b40a55045030b103440c03680c031040e1b08012808124041c00000301c4400502c00d568038282c0150103886560ba4444400145c3e49040140314107001803e0100c0c2c1ca0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 520537347 1250 520536097 520536101
    0x905090304080a0b0f0114011e0e120d110303011518031509170a05030f060d02060a0f0801050618040c140f070510020f04030b09030702091501201207060f 68
    0x582030140a0580300c0703040c01c160801501005070418100c04004589030380f5103036070201c80b20041c10306278042c907000e0811044049480c0c61381c2a150a51040d88002d80103840d040104003000c0d108019244c1408010f5078047d2181c490200344299882c02c0e2803c280f0710883d81c05a2151111076812a0b03440d1a5103880395100351401000c0d1000441d007554400e801c500308441081c0d580444007031105401c0c28000f03081c1009126110041001e8110021131000c2542ca841e4400350b51981030b070042c9081d07180c0c019144028020310b10421681c00082082000080a0034100c080b14403032048203406150403545903042c8005005010b2101c0c1c2080f0f0108032500d02c10110f040a4040801503600007030307890146003021482c105034480030380c060a104000810406210030222004c90340c0c40801d03001c03d80d0314a03d0040c00c601170054060340042c0c500c02044500080c98012158082d0241c0303c50440540c00402c4c81c00e0074030802c48440e2945c1c0100314580350407450318050070000d482802c010400c171b00c3c040e6080003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 520538597 1250 520537347 520537363
    0x3030714010510050109050f040f09061805060112080723060c090406051e0d11030d260417180a15020607030e07051e09040b0117010603080301090509030408 69
    0x40da5920800e0102c1c00400c0c1090100401003440c0021800307082c00c001540b80c8071000c044034404e0355610b40c2d0040c2e407c0581c00c0002c00c02d030080c80030414403601414002d0180e90b100c03c12034541c042c1030004510000c08250000015800050f0035003013004680c0c540401410071210000078110007641ea000b01501000042d104404c21500c9980301e20542d400c1c03000341d0301d054112034072072041c081c0a404040da0350710502c402c00c81c04130b50703400c441c082c68100022040080c107038640d094050181a181d800360010b0405100c041c1e49030380e5040c2e003000000300003594071007a100240304010b03440f45001008248405000e14907400952034000740d54082c001141c8111503404411694a07444402c41401e405014080d80101e046c1014807485902850b5203440300f804e805032500c220018414400e01c001d51842c440302690000e040151305003040e0501d5000c0103801d1080103514981a622000614410302402040340d074007040301401c41c1d02342400c06010b090010041d84840c4010b00c0005034080782000954 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 520539847 1250 520538597 520538633
    0x10e0307030c0f06021c230706061503020915030601030b0604180606080405070b03190207050f07090b0901092f09010801151707121104080f0a03020714030307 70
    0x46090f0300d805a0320700110800e9012505541116950a0300e0032070324600d0807002c44480c41c195050700c1c4101d02a151101c0c24a001c0404031501060210030030101e503010005542590a8000c80e41c6240b100c114160302c50024055004445a0306050100600a000d140c001b0014140811103071901404505560800d03406a65115a0546510030b0325403584100f0000d01200d01e0645202c1c5400c1d11402d81e208102c6c071800610b01400000112800c0d140d141c00c1c0d038081e14a040a550300d803218200700342e48540d0000d8201d614081e0240000f00b5020a00c182c000e034041c064500c9159a2825130041d000b0124110401d45404800000c03817100e2595098041e1010102201d01c4c0d15452030a00042c20514140c21111320fa000307401410f4480380c5c10084519051190000080b407a9070351000c00c403102e41241d650034880303a0030041c84a00c8980c40c0ca0103802640c680354101c4090f80e1740b40300816038402600c5005009a040060140301032410841902c0384400e010701180e1138a00e01e955a014000b107404104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 520541097 1250 520539847 520539863
    0x20c01021305030606060a1404050901030f0c051c061a040e030703030c0509210106180e0c0910033009060f0206090613050a0204050c040f1a04060e010e030703 70
    0x6401d201010403006005800d0560080c201c0e49410004991603204100f100e006020f03544010500c039071070001c111000382c40003512401e415692407401c02c103000e40c1c014003210603155004012416041511001c0c000d4480d42c8180c2038504116143c960040292140b249904440c00b041030304140c46d0b44c02178040d4000c0301401503940b01d0b140e08004040325503d1100e1020003a0030040e07400c02c1e80e6142400240c650003a1601444911007280aa0041055070301030340d003c0480c000466400b661b0b41d030201e9039401551081c0d8100c40e0b041170800140305800c40d1410b011410021042c404103281d80111101500c0019030610741c07883c000071081d100303441080c1c40d100250004000740301c040e0f88a1445000380480c0e00040119082068a00e5151140100302040c0c0304401e50000041c8181000080c034015000380c010815030614000450503035110340031b000304044941000140c540341e0001a45040741910806605150800c84e0860ba260106154030341000b160503001c0000340c2d024407088000798854419 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 520542347 1250 520541097 520541107
    0x110d05160507030b040b0703050615031f0602010c03061e140303040e010b0403031d0d06200403060e1603030203041a0705161503060521070e07020a150507120b0a0504020c0102 77
    0x50420701c4000b451f6004040c14282448034680b1a071300007400404008001e5903c0e0341d1200d590303070404540e0b862540c85001880400184554040d880f00590901e2a902403205948071948035118000307640024510000c08041042240c0080b9001e91a40c40028180d82c6050341d1a450462a8242a00080c8110b40001404c208164018169105501ea80c03c04817444145c080006095040080d8000e000140c4401800000c072103aa400b01e140c1d940c0c80325030300d07445d2901c2e801d1102c014600c40060717061031310a1500310382225404030110b000720380c0d050340107504c2d242c1480c150310303410800c9031050300d415001481a0000100b040c0703c0e40000a12221040c44a10303e00382d603400208000400c0d031824185400020b01668a480005a502e54800710103030912070500d0300307101c0c07a04d43c5170741c403c00c52081034000b400f51055000c034a20350031900034030045e900007044503000300443d50203480d4480400e079412031b80c190060b05500f0948203036200a00b855165980d0b10040342c141ea0001d2580e00051b580052 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 520543597 1250 520542347 520542353
    0x306050415050d0f0302341e060e03120423090105060a031a060c0703030e012c0102010e030a0c0314070b0f1306060e01060807110d05160507030b04 65
    0x450020040c1c284020204960314040110341d108403000ea02524195150400c041410300800404c4800400500c00d601085801150071080d9440500883c6c480790014a00050382c07015450713031200011651900111552801409a90500490b8921905406104940e180c0b10b6598009803000b04016030f07100c1030028260070100404082d240c00c1d1440b860b14030f0018040340e201c0809849103c4403d0400142207030078000b400001201da901d12a60008000905d210003c20204c0c4034001c036482526021600c0c5010401074030340c0030114180000c0c0c105a000448523030f0340e080094500032507060000048000354110181d06540c444400c43c0003180f030095190f000c042e031010f000b03210011030800c81400c052a558540003079901c040d18090280f01c0d0a0302098a40203412056402c117a80010b0400c01503544290404601078244203000103d000803000510300c41c0142c1080420062007030152515240413441560942c0002c0540d0388a898518000030000700c0411041019600170381d602403c914140c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 520544847 1250 520543597 520543601
    0x601180503060c07050114041113020f04092003041203231006020c010219081c062408041214040e09060108010b0d080403031b202b02091b030703060504 67
    0x1a134004680341c0410208004102285400810300200b04c8900340003010b094000740180c011403041c00c042c0d4400250004075030f407055200c1c6030749412032110303050200b01041c50742d3f56130300040740c004d4103d2054881c112907040c402e521100e03c006c000c2007070081d41848004a55100e6400f203079031440e5445202802d01c40e2a4041016481044091005040034500c60052000f0002010750007808420003091308142c0c0c60203c007a00d01420300c0340c2003c02406550345080c0c040034041440306425106603180c640c000d54030030452039120790f81000c00d0407101c0c0001c5100700d84507810aa003139248440300f80404075245000c4450ce500030b088800040c00b40754184102c4500719038959502510500328810000300091142042d2011290503040801c011440480503c440701d00b0402c1c0200403d07003000e070f140000c010820900400399010385504182020f49a81d4607141072148803a04151042c4600c10801490018a09540010750003044c01d807510384000025940e4106a4103d004a9110803007030045003007034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 520546097 1250 520544847 520544861
    0x4050105060a0504030615080d090e0c12040b040821100603091a070311191e2102090a060c05060a050c0a0309060b090a0605031e060601180503060c070501 68
    0x7203600a140124400c0050401d2145100042500c1e4544c0c3c0640d50384502450040000c1103070300c0c1178130480c1c400b0081c0141244c0d02c500800c1c5201501e034000c42c800280c4002034035200a008420384045071180c1d11210711108000304100d500e1036040025891001d04800f8141c80228104c0f9130302078a003440c070184440c1500720703000340c000c15151007000d2021903c410b82d4412110410070440546445000f4200e02620000e00f900300c41000020340483e0a4161642c0030f0250a00d950391003102040309200e0110280816026100040c005898084011500c0d0107140c41c0c084410300c0140f03004c0f90701010905140c0140e0080c0701241440d0095021700a00340183c9500030750900d407c0000780390258110340c00e03000b50402e410070950741e48849401c20100390701078441e1074002001c131101881d00c00500d8015010900400740240110101081d100f110070320030104064009003e000a03507100001142d804852000300820a0a80b402c00182c1d074038244034050007020601d540955074011030809900b92824 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 520547347 1250 520546097 520546099
    0x20621060d0804060c0507050d1101030b12030d0c1b03030c1403040b0103030c050102120f0702010605240c10091b1502060402090c0c010203010f0504110412110a080a1104050105 78
    0x8a02949400a20030b207084500382c55003410b105e0502041d80c100b007440d0024035080343d90010310200d411800d028070441040c60b400c0c4c01340d0b030034000003400f803042c4400100f51000c2203142d03500c14807130010b082c10540c100e41e200c2c1500345448a100c4081211014803a0b0121200798040f039919000d101c01c240d8060a0403400c244203003c01c03441d508140c2e80382900c5c3c0c8014031000d020020343c0307170300c3c9410050b0a40454401c040c0d445c0b030701d00c0b0605240c80d00c0c0401e010b064500102542c6010700c0003401d400c00550441c001a602180f4107100b810a8403401e40c030764000c10061000d400348070303c2c1c04003000f03035441a8000c8034000e00c2131aa003441100020f00303d08160390010412110703000014004a5400074031154400d0707041d1040d0085494600c1102801e020f54040b40701c50b54000f00c001315818020120001c0dc0ba03004131801c0c007295000c03030350604c1140300368014080307104600c54051000c555980c8031031800440290002c02a0f0b60b613282ca4070b0506501c0b81c812140d0034001790070355101d0302e400d020b854050b00f8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 520548597 1250 520547347 520547359
    0x111041d0c03040b01060c0f05101a04060b121806091b1503070309030909060308030a110a1b02030a0204090f060507020714040f141e0903070309140a0302062106 71
    0x405854442c541c138014400c500801c41a0540b0b50108400140056101503200080380d640005003d00c8001900d92050401000c00f1002d407003009610b01405818215441c0081ca54600680083d80f020030003c01064811840300203012590700b21010805a031080c0960700c00f40840d210000c040c0386400001d000c50510030550360420061403d2403030100d94003c41e050600081c2080d162605990031300070355014a4006140c50000401c3c0500140150311904e0031000400c21100851580c20031401004240c0300002c009544125042180303201c202455800141200c0300501180d00003030030340e081d02c03030104c500d149024041740c1000340c01c0c0200c0da0400103d0024004c401e00380301c4052465640706c150584603940f1a20402e001203c250310100300b840c0300000030a5680b4094110003000703e100d00b210114012040005810790741c021094810f03066050780e840e40e5582c40c2801c80021001501d4041d5809002c82e000000160b45042c0209840420258404115182e40c0825260102d000344098007940c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 520549847 1250 520548597 520548601
    0x151e060f01050d0207020d17041e030c0605070305070605190b010e030c0607020d0b0112120e0603040602030c0d06060e10023c030a0203071205070f03110111041d0c03 73
    0x6070b004019505032240c075400040e1201003d000196007189910710180c00b0048035141006940d02c01340040c000da90030741c0343c109400c04000c11207121542c0548400341086c4040d01060041c2d512440c02820228080d00e0120308018841d200c400882d80c0c01c1e04c1d86c4507031100d07282000b840ca0006000795501d41009003032540740303a00d80c80c010940b81c480a07070086120724400541d04003190b403401c4400c00802d4004081e21520341e1a40e90b00000c0d1005444295a030704803110030618800e220340504044850060316590540d151655100065000500149080e0809002c003014180c07a40c45540c0c000c1405940d25848204c0d010140320300c1e41c126007070802c1150070041c82880d040461a0680240082c0540686102c40892280c000800302d803614a50b101c0c0000152844650f0340000a071698034010010131800076009501a00c051003481002000e0036405000880403a000d10b1a241202c0004400400c211040907801d400c1c90b88103800484403004a52a003140110744841010b600980302e1000520314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 520551097 1250 520549847 520549849
    0x4030e03030c1e0a06090506040209061918270209100b1902030c1615030203060f04050a0e10020309010c03050103080423090a023414151e060f 63
    0xca00701e086450325072160006052403c001001001c5505404c12800c104104492408507203404054905903c0b4100381c3c4081400c40c9072010006100d01c00b28440c9146403440c00426000b40c0102d0001d810802c1c1e610882510300d140826446012445d07140d0070100d00700124410841252030160a1020b1100c11040030b011281c490803c0b50100000c0c01742c055204008094128558031403240c10180c0b03030140c5074034091180c0700b0005420a80707540711401082240700e401d0071030807030000711691603100d50324200484c017908043d80950b03000144e41c180412900c1145803610f01d44546021340000c4154000100305010500b0300c11070910307025524007032042c0d514644844200c1e000300d01401000204c0c40c194a50f9007035003000c5c0804600c1000c0c01c1e00c8480d10300251604001d4102040351818504c081010900401280c0b001d00d203603a01011500c00d00980c1d9403220b0304181c44500c0380001d82e02c00d039030203202c03104002041c4501c00c042c0ca1040c0c510b08400d0030303051940c62102401c000e00950000c1040e0300c0d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 520552347 1250 520551097 520551103
    0x3060312030405010f060b03011d0c0304030e04060512030a08010f030c2c0a06150206070504172401081c0f051602130204090606090b09040b01020a06020c0604030e03030c 75
    0x1200001031521a101d485500300036004000c240c0c0a11075031131410b800000e080880002640c125040e0703664429a004004165110310481140c0020340004201300280009002e880d036110300c40ca014000040c4140c5a07800b04049a000b42154030043e840410444070b801c4d4480b40305405081c00101d82d018035491a40d90200c01c40003405400b80310505603000103000710841c192034020b488420b4030050319081c600040c1c80145440d0060b001600a594500e01900e07000080c8103004040b03c0d9502890030307181c00e040850201c078040100142d40034421074031a800c01c0c482d106141158001c0c800003165498010800d180224440c051412410702d080c82804075500301c003420317410600c0e50601555502c10408140b85c0c50450410003540046580c40c280c030034050700d41c00380c003ea5001800410406803141800e445102c10b503c54004041c4040186130000d080580240910750b00c1030045a48103840c540c0d0700800c0e42c00601c0004000e6000101b00300906038170840d91030001c041036010f1483c0c146d4800c4e907142c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 520553597 1250 520552347 520552363
    0x140d14040c170718090f1703010e01090b010f030b030313030b090601120312180b10060e010507050a080f0f0315040501050d05100c18030602040e0a0b0315070e06030103080915030603 80
    0x2682035aa001680d0a01c104603410079000c81c0c0c0200340141e038207900c5150700881d230000c2c01084150014000040303030581c0144901c41081030144c40300303e200c0482840c118058040f42d00140d0309408280a542180c42000480300050340c400d0840d40e4180c50070000152811105a100d0644c003800b0b80313040c4001c070b6003003020003040f20145040843d5104d4000248400f101c4508001000c002c0c0003810403200d02c42000302070003641e900380d465418928902c0300441e1079015224000d0555000000a0000500403000130304041044800560500480e4424051150411203491040d412007840d070840e58a171501c2840d000d00021a0400c0c0d62441c82d850380c0f0399505c1034480c0703805910355a802c580d200e28001c51011001c0c81d0242c1a0071400c03500c91034007402a4000313102c0c2c0c131840d12502d4040340c1e80a0041c05103c01082e0050010500d00030a0120b44e0100c15014119000b03002c1044203101164980c540114083c0d8041d65403203039503c8001c000d21841f000701c0054104000c6050090054954010034404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 520554847 1250 520553597 520553639
    0x3030209031507050d05010510090e0411150a020d170606030406111305090c0c03030c031b0d0603050c09091e010b0603011d070f140d14040c1707 64
    0x140c03190160300100b85031200560a9560854070300c000c0180f1194080001c10110008900902603a641d501c14403101740c90404084000c80c13008030051240460b01440154424040c4c02002602c0031040c0c00300d6400000410100d0907503200007069688550100500000b683c00c519140e402002440005500c135500581554800c450000100c2c00303110041e04031451003804070110954601522498a80b800300c54031943c0d002d602a00d000440451810040c1c81c81c00346030710055461039032440f400c3d1085500003844020a4085104aa04e401e04c401707000d80380b84507010000084150541c10500d1031300051001c1c2c5841048804200003c607200403914800d20a0035000581602c128100e605000d00300f00800d0035008240440001440c81302404940307182c80f00801c4015107030711030312400c03034802c0700056480c0c0c01300d00000c40d02428081e10300001c100c0c01407803e400141c0e207811494000e03c1c950082e40e094640b20070b075000900c5002c081414003640e501030440108681c2c1c0c600103000c01d0300740329400c2c26 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 520556097 1250 520554847 520554851
    0x1e0c210a030f02071a15040204030b040b13080a0306091107050a02060306010201180f0b130506040b15183702030c07050d0c051002272d0f15070303 65
    0x391801002d16010369500c903500c884440084a1011a06034182008a814201c052030b0503800045034101842201d080c0e9402c482116074540c4d458613041600d52002d00012711084e59180135101180c074440203417088048641c2d001c44c08503d000c03020400d9520454a00041070b034100000000280e00090751040c440d4140c030031949a42c0c0d5240141d0041401c06481d100340d41103401c100d42004034104a0781640f07803182083d00c465441ea0b0600c2c00101c9042c002c000c0ca164007090205002c6101c0b0040150710461038a4580f1801c603130007003c92800d0f100e484a49441c29952002e110000009044520581c180c551600d40d038003600300400e0100b40b4039240c0d03030f020722075000000c22000300f080022203034042d8001040318840148100012700080410740c0a84542c041c00c050012141154000c0301e40b081c1d024544201c1200d0401d200c010000007405600b81d11140c558800b44812102e14042c03540c4a5410003618440c0c1043c00a0114004441c40c016100d4412403e0902d80d4480000c00d807040c0316014500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 520557347 1250 520556097 520556111
    0x210304032406061b05100c1e05040f0b0c0c0d06050f0108060c0a11010902150403170f0421050d0201270b010e13021914040e060a111e0c210a03 63
    0x10f14207044406c030080d0303001410051541880740e00441000200d22550002c040b9240840e00d04072030500442c09200c4d40c100411302c003045000011405070210100c0134003903524048200300042e17075140c6142d100300c1d8101d13107840c00c001860b2656881540141800d01c084c10740c0f86041e0309000454803902d82207906100c03590100ca41160025404201d280fa030140a4240c1d08024181c10012500f15110881e41a9004404180f500e240442500c510080b0503d5280c14a41000c0100c1c044c1e50490b0000c5076800c54481c00040864030400034145c1e0400310b9000014000340440c400743c80007202a4403152004040340b40c0c280020010440c050454000c140b04ca084c036286c08180700f200200810029510102c2400c00a130303450442c202c4002110100d41c1c6520402546000340700a44225000b80207141d044940010300ca2101c58201d0051800d81e0030b8500d18044848508400c0040032040720142c40c0b00120368011020410408407143c0344601c604c400801c158400120f84500c141e034000e904050301c03851 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 520558597 1250 520557347 520557353
    0x9590105010e100903020d050304180b030a020d03020109020405010b04060207060305041e0510020a02063301030c03020c0a0f050123010b0906120f070f0f0806210304032406061b 78
    0x111000195900801c1d0a04c81e1f901070500c556244c01c0703405180340c030200945050700308210300c2c071840900000c050040c2042c1412034080000380140e04005801355521100c4500050340c4602c160340c0a03180034130020752141d0030000001e103051500c0e0084001e042c981428400070a0b402c0455045648000c80540540740c20b91400500303014050000c2201742c1d001040c22100d1940100c2c0f882c1c401c10340e02d2001315608413400500c0400311481ca60041c884e00c940860603000394401e800a2080c0c4c0e4640c1400741c94501040607003407402419800c00c0d00c0048994901c2c43c02c0090030b0240c0b80a02c6130000c0d00b00900a45240c000520b1001031041840306040001e0a40d80381c0c076000b040d61b000f0b04c1245941c0f046481c1c5030140c101c0f2102d044982d000043c0300d205c03202d66018060030141d42107501039503640f0a01d654010034440c503940e82d04030f01000468152101c641f000c00030001840918465180c2c15441c0881d10843c90385d92580e81c0c0c4480d00d40e41030150500042740e0001c0000304414800c3d15280500e03039503003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 520559847 1250 520558597 520558607
    0xc0602073801080d140307020f0a05060105090f04080d050a020f07030809010f020906040b0304061805300a0c0f020a0b0a09050906010c060515042d05060109590105010e10 75
    0x154440409d80034130f0744480188030012410b503041300e2082d600240030342d41d809803040e20340030120380c02490702d442888562050001c03a40210380c4022146001481d10070b04000d0720201c3d81007002e0031400104080304000c5064402c0c09040c4000703825200543c1400c108000180b84c901940c0601c0d0f024a10100024041c095950440440f080c4001141c60f841d030118101203494070008400b100400206920740705402240c00b4065400b100017807419402d00c103e1034800c80e0706c07668407081540c0c1c0ea00c50303451400143e0f540c07801c11001040c0a4600315030b1070f021200042c103080910780c841c81c410b070014420880141d0700b2040c01c4a80d85e0303102c800000e042e510744250482104000351074581007850302018400406955083c000d408076150454007541202c4032548044d030300b04854950008802c4c020800044c56011134001e900f441075104c0701481400f0a041c51000d140380821101d04400c20042c1440425203086240c2ca00d0001454840003581040c0c00a0103c40141d01e94078001c00c500750080c0102c83c458 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 520561097 1250 520559847 520559863
    0x1b03210f0501090218031b0d110a0902040f0f050901092f0d0b0d0c050616140703020a05120a03051c1e05160c0602073801080d14030702 60
    0xc50303410080740d40c644400ca030003900503101c1d4440f15080e401c20040c00e403400045003d220600c0162101d0001d00f16028000c16101001341250920700c0c500804c01e042d5120903000e800351140400048c0c4540c90124445500c007425800b16200d0701039030f0024042c90b2545003201c2e055521070480494100881c84070f10800c04c1e00c5030801c41110404c86503c2c510b0706042d100820800680c81e40c148043c4010303004004544004403001820b20219a83c10011420004007401224400c001f009090501580760540308107000f0013004156040f002c8113004614007020000003031324082e00c8904200607504074107a60341403804000b0741800000b0a4441d4004d001c1054543c200541c50424841c1001003012442e40904208210307103280d042400203841074200c01039020400c522070343d807001c04040a445401c000e5220385070568031081d42440304000600007005c490f4080f6000072030f03040711041c080c030b40260007541038110741030541044001f850040e900c03543d40703200c030712840e92034070340d244c44030b1001741d10704000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 520562347 1250 520561097 520561121
    0xd0f0509030d0804020a17060f04050a150606080f010303020607120b030d02061e060109090c0e091806010b161b0e010f1406190507141c1b0321 63
    0xa140640c0c902c0543c021507050140d4400c0d182510101c5d15000c100071160200c031002c4041b84d01000c00101070421104060740c109004006a5440801d144c031440c05144014400c80c0a641c0c80d05010072003641d0140500c1e0340f04c403d620b01c4001650541d0703002500c4020180056017000f0f0065103220201c05103510143c0c2010004003101c00900b40320b40c020792540012a044000e000c06003d1401c03414260b11400c912880c4140e4070140202c1c1030500c004002e00d00071100600b0004202c90304e6080352900d05c010b5005610803840c445445014000d03c500d8003005801100402600340400004010030b80c2c590000d0035809036002c442c0041465000100644c2c66106400b14200500009801c9218403a101c0903216504200606070820784107000d118410032994208408080ca00101e90f507104d60081c15829120740c44c03031642006500c54541c603080030701a0303513004070a90420701c10005030031868a00301810100315019005510b82c4001d021283e01e007405141210064800680340c0401d54024628090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 520563597 1250 520562347 520562353
    0x50f010908090909100e0c010e1014220308040311010c120c020102030c030409060302180f2d0a0f060911030105060304230c120604020a05041802030f24090d0f050903 73
    0x6c42e003407019a031410468005808142261021146801d0904c91607107054165290903880002c009243c8c100e40e481541e074000940e00e003250494403401c003840c1060046004208003515103085082254107110151217450611403440072540004480a0840002c2c031031900389031001090f035000603030451050041d1403070140000100400c40940c0b0354000815079009848200302da070400c015410500c40306840030307110a6407500c00584181d40808000b1644c0540c98034071803182051606c2c01a01101c2374821300c11031a121a500d02c198045803241074000c25100c0c40074040c1c003070150700d03548a41c40b040c041c460180f2400000503051040c801481224980e091000c1104090340210301911040811820391061500a5550440700030005200d07000303d40041c0102502c1d440c00d41004028560550402100e0344546110340244c0c3d810b00600701c0e19034028000e00100e09a461100c0ba006002d01d0540307000701100e5045c00801040001c0d020b56400d854207103085036254030b010a8038980264034a055142c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 520564847 1250 520563597 520563611
    0x50a0b0303040305010e150907090b0f040203070e12010204060e09090f1507020105010e012301270f080a03080c07020d2907030c020c01080c09040e0703050f01090809090910 76
    0x805501003820304107407101f03441c02d141c0c0460000c10801416600c80c2441d81c00214280013110055114070280f5000034200d826010190b004102030340c00480d0f4000208509040b80e8995060030b680b4000d44030a032400031447c00b03003020000380840701002c450500a910840000c0c903000d004000c5040218030500498848850100020310440400c988210055003000c1c00095000340d042c2d05141070706c845d01240b400151401100b054600611201c150406c89042041c0616846154051002c180443d800000503400c0080c2c1010042e0150b110360b401340c0c04200030201003940200b101ea003094090350510b13500c510318000603246c80c001c6a006040324030744100a040d41030b113050014003800d00c401504001e981c3e8440c0150225502180740b6009600011a400741e95071250350401d80c080200c032605801c192443c00410110384d000c00d8041e0060307104107000e00c01e0003401c00c007403000e40f00c8820090003400440e0b0354100320f5000302009a402005410042200200203200d01440d08140c4c06081100c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 520566097 1250 520564847 520564853
    0x1c021303050601030c1e14060705070b0307020706090b03060f0d080904060b070210020a0201080601110708190302070b07020a05040b01050d09080318060f010b09060d020c0705130506030709050a0b03030403 90
    0xc240b5807003400c04010070301d035100c103031080c00e45a0030f0111032513603207c0c209428002091111560200c1c5044405001c0c600b0042603640d180b102660107040d15a00400c0b00038103001c0082c0c081000d82c0c0000e070a480041c410080c0b2961030200324500142c00b500c1c1120044050301e0841200d000302030010354050b080880100c1c0b83c0b015000a0310b8a18000c4600f03242340c2c0754650b806d0b81c031505000b8000c0c2c00140021300113a03842d4001c425a181600d544000c40302c0ba96a54280c050a1200b11005882c82001c1c411051091582c104601005040c2c007000d400e145c5141a4006000381e0504e20689000b00c1d120710328150281c0c0100182d541c0c9a0411809120600c0240f40c40600c03030f8811940f8007070a0a03003120300311b001280014007600c5000d21b21503010582c3d080071041a0181c121301e03100e030360014007001810f0441d40d0b60300180c11120700c8500144440d034100001c1001c003680148400c04d50a14080800640e170390001220b0301252034010b000600c0d6158602ca034400307408080b40311500740c80001000420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 520567347 1250 520566097 520566113
    0x501032117091b1012020c0712080702031c02060411041113051e0d060506030a0503040609030b0c0f160201030f1508100209010207173f1c02130305060103 68
    0x35080c06030703030b40c0920041440c100403a04044c20408000174400901000c0c9200c1c641c1e0003055443c8242080b201215a42c2000015860b41018110b4060038040b60110031410100f20440c1d100d01e5001000d90381c00c840345c00003551900000e0001d09100c0004a4201d081d440d56845040c00c2d140031204e4541c0d81d0031800130514405054440c10740a02d041c0103408105040040f00441500c000418071101d1030203544985010784005080c075a414015081c035200054020030040c0b0080601e601e4081243d13145040c000d480c054010a001c00b0302c80100458800048208100e45c0e4644248204082106427800101e00500c108418003684074581008250702100c0000b0ba40220303000d0000321050b4510030040e00040e401003000860140e40609400d00c5a4824084c400c810100b144080343c00550a0402c2e40240c02100d07140c43da0030b52101c1201c101c414030f11110300f000b41200c0c0f80342e9901d4120010f02c0022a000c8901c0202481c0d80c0c045a0703d241c044440c02c1c0c0b24000e50b0064110340455851b402c1c00c030f42e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 520568597 1250 520567347 520567363
    0xa0f11012c0a0801020306060409020f0f1209060f1909050c040501090605040e070308370305041a010303090605090312040f08060f010302060a080604020d090c0513050103211709 78
    0x112440644070b002499039014002c803032140001501e02407c0174501101040a5004030551050a00040c80900c019409040240807484218041181c460410420f400c0c103145000d016001c1c200c8030b0b00c0810403030a500c1c001410280900b2040050a00080d0400d00c0c18054681141e60380141001c000285c0d0071050341060040e81c0003105c04211b81207000c1c0181c0d03600c07422480f004050240070300403418015403803030030000090060310128800c6004551101d280079020b000080200c0d5a40c0240001d11400a0821a1141e000b080d00e031032550454502522512540c030900040090001e41081e40e91000d11100108083c1140025203c44d1228001600c5400c2802464131500c1050001401c0c2240403d803d4101ca80140109160260880c0d0850340c902004054907000703030300cc02128400890746e03c16a160640200c2c850468581403804100394100408032541c0000e00305030052000c240d11840b1401c05442e260030380303e404141510183d40e46000f0302d4034044200c02000c00c00c200d1007000301d0060b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 520569847 1250 520568597 520568599
    0x20f0f1926183a05120c0a09030f240903021e010b0a0e0702060601020703110607020402070f1a0c071e140d02011a0a030506040b040602090d030504090507020a0f11012c 74
    0x40c41460f0805003190705004480d01c0c00603003c016030200d501380612100414039a4000c0c68241326a039100e131100150720740503070001c883c1000443c07081d0346452015008490b1505400038144104126510025a110070700c0115155a501c2c800d51722410410941c01000080c1016000b002c800707a40c1c0c0b49580d52180200c1d41c08000d0f00030400002c40541c400710b50b030015a0361006641c010752202e00d040c040c0300c1d00f120004076001a82000300b800401c449440c10035195100c2d000d117141c0442304003440c5031960000b40c03c2c0d9060300c40910520001440381008008c01d15898083c500402d0050709200e44000708846640c55a40a0500c51414081c1e042d00840040342100400d41140c03030003c401c1c044042158071001d4065080302e000b080000d066000715581090050720054149003400e00041d06045640c4411804644000b508005682031800740302c0d841640741c0081d144480b104d499001c1d002100400081c030500c001e02000200c0d80c0030f901141d00078007482a42c0403c600d208174540f10319403502040c172 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 520571097 1250 520569847 520569943
    0x303020a1101080f0a0218120102070302010c0806060f03060406030605040b0f090a08070b07020106090c11060109150e0a180b04110d080d020f0f192618 67
    0x2480554003d240940c059401d041803404540d4610720b4801c025000380e254140904000419440c099407251060340c01706a4078030006994010515019085814121258080c4901c580401c913407591248240c4040e40c44403103400b81d5075038032000010002c1c080c43c0c2000300514030740717011b120230321090081c802d01c00c2800c580444415110200f0781039540650420041c00d0a0342000300b500042c641c40142c5130000614000801d5084c0c5810701c95007915031803c1204002402c40c429070f0142e8600700b111600406401030100305070489a81c1c8580d40c4034040c0504541d40100d034000c5078540030b050348560040780580e403804142c40140c5c07400310400602500d041d82d0b850003061007004075250140e0320009032644000c11910b40840048000080e403c041c043c080340040910804900c111008010b084c0182030135851030142c081c010b03000c0d120952000c8144115403000f8015800850b0364519540c00c029203000c404410510601913500e0407000c100251051251004a41380d00190240000b80d01007440600f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 520572347 1250 520571097 520571123
    0x7080412020109050c0d030e09010b0a0306051c030509030304030f05060406050108010e0a0b0c0d020301030605060a0b04030c05060f0f0a0c020301050601050909060f1f0801080115060c03270303020a 87
    0x40707081c1c030900700003c1c05541054178002464901320821201c40b901c28140101e95001400020301c021400360b01c408140c84000400d04c1c910b50341881780c880075240c11101c004080280d03c05031102075110000c0101030040018024919036000c205a03030007580d000c40007151451280c42c000e52204400c0c0ea08a80f018103040010403612810302800c2c2148105000420428006d600d840c031441d080941113024040d01040080d0a01e03000e40001d6020710300400340070901d405e00c8018441056910361080c2c408032010f01007400051050400c207000c40314211500740d00c4d91000340c0c004000b4410108000c0407600000307203000c5c0c015040030f407a20001c0e00880c02000b440c2d40d1900151500d00c941e2844951240d040d200150862610f146502100f0300050502c2060030314601041200c81034296069021441c4100100803040d001d016010140c00e2003200d03a1001e91810801a26100f000c042c01030610008030010304021400d0801d000030051345481c0c02c4042c95490070003a444100d8404150760b00201400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 520573597 1250 520572347 520572383
    0x12100603050f0c070b1911120601091d07120f090203010b0402040f09020708070219150935030d02040f052b0501020d05010b040e0a05010e1603090b070804 68
    0x612244030f41c0b004540b9a2600c94182c2e502242944014032140403081c00209210031180c00f4891100c4070740040f012280d83e40078003902c0a94020008201d1410825500e10500c102c410505180494a40708481441903480d0350340252250090504000040b52800f50710400b5154550000c46d1002e000354000c1101d9040601441b00780d10541c01050005c200c050310030408020a46c0c01003600300d0182c4c8805081406a900003212441f01959582c0c219096100074000e1900c0109140002c000a007441e13201c6034900318003031070b100a881c2c112054110703e541558884041015414104100345001d0381d03680c40d50300030144000d400a000f0350711400417441010595051101a100280d00740000104030151100c8040105528030f0704102c1326075409210000500d003840c013915002c0c1006c80044c2e5151400c20503040ba0b512002032980030b03c80c0c10507004011a581c1e0002e05d5400c2a40c146da0501d02a8101c031054015011b0b890000f405030b1008020041d00c11360180b10715000758803884407001d51010b190 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 520574847 1250 520573597 520573621
    0x60902060a0c11100e01051c0e0a1e0b01031e020a0f0911160807020a0e010f050f030115060e1206131109090c01120b180a060915030b0c1210060305 65
    0x35403101181050401c11130660156028080d01140c00c03406180a41d230032002281501c1c41d02e03007030142c0c5900c1101c1c04010484810b482040307140003211006040e6819440d0844c0e034590602c03000d00a1411001d03010311416550700aa20501d801619419100d80ea40060001a403075911804040524207011000344a503070f2000c6030030540111105c0200d44072651103c1ba03444d40709020890f8060021030000072103038981c449a42c000d11aa07006200801d00d81010311034450f0764850302c42c0c0310f41d01d01810b010345103203404605030540c0e00750300c0d00c41c1c0d900112070007242030294004440c070070500c40e040c10404101e0000041501451040e41d03060703c046259414031490710701c1038608082d140c0050304550707070551040729200295440c01e000803c192000d000850b550ba21590b80c440401608142040506610b5014020040c00030581c00c0009410792008601d07642c00790f000051980f01680301046c2e54400310800d840320402901d0303501174141000800801d505000e40f0594002c6030400c00010306101804c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 520576097 1250 520574847 520574869
    0x71b03051e100c020304051801050a300314041e0501030204061e0e090a05070314060a0b0306060702030706170906010b191e0504260d0c060902060a0c11 67
    0x7400500320b58100140c030b04040e0911000040451009000025180d81c2d461500703000c401c8512216962541000280411390119400007410142c46142100141003a594070718120074044040c1560000c19107012140440702030490b4601c5180881c02046000740107000e00380d1507000d2218180c3d042d655000650a030b010360701c1000080398100001d18203103003070240200e040d08a6481e110080d0035090000131280302095404050700c0d503550082103805c0340c0600c034500c02c0c0c4040031006801443c02d5000034070801d80a004e070341c1ca107480c08400300e412502ca0300150b40119a00805582415446d00c0000f84007140c2510210b541403040c40c04120860b8000c00c27074a0585002240d103618048203804035902021981019904110102c1c100f8001380500b004180c00740e29062381ca650b030360351034410005205540c90340c10301c81030f210a00d0581c450f01300000f81d100b0000d1007410040c42506c024141503004009010029400c11800a4420350580d4001d101c10401071154100c440f04000a0007442045250 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 520577347 1250 520576097 520576153
    0xc0715020601051002070302041b1b120c0609020a030302060910060806010b031312020309031608100504140607080612011b12110403081206010203121b071b0305 71
    0x45079006008908180c000c40c42a20f405004544026a81340e02107411180341003409a18040c40c0b007400c1c01090780c0a402043c0d01e40780500900b6030b202d0a500c41c1c507903689007508000d0a20440c010101c0c00c0003103640203503011070b4000b000e4612070741e9a820003944409084a01201c54040d10010110300961803080030241e40da204018001c0d030f82403048403034540d48080c140b120300c1c2c0c0745d07092580002001d25804c540114140d03400f0b10303103402a20341070620340361007000803003c0e4801800d001c4c41030500000343c0f0940c2100084001c0b407652941d041418502034000400f0720540160401c200025800000442c06080b0070349051418002e9400302074200c07050a90702e4030580d0300561002c02a244155001c54a0004c503150000e4081e9035015095215449940704880300c00c000305998960703071506400030303512030400c0c00550329181510807030145e1074a00608841d0400c1c0d254a40c0c020009035202502c0e0030301e501c88070b440d20444076500052500c144a1204580b20300c11a0402907002802a14124841c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 520578597 1250 520577347 520577353
    0x61715062407060b030a03170c18060f0c030d020418090510110912060a0e0f06071101020d05180d050c0318040e06040b070f1e1818020c071502 63
    0x440303900c10784680c0c0d02011007036600795168000303111169424032000c2c0010f03211345c485172101142e41d038290214240040821094442c14010210140301c522066102c4c000100ca0465940244102c00701e00c60042901c95411071001243c3c007035100c0c0040d4000e205071610201e4480071040c42030711001c181e0b864040001d0041e04034511641c207441c056000b44103021914503043e402c2981038404164040390700b031030344085a440341052001011003441040c01005aa01c00b8001c2c20182d142c1151340d84038050044030030425803008200704a1401e5065500c4c03026140400c0c00141442d0919004c0102c050058200d03d009800c040301015000344100c0f450415088091070402e0a803c0c844040d105d9070f038103071030303001919444802240d100030301c8020300c03a0340f1442a8118030304000740c0040010015650107404e000c121315840e8400e424100b0200c5070014185010040058440703024100c1a282d64064602c020540c60a41e424844540141648020040440b90121342d20386220900400004580d00560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 520579847 1250 520578597 520578649
    0x80d230715060b0c1e19030f1707030e010c090f090b120a061b02160b0d0212090c0f06130b072105040e0c0c100f06171506 54
    0x45200301d0341c00000d055440002000c542d20100c6107415801a05000c207aa00030042600c00b40c8040043d61031206955001040d559030100b204808100c100e07040a0240b1142442072007582d0b105016034450400010060303a05420201000740140000140340c501550901900c2c4610500c11005801159011810052402d2a0884480051043c00009500009442c02510300288100050040c0b184108400145142048620300c502001d01c0c0d0883e0441d0400e07603404441c0d0a48004c0390058030b44045041da51003100c1c0d01100c00910070030307015082111000d406c00810307000200b0440036188007911500b001700c600304204a441d01c2400e500b280c80a05801c41444501400400740103020701c20414034065801c1c00b45c11411054660b10f000001900000e0309000760f01c1101d5815800c0f017001c610150a2420103031010340c846d804020421203250b507484d6642c180d010503400c400000c01c05010a032500c0c0342842c81c0c003601c8400300121141800000e4001c80d06601b8403841c0161a80040021080d0300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 520581097 1250 520579847 520579853
    0x50f0109020a050c0124050603040b060f2d0a090b06070f0303090f1104060f03080d0906060b0c010501090606020705100c030e060c0307020102011b0507030c15020301080d2307 77
    0x7500030600d10000c0003070038004c80401001c01d1062070400341603030340a0f50100c000024200b08403000d0b40c000c1c03400342c0000d2040c00000380d051070610350000030072107540c603541c0d030b400c00404d001c01c070081700100840d402001c51130180791200117010b04458040e245d071641a5103032405403095400c8125902d8008504101c03c90210340c54030350340d5140701d22900c0c01203441111070300c40003103125002100b40c0b0526180c1c01e80310f40300e01e09841510011710b451a00e43c007480c0d1564952600c0d5014a040c000000307511001c0c00d00c100002540400013920b008051031340c407108070040ca81c0c0208400d000d0082094500342003c41c600b80006021000c490300280102012400020100d40c281c0c1d10100803001c2c401450003e54081c0d81c0d59003e40325101201000750348656450000a01391803000042d0604401d003c103100b018942e00c5000c44a0558240c1821211050700e03190840340b0720030009070305103058030110010030203480124074604409515511050407850b001441982070700c800c0e98255054070204030b20800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 520582347 1250 520581097 520581101
    0xb16030c0c020918031b0106080c0a060804020f04050a0e100b0f012a06091e03050316090e04030c021005030c071707060e0105100611070506091207060f0f0201050f0109 74
    0xb01c560500d0900c0403a01c4d041c0000b514640001d0700601c0700b00290459145020000d10030f102c010004280286810b900010125000c40c00b10300070b0238200510710340042d080d503c0ea0001503400050150003081946003401064000f031074401c482141d240100710102c811207916010b00c204031800280300c84d0807088980019a510001c1c03d080009403a192821008800c21000d004105140125404101c5600a203016006040d814a0058460844525000c00b20f0740c00000c0e20360008050b40b03040314241c288402902d51421582c010813030a00300008100806034401c00030400b1602c207407035040c40c0c0e0f49485000d940074002120350b024200800e210a8000c5070303021003001822a8841000d5180040c03d0303c0d40c0d800e540d10001c8854282e134580046c8600c1c00000074540b4028007071441d00440000c1c00101803502c4044034401e50f480747a1000708440034903903503042c4095118041c0300125602d4583d20754000e403c16680c0c4403600701051400345910621801030040b0340c8598000030300d50140d41c3c00c0a00c4d030340c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 520583597 1250 520582347 520582351
    0x30d0b1203091908070806061201020307020c01030f0902041d0607090308160201030905060a05070e040204080c2b110301050a0209011e02031b061009090b0a110d090b16030c0c0209 79
    0x98007490302d04002106541171241c00c02a00c8034001800180c50000d00707200340c4084004420000c2e80c4108100920980e0201c2c11584003142403034040342c84072140001d03e010344200c94029500034a008100a1903e1720500406410440b84c002d0303070720130781e030789007081e03a40800d9880701034030400081003050b4003220b0300c0c0c802c210301c240305042c00590320146855443c40e184086445c0030f20304d076a44040c810391076045480034148200c110380a5182c01e0034080c0241d1940c03401100d243c054040c2220019038145210020840e85290200d0804488098200307207084d400540b4044e8041e510f03080104010a1150088540741c15041c1c40700c241004c1454016410002400c5080e0210300052144915400301c680303d5a80c1c1c08141c0000301164180200040d0810201d540218045450010139100080440005a034441030081c0005440803919440c90014170406640e40c1100785003018030410060b6900c00e090040607c80380d01a6462100f1006604803220f004000340841d81e0103900780700514100310b02507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 520584847 1250 520583597 520583629
    0xb0306060d0612110910030f210215060405060a1e0512010209030f06060a0b03070c051c170c2506020a0c031418060c0c0a0305030d0b120309 62
    0x1071034542081e20440031544250480b55807019101d075040180015000c00c24000d00d001c5400034900c0c100749003030600300e0744a0721000740102007410f181018401002e1909054101c501d4080760300f0541450000c2d1180010030603032403500d180720045685410b05215542c89035201900503240a4140708510001c1c0760900c2810000050710300002c1900d480780003130345440300003100c00581c83d84c0d102420181408440318070350729594840010800c2c545d1352441920200c50000500c07a17075903107500004650320b483c0780601512a11480341c4034200300038004462002d01485584075000305088040460350b2900503180c00c03080690901c2510030a510034440d4200e187c0c0c9464440032401b4041d983d00e401e903003115035101c000c41c030748984100915420151040784040c811200b0362900b07604072882420f0340105110b00c0c0c0200d50104004a18580c104070790b1094881c0104030010b01d0366285072603a620350265052065040c100f07000503203035007800010301c2011101d51001e18103102d1040b0034006140c42d041718007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 520586097 1250 520584847 520584859
    0x30f020303090316090f18260301080a03033e160803091207082205030f010c0f0201020a05030f060d0b07030c030c050a0c020108060307090f02070c050102030703090b0306 75
    0x600c82d07650403c42285907120701844c075182c00e4038040032581129070300100c20000314101448034841d41c0a044480024580c0700d08079515019400d1000740080e850201c0710f0701815070000000c500c9032000918481038038070135a014010042c211451034044c02101c0c03540f10780c8103400000b000c1c1d210440005e910410f80442c0249041c2621460000080301d01c1041c10740348088004140295050705102521407600c01210b503518016955850881c00d10034070384149026606c1c00c0e0041d49a2404070300301c0c001001d0090860319000990034903a07000300040d905c0c50001c1124920340032482ca006000783d0300501081c0e01c405055940e0400703100c6c103500c401081c00303a00c060f0205030f0303000107140802c5450290707901d030b6000241b0101c140b90103402c80b44500c0c0204180103042c055512501c1e88848080300d29a42840d20b244c042d01e0707041c0407903e0400d80d60851034a50781402002c0002544580c05442c0d61030003690040800303581c0c2c00040e0307140d00c00d0400c060300142081ca82440b50960300c40086800200c09402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 520587347 1250 520586097 520586107
    0xc0809090c0d0204060c0c06080c030406020f070204091b05030c030d0e0d1704080111030606030115031b020c0a0e010e0c0f070c03081809160e011b03091701110301030f020303 77
    0x5404204d0b0f0117a0441000b05907a203404005201d25021210f0142295050010107410304d004904c40c40d00004000070422500003424200002040d0f0076210140d071301400901414108d444c10a0b87c04d81a030850382c1c7d038540c00550015007450005a0402c2103140079000d00791080d400d5a0842c0da18020184440d000b506680b10040020844224500440020608180c440c0d080800d400d003521060300582402000030300034001c6503501e41e02140d0440f409030f182d403450790710440720030b9000d800f040181d064115100040300c00c0740c0c4d0300404c0c44030203148202c0354107441c40d84410000d0030100d4207020358040d0f00800300008070400f100e04001e11102c940c4000c1d050404031f1694407c058404c4580048800607000f05a19480b91b402c961105a8108102c0d200310407440c0c025890140500e1003d1101d0400c100c1d181c0402c4564004d038400c03408060a00b010705920016410050101600740c81180303040440c0d80060700c101c41c410300ca0140402008880d0f11318523441c3d61a003464000003000143d0b4140000c000f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 520588597 1250 520587347 520587367
    0x506032d0c0d0f0b010602031c0f140103060c2d0804140607020c0a060c03080a05070918020a020d020312060d170c06101a041e030210080a0b010c0809090c 68
    0x10b05100709600c10340e00d1494161507032901000500d0182c0c0b0003010b5601c01e0041c6804842041c841141d20364902c0000202d43e0051482580a0690300394120f002c030240364008014000c8503042003140c040e25445da04089501c6c9044102041c401042501e5100f0034500800780030382c400c4280b250400d02444800304800e000f0900c4030305214080e104100968000d042184007403c080c94010004d0100c3e08281388200b83c6520050801d4000030042081d203035a031400103882c81d004500781005021040e136602d1100407001609002940300c000307003201510455231141456440001201c1d0541537102810580303440380c40a019000c112007000f2920707c2c0c04c4205054040c10108045c0032071041c0030b0b005001c1810001000d2528410b5034000c0f40c040c2c0e450480f440500680b44040704d007110310070b030302034909103444500c061440c09107608002c1d405000c038480300c08a16845525070340600c030400c204200209800005403100340c50b40d04014285002070243d500c0d1841c0912160350310502c0076540c50702d0700803902 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 520589847 1250 520588597 520588609
    0x50316020309190501140c0604151e0b0a0e090d05030a0f0e0a020109050111121b1914010b0a06050309010e0f0f06390d09060b03010506032d0c 63
    0xf484041000a0040041d90780c0319515640840b006101507241915a4200361b40310303180140050800d60700d240e82ea05a4000e69402100100e54580000d401c41030106400000780c0507c000c0c052003102c0f01c040102d844554110390382c0c050301105002b0300c1c0711190700e0403e691036040148000d1600d0307510700c9080d4688507503016804440320700c0c601800c0081803a100242400c1c0c8681c200c1410004c2c004a0344020040016508604002d00c40036651103a0540241c04035001e10351031440d842d405000313502c100c0c9000408001068070702c1060168100c0c613000c0750080c203c4100358030655010a0083c01001003c0c042c2c0b00450704005502c5c0003080342c40100b00301c42c2c030303040c40d003003100d440d0307031b10109100d00c6494042c00711940045003481240a0314608c2241c001001d06242d4800040168074180d002c120302802080320b080d801800014400c647c19820300c0d43c001c10300300c86510b02035402e0000040d26032502080e0b00f0304045c0640105440480c40405000d030100702000d54035030502c0741000e040340b00d03501e00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 520591097 1250 520589847 520589869
    0x30d20040b04120f060203010f090e1b1c0f080405030706110309060706020d1b0f020106030f0221070b0417060f0f09010b1807170c03010306020f0409050a0b0103110406050316020309 80
    0x340062904140341211010845cbc08800404051360010284251052840c2240008a80d811641e070302640d0301801c0d6841e212155100021b08000046440740d041111681c040d200701c0710102d003035605507075550001b50b0361103111903155162a0008c0240048600d401c1c005002610f005890040c202402e01e1703541d10131508030005000403205a0315101e420305601c298101421141880203111403461541c070104a03107501e4038004d01c61410380d00038204103015840e000781d072510800101ca00b0260703100030303184850380280200038080801201d10f0519440c006040760260140403400d94403a0780307050380c450541d0800782c245003040d500c58003446125aa00d402e03401c691340d85000c410300c450504000141c120081c61541801c0b60024104010075004100c040d2811246c1015000d603948800c0300621030030740f2954221707151480ca450f0a0000c0110079512140c079051302a2000c1221240e4044850442c0c041d900c01d06002030380800015031003035103480000f0701c005001d0044a0822402c440000c1300031201d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 520592347 1250 520591097 520591109
    0xc0f0417070302040f0e0601090902060f0d1e09112e02060f01050a0b04031e020907020c040f050606040b0906070c0e09010f06050d0b040f05030d20040b04120f06020301 74
    0x1c21014000c0d85401d105510640070004420405d451210070855202c02d014801d800086545001d42c030b065499050465408070800120305541d41003482c810380050814810341c03c1c1c01c082c64200700307615039140d02c1a402c03420741110080104562a2040061260380b201e561103046456810b040c060170785521034070102010301e8018090714a00b003042c140705a841680950700c189055042046603524480840d800c6d26007042d01000303c841c0800b15000d845400c400d0094120150000b0004855800308800211034000c480c2441070700c05000030303003042d00e0054a945511000400041184d802180000c160860024042d58146915a10b078076004101c1a4810080b50b8402d80030030032080000c0c855107881e95641482044294100300c041400010541e100030500c104850128007407084441c060b00d00158801c0441c1d5075aa00c1e0324544003c1d040f401010b043d11200d45581e800307224529001d032400c4d28024203486040610380034114098030103041e015a09460100401c101180341c0c0d000031070207002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 520593597 1250 520592347 520592353
    0x20609091306061712041505030a060806011d0618180a05010f0b180c090d1104050106110d0903020315041b030f110303070f060b03030c03070b0708060108010e0c0f0417 74
    0x204c4410a0705110310b0325144080301c2c03001c00040c01a1441ea5690518400851034050340301c0c3c0c1e03840c0404004203540c4e0849d108510801000050203600790040005824612502d0401a200d8900f40440c9181c045100d4a03801c0082c0001031611124400d650700380151101203035100c2c4900c1e141d15003104c80440c18811030588030100e141d40350078000c440d0740004521203522074003031600f04070400c51401403498041c4500001d4900105004600100303000500004108100b03c0d40e541c80040c101c00c1c40154807090601420481401182c001d0200a00304d0340c010380038101554142d4a0b1000000c80100304a0f240b011036100c001c0c090b6000f81c01d00340a540b0500c880c40d084030640c01c00c9030030340405169042c0f00341d2040049100007414070301401407281c0c2c000000724284400c940001d056000c4e41510044c14800403490109114078035440078040e098039221030b035454458000441360003209005002c010645507000c21149041031000b41942801d50308a24141a161400000c51050143c80780b0380702c0e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 520594847 1250 520593597 520593629
    0x150706050f0709030309090510080607020a0201090b09010e0613030c0b0901090902030127020f0f19020c1507020a0b0409020a02010f021c0b031e07080d0c02060909130606 75
    0x7080320410540158843c01e00c003810304d00c0d59400030400b141c18003684903095117490224038142d1050700150082c1520354103443c2c41d8504140c0c000e60f20701c08200c059001a00381c0303c00040604211048818888042e5540403468401c40d00b8041700340d02c00303035072880c000c0d01282000022803001c42c03c090240c03401020203a40c43c3c0304440014080e00c3c00d9003004404601c108010800c4001c2815070300c0c03d02c541c409020000c4403015a409009026402844902490016100d031195040e403000b0035002e5a580d000d22286034512000701c0e51044030b04003080d0091003148000c00320340b07482c030081c202c641e10040c007503002544c0755200d480c150f400c10f0340050001a0003044030070300703190207015440c011002101c04504050f82e0040c00c0501c4020800e02c5680d035942d6600d90640c03038a081c094145c1c8224814264004801086001135070f070b0156100f100c00328024410101809440390022244e01178000300018103080b044010400822405031003000b40200319007602c0c001502e0b0f4081c4400078480328022113491 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 520596097 1250 520594847 520594861
    0x12140f0607110d30050109020a110303040503070f0507050a06050c0c03160501030c02100e0a03081302090406020a020102070203120c010b01090509011401110708100c0503090a020105030615070605 86
    0x1500301221003483c0c214008440041d50300482e01c0390a41e02c0d244034240c0c2130116114800c2c809031540501110282003600102e4152210307001001c4840541d0341d1443c2640b00040055100c4c0002e40d801400c54008000c12404a54058501d0031407a004401303580425030b031203000403200103143e030055011480219070b04980d0402405060501101640905007400000c0900b12481105026042c141603079a0035451400b8420410b806000b03243d50030030444803031034003402907842104020403000114000c00086c01001c00a5502c41003d0b030141c4806495110303039449401a4206454403000c56600784a0341001d6a0100280070346004460085599a52000c0c40c141c01e580b900d0414038140420203004100b0758407082c03200c50450700301c11404034091000000490700c0110002e41c00e0307150b100d40031020645100125083c814801c001500300008052020140c60600044902000c190004002080554003d200a680c0044001c007804510300c03402407007000c075400c044815143c903942c0384108800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 520597347 1250 520596097 520596107
    0x2030405010f0b0d12030c02150c09190608010311010302120f01030b01080d020c1311030408180409051f1806050103120822030212040801051506090a12140f0607 71
    0x802c01060b0342001c085001616203030010205d080003481015034621805144a2081c84842c200c600f8000f03d12100d403c0985401000e80c2102c0040c0307118103600244a190340342d0203110b040896543d6140c003002c51b8130f15120b90a986120100c00750505408021940e40b401120085e1441902c5189151006506600f8230703080d01041600101d01c40d507c1b0f0507400d01100d80001f42d21141d40c0049420540040324404503101400b060035003045140404018441044042e6019004403040018402e0500a191003000260b0303804001c050240d410007490703520100740d204000307019880218004541006401901403000085480070f40703000350b5410061003082010318080c41e080c40103150004003818007001c929203404881c842c20a00b4079000d081c14003010b000340601d8810650840700369032550b40d030342c5002d806003d00315415009908100c0f0859480e140c0101034800c0c0c1480a4000c404072400c2c1003000c40b41121404058507840c0c0c00d0142811641820440e100008141d44050525400d00f00750240c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 520598597 1250 520597347 520597361
    0xf0408160609060c14010f09030807120603030e1e030706030c140a170403020a02060313020906030a080d0e010f1a090a0e0606010e060918070f110601090903110102030405010f 77
    0x10807107a810b04105450b8000c04007003145030440d0741c1104203100816400c4c01840c254210500441c10072810000b03040c2c114080c14070600058a8075038000030003c1c107400840702e1a000080102c1d2429407140140d0501e4441c0101c90200c1c0c166640444500c100042e1034480d41d54450700000344c80f0495425011b60109110884e004580134050610350300c503d018000d13074038404088003416511000102418400c002c0da5510540141c00c8590301d040c03e542e6220b6042040b8010f9016026000110b034841c1000030300344800d6500f28403c40c0c00d040304030b1625000b4104443c84030f6500d40d00c89010706982d4059109254030803212040644000400c40123126602c01d009040ca18594900584071082c06c8011490940c0080c0902c1d14100f0340b64900e001030352501905140a4105200c041b98502d52401c0449140c0910800d8540441ca910701c0807084034128540700f100d00329074100e4001046481090f41046501600c40c2c203018196440d900755442c00c90f002200c09580e26915000c806200c42c1651145d12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 520599847 1250 520598597 520598609
    0xf09090c0a0b0f090d02010c080f03011d1e130b100e060a030302030a0c1505040c06020705030c0d020411070506040309050a0f080d21090503090f1f0804080f040816 72
    0x142040380c03601191800c4d0103200c0006015040d4521901c0c01c581c4a500107121550f4005103003503c7d0307610b42c5d04885030340d0400d0103003000c10107001c140d501c494030300061501d200b400302c80482c629043d10710360080800407003e0316240400301481400e1001801c2140100e214091650810440502d0000310507040800a01058003850380c031101400070950202c100c03021000c042c00c0c610221500751506c41d58003003000650404080c54034060004101c1440c010400b12000d90f421156090380f5442010707159185074400130790003180d1071040070040c28140c12814103040100900c9040107a281c80c0d140c105501190218000b43c40341c4418403031441c001013110003800c03503da924800c6a003090509641d0752a6100c620041c03255490701d441c03501c00c00c40d5805034901c1c0744c407409216a025514000b42d494105d944000d1064500c200c3c007090500b010082c0311a006000855203540e0100b80da000c0e80c000e28003400580c0c40c0001004428458049400100014003400b0000c2490807211007403c500010240c00030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 520601097 1250 520599847 520599869
    0x51002060a051605030a111b0d0f08060f0f06040902031602060c0a0c0308090a290a02070c0302150c0604030f0e0409050d050f1b01050402190806040b060f09090c0a 72
    0x5070584540c05810b8a611055203400007c4242d01c001d000c14550181c1d1600c02146141140005840000404c10036541c0049880d900c00c803510381c80050b00c451004903a456040841c003541c46800d480c01c10007083c940f50014007960302e001c0d296021f601c20b03a40700b00c5c4c03080307001e210001180d44800d5041140a034800c051450340e500700102c00e4001000341c080d0a9001c1c6c1001080c0d00800c40710f03c010310889141e9036100024200d8114454207101008500507a800d8190904c2000030b8901c107018000c8481c000c3d403080004940500711341c00c0006031009207070b07030520441e402d0101403070840042000c0350285019446d00403a000403100018400c151695030702e4002c074100a1440e00168002608003101116818110f4644012815080781d40c0a88400c0c1c440780e50f00506180c0c3d1310b180c194080f500407402500e0f2107002548c6e1304030001d9191024030a5546075402100094046428000a00d42012004160400302000800040c6804106459425503078002c05801111031604800080003850100b40c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 520602347 1250 520601097 520601131
    0x14010b030402030a0209090c0d03120e0703021503190203040b0f13030815180a02031602030a080a0f0f0c020706080a090f172104030e01110c1504051002060a05 70
    0x441d40f213513208903009001e803415101080b00c1070002c0c004602d4000b40500050150720440c10020f00725130500f500d40980e03624042a07515000700200d403c00507290058603100d15810011030240841d03000420b040648403240030041903517000380c00114000c2d0301421510000d800c00108a6028103001b91103c2a569285207840d400a40c105c411164809003003210700b4080344541020036291110211148070f200d5008040090b0141039034003841c041d040040d42c0d8a10303400d02c403505a98078484c0d141c0d4440800c40b0400000d44a92854214a01008540c80c0105020400100d000296400f508a410158010080a00c6200c0e17108a0250348181d155500380058862500c810b032000745203c0001d40100384424901e00c0384950702d82201d01c13141d00c0142e103080d00d4580928002c010b010948040300001c0d0b035071968070015172180c02c09030706010005020703000c407410306020040d000d8400d003001440726005010000d815998200300100c502a0b43d006414985485079040c8101c036001820300c0b0701d0040100c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 520603597 1250 520602347 520602349
    0xc03071412070f11011110061a0702010503010311060403020604090903080714090607020d0f0c060f030203010b0901050706061a0a03110a0512090304030501060f0503160503061911040914010b030402 87
    0x3d0640040c07a00041c035035507040c154800482d580d0f440b212008a0a2081401c03d06c0502c4090344150f0807035400d0554686240160720240c10326129020020f07000510903c018800320341c1c0b80d507502010305801005107182c55580e5003c1501e84d00641d1048a007a582c1c0c020300e8040c1900300840643c06041460903020b550040c46240e40d0a000d40e0300c0d0700c0d000c4e04c0c000c0381030011074448610400e0390b260010119100d0340320b249090b854421040c0101c2c0b0004032010307118000103000340256030584060030151402e01c4004001100c1a42100030191103242e240c0400146092981c4040301c824210391803080e80e902c0c00c0e8000602070300c1d2588207a50341464104a8540c51641c85426a551040a074601054030340310316900a11714000d0741c1024009501c3d2880004000c1c48662401c4100e950560a41e507025042103000b9440000500c24240c040d040400051507038001818254043c50f0080da001403690301c540c00d1100355800503040f544000340e45004039200c8070080c031400b03030051001c120480d280d460254 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 520604847 1250 520603597 520603613
    0x30a0c17010606021b0a0e0c04060f1106011406070f0516050a0305030a0503130507090b0405060102160e0c040e1305011404080d0f0209040212100603150e0c0c0307141207 75
    0x1184d002903012217441185843e92241c11103001001c0070b0240030340d10b0908102c55901c9500c203106100c04580c6504100d02201d015407110035031280201b02130440c5078a4606501c030014100c54146612400c100050703400281164011031000340a41700070a0005940d42d0810240300c070a801051103104100001c2000441c004101e0340c0701d60311860480d442e40c40b012850000c1c0d50785000b0007040341c02002e00105103070701d05500c04c01350028205c03000d0103da2625001a6213960103191740e034040320b0350501c003440410f141c61104c80e002801e16132024a001d039a00b6a0300030300c1d0010ba40c103410b030115800c0c1c91420702c842400756075544202c80031115414140741d0b641d420b0a124201881d200e07180c5031038a22502c13000c6070713059900710000139009650742c8071101c100c8142c0b0740084407085000c1cad00e50200402d04510074420503102c407504008180100c0d0078100d07000c2ca00e050041028202c00c0b4100b284410440c02130028190b0346115402040c40c07803100c80c1c00f50341880d0300d10000484440090280f4004030f800b06c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 520606097 1250 520604847 520604863
    0xa0e010b0a0903080c060f060603010b0306100e04020409060503070905070f0e1f03050a06080102040b0405210109120909020a050405060d0b03012d0501060c0b0a0b030a0c1701060602 80
    0x20040c80d40e9200c81008041d111088140c1c0041c3c0544070118114569101c045410b0384a190b5407403c4030600d82d80c0000704441e60000f8025201a00020720001e030700d03400c00da03900c00031120450a080382c1c407840803000182681e0058004c0c56042da201c500c10081820200404809007a8681c02400945001c060042c0202078050640e01086001c648290498032800061003402c0c14061002001034041e0001401400c819905483c0541c94980c00140500c8103200307407815a01021401403806180804205a008818039444103203008681d0700741c5c60b10800d1003185a1a031203440c0c140d18007521810040e101280c25480044014010805800c1036580201154180d490440300313661201d801026100040592003850380d05907282c40b03640035030a082905a03580f010000c04141c541044000300f40000e40d08280300700000b08600503c0c8400140f00c0e611550b501c81c003164000525444500b0000b4540300c04120180c4004002c001d091003412251986a0340700703003541000344000e5141c01402540c400e03403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 520607347 1250 520606097 520606109
    0x90506090d2f160608070905030d050a03021201260106120201110a1403030108071a0f0313060615030e150402060f090d050102280801050f0103060915140a0e01 70
    0x2503001001d00542000d100010b411111084403010801a5103058801e8168044c010101d1031400006032014400d6803121b041d5030700a00900014210400240d43d150800c0360010280343c4c0071301c1a03114880c07c04580e2030080c0769076446050004051411018884202c41c5520036036414100148a800c0741d82e542101d40d6603080c40e003450000c1007803502906018500748020000740d04c04080403050000000514169011401561801075654a02e5414a101040940c072000010b00090340705041c071034041c1d5444800c10300310710a100700c01e80e1510100d4100760000c00360b01030781c0c84d1818a06a03141c0300301d42c02030a07007400811041c0700294411002500c0140b00920400300090440b240551050035203000002c0580300380d10101c0f2514105001c0c0d004a102141030300d6111a8484c4401c045820700500c0440544070010a64200824010000d144a0000303050503166180010400014850007880c5030400c01c01e41481410030391020303424108982c06600c00c9070495410320540b0400c403041d40c11544 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 520608597 1250 520607347 520607387
    0x90501060c0f0f0602360103140a020c030f0a020105041e0506060d0213110d051b070f030306030b0c090f0907020d0c0501061e0905160f180302060d090506090d 70
    0xf20f203881006441104a08070740300711000c0d990440820604074080900011420068041301840011022180b42c0349140b2400205003000c55560200e940c000d11801c2c5540c000c6e02d2070080112201520342d48056402c0300141e64940401040c0820007407501d01d6040391000100a8203116102c640c0d983c3c001810300d074454001111b4840456035141043d0010402c01c0a0038000d10024000d001ca07240c01c070710010b46000d800c4c000054181c102201c02800c2400319503500c6400c28140da21500d142401c920001c03410706070f4811011011071f6040d0f4400d40301c1c803c001d0040e5074541c0d00e03005000f410b40c0c81103841e5016103072410500040503000700c0d00d20000400d0740f0301440c05d002c0a092080c05051150f02084d5030729203c9120060889441d02c0640503500c2d4403200b031100b41c55812140c224001c1c00480540010741d903490340b040a0384500d600310410300d00c0342c00041d0025240d80005030740d80d000a0545c101c1603a1001980c003084414000d8542c0141c101018010003903500d5000350100c407141c0251711205c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 520609847 1250 520608597 520608623
    0x10507080913050106051b1527032b0c1b05070302150a081e0f18060a0f0b09010506030402040903051b07051206042622090501060c0f 59
    0x40c50b0110100d01c95200d081e41405076507540c0b0070152060344031070f03484615480042d2000c8140311002036030700310655200302e9104080d510440d49000c245401001c00c40e844549410069088508101403e054054006841d58a400c07104070f00701c5802c1d07000c004040180c02c2501c1a0070760f94104c8504040340d450700110120603451440c016003407607000d07003009500c4802d102c0c03500e42c05e240141c0504024141b58950001588940380707000c00c1c02e20381c5129423503900180e800040841c1d69103a0707015000615112140e000e04503c486035414500c00315680c0b044180e0710b010050071251103018525003144166800c0341d4075410000411000d1100900190113261903542a80c2018440c0d0215807140001000450f1a4068208800d8441e640f40c4116441a00027980c049200d1070042165070049600041504080c0d660041410303d40c255144d605c10f5400040c8010f0407060413240790300850702510110f045110b801c1490f0340c0c1c102e82044e000202081251230310080000c0800b070400c0101c0b038000c803a400d016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 520611097 1250 520609847 520609849
    0x7110c01121112010906240309150e0c0a0b130b0f1215150a121a030307150c0207120b09160308030703050708270309090106090807080304050105070809 67
    0x76107009402c0e4a4010000107982004803407151407181a00c0c800302050040c242c2d0381d0b40464071250849046000b036880d003200301c14040e01980c030a100039440703240509004502c1d442e0820480d030354450703030307911580103400c1c094000d18002003040c0c00383c00021041410000745125002000b483c1380100800300c6000940c048000c2c0305a8255807000410b101c04555514200c500c02c03205946558840380030350484524011000d070600c3c10759403201203569546010140740c0039840301900031110150740401c240d030305040a0303480910080017510701074a03264400c4601c0f0001030084408113030b1407004540240384103100814221401c00c205542014508046403100b41d1000c0c04d1011148040140081100000040024001c0a584a8603450710104480c0c1c0c0d98240550304141c0840b19a442c0c0a00c0300d0079038003c228080441c0c030154400600b00c03400e055240e03022501081080c2c100b14041022004100161607040003500c2c094442c8101450600740340c0720018003940500381e4020100d0a0200341d100032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 520612347 1250 520611097 520611101
    0x10501260106081e1011030a0b040f02030903070c050306010614220f03050d030c050313050a0204020f12130507060813060903030b040b090606030a0513121707110c0112 74
    0x1d0041c1c1030075512005501003483d103a01400e420038885500800304d17083c07982245441542802c00000706150710395600c1034100c0d4000c0040754035507a403007682d4a400c900d611102e44061441003024000030360350342e0200d0030314407051850307544800c4c82640300c8e000503c941640224140c01c0c400d40c18a0040c0c55003000900d0060071405610800f50b03030701000000150107003c140b40f00742168091001d45520415901c1c046080d00e0707002c1d4200001c100200080342010f84420f0100c1c200d80d0044041d12448c03c0d083d80014140ea0042d0340080381608042803442240d04458181ca400c2000002c90144504850b41d40c2601c40c1c02ca07101d00c509120381140000c003000c002e060b03194103607a8400400c0110354a20f1074050300a1072001409405280380c00c1c074640c00b03802c154010780d00600d0002c20031419a501d5000d1280030349402410380700c207036518100c0b400000d80301110340719681c8101d44512500100301100003c100800400407803c1094542021030f41d03040c0400c0b1440312a00a01e80070342215103a20600d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 520613597 1250 520612347 520612349
    0x60103110712140415051209160b130e010906030b06121b0a0302100206041704050105071707020d050304050915060304140c060f13090b06040e070e060c0102090111010501260106 78
    0xc10030700c0c0504000b80e54003070001c041d283d504040d046190307164848c54a55440a541c00542c010345400c00600c001030000ac0a0300341c1001c800000442075881c0c48540204400a0780200c01064035840c0c01d104100c2c15102c16644400305403803540895040c01d09071a81c076400541c0d40c80c42c61072103c1e9aa1101d4844604280c051500601007813500400b185000b51f4420040b03a054900f07162011074540250b520300c08030760840b00b0581d1094100b0310a5219010041800341070007044410410400b001070301d40303d004036100c5000710065600e0703520301428849862401000094070314100100001240e560724103480c4c0003a00103c540701501015003507580f810b01e10240303107644407001051034008101240028008503041383d0105807642e41d07565030582601c2c25140c909a1081050000b4440055040f0040d6845001894241e446801c1e01001c241ca42c0d0100d210b8031702917500000c0d200480d50b0842085035040d10b244008200941c581000850200f50091550745142c654402e80e403003a0f1000d4211130 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 520614847 1250 520613597 520613609
    0x120a110a0f120906080912340b0109060b04090902220213050a030c0e0a02130f060e0f0916050f0a030902032e0915060e0601031107121404 61
    0x5600314003182401d5403108202c00301a03000840007000410018800c0500d20300030030304031006041c10f04100c0030450b180e070842c81004c181c0700011903134002d0000802c01d002c251f617006248000c45240c69410038816860050b00007682c0a403c082c3e0401034105100110340495200c5400011010342900c0000d0143c0e010342e11205003801186168851541c0950007030080140803107800201036030300e400740034030112244800b80c042d55803100c0c1002524500031030350398007800c03514005280c0a00d641d209840c1c82c1490b00650300000c0c40000511110b81c00090002101c40115040c042c06800000001c041c200018902d2040380600624514400d0080c1c05884070080382ca003400e5101c51b40302c000200146000da82c01d030712074400c0c0d0b0348001403400102640b40d20351141c64400000703214a056400050940f40740c08a422504182c40c0d00c4010215115090240031032407108001c500342000018261503200900c4401e0403800c200020000c0c4003c07840004d03104417410840192192400caa4106001d160701070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 520616097 1250 520614847 520614863
    0x9090501050a150e0a0609090c1e05130b0f0304030f020109051c03060b03010308030f011e15050c160801050a0c090905060a0b0a09060201110909040b040c081902040e120a110a 77
    0x1046c200e1b00000341100303581c00e07008100220014a1000c54021000d8602c078405141c0e00900c032541d00d446a0020018a0303240c0148400c1c15580303000045050b1f1016403940401d481c0030050004141e8060941507402e03001c3d100a201804603a2107143d2150b884080c81030b41c055079140001129400ba13000300d0b000f840c40200c0540c07a90b80d01c0c01d000792190b200f161040015054000040361026110f001d030903803017042c01d841583c3c180c00e0106030b0b80c104d20f0030b00541d000d00c2800e00c500c1003150405c124450048038002010388000b071030660507a0a40704c1c09011844840c2c20044002201036014a468045500f900c0010440b81c9600c4080f40341c00120750806680c604001410700303c0d0703d400c25951000c03110940e00070011442c8080082545010b40e41646900c0152040843c1c04101409049a0442d0103082e041c2440703079450390010b19140c0e07207641101e080c0c040e84032040190314051042e40112031001d00600f012004e03800080d1010f1180d040040e003030281c2075525058840c0200480441581d1100c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 520617347 1250 520616097 520616099
    0x17070c140a060e06060409080f070609060516030b0f10031107290604151205010b040509010624020d0f110303040c0504051303050f0c2b09090501050a150e0a 69
    0x2c0b89016001d00c04001c54607100d20004a06039003880d00c600180107810203045801c100030500c00d5202a44907607802e480745525030000c000400c400b84103041c01000341940140322116110000380944203916842803145d081c1c08102c10030313030f03d41e840002c801301140c1c0b50020704130701c602c1c91846803070041141c05441da910004071405400b900206c3d801c0b1202000744c0c0780c07a207644c40d8406c00c8203582200d00d03004040b201c0f04408201c80750703508481c014068400c40010401e0340010000c102100c4040b94107404581d1107040420059940c58101504501d201035100702503c000709010356036889402d4440100b140203180d4071802442410050624020b00003078a82e2800d0600700318180441782e014007481580782201180c0d00c0001c900b00511080c1c2d00d40c45044c2000c2a81c40300c124907401444110b0000c1c000c42c0c84035040c16030200f0031110007442014419540100040f401407003080280c00001c03400345050014030895450f1803010045416035010104445205102100d201710ba514241e50483c1032000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 520618597 1250 520617347 520617353
    0x60403020f060108010c050d020304111216080105040c050f1903110901061e080612010f09050f030310030807140d0c150b0616080910020307060c17070c140a 69
    0xa1101c403503220241c11103650340d8031010058203c8000c01c144402280341045960403024490300034650150090700d8403403d0840a401050000340e03c801000100d4100c00b40c0422901c030154061000340c001c15000b0030007840c00d40e58409420318030b400b80b9485007809800008250b5a400919404410f2601c50300000a980c2c0c603280030402034040701c0d24400d90441c400400d089110321280c501c40c50300c0a1100d8801c44200c402910321203405011942c114401042c2040444000d000e60080c000c011040002e8029490915a0402c0646451040c3c180c04c200180107860a000100300143e98120071440d940d0140e03842c2c206804480ba881441083c0212111001c0e6140c100703d1415401e401405614800d83c4000000c400b1030f214151000d9104106000d44003a101c01100350b04c0d052441490550728050448000a0040030351a1226006a10015540c0e04014003405501c0d02004641098a0045039104c42c0c2244150000c01c885c0400c43c0c070658250a004a030000da0080180c0541030351003c2d08581 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 520619847 1250 520618597 520618603
    0x6030b0609151c02010915020303040b06060c03040803071e080a0f0509120c010e0604180506030f03030928150c0c0b010602160e010609050d060e031b1605060315030f06040302 77
    0x3a4203074041490040700081c07d1540700701004d460101d980c05145141d5407541c40120b120400740c0204e0b00504184408405901c0030801000541380348002552542c0d1103140100d6403410b998080e0544080c1d0500450010301000140e4010015905103000659000407048405004400d425a4486600c850072a03400c413010075012402c00003a602e08a503a40b9550901c8041e10903881191002c410040007042c0c07007000da5118640002d00102514400c00251404600d160410754002d0303a00c0c0c01c1400003007448040041c11f44025070100d0050229020700b61104030070003449450501c411a110400110f4541c41403200d41e140560005000e6000d50311942d00960301d00c9200c00390b00d2030300ca0420021581800704100c00d412103010b0768030081c80b40d0805050224020342003030201c80d042d8580c0981e03210400180f02514908900302d2032640d03042c0580c018a45010b459003101d00e40c0d56a070003801d00547e1215400c580d4408a1131a00841e09035010000c64501031118004541c00e008850601080682c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 520621097 1250 520619847 520619899
    0x30507150509150c090d080c010504030503010806070921021c0602090118080c120f0102030f071e080144061e0a0c03060503030a0f02070906030b060915 67
    0x800c0b030b4043c3d140c6600329215050195404c2d40c040c0c906101c907040303500d040c0c0301c0038504600c44c003009418880b082e03d03118251130059a00300c01280000c0010f02a08070f0070099a40d100c0c0d003502c1c102d00f105103802c03152003010030035a103242c01e00e10124a4600a54556500301d860701b0039034029242c2c0c005028200f00c0c000750400c44002e800180745c081810031548507148034206445191001e08130300c100d83d2080103098010602d0103111402406401d21a04000707101451050304130100340c07141c51030306000081100550a505022040d403441900d01b0f40c551081e0500d05441040024246296002942c040c9605042030140710941765008a500102c89107507014039140d030301c0011610b140d1074070188000040800d81740c1c02d007100302c0d14000802d07c02c2c2c07d802400110280341400240103803120f012909692101c3d0b86400031500c0c1c90b030801c05091b410803040c4000c049113041004198219a11a654903401501b03a92107465200c0100b090710071850f07110000d03005c004081507101034a24544a91004d44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 520622347 1250 520621097 520621111
    0xd0519031e0b010f0e09061c02091e0f0f181608150a09050a120302210711030307020c040213080d2706200109050f070e0a06060504060503040305071505 67
    0x11500e01003c40342c02594445e40d4030000411240b6541d482c50f086c40307800c421189070000e0a01060300110013503213812498602419801005000340582d910001700c42c2003014007180c14803050f940c2040b0340c0405480c01c0940149450840d031110788040220185050701480d4026440080500005a44400016181800110301c201110903646480d14107045841440d009070058008806880015401c1d00c9814202c1409040c014145250301100c0343c0800f06103041c45640c2603298091010240e041040c020604003003d00039841c502c1e0a550003501da0803043d54260040740c02055013440d10b0100140c41010340300c02402c07102e444450b100001d042000d283c83c030303101a0078501e1100e10f124000e0341d008004c3ea40551240035048010802c0d009072004003280302c156a560710118070002440610003c05a0306208000340784890820100d440403500281251039645c1c9086010001550000290703001c4030700340e04100d901c9036034505050b110781c45180705c020700c012000664200d8401c05a4840343c02400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 520623597 1250 520622347 520622357
    0x30f11040617070b040303090e100e0403080f0f0103050c10030f050a021b15010e0a021603020d090602060603100509070b07051c0c030917010f050f180d0519031e0b01 73
    0xd5204d8240007184076501015001070b030003820902109903040c43c190b4101415010061400740e0b907551007500c0c420241d400318000343c1010b061003401e808030030429401c83d107000c01c0b00101f5459a510b06980760100d80340d007401090320030240f1175100d000e540000b1030039403c110f0a004519121210314002c3d4040405103103e1640780001002c0810f0020701e513002c40000320019006e903420104001c020582c02007144420f25001c1005044866490842c920581d200e90000d00c00345054000c00341c222403d50b005202154828030821000d540d001420700d00d004107440b00000c4a443d440d00e01d40c2006040d401500c181200020b84000304000002c8500070110302e00c045a00404c0c00e2401200e01080e01140900080c080200030300c000d8060708841038060950760000034143c6140000401179503812030707450300b425a68008100c41c000b000000c0c04001200b07513000d410005e21151001e000b80c042c44155410074a202d030b0407030002c24000c0e4402c40a64401c1003e1000d02c1c0c201407030a00142060340c8400340020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 520624847 1250 520623597 520623599
    0x1030c06081b04140a050d031205010909050303270d050304150b09071d1005070b061c03050901180915050a0b0f03090102040314150c0a09030f1104061707 68
    0x20110241007104410301600342c0d8a003d140c2036082600c10b4050408a0740449030500c001040d90b100c41915040740e20071703202c03161109a11100300044070030503800200c0090400240c10000340011007140e0380300032810708000310301c40103000001c05480e1075600010340d84128000103031344903042409544101e10807913540d41c05001c01c2d806503007541c940c5d00f070541d042140700010486041c00307006034031000390001e910700e0185085500040c03803c900d40200d040115034005640030a1244c607403151684000191440c00f02551a42803e2002403c2190083d0400c4004650b811041c3c1c071038030041103400001d036100c0f060070381c07030b45000070007013012440c48611031040030030004132810070381c80f00b008540d40c1d06002c41c100742140c442c5580035800180010029582044044005814814281800101880141071584110740c070343d0388a03000501130411250082c04000591680301300c1500580e940000840e290160a2a10000c5880f00718800c96001d0f050201c0031070008192014001c50003902001c895a031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 520626097 1250 520624847 520624861
    0x506010b0d0c03090209041212020f090f180103150e100e060609070203270d06140a0504080316020a020306041515032604090f330501080c0f0301030c0608 68
    0x880c01c44c1da0094000b02c2200009010503451030000d80702c8080b60412111207151401404226400344117000407601020950020905000400f100c11600075100106081034013820184d008a051000038540d20354807058916203401504081107070103200301121001c0003210008405040d14940304a03581c85201d00040f084d14201180d54050501900139501e04900b140a070141407184002000c0c0384440854042c40704c0c3c84000c4d2402c0401d00a42000580d01c281441000e11860082c1c00201c0c46401c0400780b1001c620722104403500700c464066400005180304201341c3c10800007030070103035140c00b400042000340105212010038070401801700704030b00c05001004003061034a44c040600780740e000d5030707004c00b2086226401011381188040301da402c01d076440e84403400340c0c1c45407900c8044980c2c4603104450624005100003200041c1d00e02c1185050540c0104840c0b00c1b042d9200701410032035140d001c1307414683c0f02411203010100c50b900d00c665a40c2c44e400e0403110380c00648180700000d50640c0c002600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 520627347 1250 520626097 520626101
    0xc0302040b0906011706010e03060903031602030421030e060a030905010606032009040b090907060f140a0c06270203060c2706040f0e0709090b030a060f02070506010b0d0c03 76
    0xb1503c016105c0d94003007000c8801902107560020301840c1400300c2400901c003075540411640348260405001140e580c641196120020701031104484250b51003444144561107804a901d01c00da010030212309120315141c1030440d05624129040c580280b40090381501060b03041d00041a172038082e000030b118196690704110111130b6200f0029031045000c00e840080b082882004251a401c010404220b011840c8000707081100255440070b0300b50f00a000400109400c42d100326036014050601070040b4080b104011201c0c850681180c0810502c010040c007001095400300000590143c1c03040001456010260200c0344c0e0b03003c1c1030b4803a10035100020701c0d081c00b000c200c0d110030040060000e11212180b030a8408404000350099010000f030201042e8034007000c405900038200b40d8201aa0382c240280098074580c2c40307030804103625062110050543d280080c1051100e507201a00140041d8210550340003401361010080881c0210800003440102072000340c0050280075004104980d03225100740c0c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 520628597 1250 520627347 520627351
    0x320a030c18050f0d0f0b0118060e011d04030306080f010b030127080a020f1b010f020a031d1c0609021003090c06140c0d030515030105011d0705040e040c0302040b09 72
    0x35220549001c40141810041c601804d0180314031071082200c0d0b001d0ba00c48009030b80980154140c3c0500340300e43e18000742c15000e50030060150482540003541001d082c2000c19150007020340c2c0e440007400c049002c051199000d030008040d0101a83e01d91100303812400c0c00f0f41441609030f882982041032031040544138001031192502842d2140b605030b103c41c1d8460001c0d8100586140a501540f440812010700500c503030494010350034803106050340e0740e400142107110359024440465000c00c5425002980003103000c01031207d0003070300b2880c03204090000360304000d440744002d203a00f103038012202c01c0040f02d4020000851089032440048540c0340c80c00c4049412646014000b1040a5000c0040b98080d0078131410001800706814942543e1102c2689401c0c1b80b1484000069520740030044007840061180c0a072000460003401035514000480288540e0010404500c5440b41e0114000303d00601c11240141180b41140c0414030b42810240f03240303809440103038003a90402002c5256860410b100d18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 520629847 1250 520628597 520628599
    0x11401030f050c04140612072015070e0d231203041a070507140705010809030c0304090b030a050706030510050103090b070804141912050a320a030c1805 67
    0x7800c0030301d000b411000305c9a000c11080e03004002002003c00da1700403030040034810381c1c56807926070104a6022907580c2c003070450034038a00960400310b4480850401145026002661840c0a0317500d0b07400000010054086407a009000070300300c465030f40d00140c03142400c1034251003650985904640741c1d540c03120036210449005000d000b1000d4420458580c4c03803807182d0840c0e607500d00349090171080c0e070711361038081d151403801002584006c0c0c041025603444801d440d40041860007840c1000c4c404280c0980c0c0e07000d1800b408540e10303140d02540f001a00c08001400c4025001000c4413142a80c95001a006107800d807544100d86020301c9000c91030303501074061108000d50020481c9003d680e400c00c211400b00000e80308454021803142c40d00004c4804010991246520035a5150756507507a00e44005121801c3c06c151b800d219041c8401804070b50008125440c03e90042c14010001c0d17444a080150b061030001090207074103001c00c1048010703506502c94444c51140c0d4503564249200740c0b0340c0c0c0e421000782e8030900e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 520631097 1250 520629847 520629871
    0x6030303230403080711340f05060f090301110304030f0f081b0c0f121305180423031216170601030c0509090403051c05010815060f09011401030f05 65
    0x1107140503201c1c02ca0200b1001b4228152040300d1221002840712914403005541d2030038090750307840000c10100c4246070007000560f10880c1d00c103140c40042105802981214121001301280b12200780c0c40a403c01081001000c0c0c0ca190780e8641454040c00c52000750303c00500041e84000041c24190040c0e011f00e0241400721040c44458084181c004403981c04034941a0383e90041d01e00c2058107810170400c080b04501a81c4500d5101c500104130a02c9403015580b02c58459a6981001d507401c0c04948202504260442019203040d962001000300c4460700305100f405034400005c0000c008130451941600407903e0004141c0200c2d1b103100101e81c0151311641c18a502204038010403040d60080d402001a0b07a09810824107040b1107200003404103000303e030160007041c400550200040700e000d52410054030f03000420421541842d01095507602ea015984e661000050301090a541d101c500e50f031000d54000f8041402980c694503444401131129269501290400404502030081d81c066644959820980 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 520632347 1250 520631097 520631101
    0x203100312032a110a030302041d0103110f0d080f0301061707082206060b030709050a15050f070605070c0501110717130b03090109021516140106090603030323040308 73
    0x14010100000f001110501002400c1d003080c016007030105441c1d1501a41380161250710300482d140d002c0d0b10040340380b400000e02100600c00201d03000007442c05854150780070000c3c2a04a0041004146000c5000d8207442d00400d0f108110690b910043d810b0b20415602c01e2402d011010000c3d1640000359007140110384402c0c001242c1f1064442a110000340b000c8180602c0d00300b0b5104c001c01c6510326042442410000802c101065400c03082e008010300d420b0f9042d208181c80d19800340c01009a524010301000800180c3e500f49100c0c0d213040e108c0d80c0750402002c01560801c04409016104210011aa6542054100d04807607508030242c40b003054100d001021800020300c080142c550000501c1480088180000714080304070b8001740d8813602000d0300002c1c4008a6004228207152100d25045084070200904640c1c4168002610703009540410f10b405c021101342042c3e405085203803c000041841c1240000130305038150001002c031020804103c1022100c0071079a003c4841c2140c001d00890850300c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 520633597 1250 520632347 520632401
    0x40807020d0c1706060405090609070303050d0f0609020703301d0607020d02070f03080a0804210e0f0405070207170a02030a14010f0b0f0409030302070501020310031203 74
    0x812841d0042c4030b00821007400780c994000b286265200034625036580e005908020075070810b03210b00c0da0428042e000400451402d034003202c0e0364404600000f01000703070103e02c100c2c1391000c1e42c1007560711070507600c0700b4030000751603a01d50002500150815030010301010a041c480e104501160700001d94aa1903402c04c20204000c9500076000d4280070b00c1a00fa04100c04202081040c0141030140e151580508641c0807058070007458090203800c0b040300d00a02c0c1d0010400100c2000c201c03803500b1800e052038a00355a6030f04040e2a94007000c045122030800c01002540c9940d0311058a00c8441001c5072004103480706407043c0012100d0455640000d40c1c0301d030703605000f8503094029014043d81c0041c02c50300b11180356030109043c075038000021180800210040300c064402809000780040401038200584188040059098401580707214040d81c1e985440006241c400e4046842d03298208000355503a01300303c0c02003c041c240780c1c402a12031000018110710050320034040e01011170100300030342485c2c0d52454 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 520634847 1250 520633597 520633609
    0x170706142e0501023304050a050d030e0a030c080d151e080c1c15060608070e030d0503180106120303110f0301091a04050a0509010605030f07120c0f030818010804080702 74
    0x200c503244800c1e0b01c0001441da0310117404507551080384504003600308800c0f90f140092620043d651014149814003030501460b500000da505811601031900002c00d14107814204600d11808072035224113803e013180681c3c50034448207100c040710f0120001101c50ba004240c0d1201342d801e14007882c00399421280020409150602203080c017801548070100c0150b10742d0b5a039a014507440d241c1001100c2d19010204141604040000d500c9100d40c1404981c441c152130001e9204e04541c0c43c00ca00f8054040017048011030f244080352500041080204800350301c071201307034444410b451800c800090074800d401e040310b0750400036a10303444a8120101d0440c2d003499100d401412844d8406c4054002c201404816a03903075000daa800b42140e86030004440c100080d6450075a10103400450084c1c0c42041c540001031000906107085507c8c1803202900040b031850f28006000c0c1170340c07100d4100c8222480c00f0040c0003142c030003001819440729142c3c000c0c100c0078005580c844422034010b00518424041e000141c1070030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 520636097 1250 520634847 520634893
    0x1e0e03041d0a0b030a0507031214070b0a0633110c09040303020f04082d060c03060f1804060b03011802040209040f060e010914071202090f03060c0c010e0307170706142e050102 77
    0x11100106d10b0780e44403c1480c205501c0c00d40b003c1c21011078110a0010fd0722041249080f00f1003514040c02121142604942d8860000c1c0c01d10703010301c0b00d1900060034180b1a070b040e6404080c8400300d5079921540c960186079070b01211001542030040c0342461078420708071a80c041042c103108801800590f039840d03048501c41c3d040140242c0d0444a003405450040c1d484042480c0c51561200c0d481015082500340302c42140c00c103a18050286c1e01d080f03d00d0004001100e03440c0d00701541140e01595684421022501419640c0741005c002814400040381d140900412036040e210042020040303032000c1c000c1c8002d8803205031504000304518042d210006c40300b6800410840201406030300da2060f09801080c5094401c4401c810325036004104100c56107400c5c02103c9181070b07200300560a100d240d45440c200302c1c80e0040719040070703480052a40b041198503008480507103030042002940e0b10380941c19510340340454100001d4882400f094207803103101500d164094038010384c0109944a00903003403144007108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 520637347 1250 520636097 520636111
    0x30b130312022a0703020d1410141b09030a0b0601080f0708040212010e0706021606030e0c0405062b020103051f030201030e0c041e0e03041d0a0b030a0507031214070b 73
    0x9000380102c05a00c42c03440c401e01483c440d4103210b030f1450004c1106800e1010341c0624270301017401c1c0a000e42c07600103042407540d04000359143c01e4882e206100031102152040740c1d081030300340c01545c162205021880c1069441107000ba202c404a81e9200c0303090407801101103510740040383c2c000021a016050203001080100201c0c0000100b00c0c280003103c0c2d181c11481d510900c01a84600f00c00c035000790036800c4500c02002103003024013240c0356111b181600c82034a1002c09003c2c642c4c0d100018050340e12406c1e040c51101d010300ea650400f004940c4141583c81410105901107800c10000c40c9034400c0840e080c0100d4201c1840300c0f01001c1c115070044016148801003681140720b03801414029907113511484c20f0311101000c10894000740540880d0a807038110303107001070702d82007484200f1003001d07480c140c60b2090b80184101d9605540d0406950010180e0900098141c03003140c500d201000000038600050743d0040c03141e1380b03203455900c0b01241d540e00d2405004c0c68401c02440880c0c00142407480c0141c000355 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 520638597 1250 520637347 520637353
    0x907080f01020a170412050906070807050f1903050f2a06010f0e0105090601110c041503050706030e03040915270e030c1b030c100807030c03051b090109030b130312022a 74
    0x65030711030345800ccc0c103d1300040d03d0f6038000300c52026440da03007000341008400c140d013040100d009158402038003d00490b1107084241800207202807050070880c92500c50f460043da19003054000a040701030b0760740001d0103600e100489500e40170030294000d01d80b0b281201c000402c080e03019500d000046500d003a0301c4185580c1e85c4103c121f064021b82d2b40e0b018699541d224030003155a2189035007042c500d03040450b40904103040c900522410106000b0040307506903440c5c902c01041d220040c445034501c0d803203158884460001c03200d039610f040c07a20003400c41140b90314600c070a120002060180076220300c1440c03402c001a40c0824101d110301000751220522800005054031a0015008041015000341a0030b50380007804003c20070002940600c40c03c011000140360170403c51400b1094080310710851001c544514401013580141c0c0e84c490303e121006540e1044903000681803140d40314110000c4084114040307240c0c00ca041c0740c920b015200b554010784807000d0200b0070310100e41c40020030b000624030301d042c940 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 520639847 1250 520638597 520638607
    0x30207020117160e06070b1303090902030f04051c0509010e0a050915030d1e050705010f0e010204060e0d2604030515160f080f0907080f01020a170412050906 69
    0x425400b0519108840c8086440281800d408004044128444560784610300600c000004900301038840e951102d840710720850121414281a56201036562000031603500000421020503120803845008034420001c40341c40c4140106e100c41088000e008110000700c040c8400e038240d61103001e6148410b2000f52820540c1601c440102e03104200c22180040303041071400f1403003410304041001b41000c0200f8a0150040c00c0200b00d0041106000c480100401502040e403005209c0290301203a044850103c04012002c2c0e41c0010300c0c003030b4100c1c0c45070b5804150f01040180c41c0b428016001051245d00c00d100c900328240d030b6954803d010f0904d180044580b003080c0000300014004000030300040d081c0c00480c00142c6003074041c0d100c02c0c1d4510000d00e42008a0042e10580940e0000320640c0c000103d841092184c2d50380031a07071860035260b40e11041c0030b40b0403451590303240c000643c000c09134912030b03a860189117881c00100792840201514010955a049640c203400907101e41c015140601000301f0240c0f0301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 520641097 1250 520639847 520639877
    0x614131109060609033f0313030905030604031701080309030c0d0f0c090204091118010f02010e070603090b0601050f040e040503121f090e030409110f04060216050102010b09070302070201 82
    0x81301c2e40300603d4041c02e01d4134260320200c0c590354852541400d0300386e140e04244400d0f503400940b07034000646044800c035500b03100d001c2010b00070109600908000303411603e9a15142c02c00a00514461101521040c003181c004104042c0100840e4291200940100400a041401e01840281c84401581e806840390010700001e100c4003141ea000b84901e82c00582c17110f00b4a40c0c04421078502103a111541c044c10800400100328126107410b1424013402e0a070004c14003901b00f607016180108402100b40148503001c00e5054261f400780c1d1540e03000d14180c0d05550f441c5001502c0728468000c188002102c1413104020303c240101405620034856015642000d0080a900210301c600780c070b220401c09003c4015000e0542244086c40c000c10400c1d40501911001109481c1c076481039000c2d41d804641ca4040740c0410030f004c1c0c0c0886100c40d0f2071300c01255503181e5660009440b2420b04510109022071003400242540c8140210540079000804000d49070b207506500350002d5100d420100d040c0400c140c0f0340150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 520642347 1250 520641097 520641103
    0x70f2003130e0114030105040317090715030914010903020319021c09060809010507050313060204080a05160b07120305070c1b0f090203091e0a080304061413110906060903 75
    0x406042c0d072000380950420f02c03541c80442a100c0514040da00d84000c110200e07911441070780f075603810007413100d005481d900281c5082c40244d40081c0313a0750403080d40341215242c0c50380c40000000d0043c8604040c4a0700840201d00b40e40044902500603801030111107407041481440031103450490041700c407481c0c103e44264078048212621100450a6581e0800a41d50400d503445e0340491032000030040f6150416010300036000240190302e0351500c00010a0402c40c55034112005001064125510382c0f0403841d02c1540c41c1560781140c0d03d0701c000c268000070b603480f41e04159150715900c0000f0355840890040114014036004108104104030701d598903000ca900b50040e440c00e404840d07228100203003005410006c0040c90350064241500c1041001075255000c1340101064156034190140f100c03119126600c1d0003800180a8081c11001050004000e095400003141003051840341903d6522040c0d84099101c00020161000c071010020715114a0018085a40094010f1504d82054181d00101b0310b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 520643597 1250 520642347 520642349
    0x120c0b0411040606030506010c2303030a06051224060a051c06060f060c020d0203160902030106090608150906010210153308100314060a05070f200313 66
    0x1642a40e4038407208010304190180c000500380c9420b00b40f14a061010000700280301d00d402c058900c0010201d1000c14107900840c500702040b144045a441303041100d42103005107001d03c1307414420201c00c058144400300c049942d4000c03910fa10b8201440610004400801440040a0980c042c000c10400714055030f910700449603d0b00342d020b2104c4281600d140c40000c8071a15007029444410040040103da680610109680369054410120941141c40880d20b4200340707103070310815101c0b491008a0a04a603501550485500303569100109582c1e2000360384482e41650f072216040320068244449003040080c280d040748041c030456400720510440a0220782030b0004200a0342040310041046019800040411144040107505620b0751055010450052000b104080c41b25440004503402c0340c075039100d001560000e0304250700b0381440c06d40a465100841e15100c006140c2004120020300c20002c440c9658415121044080d60007000340f0704c080307401c00d614441440100b00101d140744100c44118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 520644847 1250 520643597 520643603
    0xc030302030a09080f1f0b09040305071101030903052a010203090706080f13140a02031c0825050c010f0c02060106080112030f0806010c1202031804021204120c0b04 72
    0x42d102c42c000c0c40014400450f9602c9403440303512014041e5203d04001c5000d4056814a42c0160040c030220306d100d0014117614a03400390301240d0344081109040d0464020110f26200d100d40903601c441c0f440c0150b04603a003418001d80010390a014010204490042d40c0390368a50300c0481894860646014500703a80c001c44020105422407942003101c01e802a09854001580f0841c034503c91510607840c4111803603498003e030046d08080d4082c00360b81b40510443c0b0681d074001d01510040c2d01c1c083c50442035950042001000998007a0000340510b000d8011560200d0070440c1e140c00034424404216419000860410728556a4150b0300c80c0c030058911841860740c4d0030b50043c0001d989000d001400014050340805446102501400b00180e0320100040a07204c2909280da0241ca030000101d48080c0e21240c000c1c01b000340c4195040580f600000580180c00100c52061540050541880142d014420b5845d071041c401d600807030005020214003540c0d454580c035000d510101c03152102000b44109540c19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 520646097 1250 520644847 520644853
    0x1110d140a110a061a040615181a070b0a05091f020f03090601030201020f241305030721030b0105070602030601140f043f0c0f060e12190f0f0c030302 66
    0x4040c050320003010140084c1c0304035400c2001c1c030b16148d41900350036508042c1000300900c0030400121162022400009440d07a40301c030000740103c070320300300e03d40354480318080d0b0b07010440e00d0008003500c00c0350240d540304415140142c40039020409500195503003058074074081540071301041d00c15800d58009180300f0500800140260f500d903000190504082c0072a1503601e0300b001c14032080c52614017038402d01d15100505007462903540c001d40011140c41040c4000d0141c04009940011f1001c1d00421f002405c40c0c0084460b859902220240c003102c030380c443e941d4041103040c043c20010800e03560165a0080d018102010441cbc251505142560320458455180020102c1e007400f00108811072503603403c11480c80d94081003c0d0080d00030b68802d4484041503460034004400c010019100e44103402888a41c580510050700c448000d820180440c01e40c078003803641210780800c041d03400610302c0b80d110400d411051207070425466039402030656680681c0c140000d801850000b406030640140254000c3d409 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 520647347 1250 520646097 520646111
    0xf02010f0e0714060403210302070807120f0207081b0609030d08070f051806071109070908060f01030c0e0405031303290105011b020d17030601110d140a110a06 70
    0x10641c0c454005140d44c000c403000d00003071001502a02d98190403903120b5501082c0b2509800080f8080c0c0b10303c50000b425080041202d408200184041c40300240c0a03485802c0400003068003266211224805c0e54050362104a1100c00c404092400b0326890f5405070404e4648102500400d1a0001007a40e030f40c00200d410702001507055200c3d00c814072008040c035141d032905070303107803100300038150b6900c0300a03c18103000039100d041000c0a614803070b8501c0050481c07011454031010280444420340b25000f52030140c000080c1c07401d03210064041c1a6a0300420444075581000900740441c01c0007801203509101c01c00071540c0b607606c1c040c440401180300e9455071148451405d0000c1200c0b260b1803031050b40c3d1420388011b10482e83c001c0508041c0030612406000000f980d0b00018282e5074410b0b20280c4640c4a80052200c800d032118000e601c580c42c00e03201c0d041d640340010001e41d61041c03428501e10000307844200854000511038010b044000e075924100e20883e0040c2e01041c1001e030003c03001c43d04141c0e1088 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 520648597 1250 520647347 520647359
    0x30a02160b040516060c02030307111306032114070f0c031b17030711100e06040b0a180e040f0839030a08061513080102120a06080d0f02010f0e07 64
    0x3501d0005041c8a00d481c6c1101d5500b540441c0c2d0b02c1c05075201c01800408003504100c1c1c0c40e15014048040301904e01000d1044556034105034010700e030540c14641e5400b0313580015001050054248007214509850100d16103404c648911001c50540034040715013a400b01400004a07172014080c0c00c84070710480c40c40408614003421103c0d0105003c1e103566050700140100d2011401d0f001038503008510a5403510594059000f00f140e02d20708205250781c0c007120109011820740a00301c089d181c254050344038450442800c040341d46025109108690340c8004a2002a0008640743d42c41c1d082580700b500003908107608200039814601a5050702900200b2666902d4408070032025084480a24400910701c0c003030301c02d50020280c0c0c1c0c00400140c020244c0240503c151204002100d03100c065815402d901161520655400b075807200044042100f0705402088410201c0e1103040100d40d1303800c0042a90f41c0301c0c1c00e010b889001c40555160155541c07003100062906070ba008031401d625a1001070012642454 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 520649847 1250 520648597 520648633
    0xb070c090c050c150f060f0d060b0103060b04080312010b0f160f0b2a03160509030c06030c040f0b09130f0e0601140901210f0602300a05070203030a02160b0405 70
    0x52016210787c003202c58507103071515108401521180c0103140440d408202100681c0500f100b0761100602031400207001803604000b001500f10010500040030b101d99881400705003c1c000c3d441c01140e581030801c0310104560880b5040c111061089855200742146903d80300c4080e441200e646007040c039520320011000c1c2c00b2006203c0752258543c0c401d400c5040c900e902e6443d03190503401941c2440703c00030b4030b6011903604002c001494034004100d10743c1c9140070000e07900150020f2141c050941c40e0f01d02e0100744160030710159460007a000d0100c0d030b1f000c500840c88102a00b080c82d40794131095528406130380200703828800c0303d0103050403c000d0078020061105020010300140d004001c1e08540603100c1d280c005080521f2032605821203000042d044803800c0100c020311610304034020040c040502d0704a8a1042049220303040d00e1a044407510f6560032100030103540007120120b00580040000400c01b80315a40909008450714140c401c04140c00d40e9003a00c0d4200568040c0c549903c0b00700600c1456140c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 520651097 1250 520649847 520649851
    0xa0510091d070f08041104110408030304030207171209041d0109061e0209150a1808060601030b011803060f0603061e060501110d0503071103030703090605010b070c090c050c150f 78
    0xe840c0804c89440c10351551590030604034511072155454100c51000000524180d801510007441501d982c2d08261401a65559445c403541207003d0b50018031489070b203404100601e0400480e00c101d450482005d0030400101001a0303442c542d5500d49124865a40e02442140c6100d0311803030001410703482c2c00c241e000b100da003c0c007a001c04c55401000151840d4459110802c408a500d14003c0c0e00d031040784409840d0045440103503001c12003039401c0000d0071b1000140041c0948000c0c1c0303080242403110001120328004002c540780100119903010130000398554040e00ca2984a81c0c00011102e0720307555101c01740c41469803440103003a0300b00c401c014901900d10075440244001d00b402401e03511101d070019110004001d04809000c0003000081c1c18902580350b403910043d24000356543c80c0f034030320006401807000800c1a66582c0c5800004030b03446c6944011201e4070354008028800880c6054041000342204c0360000042000501039203e081c01e00304402c0f0000840320700550300d503160007000304d44a40c0c2c3c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 520652347 1250 520651097 520651127
    0x60406140a09020307030b03030c210301080c19150c020918150c070b0403051b03031b13091103040516060c290a0903080906060a0510091d07 62
    0x484559180315681d049007150032142c0b801e00150300c07942c4203082070b03009144204c41c041e0503000c0003134105040c3e240454070345000b05482c15150b14010090400703019a010034012040540d001001c54041ca00d0840c1041c461003042c81c80117840b07140c4500410b40820f030040c1025004c1501c610742e6204600d00042225400040c03040b40305040094100d0f4140d0710100200100d42d01207664021806407090740040701c9645401c00b0b1503030294142450018126030000c818546c04002c2c0b44103198105002104490007a091800c2100b01040c012040300c0455010101c210800d80c1c2c1d42d031001450400318026106c1200310340040c0d07a128607290a0460408054088502d80e250928100703101058008103021044e40e0400d00300000c0c0082140844541244020b1140c4861015010407181103a15086a203240788039580e5000142c0303641078034542c0c440302507501030307403180c3e03200b80c240182d0801566420030b255007460800507556640c0b40300070102100540c0310380107000c140c6c00c0000158000b81c0000980d81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 520653597 1250 520652347 520652369
    0xf0e060612071202090301061d0916181d0102030709090908040b090303071406090c0a15050705120301060c0b07020a0b0408031b0f070c05090408040e13060212060406 73
    0x20418a030768a6000000c003650700f44120010507520040c6240e05171414004041c00820030603440e903180010300011045110500c60700d12000440e409401300d08030032070010301c1c00d03800c40316030401c41410b8503c0d0745482c412400641d611500c000042d6011500c205d519100700005a69040000c0c0061a21000c1d0304551941c904001042d00000c4c1400200d03022541c81d100103a40307a4111000090440c400c0d000007038012a440001d24440703640114080e40100f0500d4201e945082645051003c940b24034401d0500c05000e650384d44020031301600c014028103108070300340c45400d00505003405503034100ba0000800141041080c80c10484d030846080d03013160b564002068800203e80c6c0d054690f8000a1005100800c04800300b04402c5816100100500c0311b15100c0752100381c54a50005281c2203148140c0c3c051400510011302c03800c0a15085000c0c0b078001e04428681420700ca2840e44990001d091001100c54504100c40400d0311440070300303089642c0b05003403040b40c00c040c8100070a68040350005003e00b5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 520654847 1250 520653597 520653607
    0xa0f14010510050c070b1b0d090e013c1a0c100e0613020f10030e010f0e0d030c142107050f070f020a030b0408030714070c051e06040f0e0606 62
    0x3440001c21800715641b0507021a0348103403541d0454000c12119085020038810294404000340e0840d50010580c0c94892090351580e99640b4842c10900307208501c0700061b45d4801504401c0b0031066003a8420004001c00c500303981c0da480c0841c0c0034030404440c00454001d0040b070041ea1081d0f06000c4429000d4000300107100040d0b0014001e5210700c0c011700818081000140d0060071910340f00c2d03a0340c03142c9000428918000084d450090064069580c60485c15441e100e008102c20003103100e0076640d10741580c020b0071000c42001c23080d80207119640c0c07a0820b0103a0350a180b034903c501500108038200710034410340000c004444450610716805882801030040c244040c048500d10324080d0340d00c0c2d40d00103002e40101001800800c0440781e031908003414448030b200822061085040c0218001d4050f0365034402e120040c081032290b24062540010141e58603a8004c2045180088101e409406812560040d0a24500004845510a92110f0140350200342c0070400d0600300c1402e90303800201a10024902 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 520656097 1250 520654847 520654867
    0x315010c02220608010e07050418050a0201050f0702090a020c100912180b0301030501090210020c010509100e181b0403081b070b07030801030618020d02090a0f1401051005 75
    0x108030019010b1000b808500d03502d14030450760f50844001002d00c000200014440d844440351074031110701030382e4001c5041440302c20406486544070790981340c04c10094030080d00c4503401102c7c26840884140d00c8035006100c1c000c0581c0d6803e8180b40542c1071030700e0050340c0740070711907586040c1101c0c240440c60f4145080c1e940400320340c6880701b022020000f46081900c107003104200041004a40e00005541300d00800040308000055200d07071007150084803690030640828900703d0b556892000c4d19400070700144410791490901e803010501c240c000c1e041020b008107109000c80c00090010441d2041020400140148003c15034590401d620701881224a418156141c0c144144108519071420b5444070318030b000c100c0001e1240381d0281c155281d01c6030780d6141a007001040100d080c002640e0492504600c1199042c5110048040d80d602903c4285400065020402d4400c4000e181c0500c1588452140c0c1910300c00d48182c290030801201003002c15410401440260794606001005000c0108807038610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 520657347 1250 520656097 520656109
    0x7020a0305090a0e040b1b04290c011a0f0f0603130203010621050601060309050a0201032c0f0c0402090d060e0312040b060f011e1808060106050315010c02 68
    0x162a01418069a1140e454000c2144071906034042d4510b501c110090004100e041c2c0c0c103560144a450a50001c06007401d1401c20b043d1040d8070401601d603040c4429a001844030300c4034081c402d0a20b455050901074410000c0d03080d03880c8040880004151810382840703901d0101003082c0020819514142d540003900c022401c0380c400070b07021000c45840001c1090465400f5000f0701c01506010004e01070321142501c80c1981d9520b12401100d0a024100000c54123500c40d10861546035040b1006102c0042c513900190001c00040840001a40100d2451035402881040c507104140c02c0d00001c103000000012910f051500b6402010302c00c07401000200c080b41c0c3d071840c0600400d504036170700183d004c14003210b0620394450608018846003043c020801070141c4024654402c01042e03444c1082d440071107004685020010f40e25120b480401115407d00710320403000c000ea9051400d000c1c0c8041c0f40c0f240c40380740c03400e20264040300004500008100c6403100808240c1d600130028206000345103800d500181c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 520658597 1250 520657347 520657363
    0x501120f050a0c08030703120c0806100201150b04080106050406050a0302090903120a09050c010c0804091e110c12040f03030309230705030d11030a05070c0e0f0403170702 75
    0x5451600d101241403001c1031184110b5203030f003d052002e1140c0e07a6118142c580d04070388801e8000c00c2111382c242120100d540500b10312094944c1c0e42c120701c0e603121010003180c0001110020115980c6450f07905201d410040b03518058143e502d02c03a61907601c1c00c4a01825580f042d00328034003413800d203c010000c0351078a48003070090303aa04880034409030390392280c410310354015000c40c4032242c0091414464104135aa00c104100740c000c80595810107800030046d96a1076219a0003401c1c282d00f00820003141805600000c51400314150301900e00e010842e181042c1e038170909821101d0000051400090700d420031550341e413601d0144400d42454a040b0760707400014420f02c806414151216042c8040000c0c80d0480c1002a5031181c2030050041011046542c840c0c5138050f850083c03241e900c0100300180181c84103800c50464400542c609201c529086815400c048000c942400302c00307901054813600c190b2194440e000038034903030116150504000307002d914000311001c3c0e0720b041e40040c4408144d010900b50303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 520659847 1250 520658597 520658603
    0xe1c121a060a0302090d060f05060f0d03020d0e01090308041d0105010804080f090f06030a050108010f140114010c050a050f241303050409021c0f1506181a09040f050112 74
    0x140c9942d20740021403454606d40030002c044c645804100c0321010f40c0c9074807580c05044244c808180080400c010b006d8140035256010340507034007041614171031034480c0c3c4040d020704d001031400b5100715a0b00e60350481140c10a401000e030300c0041446031040c0c080c40b0314801d8010542482e080c1da240c14a619017141c5841415044881c18100240c0c0c941c403900d07401c182411a04c0050006c5540b0305c0c00b5401e001c0100707002e0242d01071550901c81282c101d43d040d03000e010409110b0b0036400070140d107021104061401100d05d500d0520020345000b60120320140407001e00580070340e01500d005503c40302e0040c1014001810303d210000882075043c40c03100103842d596800101500412046403275401d0589940c003c81d4080680c843c00040c41d90903c100d040c4203c9800c001021081c001040e0b40c078003044c1070724030203d41c40c1d041113000d500802240c0d1050780d510007601202209014240d0303ea919021120b0b0100c0c882400d03416001802000c10304117031164a40c0920781c04020441541050155000105001d00c06 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 520661097 1250 520659847 520659851
    0x18050a0b0901060c062a02010b090601090b0c070e0c0304140a0f030528020c030c15070201080406020903010c03060303080f070206070521092505090a0e1c121a060a03 73
    0x104c41044540d6201009008800b42d01144e00241c8210124001e94610b60480040d400e000301840b0b107040034a282401000b0585274032540c54100701000c5080d80040d1004202031003660b0000490100c44009980150800d103540e681c0c0307260606281c1e0145000d021424900c2c0e018000d40c0012801403c000c0c0d5a00350315160503581d41680401c00d512680306410b036080d444088042c0880d0f42a000030710360604050603010364010b54105010408100d0f45036521841c203543c100f18410046d0321a220207580a445082d0050500711402c011070301b1a0030a03d101d00220f56a40414018140c01c00c0d0303081d0340568841491503092070046002900d4540142205051105c0803881941c80a60100400203407007c07040224210328060043c5681c4402048141c0800c54a942c2c40b07004400b80300c19018256040680042c4070740d1100300c030b584000d24030000310507407901032740450703c04c1e0200a0718002c4040da650354030031502d800044200c20842c0d001c4407034211a03502c0c041072101c0d036445030015038016a00038100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 520662347 1250 520661097 520661117
    0x7061d1002160f060e0a031a0c0f031303080f070c060e0705090c0d06080a030e1e0301020304050d08071803080a050c030c030712030b01020604170c030418050a0b090106 74
    0x16454081e00c502e458000d1001924003285054520f40300708229111039641c3c41c0030161142c24024001030360300028240d041114160303000c0140011b20903070800d42d441d064500e0300e44401714007600c13030b003060782d1144003200290b25071014107a105100540201c855a50751302c0e90304180c8400750000443d510300918094075608110035400b024000b044c02071401402c101c1191401030794043c420707442415036407485442d01c030020641010004070a40c080398507031280c010090f00041023000b445c80080c6440b10b0305d030060704811440e13102800554000c52065001f0301301000072100141c54010000c001e14104096000014101e0024100b0201103c4e00070300199904d003043c0004071000e115a901e01151840001002c4699240000007850b80034001d03080240d000807c8401282034031401d1444500683c055800303c2e001c961074a2100700d0158504030880d14082c040c1a0041c01e42d00036901801d9041722251240b4600b0703040340681e03607000354010b9041001c100300c0c40c00036050001c1030280d0340c1089441c0700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 520663597 1250 520662347 520662379
    0x54f08070611210a020415050408011b020d030203220f02090601031112090a0204060e040c0b120c13030b0106180b1603120b15030a2409090206040906120507061d 71
    0x4100d4001d0480e181d04c20b240c0300b50601000e2300703d90140c8200101c542c41d01c40d1181e040c420314441040529800c0d80586292150702d0400c85c003079013010b0040741014015404903450700c0065402002400d2080084a1140e1010b0040018681d00100001c1c1458100b00e19014201c0d500c000301c0d035003a84a110741c81441d49401480525280303072407100a40080c034008020410103101070041c0d1240e031042280c3d00c0310369160740c000b92040c00740070300c0b590b124080200498804070208001e0120740210050701391080340d807501c80c00345040c03081e88450080382141140c0f1840f42072240d0304d01301a1610b005400c2c903081d036051070196429000c180c06030411000a110341c0110550750001c00c402a001480d038403d00d0381c101c45100f81c503403058800d1501d0303614003a428207880f0b48500c142c0400588001e1001145890003c0841c09410011401caa0000041201180c0800c2c10701c1180040c066040003078020b90414600145018800e0b04080b09021629503001d410422404100c85c041205895051500c44896 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 520664847 1250 520663597 520663601
    0x703031104030b090f0d0f030b061608130602010b030c01031d010c0201020406110c031c26040302010e030403080409020d0f1806054f08070611210a 65
    0x910000400360000074000180a42d401d85036004428940556a81c807110140d060750740c003540600480821814110f84548034040c3d071007015542c4020701a07134580004140c1c008181e11992a048a0103c070201c1e102441c5456000c180d0050003042c00200003103200480000c2e41d0380610030f0002d04040e280e07242815581009240900d1091000e0700a021030101c001019010713401c6401101e00042c00d41c841055451000038034103a0303412019018201c120641070880c0160101e09006a05100b40100f0030031543d1135400300b10b03480c0300c420920300049050a19009080d1090904080c0b09640244410b00104041c04112000c85402ea98010780d2401130800620241156900310b0a58500e424243c005410802d107100550b40e01c50001006030740e480ca000235005440514051000b540c01d400e920210080c1c840c640503030740f10500510300c1a41c0a46009101b41c003120902201d0080c0081410000c102d55400703407600101c03404010a0070080c60301d170000c1101c451283e00400340f41c01d130707030114500035180c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 520666097 1250 520664847 520664861
    0x13020a03090f080c150c0d110f040e0f090a0305030c09010207120b070306091104120f050118030f080112060b0f06160c050a05090c210703141b0f070303 67
    0x10a0081100c0000d90030b1054268001150130001d6004580e901110340c00c000c0348207032251004d40328080c1005a1962000c0043c03040403141d0444010030043e0205034100140940000d02032000d411019180880c00d103240c400025080d5000307a80f00c00303011000a5000b00030f50b9848898040055118800d031b40040749498840e070b200c0040c000d50b080e142004c0c0f0000e0907a0702d1061409450a01400d1781e14032103a0202d81050006030021441480140b08440108070f0004a5078005e0864030064661500c886084951040e080324007031110000758000c040e0000c2c0707400d90042c501c0c24425034642c503050000c1d652030641c0348010300c400d40c0c0d00840100da50380c0b10041500c0c03a102078105074036030820380007604440d1003c0b5010740c2c469420407400211450f0040a4400350340e005454500581c498280454164101e480c1424140c0a50901900e4a200e07078841d8512900352950027140602c01403404214224026000c2c2c6240c1603a101005140048402201c801089414001e6900c281c80e041c09c900410f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 520667347 1250 520666097 520666103
    0x50c091005120f0106200c060913060f080d02030403030206040b090a150626030f0318010908070c061e0809100219090f06080103080a0e0d050f0c0d0213020a0309 71
    0x40e40c060200400032000302a0503544240c40e40860000380c40244080d80101141025003940500074509848c1020070244c0850b4401412501400c2c0800c030340d000036603101d600304903500c0c4100321040203205010005021382000700d0000d949401d0640c0c600035220f102c000c0c00580140200720208010000c01c0000c1b07082107070480d10141d4139403000391310480039010600c0744c1012604a0306c0403080f00c660803003050010440c0d041c01140751030040c000e41840c541000309103c513040004a900915600700380220302081d44500030706940c4401d1450220000704140d01700504000c004104003560090b504480d001049481c2402c81c542e030703600020700345056030a099003020a400880d485441e0a03640c140300041d00c8903500c4400c0c0b899122808900c94085c00d1007180002119100100041000e1360010600e1011600d40030621360701c404040307800e5000c08002210b031584404402c640441d818030003039024140403501400072078842c0c1c001440d9000718490070309140d5800909000014041d5000d1503100364 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 520668597 1250 520667347 520667377
    0x1401060c05121810170a0204060207120317090601091a01080f2203080f01140310090201030f110306030c10020c042a1706030106060507030809101a1201050c091005 72
    0x9241100104840c41282c0940805e10036540071a007950081d000340c1c2c040d00c282d0b50003440b40e40c1c40c10402001011410205500340165100600f80340e858100000f88104c090000030030103945007074655011038894014140555602c1000340c51140e030701aa0355a00085805400d00340d94890100c1e0824000161102d4069001029400300405800c070f41c0003803185030a10401c000b103aa030340c801014520048965982e06401c00048420920001d83c032541c92640180350004042156407001411101d00d0800c0c603001c0c0030040200b1440303150030082d240d1210b409480c240184000c29001070b40d84c1800d14010b1b88501c1d00c0d5000c818440092440d180021041550120403240d0212000351070320480b40d6140c03020322040c00000c3e5060034140540000c592490b90b9003840c140c038a40381182c040b140500015418000c1003000403016105003c0c100382d2130180350a09484900b2101003180411f42044800c0c2039904110400c0348149100080d640050001d552144200302c02c4002210300b481a001e803941251 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 520669847 1250 520668597 520668619
    0x90609120c050a1203080604020304051207081e0903010e010b091902070503030f06100e091902091e010318080d2d020d06051906120e01020c011401060c051218 70
    0x1301c03403804003c409500a45541c103042d1160403d11040e403004440140080d80800c2c2c0040d20034040c10011704000d80120030300b40c03c0030100043c0795480044000e00b44460800440c540b5240c0c542032045002c0301310100300810040b0303001e41c00b00e265642c00400a01036070002940c0480e6099081d0115078000f9032210a03a580c81c607100036011801c6005030303101c0d40134154810341c0e0510140510750344040183c001780b41d206540c0e290503250b96030034441911826501d0b028840f40714103460307030300d40f200540d45a4492950741c110390344c000404075021500b0840302501450903400100b49001c2c00c498082c4218900410400046501428200903010070080b0744c032440062415420304a502a003d0802001010b00c8410389da0404c0100d0036203842440b00c40c040d01c1c901d040242c140500d28000320446942004902c1469070101c03c1d089800001800c000da0b51100613210841401040e418050b101904101c4002c02c2c15445442d03440301e801038240c41c0c0c03100000710b40038214400000f031625114001c203058103131 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 520671097 1250 520669847 520669859
    0x903020402270303030f010b03130b10080d02070b07020d020301091502030a05070306051e120f060f06030712060e031309020c0c10020a0b0c0403060624090609120c050a 74
    0x38000c0c94981400004072000403030514035000c4116030146d006615034903116401c00d210b40c41164030207000200400c0b4544c016000103801c51803094420b6034401c000b280354070300d044003485c00c00d000d0a220b50110b4000d0403060021030342072030660b40019010b80e00c3e521585180e10200c1d0041c5a5141c0141504a182c9820403451800340c0003944124030141c024030460316405829000d9a441e40a45540302c440d18a10303160b401901c1401c00c41e01040144125031035042e0354219030074007030740407003c41180e08880d082000c00f55840981d02c0c2c10040c190010f0001c1c614186c619a0b00b08d82c0000c00908c0705071104118040000308100766400c40f0003407003128130442d03030b80d0b800349009600c2104042d20034000c4900c802100c3c9042100b0103a4100e10ba0064941040c1c00e0340d49034403006004080440310300043c00040b01080c8144207000207007800d401c1590761044100c040041c10100441d626042200b5003805000040c0d000c45040102c64581423640300d40c0c601880c0140900c1c03e250001c0750024050300000542e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 520672347 1250 520671097 520671127
    0xe0d1b08030c18060f030109050a090c0b120f0f012306030112060b0d021c0510140907210b0604020903100f0b010503060a171509061803030708060906010903020402 72
    0x400e181d4010801c1100f01500070f02001d030184542c401200c0000740010084020107400c0b06502004009000034000060354408000c010320390001d0700d500300c8c0418558100c0b40c0c0007802981060350f03000480943c2c9041e84402c0100e55050144400130804411a042c010703440494060030b04100511140d11381d03844500d001068180e09405031401414030071000c031503091004100488507005050681c40440400e407441d8503624414003101d9900c601d035000c01035095140301d61a0078090041001e040b9040c4059803e2420b20550054035800c141410341b204a800203108900d07180350300c03d01d10300007580d13444000381c021702554a94036050b010711105c2d0102940e80e544050351210080c1410007207900001c2c011039483c081110800d0b04040e82940600105041003903141c9242401e500702c940d508140807881242200555a412040e0300403001d2182c0d10003900504010242440001c0d400c40c81c1004d402488600e01600081c0940401c50104165034424083c3c10041c64000e4410f540c0c1c0c0c650103410400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 520673597 1250 520672347 520672357
    0x80c0109120801140904122a050d08091009020f130c092306032a0901030c0f120b01050903070305060f06030a03050a030b0a050405070c0b09010e0d1b08030c 69
    0x202c056002090010900340321284801c03000c2d01c04102c640e0b8a55a82c40580101d40c08007080c000c100d50603142d5400c800e0510800c4e15105040f105008034a460881d01d41001c034640d90b024065054104928040009030b01c0440500c524008a101300a40c0040340d5200c1c140003004e0307000f6507d4076403484440c20f1908101900070a50ba6041503440e600c003072a05201d501040e5180071402c20740040c4441d03203048e002540d0801c2d00241441840f2040b1100642001040881c00d1401794001c00c4e002e50035038241c804d0255001c13032424401822241030300700400300750420020b0015917955400c1e0920b241d1044060b0380003080064101c2d2201c0e5220308009aa42e80c040700c0c00040c00382d1690018146040114581c1040703545600e4840c01d00c1c038182c2c1c0690103840100c0c2c0454110b44803881c0061a6900c60052a00800c45c80e190210505114101695401d00052800b05140c1c1402580c0444100000c0d140407001c0300d503c1d001d50720a9040c2c20b4803000f45915003001d08070304000300900c08401907220080c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 520674847 1250 520673597 520673633
    0x20304030302030411091504050a180510060f030c090903021e0a2006040b03090c0a03030302030a0b12060c0a0c050105100501020601080703030f0309022d151303030c080c0109 77
    0x283c0c004000401c021040b04100e864071f6114812680c00e8142c0e040a8210f00d4004c00120801705400e80740352a02584200c82100c00c0d507007079205040549803040240b2070750300038140d03201a030010b20f82503850b01a43c040d098482d000d290343c2c0d5440100141482400f080c4140c543c10100007294a1000b100155a4400d2200c141c030300f8903440c031384800140407807902402020009441c450501e490850107000c0703508000c081c24024011050540000e41e84d03c0000c00c0a180300380c5006899040c407040d41001ca0b000c03036041c907009401284010384802400103105501c004a070b2149039a51181080403620340c84c1c03180300140103600b000c0c184041402d116000b6402e903902a400ca4489a90b02c11083d540c4901c51310028011075030040030031101754825040a40014006007444c0c01840720451a1042c402001782c426214118a0000500624001085c00c5002584007416410415240300321603401c0d6852000500340890100c00d03608002d10042070301d0034480d200c002000300c540281841028451504611 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 520676097 1250 520674847 520674863
    0xc29010620061303110a05031309050604091109060f04020f09090f1e070507081201090b030c03070902030a1503141614240a0302132108070f02040203040303020304 72
    0x201450400000c0c02c075128040b032031122a401500c60b01c4c00e13982050745502c0031126000c0d06c07011102180381080240b0040642a031007102892400a82604540d4080e1219106234101040003000c00d80482d240302036542c0440721800310f0f0300e85900280c22401e100001c20340080c00030070b45a446104d40005090317218019034401d01c10303584802080044d00400c0360000c042d000250031030341c40c1d81c56001a85600c038055081c09480c00d0b000b52648c1d800c1d0340045040c0d0750595010720043c0000da9480c01460b046040540003480680000301c006522141e0600964465030790100001c0c500e0780b902d4114200f07401d210020508203680360304002c1070758034080301540c010b4885da150703114a03001214507032421162000010341c001080041089803003201d0b00303804060b08032541181018400048010081100203490043e5600466200d805031300d01581d0000e01c0c3c055034a10346250300e0110100380441c00740c1c4010b415603981214640b40c4c42c49401100060b410a2001c0200420507400d540114000e034000d01034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 520677347 1250 520676097 520676147
    0x9070e030d1106010603020f0f09040f0e301b0c27071706040f090605090c0102071203141e0301030c0e0612030901110a05160303120209010c290106 65
    0x101b5804ea00c900c07414540340c200c08101d070340d6030300344004007610082000134000324105203199840c0b420740303502c48841c55158000c42d104c208260025a000301108007503800c0421010000400700c070250007040380d60f080560031203000300190f0500703000c581207101000704416183c80131a60010811101211901984140319022500d5240900a60344d00d110981d280c0e5262a5100814080a010b950300c1043c1a06e0b01c41181500080050184a219192410042034000030390070009140152540c011140500388150400209a004080060f01c5503d421055038400c512800001c1c5900108084066008080300100400401090b001c040303c1980f0400c02003a10b40404000440302c0a424004c0c079a801004aa040d41d4060312203510070152401c00d688001e0001c0c0c172000e00b418181012071203142e2928030b040c402c05070010750341603000c05145021824501040000f8200c0c4c0200003014060600f262101002c1c445002c80044407820800d50741c0015503598000a030400c80d111079031800700d03400d08103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 520678597 1250 520677347 520677359
    0xf120c12030402100f02151807141e0316030303020306010306080118170d050408031806100605070f060f0501090b030a0b04080c07120302030702011b0f0209070e030d110601 76
    0x41602c0c01190018a10b401c440c00c0001c0641d111018403802d40c0540c004d801e8003010002003680141e00c00c2c0b04109800c0420075004140d20704140b01ca800142c1c541400c640d601c10244c45003c000b404262241004080180240b000280b402801d0900088500e0618101004241c0d05801450041c10281c0b030500949450308556400e0b00d095030340c0c507481682000d040b540415540038070748001c090303148009880d00d00240e6085040e10700484003914840800000d011600d4003280c8207018800041001d480b1a090014603800001000c0c80742104021020400300240004101100d00041d4009400c11040000403a1100989024482c81c111145000c0103002070b800c0100c1ca05031002c9d032022680e10350340e13500d590b01a0035801442c0980c0f40d52040c000c001c20030b81c400c1501c03d503809000c2e400941d140c0d00b26100040030110100706561194108001c1ea10010369010084403440344e040b40c00b00300301e5460b0300045401c1c50452034a203526118600010300710039001090403960402050a44105a0b200c0d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 520679847 1250 520678597 520678633
    0xb0d180b09010b0a15081b0f0d06030c0e040b011514030720060c0a03050a0b0a06020a0b06150304060207030309020a060f0201050f09120f0403060203010b0c0c0429030f120c 76
    0x3121940400d6225000a055a414032100300540280d06a128105288c4c3c0550b0b40142e0880065014207907540c190a005000f0351148031002070a1500d1288074524080c2d603440202c0c034061081c44142c03020b5800400781c1e02d014261300020001842d912a49900d0580d00c01401040c3e030840b040007040707100c0304002d02c20801042a500c00d060744c6085520b048840f001c00c80050400408000200c2d980c2e0b210950030340e40702e40c003147c01800349a0051541031700c1c50401c0400c0c01d030050031240c41140c038607079160340d40d010300c000b80ca038000d0308010300503101c2038a82400d4001d1320368054000c1d8451a400404185181c000300540404040d580c0204007036610002602035a10098450003066440007410240c80d100c00390040030700f0082c00c4052414260340c1e96852003a6082a00400e143c018049901002c03403070308100c40c507818041240d041c010341c0c05407407808079100001d0780c1e04016040710080320000c0d42c904011210040c0c21280865032140180ca90b070303001c183c01045030381d0018020b0103c0303000016010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 520681097 1250 520679847 520679879
    0x200102030a0f141908180613050307020a09050603061609060c030c02030609030309121201121a24040506011d040b0307030602190c03020c0402070c15090303080a060b0d180b09010b0a 80
    0x306d0080c1942c1e202d92120009141517a0411180d41c40100300000060310707040d01c2800100ba4011000c0340c00e0428004143c00c00b68002d1280d04c04814201c0031903c06944004442c00316462410b241100c1503107810b0440b000300540710003a40501c104000d002e248030707000004500c100c4204081e40c01d0300944d880400d12620403036412503c411020001840303030190340200c2100b01403103502031200b001d00d2509002c251100c1103505844000702800341d070501d4543c2030607941c060041101c00300103900d060700019040f44509030802c8407079582c03054400c80c503440740d030300c80100702100904a0b941941d907450075501a51000442202c002c05612000d980c45009050702d620040d0705801810b860003000040c44002d401004d070694460f140e210001a14240c000d444e103007100d9260b03035961110350443c240a0100303000940000119850590300300400414001a42c04050359100c001c1424078a030080c240e402c00705100c001e403034030b680a81846200d1005510080601800340d80d00528280d444040c03100014079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 520682347 1250 520681097 520681141
    0x1e03020307140103150608090d0801180f020d061214010b0105070803091608030d1b0f031d0729030606090f0a0f0909200102030a0f141908 61
    0x4101c6050128250104040b049100b06240010314031078801ca00030301d801240c0c1d0240c8003007040300c41400006441440400b840010a041c1390409503d0040e061070a205a0344003030b12075a5541e40f1007007a0f414203404454541c030b10340000b40000c80c2c4a100101c0c407900c52440c201c400b413007600941c4000a9040c0184a50124140c407401d0070040191585c0c0381036400180302c45068000c00e05d605120b100300040c40030141c00c8840095480749102a0000115044000c801d050315007200c6040c00342c03950007108940060480e10303001c108103944404100701c070155064100c12601070b0010219810100b0010b164a00c921616000c000403564034090016120564a640c1c000f0420402c01e1b555080201c80c000314110040e290b41d40c40c0d0303600c44080c100b1118a4002d581c0e161389803200c860603c41c42c4031940f16079807800c1102400d115007050020f540c07481076071050820700c116100404113945c01080c0e0716003580c00e4a01210303501c2c0034480d015030729844006102e0340441c00c00030100e09800c0244140d4000440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 520683453 1106 520682347 520682353
    0x1090501090b0a14150712030e0d09050303030601140c100f1a0d020121021614030a1d0d21030b01080c03010306051312091e030203 58
    0x400482c1c0540302c0c0ca520700084c080c3d1403111201442002084403d8440a0a02e10301d0103c82e00502c20058031450b4000d20590005030990414403216640200b6510440590380040d1810748050040d2601741d0300c1032001412075401980c90311200440401c0701c906100002407494500440740c08884805030b203808485501034410300400c6046489115458020349440010504564851a0103410004a00c60103e81b07501507035013456103c5402e120542da5194046c84180c060100303503d0031162a6038400700001018030100c1070310f0148002d65904c03020040c1d04000c000c0202003850701103500018038501c500004514481603547c54140c124441c0d90a0600b51000c0c5c221130403040901d06100c0003070304200c072148140003200c5c1543c4e0300400014003520f072490032011548446900805001200c2e440b84032403074102c04100101c1c0e5030b9402d00003072801d000d410440105668400250540c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 520503597 520683453 := by
  have h0 := BRFrame.cov_init 520503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 520503597 ≤ n) (h2 : n < 520683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
