-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1208
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:46:13.749959+00:00
-- url     : https://prove2.me/submissions/e935e1cb-8830-4ed0-beca-c146d67224cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 217086330 ≤ n < 217266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 217087580 1250 217086330 217086341
    0x603051902070f0f0507060e0d03270902190810030209040f03020a05013b0606010f050415170c1911100908030a0e010b0306010b090109080a06060f050f0112050a 71
    0x10080b40401c1040c2c032a040c1551509170511487d0302043c81d02c4400017450401140083d2855059200e480326190541e5010491424444100000300002100425a5407880c405000d402c0c111030b00f034200d1115410405060254094043c00c1c41e88114002003005994580c065030740039a0002c4005030f440c1c03076890207a2910301482001080d03542040042e41c0b00000c2e106450010002d041e0207900c3d200031410704e020700c14286490354103068210344006586940a00a525035154142c508245070640c1c4032200500490403442c02c8000904007a4181c120f0b6554200240d00b241016540d20700d01280360709548980f00010019106000520f074103611420303018030400f10720301c02040082c00311514a140005041c1e0040360b4041e5801d01c0d1001e0060103503414810f400500d44054005d2400380d00b0031071480d02c1e40d0170000f08941008000c860107e00883c090040b0441c50340b050201007621810b20420081003a82500301502401101d03001c0900e5a0b0710030b6207421a0804010005455220010007002404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 217088830 1250 217087580 217087583
    0xe0a0813031401050a1d0615060715020301090b010513030221060907051c020109030212032106040b0904020f09040611040b0c0f0a0506041212050702030d060603051902070f 76
    0x12030b0071090104801900704911498100d01d0801001c4110301091100d006c8200028880380e0140c4005915032402a140d94005803008068a003008040c0c4c2d00e01caa21140c02040108081c0c01000402c59101c4600400e4510303d001d01f003403410101180340c4603c00d14840e1101034410501d1045505000d54405200f04020310600d09407051460302c865255a110940c2c41613a02034000e600094040d402d0010004c0951603050791a14041c510719001c00116800b80355154090340401c00066036042042c25000c106030340d403601b0010444c039041040008440b20000241c1c0079208040c1004010390301c1d800c42c0c1000d4801201c0740c40c2e098489040001c01440140406100a070380040c4c081070151010700a0308800b14610111080502d0180300c2d19112500340600070103550012011034002505030348032440c0c41910b4034042640d904403851071070555034180c2c0c0b01d9001d6000001c49010305180d5000300300141c049401c05001904091040b1042e00e04042460100707550701103450820000003000c42030405 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 217090080 1250 217088830 217088843
    0x5041508070e1c0b0105010509030316020f030d0c050d050304110d030915052a0703030809011503031710080c0d050102090303131712030601081330030e0a081303 71
    0x8890480c0c0a40c50740c016503c0c00e5421095002c000141588504110b40a00c40c01601a50030b011911120180c00011482e0880e0311205a28940c00952070401c10020b01407507960724464002183e0400070308120b119180d140802c4420002c10002c0345000780303020058907003610300a02a82842c101100e030801c00350442e10702003004500312264164064040c000c50b810800010060382d11801c8401c2c0315910307003032060180e0303080b0301420404a80207900f00c0f540440c0c1032002240340c1482d808003400c03441d6183c004401103601d0743e404d0042040e82502d0300354040c9400d98120300460030b203804150784245413000307144140d1282403048200402034054420000c0302400700c903114082407000080000721401202d42c10703411162101e4280d007000850b0700ca043d1041910740d10b1503d440e401100d0000d401002c064481b001000c06000003108031041d103265402010f44c441c0e52580d4440c2d032030400d0340c1e00c0b1003c000b0507041005d07104000f50b0108021400f00c1d803090220b41e41c4d0b1101c122070000c1300a80d44c00540302 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 217091330 1250 217090080 217090099
    0xe090f0a0803070201111602060304020d08120a18030e0603180102040f0314071d04230a030306050a050906040903091e03060f02070f02040906020d020d0e060705041508070e 76
    0x400c007031040a10701552458000740980f2501c1320f4100000c0c043c0d46260100f841159402c403000d82000c000464119002400140c43c020b25500c1e007481c1644504104500c41190904100b54183c951180400b6800c40c80d0307020b4101001600d0051883d00400455031080c0340010110754090010300e8000a2074800708001e40d01c403a0b45101808802d80c41c1d100c280c40100740c440490f8000007000c20380100342c2e0783c84c41e02504200fa00c94040522068002c00c1180c94402445080c84220180e400005844580000400c0b1044981c507006058405981c0321a00951b000d00052080340c0c0d86081c125800728065a00091940950030101e450021f241e03c101418a00e04a41581d110b480b4002c4106580c003c440600000c004295018100d20810001501504540c01d44038014a010380025142e0350044501506005c05122000f089900ca01800e060899440700c204042840501c1129440b031024202141040d03c0c000c000e00c0858040381140c401c20501d1800101114007910304928840c9010f48030088 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 217092580 1250 217091330 217091333
    0xf02011506080f01060c0308010b0c03041706180102180108090309041b08220303020a030e101d06010e13030c2f040608030a0c170c070e01090207050303010e090f0a 72
    0x4581c02c03d880c00000301c5444800411800c0c0502540982c050b41507582c201140e103848404c44007a009000c801c002808208000259000c50803030310780b40507268101400850612030030201c40c114070300018200382d0340107212215011482014444421800f803c02c1d1510b503542003004e500b10321a0a10703040d880342c83c1c000807000d00800385644807044501510780c1c1c00107071604107407580300702c89044214198446802441001921940250003103010f10705001c18540050300290341001c0c40d07180e03d0720081c2c3da240c403000c07000e0040c007040c1447c070f03e91140a4203865040c400d81d80c0103c100104200201c100d0100e61508062007112000c6905802c02207201c1345210b0340300e1444007144181c1001c0c90302136048140c04642e01d01445103404450881d0000d500e424402c0b02e0640e5a070184603020355003e265611101c2a500310708000b4040326000c1703006854900d06282d044a0144030682111011920501046c0000748000085134151090291180410340d1000c101e185449a0300c0b8070300b009405030004020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 217093830 1250 217092580 217092587
    0x40605120c090f010e0c0702060d0c020d0e010504050a092301030303140123010f0e03060a02090418030c02040f0e0f0f07060c0c0e1308040b030103050106050a030809010f02011506 79
    0x310041c0048a80040945405150b103003520000c1c0109000c03901c43c0e901080001031410b001b0201640302401e03160420f59100700850488003c2c0340110f016800404031840d0700c0340e120903030114050003401c00505040c100001300300c0c0e61310315000c0d40710b6040ea91032021005902035028001d160800706050308256841e4035005024001d110b030041000d624010000c1654000340c00d030760b0183d5022204411480c0c440c40c00443c2c0800780f42c4107107001e00c80c240760540401e0b1400c1c821a0300c0313402001740243e6504410000e01c4102c440f9400d1800c0003450300400100062b600035042580250102c2d03002c03594005200a1400404a0001d40200c504c40c1154403e1013210201d07034082c401d504001610b84880d6200b0f810750302346605910017000d0040e210000d000181d0160311464025003d0054030004c0318150b510340d00942e01c1a002004c5514002c8010030401100b4003640000c2c0205071550314100e40b455481454901450740702d14103121180c0d1111030550f200754015011b400c649050f06010365a0b49030085c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 217095080 1250 217093830 217093843
    0x20a050d020c04060b0306030d120b04060e0603070e01081c090b0703110f010b13020706111308060a0c0e040209010e0a0b091e0a0302120309090c041e0509060f04060512 74
    0x1400f40c0d040010018030b0744445030940380700c0c1c0c0c0080c1c040c0c480d258200c40c0c00c0b00c0c2044c40340b903d0070006a417807941c0f001a403103074403403078000e404807420f040740c542404030400d441d009003541700002420030036005019043d00841c2d400325441c41c0c04914420358481310401c2c0c454480da904004d469241c045003c0062542c40f040a0b19080c068005032607101c2c2c03c484610b030a80c0c2c050303072005070031000b101a22261850709500400c4014010200029000e40c460b54000207a0310064044003058044101484401c90911059400901c21541001105080d800207014540909401c902c83d03607000c6281c00c0664050780003200340580040c00c441a49881c0c0f040340c2e0141c2c011030891030052400440c500d000714501d20700038010303400c003d00d001c04551859007049a41240d640c40c03903106001c1403040701c0194403100c094a028154480400d42ca45080600120002c041c45110507864101100c04100540703800400d203070087c6050b1808010996a030700402c1c05002550b000a40040d550546c2a17117046020600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 217096330 1250 217095080 217095103
    0x5030f07151b0509120d02010e0f0601060903030302030c1e0a1d06030103020909031611010f2c03010e12040e130c2c040f02100f0e090403020a050d02 66
    0x260040a203115090408640c2c1c0d007681502584002140c40b070415000d03001928442000400100b03020381c07010403032030138003005108200150b074665850f04c06030344041c040c0540750003c0c4030080602c1c3d0b14208005084c00080d10003d030031f00d540040030400514801c4100ca803d060b600300c1c000720711241e036011007099170b120f8515034000652200602013041000c0260380f4987c900200000e0440c0d00f15000c1140ca940d02070540c014500c0200319103034400d4503030044461502e000300440150302c941d52002629525409500600300040c1c0d039104094140d19000d540650b22817062921621072502d004a070043c0699000300c122440b071203080381c40392440040103205031050210000c450307440f80100705040c82c00800700140070600b6000140b05d004e840300c05071444080f110401e62400000e45508580781d5809039400c0c2c6031460145189002c1d4101521118520829441c0640d0010300344103005001241d0003003190301c200241380202d42031610800031a041303590400d00b0346524520580b000795551a0030101c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 217097580 1250 217096330 217096343
    0x1003080a0c021c15060807140d0f03050c1516030e0f030705100c08060a060807051c0b0a080613020d0206070b160e0f0d0803040614010f0303030b030f070b07080705030f07 75
    0x2500131984103500849040701e011030018044242031901d04041c200200c80310503044038032000c21380080341c0c2050010502034040d0b110340d0780d58644012800e040c5010f050400f0149212a01840380100c8100c041c510313a41d049180000702c0e6600766401600700884a82d03001c0c000c0c40080350400a01201140041100c840c1d00740422204825000540d00c00c0380455400340c0c41801c6071010070100340030303407025540031100345011b078030707008204110825094910a032580404daa0b4820303801c1c0e0341000301819000d0b009400040c1a1890201400b210354042548028010b48039141c0100c11512080d081da540b807544003c1462051401002d4120001810f000304400942c1c04407212405041010a011702240050000780c21004c0c1911842c03800da20103032007111065520107621081500c0044080d018043c0300401e07580c01851030600909076031110308100d219405c003080c07031204040e00140314012140c80a00b0306031581003d040002031400383c040c000d4240e0100003a401490141140109583c5101d0752 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 217098830 1250 217097580 217097603
    0x20a061d0a0f03030c050c0312040e10270f0509030909010b030415020307120c020f01061d060d0302160815010611100f0209030a0602090f03061003080a0c021c 70
    0x1010480000828440c00b031250781503103001c1c004a03124280060f0740d18003420841e560000e048010900d4811005924007203468081414842884042c58182c1c10600700f0410610881c200a005811003034241003800400a010746c0c5c421441f050741d00001d000d0365038440d08000c24540100301c05d45036400071001500c5481d46100220f116090602035901540d00441c11460003940389007203070300a52010303001e1410b012240c0800036110b900c1c1e0080300e8503010103a01812540e00103603c2c8500352801d6400c0070b007005141040c00b041141b06101001d40c020011100c05a212085040507424440007a0144103010702e0000041100c9a0004000e4680c0320841580c0b1031503030341c0301402c031070b40d13800c0003100082c540201c05038840307031031b003d03049456040179900700140340c0380d140000285019000d000441d4403507008547c00300b191414440310151040190b0141010745030100c101015604a400010260007001c12040340701442000c10040159000d000c464040190b6107000d1384402640f00210344104840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 217100080 1250 217098830 217098887
    0x10906050f070f0f03180f0515010803070f06020f090a0e0105150307081302030708101b0c0209221709040f0209220e01020a0f09060801050a05061303020a06 69
    0x2072030111401c3d0b000b943e07100c0711002c1400d8202c000e85500185110315068000282c0042404400c5100045125000420314105512045666500140e0101040c0c0d0030601006001c91907621810034019804800140e5403519070b902c10705580540c1d091503802550a030700c08180094500105810303501c0844044406141509085810348070031a400e0f800a0311035404603101900103644108664801000e64440c6a162403800b46005406606e2070000c0780c03990342c036100c0c0c01151040b419402040d81380200d203444690300810311503c13016006a0444182281c54170070300e40348110010405078440a0721050b50300e40c04800e120343e08264080d501c22031038140401807100680c802c0302d250850207000c85500c0c4028070444900400702041114040745c403480ea214040c0401e200426210740e254450710b210030001d02e0000c019640d503800060038410101e006200740c0d950b08488400301ca0382203905030307980d59402101130130610017540001c3d0090fa503050702041040d0804030940381850364002041d081e020b0f2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 217101330 1250 217100080 217100087
    0x60f03032f0f030d05010503030a210b190305160513020903010b0301050106030e06010602010e030d0b010201090b0907060e030a0b0601050901051909180c02100b12010906050f07 78
    0x1148001004560012a2614001501d035880441203149044450140d5407404030141000000951410650000154061003032038512810f40074103c258011070611070207800c09011030350540107400c440c156203100ea0800c103030750350090029904e010b0300b200401b1904070106103a03201c10b400100d98602034a001444c840c0701200022003110001031842d640e44040319800b1300294084c401d80c5405549400c0100090380302405014024502075900285407192250000e081501c1030f04807408590615001e10440c0300700000340c1f88001d0340200c00089003588000141c0c0180f9810038000c00d0511070900700081100041500021103030f03e03894a40d0040c0d0003404054662400500c010301c0018104c2c003082c3d81c0d5120348094100c034007041c14082e1600c4100c2040701c0c0c4141a017001c500005035804804e1080d103800102100024040d4542840281c4420001a4658510b29a84a950766481c440003409a407504046600300704000004c11402805040580191030200e8801004018120124807032910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 217102580 1250 217101330 217101359
    0x50106240c032a140712030c030f05040504090b0708090703080f0a0e03030d0911040905060f0402042013060203040f17010204030b01080a050f0c060d090606091b0306 73
    0x6150340d8022140d5120b5500707480b5403034404400315082a0700b5102d6110442e143c1c0314840c00301d02483c8848070006058203800d1a1015035004101d8403140840c00900080e040041c2c0c16500c2e030700d070509001c030038a40c980c2250340f809150f004035031041c2814015003c1c0a0840c41950081c03040d03a84910043d59084002c42da14401da200060a0311030070000001041c0c00a005460759407180e2502918960006000a1643d005100d000a000360b448449400304040f0f00303840c0c1c1c03c142058034240800c81c0e2a480310390311080c00030108a607011300c0600040456039544e000804026400d01d8103908040341499019240d00103114558810340b00c9040801c0d100c3c000820740d001c80d1b02c1d044601c1900f81c20320b4104840c0c001c41c1e240720302d695902031002200203980d082c81b00e1701a08040c40145800f140b02e060441c9415076003170f000040c07500480c00c4800242c46000440782c203040070b11000300b1003540d5854034000a0140e07501c005942403402542811804041c03141e042007108583e0300740a8151104442e200d4081b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 217103830 1250 217102580 217102649
    0x19030912021c050f040b0a1d0a0509010905070c291f05120325111005090d031101061d0a06140d050102090d06050117010902030d0305090f0307050106 66
    0x1100440494030340f060004240c00803986850600b4169581c0b5030341216004040100c0110b1700090b40044d2005074100203c20b852401c95104480301d02d0000030500b07045041c05404e00e01900c40740060002401400741400c825804980e910940300c6c0b00c080400c54014031400c0030601c105420100b0400c070a20040300d030641d410b60400c003c1b49850202080503004401405a200c1e02042c812003405090240d441401c02c080a0641101904146080342da0351041c11681d9202d840002102541c0710350001c1610b440e840c0075510300782901d810f400c0990307250038500000c3c12650309011700865400e100c8001d50012424900307000102c0e4841d092200306035241ea0140302e5070601590381c03010040c5801116600703042c0c0038400051411103c0004941d0f03625200d0310036210340d6203460040010801e06506101d91444840080082c0c1c40103070f00281d25040072a040004154640000c114030b00e00510001d00400545001c80344c0e607a1480c031380300380032304590b1043d0600c0c99450750340c40509141c450500e04102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 217105080 1250 217103830 217103863
    0x3051e0f011403030c060f0403180f050111010e060a0b0112020409020c240402010e2805030d090e040f110307170c0109051305090c03030d0b27041103031903091202 72
    0x20b1f035580340198080715008006501300203000c4030311a94207040c8543c0c3d40c09880d110000d500b2103418800054001e41ca00055441e40e68940001c80c0203140c40490225000b00d0440e4011403203401a00049865200e2000521625403002600250142a5030300078803c002e54202620120800d0f072503400c0ca5001c0d070842d004813000280002500640c411301265030b0b0309000400c4e048900c2201c1800c100d09010301505c528814400c0a82801949000c00600900054500e00032500d0350a0a5503c138045202800050a0403169103140302004842c01d04010401c43c00780c00c03180b00300e9542d00c4030403009501302c41da00d0345805004414801544174410203829620003400040da14000c0c80c3d08071000b420010000451030243d0a903409160382c1c24030040c4003801c00d041020807000041c000b009021147e1180400600189001c4900300000d4a45055802038201d01462507400b981008030707045104a080260308101c5426002c580c0d5501a4450b11645026038042c03200c107400e0f400c0981c3e0381c5003001d20354100c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 217106330 1250 217105080 217105093
    0x50f060409051e01032a150e06040806040510060f0e060915030706020d18050a061d040906090b070305070806040207110d06021b06010f0603051e0f011403030c 70
    0x321241d50402c50b000100c0001c455144050f10f007444501d40c0c1c0070382040319082c615a840b0320010000d1108424000b40a01c404c42c3c0080c6084c00903018920801c07880c4050103549040445140d9810054400800c281020b6480601d064541a40c54101c1240881c403001d26001000c1100701a0a80704800d481c07a409080741d064403070360100020840d005108404561105800c009035807002d0154030010421f070740007000b00100081e005001502c210440c0c0a810b03440103020072241e560740b0704010072a003850408213200c24070145045000402a072095800c035040c603e40e0300412025a22854140b401405840007075210450100c080e2101901d016001602031404105180f41a43c0180041803096601d0740380036103007401094209000a4054540503400315902800300f001c244c0700c501003800c06003e400a58103141111190985c05d014036802c06940d032000030b202c003000d6108248040c59041ca0030342070b4903b090089403801c0c0240071b0440700d00c42c404c42601113414000240c480d1050072034050041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 217107580 1250 217106330 217106339
    0x30e10110c0913020409060b03010b040b152206020a03030c11070504050c09030f03030f011d01120305040b1803010605040212010b280201050a1116110f0406080c0a050f0604 76
    0x7441e28018142400403400f204041c001642c6501c260280301e4490355000c40c040301108101401c5982a240d854055410100000c4207540e407402c01c0031610301508540c03621400d0303c100284201d480e44541c1c1a01850700600410f40540007d00c240c04035110303503018048103008030011034100d04540030780501c030f0b484584103011500e025042558440d0060322118100702c44400040d150005c0c610340480260800000e119801c0c0744612210302400070080801001c40b40160103c00800e0140306c1c0dc9000004030054004151068003203600070420b110520341c031000010202540c010031209000d1180d80b0f0701d4030008017400c15000b41c032040f16006e4042d2460381e2901d03a01341c08943c018140b90301a05514580e2a582582242d580c101c009016400091285800c0c00d81c1403c0313941140c0404903050301800140c500c40c1060a040d00c640383e001c80100c040a0000012400810580024980c070030f0801c07001103204440022050b200200440d8043d003c00c2e501c1301448410540b901010390400f10810080c031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 217108830 1250 217107580 217107589
    0xb0708040602130608010302120a030519020304050a03080909011e030201050c031306080405010605010e062a100906140405032506020313030e090f01091a03030403030e10110c 77
    0xe601502603080540341541e4025114085a200c0c2c1140000c04e90300c1c4014401c1d0b0520303100d03002c190b80050340103000500c811f4502030441e000e43e1400c0c500400c40b8407009000d20f4400c2c000e136001020090080707280c0a03141d01d01880c00d40c002c3c42c00c0714092002c02c1c1c00010400f0906443d540d0032000c24403820b40080c1150011a140c2d0720407001c1c003010b032100704070a21055200c4c1460000030712440d42c441e5503c0c10546415800e550385507008504111040310b000140d1741d038400c11180c0404060030302c840c00c218446030440000542c0c1c58080c400f0b0040a20400560445800241803e84182010008490a4119044544425140507003240d00c24401f0402c182629440407941519126115810707040c50780d1040284d9000300e5140604150280d4610b040580144070146450390464154181e8a400c0d41000d10030034051103141c03a4035403150001c51224501c641001c0d03003011301509072079485459007005407141c0080c8402c4c0e070040d00d01d510055110ba01c00c54500031948507010251004120000412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 217110080 1250 217108830 217108847
    0x3060a0501140f0a0e090102030103141b01050d0f0e0f0c09040c060804150504110a21150908030a0c0207080f1c0e120109060b0103110306150f04080105060a05040204030b07 76
    0x104d4000c054500d0200b09400f0a00e1050b20800090001503a43d604504d400d110300f40078105d0045580e84001c14001d222240c402080d074540c0401c0c03030b042c1c2c1c4880c0780c0c075450005000300244501081d494065a5100e218003c1030072040f0800304421542c06448035402d0201010b82210040c00c1200c81440511145128402e03807030b08136001380c0190039468080f21803503044450958085421310100391100b80241040c209550090502052385001c900200740c0c0b941103494000002414440e0a6031a00202801c0380e0007400311a4100c00c2c05910b91402c1250100100754000300480548243d80001400d035800160001c20107507548040e08034082010219885c019619041d8000d126107440c0c4046d1984460394400e4172808184004292148241401ca0440d9900366a150406081800c0b40201c241c0c240c080ba50444410394160b25144894070328001c0c0f5008035440480045400100050035980540205019110840704020141c0d50b0710100800c900c49c0d4030000b811403c039640015019400307488030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 217111330 1250 217110080 217110109
    0x2d0506010908061801060b16020d060608030a18080703031202130b0706050a0605060301050d0803130602040b0d050a0504030c030c02030f1f0605031504120507060f090203060a050114 80
    0x540201d03500c0e0b8100307074140b80303088583d400e2030080c41103c40094902401484003c014001032103291016006461700440300c01e01019004050240504c8100540360348840002c0003a001a02d44501c1c000400510280002e07240b035141440f4440b022542c0d03013000c0b40301412a607160315806c40c2c07240350188020183d0001400d07180708040500c800a180c0700040014115a0300c500000505c0f840c0c11450007080b1070494008a005500a00041c0b010f519003442c01d42074682c01c04d010a0300e07030751422401c01925042c141c00030301041c000b140000300118800c0180841c038000c0c0d0018001075590440180c02c940b42268054005500d1b40100760204c0e00621407080700600107000d030392200040c900340d20f00d4045080802e10282c1c0307414566028160191040c0405003c08401078202a02925100c1820990180000d80384019100c401d00c032590040c0101d500c282d50200043c443c1d041070203070081c01040e6408050b07009006440001e03888040d1841224140c45070380c3c2201c1c040c00100802e102e00806a01030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 217112580 1250 217111330 217111337
    0x7050406050328020d08091003090b0601180b041d070c0f06020a0302160b07030c020304030b070e0d060c09030b0f090d030f0b030307110f010810060309031b06090201032d050601 78
    0x6403070f0150b140c0d100c86030b5200c1d0150900300c0d95010414180154003024135070300010103140c900710800140c070340141140c0140d800d04c1c0c2841c0399070001e55040000e401a44c0710942208000a00184180c420b0b040c4002d804100315030032441d035890300c900365641c542080004041d1555162064006001c503405000d40c8841460010b0411b40307074804240ba00500150155202902030f000c000720140d0500075000003400d148003070750510b440c596620f6038260002e0b090009001d401c5600110948892012a9070a0341040c8244004010440090a039055500040c4d400f2900480050105260722281074001d00c036805c010141e030664120118014031980203640c1c0a15100d0326a440e241e5410400703020321030f00844094681da040d9030b0400001d41411101e150500140e501003012248201260a08030341107410081a10101444c045919070711a1082000441056010030140480d0740d02c01741039a8402e0702c04000c1000790880c000300741d200035002401c4400ea4041603444444090700640c0d0010410705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 217113830 1250 217112580 217112653
    0x50c0f09060f0702100809010f09030507020409050a0218040b15010507030e061621020c0105071e12120c09080c01050d020702100f03050c16030f12021902070504060503 74
    0xc4c00140408481c14034800010b84900c10310403220000c4c821203500e00000c8000700030000d0300b940d0240840c050521701034070440d503d032080018440240103ca0000358000c01040b0b256042c0300348148000380c155001d0b070f69000b0b850001290f4800c0003244848480d0161102c80c203090140c0d500b12600d03541001d020fa00490288400e034075030081c0398000600684aa959074054807288800210034508044a99085600c101d2000741d03640d070811308607601c658109074000125160500d4100c118103034244020030205000709803e0b041030344507003d02c0000080c0002804640115401100c41020a0003084004c2d0480101d0100320340c01040180b103d00c222840160030003030a900014940050400e00384081110b01d82d00c91320042d41071082c25441020032868605218004080ba200c00c414100000d09005000003185142d500920400590504100040d9647c41c1d0703106a040e038120714030300d0040147c480c0000c0402c062515010f00015160090018118802480da181d030720b10328041064800b0b0304558 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 217115080 1250 217113830 217113833
    0x11203091a0a02010b030331050306070c02010206060d0506010b131d1009020c030703050702060c06091c02060f0a091505040f0c0801091104050c160507050103050c0f09060f07 77
    0x644044003107845503034840d911898035007806820760b03910024081c400d8004014010a01d4803207400280c01c0084226a8407900030404c1c81d16100d82c1581c0c0186515109020400c103800750701425132907080d0b10030b9003030b1042c5440f00350a0161224030450f005000307400041c018420a00d801c405000c2d07095400028510280c0d4a012a550340038104284403040741c500e00410502c400800284002001503030700031460702415541b00b549902442c0f4005080100010b03040080d9650142aa00c40e802c1d5074064074000d081c40195181d580b590b0305621007151210402042110740045121881501e015580c00c0c0746170384d0703440510020706042c00119807440c011581d81c45c285d00c851040b9403203984108800c08580781141030481112002d40c0c04503001e030f810304144100182c05c0f24200c5440010607038011680d600c424003441e0480c080c0c080011150440c084448040c41000207180003240c00a881c20442a12044076801403072149103100c04100b9410060300000c0d08144000306503000e42c0d036071041d09140b001e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 217116330 1250 217115080 217115099
    0x150a02060f071b0501140115050d0b0a0e090105180d0203031f03050604080d0b0d031d0111030d020415050412110312030f040303060b090109030b09012a09050d080301120309 76
    0x3003d806855a0b036498880388000c8850f00c0c00640540a250011420311000d081d0080041c030030381079446076040e02c0340c807403910b0f0361120400c1c44007400e00c0201012562400c0405140245422940d10007500e403c144111642030000c6001e8101c07104c50341c091480d50742c0d50030300c9001900c5c000f000f40107102600300002010076024005203008611070310038195244540300d410015540c10981003403003440760720300040002c1c3c0c10540c2030b9104044608543d40b0890304600581e03034150068040220b41c000011448200c105a500401c02d80b803401c4041031000d81c10140449403401180601c80d490000100f84001056a030031214481c8100102100c14400144049500e0351b041500c1c1510280180307000c1c0000c064150080740d0242c07245400c0c0600340420540000c11a0006101c09042c964241000c100c034a0340079005503405400503004145070714100701c00400c40441000002e80020743c891000704092906254514220382c20030340e0b09040d07908102000c144400d140c2811001c0c0458080e00080301c121 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 217117580 1250 217116330 217116377
    0x3070305010e06010f0f0e010627060f080a020405060307140708040906051311190c1703060a080a0b07080a0b1002071d0910110706050c09150a02060f07 67
    0x31050094001941750142a5030030b030710310380c01501c1250050303d418050b5002c4050f4580c11507209203840006580380b0707a29a0314a2644040000e400300d070030000803178620380000703e0030b8042c81c0e583c3d07407400941c2d03c01040c6030403401107010b2203500403000c10101d03014070321980120980d01c545481983c980324090369880d019500641c80710100d5030312001d0803c0320b1f241480a409698004601c2032140c0c03c050070342080144108ac0b40c400e590b0304481c0341c0c80d629901c54203000c544503902540c0d064195405140c1c400090300121140c0b40309240c0b00ba40451051408540413020580c4401c009115442c6c140c0250f030040802449071040c50364644550075555030300160b040c054010398001c0d045190402d5280c0c0c0c2c004010351002031070903543c14140084c0001c00120280400380095000480c80e864950380851391040b5030340900301600300418031a03245c00070002020b104208540900700f0705070380c54040e10300740221030a00001d41c00840004020b800c0000362143c0c4151146042c0545c2e18808551942a03607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 217118830 1250 217117580 217117601
    0x6110f030412030b03030913180b1005040b060f04090c030e06040c08100e1507030608030a0302030601020d0807020c0d0809030a050f060106020c1c050c041107031710050603060307030501 82
    0x82c104080c100c0c1c03407a014032480d000c1d40000d801461500003410003141c440c1510148210f80c0c0e07a9201c803403005160f1002c050386805640108105224240b090b000001140c4074001ca40c41146084148022403424904030b51042c00e01c0c041d00ca0030603240036002c000915828443e80c1c10b05840c1c003031b01ca99198050002500c80d40c4030740441c03c03c5d581040c156030301c2d2444917204d102c59549403554607500880d001414a60340031502d85402819603400750120060011070b8061542c1c0e210208030804042e400d0340140d4170420080c0d00311280032140c42d02c119040d984c00d469440150b00415582082810402d2032400c0c468040d00001d440c103501a00801c1c54120301c8c03c025560b607001100000326000381070040720700502c0d141c8001c0080c019003200044400c4d070300c2003007001c41d0b200c1185401c017042400d000296003e40004d004006c041c196040c29400381d84268011000a41d024816007000d10020070380d0390003000544200b403001e0f800d10051042c80c1c1e1001c0d18403035061050380710000c00142c00340540094103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 217120080 1250 217118830 217118843
    0x605101202210111070620030c0f071104060305061501090303090b1b0706020a11090c04120609050604080406030c1e181e050a08031206060711150c0706020307020d06110f0304 77
    0x500c0100035800301e180e5640b400d07c0e00104108280803001b8401c40540c0c11002e01c015200e9601d80403441d241808180020446070040d08000c00042030020124200d44116118150714a040008000440d00b01c030702030000802042c030b00c01e0306008800000f0040c1030702e8000344031070304580e00001c0703011858000c2ca6400707480180e0002e0010400c225849036001b071a41ea0503624040c290501c3d0415401a000e280584031502101405d2003050102a400170303644650003005807843c1d428541040c04044d0701500403040440c1c10450401d0384039100350310040c2c0000c3c10640c07503040d002c0001c01c03c8a00c10700103c1d4600425180401c0841c2a0403003d04078056548401e8040700d401d031401d0144950100541d21091440e041480080800d445d06800140e104008a03110365039001a86001c00c406000400515045050b0403d003192104e0154010004070b02910304544903242d44180407030313403442014402500034035405002e45c0040e841d904000ea034503405c00107141c244100c81c071100c022034004070f41c01e9a21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 217121330 1250 217120080 217120091
    0x30a0c080c120307020a030b0403180b090907170105090c040807081b010203070c050d06091406091009241b030204030b0703092001050904020706051012022101110706 73
    0x141c079040e6035002d50301005030051801d018058001644401551001030b25060026000400b054428101d000d4440951200220a00d8881580c403140e6041106045d009156410108001c0c6026100c000300c0f40411191b000c4041c4c1c00c10040c000300b80c0d030251603042203400a05c000301c1d035030000380514006011108020103010300c00ba075070000c0541c8061862415904200075110126106452103400d48000b030324041c0101e006072424000900c4000c6c005040311090a40941c1440c101003203081c02041048101c40c140341e150510002200c800c1800103000075041049100c1010000880c0d8021909429000600802550100c4400f82c01a1101c0f800640d00280074030402046010180c2c102005140401c2003101c25139a1400901035001581e03c44040c3c0c250f00d800b00da1082c42200c0d826030f0007520035903d840c1750b80707000c1780038000c2540c0d1503090b0901040003007101203944540d803141039002030005500c1d0381d039820100c07580c12440707010785155500c0f200c0090b0a00400001031071401d00c0789200158 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 217122580 1250 217121330 217121353
    0x301020a02150a0603030504150210180c05030102090307050904020a050a08100c05130605070629150a02030f0c0a05060130030905040209060d0e010b0307060c0b0a0b030a0c08 77
    0x10b2800e0007002c0162032407904d18180f000c00d60203002d550684058007009001c400003000c0a92504219092410b110f07130400d5041c80d1071560203102c15541610440b0b43d4169a0b844508142c240d00a43c20820340580c07190300c003001280703401c00d0031641003400980340306112502c0d00701084656209804c81d0720b02d58408110071050701140d1084402070002464914141210640412013050081c400c200c01c1103004609802404403641c0300b52012206040a400d50750b02c00010343c60080c5c00c10480c14400c41041c001d0303a01100300c1c0c400b01c07100e100159019601d00288110381510a803c00030511803148240b045241c002601000f405000e408051320600107038210520304c2c50f40802104040360140c078400306050029030854813120564004450140e222071010380450050b0250740d15251901d800c0078040100c03058190310115040105030b041e2599030b51200e0090301c0720209200c0c020301d82c3c4440400105c84401d6580f0100035030380010190b4071601d039291a0705110301021741041c0420380100b143c420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 217123830 1250 217122580 217122613
    0x306090319080402010804032f0f1b06030c0c07170604121b150e010204030c050f0604180510120c060801210615031a04111203190e0301020a02 63
    0x80000740d180c980890903140c1640000c1c50424050401002e0000c4041060058201c0e101203a004088401d20080108402c40000356203507540842c454942c000c00480b0290080b042e060a400444050005131561701c03056500c558542c80616604082e01880c04c011a06c01c100c41c9440b003d05074414002d0105003414240040c0c581c400340e03410001d0203800d0402021558502007204c41c400c0d001200c0c4498072030712980c860041e007a68440851294400030317012042003a0a1540401e40300d0544d4034080142d841401d20002d0321a0307008121214042c581040c400c055942c0000d40d0000b6010f4200880582e5020354440c42c80d851001106d04565035102400380b140d0101c4c1450041080c0c9109203500b131021038420060b0795202e140600b0103522804111005d05103103843d84000c40c0d1016045100c2d5010781e04500801a0650703080318141941c0b0401121461303c0c0743d201c03c2c94810071000d9880c040820038106071040403c60f2020a100b002920050030750f4007032000d042ea00840344c001c0d003001c040051058 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 217125080 1250 217123830 217123867
    0x904021804030806011d1c03020309030703050a0b0c1c02070807020414040b1b09091e0103080d0b040603170d0915090203010b06070302030702120f010218030d02010e06130204060503060903 83
    0x840c0784640015819000d0b5440f1141f0b1030f00c22001001060021071203080c107c0c11880380d608282d405214900000081007000103605400c240110351a040b0b40d111a103508040d841100d000040c2c0e5003540d4009024041c2c075600904034240306d940c03124030340105540070070141c55480d08103001e4000d40f101040140100161216401584041d001c104603d02c59406140360240f58041402456141c002800308141c0c0c5112441f00701e4542e400c03e4041da0340b403800810503807200810f8070100781424282100d0b810280181825660302c00812000b10070408051100380e040341811000d541d40300e420100115a07000000c80355802c60200124501c20780e40141030079155602c0e4414040d0030b0800403000031a1780407003074641c6d941d412582c0070075808c006a4640d1801c24a0940c1c89081d5200044601303680e1119141e10400082c10ba00703031012009040000c0e4201d5042595403400c0c3e0f000400081c24200d246403544041c0da10062000074055294000700e86810030483d06405640e000085032052210780c0b0084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 217126330 1250 217125080 217125107
    0x9010209310f0c0f180909150e030a110c010203040e0405010b090405031905090a05060703090317070c06022d25050f1e0112020d0903210606020c090402180403080601 73
    0x110f01c80780c82c40036a1700354a0841c456503201550f075100310400c10504910040041b04203070780c14002c4160100301d0760f460341e000132500d5000c5158160301c1214010003003040030710380e04143c003c1d5007400c0c038128506543d02c100400488a80d540e135100c4c2c00c030341c0c0d0b501e6040c00d004a001e0002103888800502e036012401714010003040038000148080c00e61030380c1d02c0c680e260540303100b03503851a1038524510301a604201d26420091207500f014030f54115029485000d400542d0180c0c0703407104180d076900c0d0113903116022402c043c1240c140e45540f985000003003e0f50010060034040403162820402000e2000002c800c240c000040d000106080041e481c03c0901d00125074022208009114540030310411001070040300941800154540242c14240990503201c03d44501442031011250a1400514407804000c240d03003132120150101d00d80b03d0f03c81c401c0d2000c2c2d56150300104011078011040000e07801c001402281d03c141c0c1c9041c41d45a00d11540f110364000d51090725401040e00b8079500141c00300204006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 217127580 1250 217126330 217126337
    0x50d0f0536060105041802060313060507080421270f06020127050c060c060a11130e10150f110c06040b070c050405090d0809010209310f0c0f 62
    0x7218045107808078403036046520407100040c46c0001d1241010340c0e1210400007035442007012040294101e201010540140d102d220b00700502d96800c90f042d11070703003003d84026000801c10360381411517800341c42d40e50b011810304d8103000d4020003201c1c80030300c004003030544002c0806011540030080c411400e41008060007150000780940700345d40c020f09100c180740c04160700c841c80300640020141310007803280d8a0900400303800c0e2036440017a4030480355119000d0300c003180164540800d00381000c00311020340700303c2d4005000b01d54800b441d1240b04041190007501088000f2020b10740000d442100000c0e20b4520000e54480401c40b80100c40050501c2c202c1007400f0360355401900301625107a407030208031f800340c505d03400f001516450725041600b14a03032550083c5412500c1c0070309108120b0800034450321410215501c41201c2d595000c0b84600745e0207071116550704181e0003140003c40b2500000310800503c090303840105402d61114800f8182c4070210b00c1806520355800501c0b151507403084841e400c07806c0608 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 217128830 1250 217127580 217127671
    0x90a0b12010e0a02010804300e0d0b130203100207050106030c0b0f0f0307020307060603030503060f0a08100b01050d0c0c1707030f1b0c030605011e0b030403050d0f05 73
    0x81c1e8242c84640183c0028100002840058200500c0003411a0a00701034501240d1100e8003500b4003030390000170000e450200707030a006412a00d03d04203d841d03c24550101410946440389a1160751401002c00700700d9050144d1000c1caa40308030588041c100e03a900510000c50003600e9414180d4006145410100000300e0400580255a8244049440b0040041c00ac941d50741e9800d40200e00310300403564000c0c04642042000420b2590120286020b144102c80072148000481c0c10400b03900110302c29004143c01074a50030345c40c07041c80d40c0b001d001c101c2d040c10090b00d05400502040115410b50301c6800120b0003043d9250300b03101c9c2d0b81c0164001c480c05152400c0c60109141c402030101181850400c0400c0071a9803101002c2080c0700603500c24650041540195036101e15100c8080c0c2401d011f403000c0a089014074611456040c2c0c2d03a1002c491800c80c50700c3c6140c60365203044030b540d8000702601e0b02c007031340300c1c000b44450150714400e4a100d60030a02d13100c3c01e0907018105d010519031401c0c030081202c0c501c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 217130080 1250 217128830 217128851
    0x7060c02010c1a09011d07050f130605090a090c06030b0f0f0102030f121b0403080304032a050a0b060603163903110d0801051e090a0b1201 61
    0x20500820094090030040d803004440c0c688a03802c405200b00b0f0405030310010301031021401c015006901c901c100d8054000c2034060b50641a030b5a1942d034881d2942c01602d0399481c44d41070400906d400781c3c5000794040880c2e081e03120710200303207000030039500e04200c80e54920320042070010028642d40602081e00d0203100030241500001d5441c143d903218240f2405000392813a00583c000c008450030b03803d068000607159103003a080044590000c69044050043c079048280c01000c10300201ca00b525441400c850030b544482d201220f00c515000000054150381c00b21000d200001c40e0848296988100e00900700075500b0f00d80141003200113401140a01d40038014004420102d005114043c0111304c3d0104104086012070030000042601586c504211081e28903011050f01702c0f224140c9010b40c80b500c07a0161107002c815618100b00340c0c88000140040f005016514080ba0103903070015007010240b118120100016017260001c4d13400c404601d0390740d9104c00c80c5090103500e0010700800300000304400841c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 217131330 1250 217130080 217130087
    0x120e0609040b011205070e010e0d170a12060f1d090c060901031103070807170103211206080303190b0607110604081b01032d02180301050c03040209090706 68
    0xd80c18540e114584402607403050340d10071803030003654140502c0280101e00300710b000078052201108007540050340c0640000a07034208603808c0c0c2441a842420800c0c6003035020000c01c030a0308106280c81c108804d1019000c10502240214000f401000300ea58003500e01c0c0100c244c403602e041040b140c603103421b2041000040c03e0701103450406414141d680395503e083c0070004800800e0140c41041600034040203020310346601444c00d07441600c05480311007103090750f0820020181c0003440000c0241824074481d440002d018003140e41200350500b04903d810f841030056605032440ca800c071900b00e034804810405d07901220b046400540100000421291080d41c012581620615070042d1841c28000c8044400c1c3e11110100c4e4028032070742c400da904042482207034290700000800c0441c0041d0801145a0001030600e00d520001c0c06602c070b0048101c0c8a0903603540194001c00b029002500d040d1418118a4a0a005940c030841c00c0b113009a03030b02d250070300c1080030304400501030745101ea10400050110540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 217132580 1250 217131330 217131337
    0x90f0a030305070207050d0803090114042111010509160b04052b050303010e01060315050d020d03020304080f0f010c09060c0602180a0305030d0b0405060109090f060e040f120e06 78
    0xc0516001c00d070340d500e198040e450300d016503100d140c102d418021b08000780502d00c405035000e0801c0800a0004544070b070030345c10556409488c054055041c07541e0140607405140801d140940990070f00740c61590350024114211101250203400d26000b41010300e900080804800b030203440500101c1381440c1c207002c00300300d890101011802503030284c44a51150761218148040c44c895002003140e5680d80c56074000700302c858081c46180080f90921800408008009502105841018211a86404550302040088070b60104e0030340035070000308000f0802c28010300c801c0c986004010000c0800130401106642110700f140060020403031502014084194000c01da450b8035608480b0142e102c240c54030300550502c04105445034001c03600c0100004019000c000707002d400701c3c442020440480d411040c4030a6500c1101c41e580000d524500034000003c06038042c20000c02070100001b1070b19181c1c00c90814051059034241d50b4221800101d0003003014000314840305c102903240001ca04444030020800502 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 217133830 1250 217132580 217132583
    0x30c220807061d0d05030a020705010806220b061303020112050103053a030618091509030c02030d051201080f060c07081309150b1207030902030708030408010f05090f0a 74
    0x10a08001203203000c503c450400400c00000c0903401210301c030b40351042e6203503c510348100c0940104240011150b002e80d00f0640702c0c0c0d00142c007420701c070011850360120036810940c0741010340d680c038030182c00300c0d4403031501401703100700c402c03c00821140c15800050b01c2c10390706201800100b030400c00144001140410032030601e02490010412550b80d401e0343d283d0400e81d5944242c501150901c0381d280ca160326800c60411210b900ca0380c00380c034000300e48141080e41d14404004c6c281135008020f07001c00e00750591010001034080e02d004d110303d080581c0081d0400c4560502c1c0740009a0118400d0051500409030a004140c02c000510301740c00404c201a49400e40185072120800f0040740d0101400030034412a06030144034091003210a40795110040245140c01c0980c0c04100035480110300e51405100b240c141e40d00024407926180e4076888200c02804190300d04a0b0540500640020045010005030029040b118008280b06458078001e00490b50f0007040b41d04070707922000e00c22242d8580420401c4100303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 217135080 1250 217133830 217133837
    0x614130e040f060906020909060414010e0a02041a09010206090703051216050f0f0c0402070804050d080912010c0f03090803070c061104090b040e0309060f130b030c22080706 76
    0x255036a080503490b062200380060815410705210f030041020710342c000c140040302299825001c2e1201400e000446501c1c19014002041e030b60018486101307007a001ca94410400b41c0c02614141d102e15901d5040d00e002041d44902440c080350b074500c190b0701802500d038072201c03000051180e07904e507850303e82d59240030001c0c2d1104030b10001080307148204201c0e41c0d601c1440d0040100c4a0724100e988032140d4034003030b8003145047d40c004c040f4803a600d4070b070900840384460303041800203042a00b01410485440004a01121183c600300056071068075031503100a41000070000008682e00c0c40702024000c003000300020320030149010306500c00134580c681607980004503031a14261a00f034034500000103281c090000801c00001140006e200180c0c1c0d0040514494291414030612001c46140341d40c81c0140708030150703c42c0d0107015040061180c000038000e2454001320007601e06a58060024050b80306941c1c2c510700c0c041c00900c210350943e0300c04d00e003881241c040c5204800c6a1518071180d803600070f24081d01040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 217136330 1250 217135080 217135109
    0x608130b0408070b070c1a091506030a0203070f140d0c060503072f1c0804030f170103030503040501150e0a0c02010902060a081017030901050304022701061413 70
    0x24001458190703524284e000e4411a07241c00c000c0b00c040c041d000b15020490f030000d40c0c00f020a1f50b1204810020740142011402800c4c61410029142400b031130041032140c240c4140c0c4903810150f501040860018820f00c00d040f00b0a5040038041e64015098904071802074420752002c1c0001100c6240000c211012481d02a450b40ca40580c102e80c00d50b04020700d02000952090310300d18911031201c180107221040001c5030b2122038112000c0070880300a107000702c0030880070000070300406c4c0214059010b14110b0b02c3c01c1c04440781c440300e9050100c00700303810503000583c010040004020303091017100140c0240b2a406d9002c54a00000c41c80b491100a10740540b080e140c010070090790f8001d4004000740355006040f00d403907007405200200701071000c44d545016580d0b05980080c01005c40c41d4003d84419014014505d0721101d500195400d9102404c12600101c914005080c5107448081002105030310991402030355140800c024041c4030071a40d0a0015201002000c07461a42d000700704080311800c01c3e05000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 217137580 1250 217136330 217136333
    0xf040506040b0a0303030506100305090606060f0d02030112020a06030e06061509120a0209060a030b010b0708090306101418010e04030207051003020c0712080315060d020f07020a0608130b04 83
    0x5031000c2c4480a82000d920803001c420103405410182c442c41d4103541851203000c0b070000850940d2802c0d5031401994211401241d00740c1030a8004140862401092a1170081043c860a04a81c0264410a040405150007400314540008440002c0a06103802d10980300900003154403082d01038000d0342304a0750050210030000702c000c25a041d801e0010108002c83c4201031410761610f1940404078800c5501200280c51450096002002c0d00e4200c40c012200368208086034049500500040d0f0b1048400d00800d01569400c100e0b45101e0102001d660010b90302e003d211007040c1821114091040740c100c0d0501d10a0440c0d0400300c0c2c115420b4003070104064480c0d0400760305200c800d802c0540c00c58040b140c5907070856050303001800c049139140c00b110402569a00003240c6040500001000f106082010074881030405000001d0800020001071408005c0c4d08403004981c4110240c07003d2010114110f001e5207080f005190040ca01400e118209107400703240c0d07000e2020743e42001030071942d01d60302250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 217138830 1250 217137580 217137589
    0x6031207151a030709050a050c04060507030c08090913020111010204080a06021308031209070602012d0b060310091103090c01140706051008010c1d0f0f130213060c020f040506 77
    0x4482e1000602690345907074495840c000544001c80305403200c1c60424003c00c54a4422600326400c4621942d01d03075040000d03981d01200d0081d0351071025910000c0620241c01079a661403141350180e103608041c803020704041e06c00903003c801d80c501c0c070b01c0450b481131004025114010074039180a82d8003400050b40d07140c00320240000014141c010084521010030826820402030480b21f00809500c07040700c10041d56140100d090311402c4110b804a149000000b0402d00c480c3c1c001384450668134400421030700616408030f02d058000703c0c6ca241018411800400c00c0c10554440d4210903108070584920b50b00c0e0500c03800740c0d039240794441907040280c40c0302d403580702200007030603604200d52007002488141003051554140e82c80c98042e07142036500c0c10710411804d900031f004050f2251284001b00030024221400c00c000c0d1548004034a80204038041d000d5074070b80d9032a001e120070300c40d140300c0161200007142d1418a41c00d0541c01a805220070411198056500c3d000c0c040c0074550105c030045890380d079000206 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 217140080 1250 217138830 217138871
    0x50706050a020a200111060105060a050c0f060403020610140303090d05030408070f180b0a05090a060e040b010f1d0a02030c0c01090b0402032e0504050a080a080603120715 75
    0x80c103e0f220b94510302021484d030300034484a000c0f003669201c18030306046d8422503c4410038071842d43c3c098020000d0a100c54042d5002c0e15003072041c0360684114004040b050b0303082190803101180180c219008000c81d040e4181a50b030090700c2c3c045101c0a0100c00329000c80d5a038469100340d00e1007000582000c0c820844c041080ba0045c021100941c1d4069503031f05141c1a13418418011686001c4002c0040e65400d50385100794030001500a1401d0509480c1005000e800b550150031070501c1c03602c1e040c01091044a0316155801b492084110b44429854105050310003002a0400c0c0c005078114600046103a0701e14039065001a5003501c010381d252512801000340340b244010040f519400c06800e8001d02c090000d00601c11741c02641070714640c400148076209403e1201d5102007042445068200c3c082c50039171303c0b0329407051043c01101c46030615030f142e4007681d401140c01480059070140030040c20303080c1031080d550301c40c8004045c3c81c1811440d9566501c0c01d1103020410784090ba64035003007200065a85400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 217141330 1250 217140080 217140083
    0x1104060807060512010608061f050906070c05040e060c0a110703020a0602060703060806160e04110f041d04030e0f0d02090915090f070618090507031413050706050a020a 74
    0x1c48481a42e10300002c0c1440d082080214031219081c400040c10034000c000792845004000c11f8281284e102031803c00002c0c0c0c40c0d00000f410003d042c0007220940c1c50707402c000c04c5070300c0c0510180100c0d0351400040105a070142d15081280f6003014080c0b1002c08140b20944007802e80a060034803c0c071030340c80c0c8424a0007030164000b95125184410000c0c000c3c0e00499001c1c003803500c40e90184503054541e002c05940d00300650b903542d503100c402403408484521411828100440080c408a02d40b0a4500b0640741da40099080303440e1808002002c20150900381415801400780f4801116117242c00d031070180007140d6025440e400703280b10fa10140080d40c1e5100005201e654000c0c0030065a007031411841d0b40e10088c0700c14100461400e0390201f4042c05000441c803400c0a0201c2c0101072031402d0020440308450b94190340380340422600c0d00860040c8550195521034044c0d99000581080350710340d00b00a45034060010420541091305060204402146a0060f2651030502554071182d035001240340007500c160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 217142580 1250 217141330 217141333
    0xe120d0f060f032a0b0702030610081c02031606020909070201050c1c090609051c1803121b1109071809020c0c09040f0b060108070801050418020301091212020705060411040608 77
    0x3000b02d21713a01604041c0000c03038001c3d003c035045591850b00100081700b25000c1d8a0907940300107141c42e00b004c069281d88142c5075851050740d050080001030814141c5080c1411901981c0105002d0303064140000e103564410002e20007802503042c6600001044d1064440701444000b80c0b15101841003c907802a800032588018100003050725410006d485e03a411070400180c805d40e280c0382403641c6208500c000c00740208106003580051856a071254843c041901500034402004808642c0c82c00905801900c0da025041020190b601c08040004202000b0821024402200320b6822088000340045080c0c1d00200e100590720120a0350301c900e0004103c41c1280c2c807503d803808000421140d01003000f5028858405603501e80c84881c01035036140d01c111100c60008a201d4010041850f05822010400441c0c030b46920742e1074602d030040703825201405400d40b181c9941d5501f100b545503000c1c02c1001c2800600d441182041603079a64a42c941e000a0000b400801100c080e075006030f40c45502060042c400f440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 217143830 1250 217142580 217142663
    0x60c0c050d0b040605060d0213021605070603020409060501030606020d080405010b1309020406050d03050a030b061306210b0d02090a0b06070b01061b110907030e120d0f060f03 77
    0x5084100b11504881c2114a682043d0120702241001204400829402841e0581e0130a4540f0900e00a4011403042c8844020f40c81610700400c1003884800d0140c504e075a400b503030300ca0401404500741c2c1c01690100f030401d45003e40400590b81d011808408a54151400440c5901e55003891703405822104042d40e404000c881e80060a060701d0790254030341c10b00c01c2d40d00340102961101001a00021104060f011520030428203d40d62310a900c102e013942401001982401494100b13080e05114070f40003140031410348200f13a0000180d951840c1281d2101707280c1404413081e41c001043e176072580c03c1002805445208040b079031851b016041411140c10140c20943c0301c41540c01d00408200c1d0a01c20503010880ca0301c0120740089a510320382c100d03150050707404c051389400c000c107104000b2030040c812020580d44800c80e0900c0e4000f4400240c0d6041c03400400c9854801c0c107150102188d440c1c400f9001010310b00b180812040c18a0240c0c4401c40740c02503104400d0707c601d0b1400164060140b4ac501c8001e90740803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 217145080 1250 217143830 217143833
    0x403021014030903090a0b21040c08100518070308220504020a030c320c01020d09030f020f011b0503040c081609140907050f010c0b190c0f09060c0c050d 67
    0x5071014050032102003100b02d5640c090a2800e1090300190402ca40423425505500d511900000b50014440c1c20313800c1d151503031001c226091803007100d000e0b0b12140c0c45400340f10032492041d10501e40031420740d0151200d145996564450b9203e02c52854690240020081c00f80151a8821100408000d402036654010b041c04c0140200003d03000580429107020701ca21104600e028050042d001c1020007150001c0700d020709004581006a20f044d040d03408201c07031856501980a01020b061098503040c0c07001c5405100070b0704122481c01106007a030300d0311180905207960700c040c1c025a40d505003003031580c03502c840c10580d0f000405a0018169481118522508030401002c05002c0b1180c0f55400c112030401ea65140c10340400981d01c4560ba035000c008140305610340447c0019240a050505c0e001c100541d0341c030b5153750001290400e06d1913861440c2c0030044e401c80e000c1d100000000c0d2030000551a0142d40182c6100041e02480c000c01c0a030502e8242040186120301001d4200208040c0000d10b59 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 217146330 1250 217145080 217145083
    0x6030a0c0809061e0a06051201140a0c0915050c0f100b0609010203030609060a0f03050c040e03040302150a0302120a05090f0105060607030507050118140606011404030210140309 78
    0xa00500001490000c0003414055011030a0f034029840011804d0012546501e1800e28081c040c114150450f6650b02c00203580d50342c03100c244c47c084542d074004203da084e60550101481c1004000d00364107800c080b020302e002c80d8064030140a80d000c80b0081c1025540c1e1031400c5500f80900c0c24040d225118110f40042c4d085000a1040c0301101c0d116002d01c501030f000014012140034a01100d40036a00a20104d1403c0ca009410381b0b511800242c0100917090340d40001004501e0980e00a480c0364100c54100c0315607003454054080d8140300d40d0001d43c98a072070744d4042200b04802c4203035801188130120380c2d1a0761a11035012110518054080041d4600703140304030500a25003503038003001a1040e407112078040c0ba0103006281c4200d20040c807850604001d40c406440360350011500302c5980d542c1d0300800c241603051898a000040c043c44481d004e485100107107510f00700024103468140b00840603903841003c0e4040c2200c2c02d803a4103840910401c0f202d0601076506000d42030207440c1d0780c6808010800f08880 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 217147580 1250 217146330 217146341
    0x1e031609060815040605090c060a030b01020106120206070201110307051b0907092405040b0c070e0a02091c03020f0d050a0207061b0305071506090203060f0616030e040b06030a 77
    0xd280010000c403559818941c2eaa2181c1098802212000900040100d001036004a9000401506030f826414100d400101c1c99030001e400200401d95920704000d0a590903c999805409030f04c0c1c07011210980303900080c0c943d01401d100241003140f03d55045040140c14002d8400c41a404000c40310144000123189150300001d807541801490644c0000314118807032076429080b59100320181200d4480e508030b45003803542d299001d10602c401004002010440d200c014120100044040d0410b50b0810240901c510f03009416651400e005103d19052a07a03944100c0e0005501d040307541021555901d416420f11241d011031481601070901c1e01c806058000000f440091140c3d030a840f141900c841003900d200c00c8a01c80140d0710340c044200000028000c800800000340103907280152104031100c000d040e034185402100000e41c001c01404803d040c00c08440e1881e140c112a4182031a00111403c450b0700e001b44c401404200c0d500e1808555a241c59000000c0181c1c040d0020f5a203160a101c0c010141c403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 217148830 1250 217147580 217147589
    0x90318030501140c1206090711030c0c011e05030606090f090f070807090f1401180801061404020406051e09040e0f10050601050f0c1009050d090506030c07021e0316 72
    0x24100001d01c0c0715442004441d24000e500c80040000d8407040c0500a07c1c01005080c0410b00070021500110418208058003061102c00000c2502d00d0010000500746103800d20082101030424240500c00754111007500d07803091f01a01d0603515101c0040001e00050780b14030515800912003018040358040c0c4151503403103002d8030f8880a101e611040c804503129981031051038410840e6507014003107401d07402d48824111205240c04030544001c01031035070004200394071210050b07550304020404c03000f5220307a4020040c4101c504508040c41c10f00040d242d4480c41840c4007101d00480d44000350440e4140c2560b044131030183c030070400201da405505036980e2803407500040510440c80380c0c9001084a005480c4200c0301a51054249590f000c0401c9150300b00143c010240d000701e40140381c10043c18410000f0490040c00181a01c02c10700402401610030f42e0400b6000300030030410020896800700c22104181c0e41590040d0b841c502c1d08800c64550000000302030380c0750240301c50706c80400c03440104d540c0c20368 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 217150080 1250 217148830 217148861
    0x40e0403080f010510080406020909160e0604030c05011b14160503010903050f07030504050d080306130e0c0f150a0314010b0901080f090f0a0b01060e090613090318030501 75
    0xc1c2c0354241d20300d5507000b00b44140340c0e024004c0c2481c8007a162007681c0c510b4200d4812880581000f02c1840000c0d2a81001c84a0700c44102d480f0810f00507041e800180721320051015a0b68500d8507055895270041c0d403640b80515414060607003606544240144000e459030368006e0300c1030001100210324161104100a82e25500408000f004129468103110f24241d180c2c0c1900c80f103103401c1e1510031056180d0402e000550a22070240000140c0707441d49401501c08034810090f5555a00d851402c015030110b0205060407018504108041210400039402d4550a001c0b03401d00d070412060380c001444150010f0070100003520103d43c0c01c8101d901904140d0034029600e1026905a8031004000e48030300424500a000402e400017041d8010907010115400040c08415100740c0c0c032420802502e0011103100481c0c1c0c20541c10010068039030b001040c55074401003221004040e09003400011310140401010303001c015610b01c03040301014010794041514160b00300231450003507680d0030f103c2d0007040d100d03805129030b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 217151330 1250 217150080 217150097
    0x1503100b09071125061202160f15020c0a12260a06081f0c1e03051305030a0c03030e070b0304080a020f060405010905010501050f010804120908010212041103060601090b0904020f040e0403 82
    0x11b0090081d01e81509800071030f0003903901c081c0c40b04c1d4828110080281c41c42420310340d012103156494001840240032400040c55107420b140f030110103a8072402036410802219101c005070641c0c201100180416142c6030200d40b40d22103001190080101b680000e03114490024a00100385000c1105a248415280100680aa410016144070b42048918018100020701100e011030203640b00a801c42d03614603c0740d004581c2d0b0340c0d6680c41d513030003021a503021074441d010401c10507625000e420315100c0000040d240ba5440e01003900c00500018000501001010580c02c01f01c80c82001800e1845040b002100c200d0306203030602d01e00030510320009591550030100040b41c58104007003860160141a501c100a55846031100c0940200150328202002000c140000b80e514090019101d80307030b14110b0018250500785002c0d00010000740c503290094000a0400046030781101c610000c039848c3c03002c80303075462841c071002174024030943d056080c401c5400300d8003141e10b5004a00c214441e603c01d4a03480e10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 217152580 1250 217151330 217151357
    0xc1005160906140304080405040c0201091106191d151b01020a0e12010902040f0b040f050606070f0615030b09010b03070f120809091503100b0907112506 67
    0x403200014080c0d140412034031468508150f04a1004651250013030502d54103142e240c500080c00e03941605d04010041c1c5d10f03640307a0340510600030912010b02004540240c50048034800317590b01c40304200582c41c148014491f440441e400072030000424a0401451008a07107103c0100c54581d420588035141c03c3c01e100c0da610204030720144221061103da585541c00c070142c202c4c0410a80d640880390b20a5155250310000300161101e000300b1140000003580410341c0c075170316020b000441c0d40b000284080d49080a0901c150350303c520007110b01c000d4111058141091f854180340020789a80201500d8505201c0800414030a86100030742c000c5012a0003403200c51150802c040d0786090360300905141d2034016030704110710b40c20982c003104d0061207408403908114900d030004295500031038082e030ba1180c03200c103d503040b40b905001c40350001841541c01c100600000005c500d0000d0000c000c0c00074002803c400c3d5034a00030420403d065082900070741ca0148140c2d502e078040c030000b5407140e1004141700464899 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 217153830 1250 217152580 217152587
    0x80a0207020a050d061b020c1504420503060108090c090106120b030a0609060b09010303090504090f06050a0605101b0b0a15080312070504030503090405070201020c100516 75
    0xc06198004194440380c03800c0104025400851250466880d5078030b140700c034446002104020380455003a000741ca1410802c200b0302414590741070314508002c0c4c0400040c04070f003166180c0c8529440d107105441280507405c041c1c0c070b245807030080640fa41841000b50322011141d8000300440c82110213036542100c030b44075822030030b40d503d6494085550040c280001400314620a01402c02e488080c15030200b9070803040c4005c40e080522405060705d6032174035180c444041c41454003d891000b107007618161030542c51514000c02000c014056684119110395980d802e10950b401c82d5007a168100c07100f00302c40e0400e02c1010b0010325040c805c0303501503005404002c8000307002d041d06401041890140113040b500035a140c40203039000511300c2040541c1c52a0b401810711001030300b60051b10038440110b0f0345886d40b0280245484c002815903007084000c000510001d80c02005445140f08141d40206158443c0170003640a030003840d040d40c400e407080c281074400c94030070303608071502a01020b211260103002d01c92088 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 217155080 1250 217153830 217153837
    0x60b03040302030d09020103020417060f090712060e010609020409090b0606190e03190b0103151a0f03210a1710031e020d060b010f0c0c09020901180b0a080a02 70
    0x203400b50304103000e0000b1040c0c541c2c104030400d40c4145001072801351036503004800c0064500700e0004681c003000400800401c5182102d0700804918014080e0398989041e29003c0290040010840d07921803000e40d480010940000340a841c0b603582c00d5484a0300ca101c020000c140031241651400d640d0004107405041400403110300c05012492503003c1c0c4a10401a60ba00242c0c60a582d0148103002040030482081c030240703038410303114800306812035140d414001e46a9010803041524546048501050b071030380000e02d000f00500564880c1c101c010760200090601c600340d440c10400b803020403e0307900340c0c80942e03004006098050701e171030310507580301040d00c650720030708482542d005420804c00b80089804074028082e030240403924a03200c6400b59011440c032480041d0115810f41e2101e000e00055a00551001001c04a600d80141c502c0810340307903003500ca42c0c40d102e80180650f00141100d490f0740300c0d408004607103600e030311140800b03070303982c40740e44804e83c40348000a0004071003a0105860b081c132030089 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 217156330 1250 217155080 217155083
    0x101b150f0b041b050f04031a040209010801060f05040c0e1905190b030a02161a1b13060f0e0604080627030f180409050f0706092106110f04030204060b0304 68
    0x46112040d54220141c0d2185c0c80f495099803248800d010010003d402255007981c0d00d5041e00008400d41414418415911010303002005140d040c40014401340b10044543d408443c400c89000c12032031030040050301c03084010741c01540c00840c4030014903101582030720010220f60701600c2d030003110611204070b40b01003001809000c043c8141080400c10350010f9070083e1191786403603c0c1300c112a105958400010b05258410241c90710a60020031020080a00c2d008100b510440112840c1204104080041942a0217484107200e501e460400c2502c1c480c0300c144c40a404d000d008144d135651240b00e0341e69140c0c2c0c2200c503408294040804848008000d51811840b9440180254100500082c000e011a0408400c00160388009041201c107a03459002c1c1038031445c000c501400d41108420005805d0001030303006032003800008142040b94000c451800742101401d2541d4003078000c050718005001d009011000e000398000885c850070f41c07160170802013080701d1003250108841a0750760003001580c00203c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 217157580 1250 217156330 217156361
    0x20109061404090218060d0501030b0708010503101d12120709030218062707030f02031005040e0307020612070e0d08040909030903140102091e101b150f0b04 69
    0x1000703184040c0d00500488500c034000c1070021031801001c030746c036034000000701e895aa8440e0700400c1070044a00301d1607000301151070070ba6442e40c10708001c01d54540403d00031400203607a64120008440c2503081354129866148159032205042034006181504a83c0c90016800d2100020a41441c010890303003084031f501508074802c0e01a44658401c6005000b05020341080702c0c40b90041700704208080c003882d82040380115910504001000a084401580080d800c2e1441042800203804c0442243e004890f012100803503e004c00101c0c050950050b010002e40005000c100b2400540313100c81e203180304102550b5051a41640d910402102e0b10299a010b00100800c00040c010001c00c2e81240c400036019041001c0001d55030703039405a031001c4604903a2916507011813228014a410710103d41182414100240c002c002d0200040c421003040ba001b005100c03c0360160355400300c1030400f102c002908a501d25050800304200c2e84080c04013020000034241c41c15000c068945000d00c20300d0190402c490 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 217158830 1250 217157580 217157587
    0x60e0403020d0804150612030305070f050f0f0903030f030f0f0f0c0f21070e0415090b18090105060a060503100e07030204080303040f0308010503150c03061c0b040201090614 76
    0xc2c1c281c4203503101600a4071400b9110180d11800c0c6414010302c8000e01c0d80d5958890740b04404d00b00101200c80103443d242c100300d02081c0c0700d90903903071040643c0c1c460510051101d40d10381da81d40000368039116034003446405003c0451211001010403000c0e40c41489055522043c0d65100b14160348040421541031140d1500c0c10f02141000340c2a00c090324401040112007450001c2c4c40c198003440d00c51260441041010803c1003081c1190310118800b00307a807007a5418449a4051510306541204e00d000b40140d40d03903140310006050f56501c035044881704000200038864107041c28038601070501110954006c40d20580c0c0001c025100e942104c1c82200101110f00d1107d0804070b5401c00e141d000340040741059000d001c081565038042c001180100c2c4625035408507400c162601610785041680054465005002c16030381c2c6108020703440b03600103c0c86154951740e603550170000c0c4840300f00000207107082c1244070f104002c0081c00240140694002d80b1802e625544d210303030841d055404407072081c040980a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 217160080 1250 217158830 217158853
    0x1a180307030302030a0b0d0b0103170702130e030417071409060d020108041113060812041a030a1404060506031606170a0f0e031c050601090b18041e060e040302 70
    0x283c3c05190003a0412202043c941c21180c0010000c00a80c0400e40c0e00f120f00000410030088003441e911040c0504540a50402c0c005400180034285140660442d03070703843d10f1021008500074401c58000d0701c241d00784c40140483c081c1410341d40741a10700414192000307a20081101d0324200c2c1d000c134403031403006000d61706000103a401115984400380044840f1200c0d50783c1c0040303e698040c200000f440c49450700082c07042c90220164600503200106410507141000300780807003c00e1480c4c4d04078440650480d1b65681e01d40c2d2010000821003040000301c400301c0c0d070050208004040e00418010002102110490703081e0045010190495208005c08985540c1c080034103029400b080c140d100c4074031800001c001c04208a610705031440c0641400442d00009074041800c0e21800c0024022000608200132a103002d1001910900e8603000f205454280420a038815210b040d884c1102d0308006001400707401c42000980d0b5400600360b20340ca400e82d042200108030070801e40d48030351055800d0750041107401e180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 217161330 1250 217160080 217160087
    0x60103021213051c0f030b120a0b180709050f0f2811041d07080405060601032a09050a08060c07020409021903050a1202060f041e0f1a18030703 63
    0x7042d4119160b004056040c1001c1d104a00d041c0c0300381a0940300c01c2c246a071880401012101458041e40c0b00321810a602041d5000025003101c29680c4030780c51025580b500c3c01c0f000c3c0088540b1700d0545642c400c140c1c000c50503c0706500114050080a544164070740c4415074030f14850b010440c1c024078024048890500e0a03d6809800b010b0031074a00b400158068038110100580e0344250410500301317549031184640c00d0030b01843c00303034400c1d03c914107041d00782805d685850329a0320180c5600c0c101a1104600c01d131141e004554047c01400c0f00b2150b0610041c0b501e0060704440d2144600c9109204603e0001001b14004c0340039031103140e4409248e442c0007070036800c00000308004c65059070440410f100800ea5a01145440006540184000c0104006038600020068844406241107400004c148030000c2e0344942610b400c180d12415084015280144100080310481000b45c9034400441182082c02060120f510500315010b075441603a0b6183c0c807668100300d88101502040794010050b20b408a4803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 217162580 1250 217161330 217161361
    0x1005060105040b070f0311030319091a04030908011a09040204091412030604050c1602014b020c01020d120b10030509060a0b0a090906020903120a080601030212 70
    0x814180581401c0d100c1c44404156008044200c03900142a55601c06240d00043c44d14091260f00c001140355203040c10701c1110341e01030350b074050101c9500c0b0b00d02d101c10080c070200d5a5400385840001c81900317241034100103007030038001e00ca03840d595464080080014840c403800c500c4007041c06031400c0b00c20f88803a42400001d008080d0140c03000d86082e11105034403141030214074a00c0b0000c2d581d0945a05244040004a82001d081183c074000204034102c000248044003489882d0242080c10251154010385044c00c100c07511141020780b031a000e032003c0b0741000841c0140c40d00e40c91001500d98145d429081ea84d804a52000901581c4044829010b0314450094140d00034413041d404240d10150340041141c20780c0032943c1e9400b00c2e40350703001c100900800700101365200c410040144180c1d081e500116421401c540a4090f17402c0e210b6005005020944d0120748100c00d001d011a100080103061040194200c1c003640400a08a400450f0017980f090086c0c500a40070f0764046d071065100c0e40040c680810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 217163830 1250 217162580 217162591
    0x903040e0910141b040e0402060c16080109050c06040b1909080114040209250c080c0601080606030d030b010212070201020a05070b0405040c090311100903080403061406010807021005 80
    0xc10282d00a409030500c0c002d91401141c1c0d040002d6450508030b90613103403400103003003080c068401070004200c03520840e41210740282d01594810313a980c42c83c41c1c0990401009100466203404100b10019802e6030550001000034007032016a80d10802c4041004140d108612441d40074481c20700c00b501940c1d401c101540c0c4840d6083c10102021940c03483d681d425a00a4418428149684e07400c00040d41080095660721045811040c8010040d40e24080c41034104095450100403a0030000d42c00c01001c182100c420704020012203144c0d41e55148840d03a41d42d401c841482c000c2c041c61b41c903025550300034010580b542105030064608021000400380c1103800c5600140d0461042c1c0d1b00c00b8000c80c400340303c903c0280504d0303a050f0360741c2d0307080005000561f1030242c0400104840c51070200085800c0c811a05034805080704c51524024400e9400c844464140d04003a010080000b8000104030302e030b90060542c03500300801509140c4d1158015149900b0031a008405600043d14074440061b403070f0311895024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 217165080 1250 217163830 217163833
    0x6040807020922080d0501080d0909020a1704060609142202220b030f0c0d11030c090a05151e0d0501020c030a0c0507050a030201091404020f0a02240903040e09 70
    0x841001030408002c0811990907150810002101e113024405d50003050302400303a5100400c800600b030440108420482d200c3c1503042c590104051009920626500c95818090200d880a50400b814070300020402c83c0300d0398903500c0c03610344800b00c2101c16130f030401d100b00c40001d410320042421000c0e0002000ba900d2040b0f074468980c4004800001c120303509580f04e60f4215400040c404a0f80d01414504000340d0740ca001c03180c1c4500208190fa50b180710480e04407a81c000301c0f4124801e44907000c64a000150710041e94002e147c1c0040100c00341c07043d0b10503442049600440781800600c1d0301840203040c901d0030740325140c1f0310410a0b9462418020b500212079440b4000052034210b140c049541590080640c6500149810380d10005000c0200b0141c4040c020465503a510390346550f0000e0030803c81e900c11072404034501404480c0c0c940c7c690341964502e02c84148130941d1410305580080d21032841d0041e1030f00505003510113464400303003020658410100840114541424030400306103e100007042080385 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 217166330 1250 217165080 217165111
    0x190b01140315010305010c0909020c1b180106050d150e06061c18060f06060e0d0f02090a0209090907180209030a120809071e050d111504050111060408070209 69
    0x10000203051143c000c50003100001005050080b000b03084c0365481d48188406130052007400d45000011441c9400101614143d0700c040e00f05101240000040104e513140400e0f1079000020416000002081161001c1504010344040541d541c03005400764005c3c1703040700002000007066402c10304018107040c00e0850140701c01c51080c40c600025201c40001c140d440d826010200800c000d880d006251541000120500400741445030082c00d146400110b0761003642d03665640c409014091007502802c54004c2c140c079040307107007000b4485c010394840000c00d070050a07010002001d0500201d102d605403050284c0091300043c0003d04580a50400344005516000f4000e42000146181b00412050035554403140c00320700d01090318034101862944010301d1509000190b1031103030000c0f0f2a500555000b25070035400032600e030600c401c1900d10150030075004403850b5071036280d100103540a0022203000341e80e1070006050307402e00607441e00400d6400500c18081408100010b19000d540d607035124a03500d500c50307034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 217167580 1250 217166330 217166353
    0x50a030b061c0c0e0117040201050703090e07020d0e061602060c03040906080a050601151202031b0d240302090c0903030f03040602030906070509030303150109080106030c08190b011403 81
    0x648100002d01e6105030b0b07512001ca03c961034200004102e505801d00302600381d185036203158a2034180052000b41003200006150040500070300c51100502600d80b100c6c8420b01d0038840103981d87c8242449880071850007800d19a503440d0110840350303051790007003a030120090180e0a020a0380c011015446007400188404a5500ca982c480c2d40d00620600004000048160500304d00b410340c181c029000c079189000900c3c001d1781d0000400f40e100d0205850040c3e0325656200083c40002d112100d802da84000082d11285050468001166003041240c030310190f00300040e91000300140602c002034100c1031500016401c002904060003803100f01a090700d1601c4045080303c17805900842e000c80704140d004c41070041d500e400b0405a540451141805440c0007810743c0040c1c0e480c0001404401e55202002d400e02661344a600d081d030041070464000e010b0582c40c2e142070345007003980303018004d214815070314001d0f5500b4841d541c142015401c0920301d14140d0900007107000140c0c6148840e505071044d641842d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 217168830 1250 217167580 217167607
    0x30d0f0617030d050a061d04020f0907050c010515010c11030124080f0109030c0f020d0b0109020d0b040c0509060f0919090c0e1c1a070924050a030b06 66
    0x1000041d040c06540e540440c902c914040303801c06000f000d1818542141070060070b40c0b0705000c0d80104140c0c41c0311a0b695456200040403d002841c02c6a008000340b014003420a070000082d205018010b0024005c0c0d99034501d000c000030403120f81d21030014611003181000700326100302000d2407020207000810083c0e45507100e19400d000b011000501e082004408014030042400314200103000000244110700690b00e00400c05009880c028041d0301c03110015400f199203101035002030a41c48041d0440c1503a48001d007800039045030821240080c20048804454646803159a20f486c503980c450504060325601840070700c1e000382c110602c810008102034802d035910303014030b040114140c01031500400c1c20221008280c81d000000001071003804480000f0a544000032085401030301c84a43c61494564201000d0780307503401e41d000501c50036990900c00030940c40492441607481802d120208040980d6103c1420728002c54040e0000d00d0601000f94414440e03040380b40d02c000700401c2203003403903034004041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 217170080 1250 217168830 217168859
    0x70b1303051506010906020105071706040f0e03090301060f03080d091407120606060302030f0c0319230112080d0b0a0302040f0b0103060906032303070804060c030905040608030d0f06 80
    0x40b620340082000074079a0303c150391101030407844c4001d0240f410038a10150440741102ca8180c9012003040c005001c64a90b41c2c04141c10250841d4244000d40c1c40c0e2840503240d030305c0005054025400c0483c04229941a001d450003101d92240c01e403483c00c1c040c45000d100a040000045034507a410680304481d0320820000070003d000354542140c07880f200e41c548101102d820340d020506143c014001c1255500b0a0400c0740d03400840b64010b6903030b0b5562400f41410084d07440c903180301c880e45020752001103441e0f00400d001c002ca56141d800181030362102d26003616204035001c010122401000180b81c005501e802003100c0c50000f81030b1040343c54496000405842d816185e4001d5190b40d40082160b075a45401444003c041c0c21604128a42c01c6448076401d262800001c0c040c2e1402031480f4401303c0c84100304448049400ac1c0300b841c2c80c0c2c1d44585000f00002c140300d50540000fa0b24010200341ca203030901c201e40899000030700451a200400d1100c070302803c54201407484017591648005a40f81100103903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 217171330 1250 217170080 217170103
    0x90414060903120f0105010f0309080f041202130e06041e020a080d030c030b01020a0602030c090a0b121e07030506121c1116050112020405040f020403061d070b130305 73
    0x9141c5500301000c00a1500300700400108201e0390a130010001641c006803402880f1038245408107651006080c03800d100c1c415804e40e10007145000400041c03103807509043ea0040c51003222001c102d1b00740581010141c803843c3e030600b0203d80082c0b001c078001602d42840342000510046076903a1000c020380008514941d1507005904940040701c6040000b179041c0700e8001041c1c0300f41402c0080002e00b1000070343d038035986407005110590001c0414682c1050200b50b913500d40c001007a11a807251180c5100f1000c0d0403162142d0b5416a100d400305024120305004000850721042202c3da0940d26204200d002c0e107800781580740c22101d194038032440c1c00c00601c01c03014850300340e01c0d50a441219021005040d06190001144a41c00504881c11744150b0340000300308071a402d19088407202c00181e00d6000034440d82d804590b20900d005504400340c49217402038011680034820810410700e0040762540062100011071031190403850090280340310b80809094521200c0d281c13a02d010384c9a96131103107010a040c84 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 217172580 1250 217171330 217171333
    0xe0d050a020609070e0a0c05091f0207120b0402060a171510090f03030305092820030706120e10060321050901050702060903060f060406050604080703020904140609 72
    0x1120310000da0100801c81c0c0100c5584001c0a1242c0703015000c500c550030250000c0041a00c80e8a450242c91041c02650801100182420100003001d40c2e960070104203540804098011040e00041c0500d50b0402e0110f030719002800310302c19681c2c1d03a08005581e4001007401d8207001b0300005800720005c40c40e420314441c624142c90614002c0d086010048040e1650581701c040000c6000c081c0300d14100039004800712503240c103011505840c1d540e01c107400c240c411000c098a00e24108403002c0300d4000c400810389040c0c00385400d241c00090384000c0c0c40c90132014007000c0d80c240d40942000c221840c803402c101300b191070480000043c2440049001400c12200100d460b0640b5203980c414810702c030b5140c25256103c202884440a0308070aa00c02405500a550445051000c08286102591a10720454550220080c16287c041c90000419011400c0c00e8031128088d5140000220b12401e0105c1100e041d191300d40006c080b007610b55400c000ca50603006000311040d0342c05441480c0200000c01c1340a004019250 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 217173830 1250 217172580 217172587
    0x17064b0f010305010b040915090311060a0f1802010f0f0201270c090e1902130e01020c010b06041421030f120702070e060111070e0901061d090717010e0d05 68
    0x903c1c41c00e60b440c000301a44a82c2c030304a101000501400200340101c0d51081002c100c8070003504058949030300680c4582868041d440c1000641c07121035000040c848403030401048212801d4031030307420291215100030b020075144034406494030302405030070030540c0c002e2002050801c002484000c0310080000c410000100c0050a0707410000707070105e980b000d050302d440c08004a98040d4442580e440c4000030f644091221085c825085d501e900c2a505614031023020103014044900400f58000d5124160b111482d51900c00c03100820318240f011642160491740b10741c00b00c03070104c1d810003805184607003446804120b4111099203c41c418409092a1200d00300300c1512160b140750440481c000091007401190010001401a2282c4403401600304d0070a2030300e000710150307074401c19242c1a0303180c0200d1540c1c54060f0802c02d0180701500306000b55101c10000100c03840c0100c0004005400542e08000b06411510050004000001030608424510f90001c9505401c0100b81414254012402c1c0b00140c03001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 217175080 1250 217173830 217173833
    0x10513090c0b0f1206030a03090512010912080708060a060917010e070608070f030207080406050a11011d15010b041703040e07030501060e060c0c130e0717064b0f0103 73
    0x104c04254800015000f03042140740b650f400030200ca1090065038032401452480d03540d03480c02503004a80310755100c5c2d281078401001b900040c010840c202c03062000250080009001c9091204002003107581c10b48410b000c0f942010300c1c00200312104118024250359540c28403021200c101311040040c031607501c480b902d60a103c140100540800d010354020703d8010001c050000e221782e42281e0448215140a03510b039150604100c031200d025070503c0015608200600340c5c6a4001c1c003000300c020725035a0460742c4102d8074003541e4a100809100701810500c041c4001c209000c0848602c0740300c00c0078101540e240c281c82e04120f0040030001eaa0b031100180d070711401070061b56001594411030020850700c5c00c0c14400c465a00135034810300310200c03030b00456103900e100c0c05450441c0c0007050720b8003100060368074bc0c40e01e9500d0444a5401f07055484024419035000c00c800401c0c000c01e050b002d5501b8280240450b0740344181d1589803c0840400090320241c0d90281790612a100406000714103050600f141949035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 217176330 1250 217175080 217175107
    0x311030a020d0606020613110a17010e07080d0203070b10180608120906090415050301110c010515090f090a0c0e0a06060201020a05070201110106050303070f0b0a05010513090c0b0f 79
    0x2982007101550302550601807100382c00300d070300c1d544223903c11440090300c0a101c0c00325804844950021a01c000a140581c13130554040d044003148080b1401103c034000d644020040c3c1c0c409103500d004016070010000940451341604000d40d00034414074481c0019640d03031003800950005510b040c1c001a03607400b000c1c40031420921203090b00040d0908150300f0301c850900054040d00c0340c0781a003882031f170751092001c00c0c1c041c009222500034070b00100200301c048d001c80d0f10f5903010752090345200425442c000000b5130f10803a0359200088044007078140071a076541c903007910b04880e00140c8188117a200d07501c0640002500ca600e054041c00c281c006e412458100880c4031000e0355004e80201f001d6900600007081e12640c810180c03049244c0918013601c054050882c150f00400d0755802c01c6e50980130002e5544c1c18000390308110304d00d1901c131307102684250351200f0340385080796001e01446a210700e0003003007080c04c00304680000314581e002d111021016030780c840c004101c03079012104228842d0740104415802d002c0e03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 217177580 1250 217176330 217176341
    0x1b080906070906090e060120010905060109090503160807050703061b020d08060f01030e010c0206040318050306040b040614010e100b040f06180e010b030609090109050615010311030a020d 82
    0x3614100b00d00840d04120300a8081901c1e80103c3c400b00340c5000019205a1092129001c8040c0080d494882407481070b00c0e5601801d45080242c2d05032054100024022000d07210741061544c02c10007840c2031200b503058880c00301c02d0021007951400303414413100002c20810701919005512030400050050310509046a00c80032921810040d50481c180100600340c0000d45294031020403195120203032000300040c1d00030440b42d941d8002ca58a8040c440c00c050380c0000e205400766000b51208170040640d013980d1b0741e0581d0703d03010307040e0140c00a20100c4c0001e213032004c0e02d940040c403900c40030480c41452401c0d140280001d130f2104040c1c9408405004502031500340c400c02901055060f285450b00340040140452400e01c00c020800c02c0d600c51030042c203034a003d49040a400019004031041d659161a06a240c1050311400e106000c8038021035000d14052041d0040194000302502c100d55426034110070381d010046510341407503100c0750611010400040214441c0582c01001078030b03011941d080500b00c2c0c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 217178830 1250 217177580 217177591
    0x2212d0a140a12150911030117030403030c06050403050f131a0a0e21030c0a110103050403020c1e0a09051e060306011205100f09030e01020706120b041b080906 70
    0x40c08000c2d81c9071895101108907034408142801003102c0403414102d440c440030380d61205804628000312052845c20400c000c42c12a00350b05940c05c00002c2c1040640c1d1248940e100040c081040450f12100041c59a0080c542c401d000c1d080540c2130030313038100480840c1d0340720f602c11100401120400b03024164850710a00c0035503c2e10b054060816014000280901d084589510301c58a0450003085000400f032421240c3c01400d401603c0c0c407081d1483d060303640c400c80120121010801c1100158965202c1e2041910503074055000707005d0500f442081c4000c0b805c045180a81e404203481040c907054071840c1420004240380c91000455151901c521064600d0016040801a144a003401659a0000303800d83c151030740324030500c1c400c02c107604d0b000d40341a0114041224003400c08082500c142116446826618020b403540319031203c0c150012a100c0e8030b203016410125082d003400005911032613001d5080c8060180c1b001071042100010400d00c00b40323190118002811510402807049400c0c8007046c0c102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 217180080 1250 217178830 217178867
    0x150819022d0c120d1d06070e0108040309090207050a080a120b030d080f2e0302130b1e030a020306040f0c060305061807200f0c0102212d0a 61
    0x1602411070b0307840c1e8001d409503121050300496003440380542940074801140c40d0416a05111001c151400e0b10f070401103425074045003004141d0003055000d00891403050b0380c10754544a225080940340d42c02500320a8045e02d081c1b050304580c1c000a043c1d40300900d40c000450301c481400240b2400103a0070f840d051442c16000350031000d00001c0243d00b1004603500200030070303d508402e40c0e1740a05c60f205060000b01d000700d102e0344200101d003d01c01202102040d68000c2d541c0c81c80c0d110181148030191980c02c00c1080d044000d404401901da10108404401c0440007819114850001d400192510800b07032025180c01c0d19550306001000400e40401004040904013442285010700005603d8600585c0c50102440d50390001044180b0503c8040c0d10703148030312f01c098a81c3d4200b03413019030350307190380701152b580b0303204281d0901e05540c00080c00182d038088149241c107000780340200c0f080807034210710030034050341d101c5d5982c90b00c0030035902c1c4d080001119244182c5440316140780c0c1c010481c0300355400c446c020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 217181330 1250 217180080 217180087
    0x1112100e07082e020313050607030605010e010c03020717031c050a060f06020304180b13050a05070201181b0b0d0b030601050108010b0306240a120b03030301150819022d 74
    0x1044154050f03480c400d54245401600c1c0e0b03807804100e6145d0307000f80034010f04500411082104180d019480401599020303614a082002d540d801903401400ca400c0242c096031200c5000c01088000d0f40e0791300043c0c03100105580c104040100809140a20b407002d841896403a20208030140c003040c441c2100411113014800f100502c0c00310042c0d00e0744a1405500c1000704178180c0011120032a82044480b070001505104c040d100ba840c403500140000e4805401540c04d040110b610948140070751422030b44203091050201c40d1680c1c5007440880107034540481c0280f10840050001001400f45c8561403942002050300340365002090f042c40b405812880c14020142d0041c02501c0420054941c0010b09a805552044040c0c0012007071100940d4004031103040003031050007056010b400f0704070660a0003820b103c65100603040584a020901903014190301440c4800b5a0398410302c0982d0b000240c02d01c0c40840f070541d011141c400c0e607100312105c602003002408a0008544002c24900d02c460380c0f4180c6904 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 217182580 1250 217181330 217181383
    0x50f040507080c1608070803060109080d090b070c080106030b01030606060f08070f030908030705090301060b09060a0507110a0306020a0e040c02190c051305040209131112100e0708 79
    0xd000d42c05440044030110205401d003050819001542e0803540100341991216910715000096901c211030450005117101000202c40c400010b5280440e00103440388010b0301d041021042954201090641e2004e0380038800141d2000284600400b4500480b4a00c9840d07040d410110b041c1c1d03402e9444041009404440c0901050740540c40c0d40d00b11007203240c400c040340c0442c81c0c11030180c1403100001d40301c21000410b01078a0703500000245020705040c0c000b0310402c2d580700b4040c59940284080141c005404000340381e0f90b40d204200804081c0d200315020710f45605020049045107010750022201c01c5e900003003c50034180c00440e08030060702d0895050000c1c4240320402521010b8684421000084d000a08810405140d96150181c41c02038080b4440004000e4880d0240c14150ba050b4044e04640000c900d0803000032903403110360740c0c00c031035007184440d070740018080e02c0d100740c01100b800340c01141d04203d0107035001c2c01802d554009090003000b900e810010000c0c24102010036001c4038081c0b40c805001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 217183830 1250 217182580 217182587
    0x21c0203090a20150715060b030a14040b060f030a080c03072a052403101a030c041a040306051003050c0d0209041203021315092106050402060c070609050f040507 71
    0x6416548130f1000c15120025460174204042503010601000c0d0304001000c40d94103003840c041c40c403402d1500300a100403a40c50724454250001070324090420b094520000d00b00c4d06081140800244000d0704984041446071241c090680049640021540002500805002042101c541e02c0000500303c070f90070031444540079540c110540301da0b074007444020a03404c0d031030046202000102c05051020342d5030303494180d622148811980c01180942041d10080000181061084d43c2c812582590514138040c28003411010480d00290000c01400c0704000c0800025114054140178070100c0c2c000702040d17821841d0142c10030b1640d903150341c0180045068640541e442140c05500250810000b2000301580d0504130040e100e581e82c424065500500c2c0014445034450100e00410816070f2034103100c984560a00070f000201c0c52522800c83c441c5007001020a0140c0d2003250401d1000348060b15100c400b41c84141070031440d500c1403011800140c2c0401150411500d4405548407c42e4104854500010302a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 217185080 1250 217183830 217183849
    0x120b0f010516060b0409030801030b010801020408030d2d0203090f1207110a1a03100e04020105090105030a140c090102150403022503020303040308030a0c02010b0310021c0203090a20 80
    0x82c0e2003490300c15124818030120741d01495507030341d01030310901c418503060034080e01c0d5007005e12040f06c0c03140b284000059109818400d45081e5032105005d5490200401d4540010345030b0441d4130540d405461140c2c64400800070360840c040f170290303100035841c2c1c5410046642442c80e000307080c082da5004154003031049000c010890381110f5000d150240c1811003a000300d0701002c81c54028200312607111041c1010041540051441142d403d80740545490b150b01d14041000760680e4000d001c2081845140e41641c01000a550b028418580000d00851480c0304418034100540c2c80c40254000060b004d206540d050108607103500e0b00c1c901880d080d04056070000d41d100006030f000d004040144048500c0c0c41c02d441c00c000c004680040841c1d464030b0300c1e070410300090760081e43c401c2c050074940820310407660b00601a03d8003880c00240500038115103481100040e40c000e00c1c04040b6250791600c9064052454400396000c2e9420200078140d0311060b280c0010304074a41c00d010034040741280220f40160751041c3c0c60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 217186330 1250 217185080 217185097
    0xf1404060914102001020f18030714010203030703020f090a0314010c020c060d0e0708030705060106080106020c010f08090c1e041103010e01180e030a1107061d09090c030d120b0f0105 80
    0x2c10840d9804d11000760300a00071001403e030b503c0c0000030909980342148104202c1003908031300b900c001c10394070326003950710400308034410f0b0242e00b003800001c50980c040e5000e401d4282800e004d032807604950500050340d41d4216002114840120201985c003260241b1646c8801e03000c82c00249039403211200015200c2c0640028000126200e2030f03948000300701806680003e11224040b6a05ca0040d0718020b6101d250034001d41c400280c2c0800002003080c400514000900d00684684804d100d0094041381c0401b801805500148509020f040c115240e514100101d48400018610301003a42d40420040c2c81540300c1c445c071800300a10044c8001440f5524a50444400c00846220030f180c0b00c1e050700281c06464903001c03641c0400f086904c6940e82003c8801150984401951030068440b601601e10529100400380340314a041040541402d01d06030540d007101d4030b03504403008040408002480d04980000b0400040d40129000e01100741a0042c40c8480030304a809030010100c0c0b0300000d0660040c00310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 217187580 1250 217186330 217186367
    0x903020f061f050f040603080a0504050f150a03052a1201050603010305031b0a08030f0a0501060f0203070f0c0f0602100b010309122001020a09050f040504050d0f140406091410 77
    0x7003241e0b490303841c0d1b8080c0008551000c0b85c941c4a0822003000b400a40291080c01c0c0140440c2c030080740d0928000b40c0e183e02c0c2602e5080d903d8140080351404400a04000307086041151500c0a00035120b100c10041e00885401036129654480c092050a80e4006041c0e000700d0141c103090005200040e0080b003920311141c40042100c6d00315083c201910318148086401070507800d8000148404031150f10070b241d100d10900c0d1400d100e981da880004503440c0b0041a181c04c0143c00c10b0044d040016001c2c00c140101c1c6000791502c0d265651180080380420650398001030140e405039880c847c450b1400d010b00c0e01054000d00741040501c21541b1040003051017800820104a820081e0707950700c07599046a512600c1040b80215150040010090010406401454407400d20b417118000c142c0f415010302032055034010050844200358040a5031070030840346181c0140f101c4616010b4846030307190041d00051180c1c0e59001001c52078240e620701c1002d03002800d18000d0360780650304403805070082c500e80b159414925 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 217188830 1250 217187580 217187599
    0xe030106030c06050a0203120a0e0606090f0c0717130303021b01020604140a060903080709051e101e03060e010e090d050c031201080c1207060e010f0905040903020f061f05 75
    0x40107d086200d80c1c02d000d480e050213103051000a9440303601a000c0011100221407283d281d910420410784412200c0441c0706101d200052103640018000e0700c00240b1494140110003001000024590885400c100300c59114100030002e040c0d0400080c0c18445100209840d100f5402000179124100104007601c2c3d51007403085401c2400c010040440348540001d001c04c4091074030f141c01081c200040c3c030500c2c000303031840c50046a9440e00c80c07250044404210f84101e11002c0c05000d1007881d600485030703a001d008a80b02c59000c1c0c501d444141103940b044590300011003e080c00c06400311094182c01075015503150328104020800f0000c0d9110704100c0c1800c0094890090030901469072080300075a00344003001d14000500410300107078001501008071554007601608261041d42d4070a02e10503500003d10344c0c600341d54154041c00a800c0140003a28020040c9a1100081025659a010110b0040c5c1c8400c00c40880c0341424402c1c40d0b00003071407003c080d801d100005e0448202100714011580720b408001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 217190080 1250 217188830 217188847
    0x1e0d080403090b160c33020c06070605061f080604050c0c0106140a050409080703050d020d0612050f0c220f18030207050315070309020415080c010e030106030c0605 72
    0xe150400042040d078030240d643c0c1100400c50301013203404001c00c842a4444040c08114101d000780408001c0b07114140c0c0900082c10120803140e0002420400c406600807015005141d460302c80c01880480e0050101150504000c42407003c00400d650a5507510302c480725010000e607501c0389071241c0101048502040c6a00ca980d551015480303102085a003a43c80d00100190812089042c41820b610856a219000380d13900144400d4802c040e41c020202c9104001d400300003070041e001340807038000540006081034a103610902c00c0f0307040d41e045a074414a04110a5040010801030f100342d00d11008040d00c41c10b00b0365404504506524244104600401e02c1010007000e150b81c0320010340c1c1040d00c0140140400c02c8061079205810100540050051f04004103050034005400007a215010f031b415201559800000c5006085c0080c049901c01d0303c0d2006803c2d1548444006006014610040c0003280c141500140c423102c980140035001c2c1c0d041180400c04030f60000716000c00c4500d90f05005a948451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 217191330 1250 217190080 217190087
    0x21602130e030d27032a0f14010c0c0203060112060f15050108010803120606070f020a0902040f080105090a03030b131506030f0e0c040e070810020304051e0d080403 72
    0x30350401075840e10010500c8810051941c110441510028441195402e82c2000e2000f422800a0000c0c011481144641700400c0600040210742c038114400c0204c44a22560340346140c034411802a99001c810115a0400b46000e100d00d6950302d0841c1401d4a50000743d178003098030740348144a690030300f50700303000d08100b03102042d0826400d00d6424201013144e009408000500035409000e141e000459100000c112034400008880030310301c00d82d40d8010965030f00c00802403a40d000b48812074103160050001030050300c41038407101c0031f48070210016864a00340380d8585005002c036480a280749e81040c0c00d000140c0b0380410a8103815815103004031301c4d9911080420001880c905030322050b40d01c1d04007044001c58a075595842520780940e8240881c2560040400941d410314891a800c1c0d0003911a49003a0700c0e2070b0340418034284141c0180c07040346075501c006a0410480c4100403000540000030030041150510681c1c600910805c40c25101c00e800e0030425540d0344400c0d0844040c41070300300120381030500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 217192580 1250 217191330 217191341
    0x9020a091107140d0e2d0a0306091a0705040609050607020d0b010608041101030c0f110709060f15020a260717191407020607060605030a030915020102160213 69
    0x1c0003050b40c0d07541c034002406942d40d00841c00703c440c00101c500300c2454203880c00d01546d45141d000e2900c0b010128480340ca01918038000000240c1c0d105003c2880000010141e00628025034044c401c200d104942c6840c000c40801c40017005001041020001400310907004503902c419140c041d00c1d100d48452007803000c140e18200d05180500813600c00c0b000016016400f0040d14411441058a03000d43d007060f20064003520000304414010072840c2407014046841107a5890b00c588602c01100e05641c1d640c60441308580343c542091061110350281440b441e1107051552541090601c014075111030386840303880411034207941c210404800c2c00801c0c41d454401406507010b50342c0000c602080d8445009120f90b02e5400960840509100440740302c040902030290b103402c3c1c5090071b07076407882c1c408254200019a48080070032208540d0b074080105064604100f03c0030101e00c2502c0e150115410402c032403580d0300c0e90b080881d046a004000d1412080304461540218a0b070583d070700c250300d09410040001910 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 217193830 1250 217192580 217192583
    0x60c120a0204170d030c03090b0609061908010b182707080336060301050f04020705061006080c090a05010c110d0303050a0b0a080a030f1103030906100909020a091107 73
    0x402483e408032101c40041800c110910703594504124400c3c004401341d09940c280f000280c2640b07428000a18507007800324000f50701c408020041030900180d8404c0c0c001d90400b81e008125142c0d980c0a203001c25081c146002d03000d5500ca600002c1d0b013442c00703000c82c0c04c965451760411010700c0800003c841c100c0344204110406010f41e501070320340b1801608015102840ca103002035415030018024685c079811102d42c10345842501074400c0d49560700303000900c00341008180c0b000c3e030465820400300021420901217140282c0003045d9041e1454501040106480d4001c1e00101944400300241d0096039281e14003103084850a003010f200c21405410141851100c02c1c0c68250401100c80c0100c0401d9459031000d88034a00400341013007641c010000b0f000e0140210b020304045540b00b039040002083c003a400c40c0d001c142d56481d00140c948190050141150416500c00480d076100109018501001050500151109500801c401025500068100703010740c458000013a90354000e00070801041c004482003e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 217195080 1250 217193830 217193849
    0x90206040306091511092d0607050c01020d020303153601050316030203100e03041502060618070503061207050a030c03110f0901031b0510030207060608060c120a0204 73
    0x302c403982403848442c99146184640d107440c4c441ea091350000c020064906e0303030f84060318003c2c611403103000c00140c000c01f6034a051203002c03811003410800d64501c40203207080791280020b0008010680000b80c07030040a10310f0502590814000c01041c0b809440d207000382100100d4012034010408140790f40c2407030a0780080e00304800703c9600b08440500181d61107040350f2003075003114400604400d0714028440f031800020340c55082078400b42079008590300142c2c1404130101c2901d1901e503171028004000412116048051f03000b0300d04105291801c160121300c0450345aa50500a191540004102d031100800c450302c0347d0055400d40b41c401d10200044400317410003800f600341454a030304140141c02043d100441c0e408540c044142010709003000e01d000280400f9119500c80d900f16510b06120b2a900189902d10011003440010700d540d490300c40300d0008a260302d0050b0b860300d5030f08007001039480d240c01410301c81c0d0182061007203070030090048a2321400441c0e13401c6a2030b280c1c86c1218000c0c0c45241d01c0380104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 217196330 1250 217195080 217195091
    0xd020708071421040608100f0315060b0310030209100527180604030c06020702041112090c01050a0509010215090304180b0607060c0e18010815090c04090206040306 72
    0xc101c01c2003000010001540c040b241c4084520150f09109407100300041e10300101030000300311042c0208061034110106451081601e07480c0c01e40e180e1110425441602c1e92030310007068a000200522500c00503141c01700c0c0c01851850320000c0e100f186006448000d000e00c07881c0300041c0076404001d0001c0041c0000903ca12620700f40c1c0580c2c0103e2450708207003540f01c18040c00105400010000d080d6160016090103051340d60798544027500d09a640000983c0d805408201080069607140705052680405007182900d40c1c50218000c848450001d02001c0643e0244940e241d1907030f040800c0c0d4081d2111441d01c1a522040540103c1c10003d90300043d03542c1d40081e40c00c0c4207003508080007820558aa080044800c521844445410382e89000d02007608030b40c2c100b02c0d0701c002ca00213812115400751682421030385208100d003c101e1500d41090207860309441d040c0140310110b0140022404c0000d00807140a25040c148001d9403030b00c00001007144034a42c1c550b01c1e40300315202c01055800454106008004c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 217197580 1250 217196330 217196333
    0x7020415060201020c0c030a0c0317040801020309031803010e0a1506030b0103050a0506060a0f1a0f03040606030308070507020901300807020103050106210b03210408010c090302030604080d02070807 87
    0x203504842c0d10403c440c040c4106c543d0590800195005d00d45401010644005145440300b104441d446101d28509840400000c25030060034001503000b20000c50045645041841d118400003021941d094400c3c0d05003000340c524042d00140c1c8400c7c5030f03088441c01d6800101007502e500180f0180c0c1c001841e104401d1300000c10300c0004100c410241e809207050f08c00a43d80c180c01c00c000c9520500400c43c2c141c40c8080c040c030544c5501104c24141c00c003040e403410720340003d5012071401d64204480031a40241c42d801e00740205940484a107400440d00c0c02e201e42401c81c144e0018070004014013548800d54070480d0740f48489880c1d5034108000c554691210500b0807100e04042d036081d404400168040b23401c140002401c2031280b00c550082000300c075914019030605012480190084142199040c41400f900b00c0d040a0400c2c446014011804a12681e031440c28a5041c00d488a21401c0014410b01d207e0420150700c0c0821210340c01a80150504e503a9030b07001e0034000003405010400303861400d0210782c900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 217198830 1250 217197580 217197583
    0x180109050324060d150522080d0614100509030a02090106053606070309150302040f141c0606030b13030219020f1905061305010f03020717070204150602 67
    0x141403154803a448070307160f55900a000c00d0041d80c1c00014a100c00b21418100c007036a0359480680c01020484d00d40301002e17000e1455809445500c1400c0e1014940006d142440e15140d2040c100100a64501e00151050460004514410b29032078002804800694119103980c148140101c0300d038010111042035841d900024043d4000c0c8080d030009101e5854a0140c4015980c5000e00728440400318000d105c540c4000e002050300050012024081c1c0040085002c0f000c04100b044811116600103849602d007910b402d4030792045078040242c036a1503400072074160301d441c03000c0c80d900000320000290a00700c0c5c1c54280c005040c107038400361030f03840c0311802d004003140ea80c410905114020b40c200c540d00f82959aa40001e12001c0200950000b0003c80455003400c00c899101c044003e04101c0c0c1c804030743c0d10804111a40d00110320307408001c030700c1c0009200c103681000307507918132410501e01141400c940b81d84002000c000c08070030095206000c1030780e1b8219502c139005210090803041c054419a07550f00c1019 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 217200080 1250 217198830 217198873
    0x1a0c030c060108030c070f080d050d090204060e0a1a0609061b030d060e070516020918010f090210020708060a0203061c060b0a051504150302130f0302010e01141801090503 75
    0x5001c5806030b40b1b40002c041d04a1b45903102698482c901a040c0c03000d01c120207403442d51160b25040c0c2501c3d214100c0c10090b0342c6038850f4200a000c0000b410380300c3e1030404251030480d44010400c6003052015002c0440c0303070312690180e80000b041510303540d554500101c209042408140c2050086100c0090300d0f103410f82c0386421000c11540b520b01c0c031102d80e0f150504150740c680a6421820032449144803454091b10f403907002590401e0999040548510980300401e0941b40d500c510b02040e65144c2c0e551000b1414031440000115806201401ca1079040c00c210070b8407a074001e00302440032171300071000c92105e603540d00508906040d420900420f2041034a03098010b041d030424410310611203c0c400003954101001c00c3c050403080a84528603060034159154403034141c40c4800410140d090242c1074843c20b2101034100541000d401e104000d0341746100043c1101c040c20411810802140074207026004c4800c00e4801492582e0140800500c4850040301e1040882d4050740d0700d0311608001112403090700303070309 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 217201330 1250 217200080 217200097
    0x70807030b01090b030d0e12030409090b0f040b040303050a14042102030c0304061107030f1b0914070e0d21080a0c0816030605060d0e010b010206011a0c030c06010803 73
    0xc0707480e80c1c2c1e40380340c4811034008892441c0c040e00000520b102c11881100240c5003184010040c100c00c90040a0240c5540c0003900192410f41d80c0da40782d00140034040d03034615404495a0388400c0710b4501a52148868130010300014207041d150000700c0e05000107500710145400115445d034480d8074090400b00c1403107a5400b80d04d80c4941e04200d41c940d02601c04011102c0520429004600c0d051604204507519654050a13003410b00800b42c010001464100c00030141e140100b0403441d010015021013030b044c029590100c1c956924000d410700705012800c14841c1d000c1c142c2d080001004030018003103202680200301c0241500810030380c1c42003022410764401c98169075a80c1c1e0b2a4075903240700718402140c100c26040c901240c81c213070014501400501010090b2900d928000c604c0340c0d0386501240590b0070800811200350380b62034603144480030034403404071840000d03c01450742c0e51402900d0000c620714071440c40e51b00140020f4085820340d0800484000414044c210b44066942e030110544a4001c1041d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 217202580 1250 217201330 217201343
    0x181a06010206010b0a180503030c010b190e0a0c020c03010f050a0c020307050615150a2303040b040602090f120a2105030610030e01050420100c06020a020a0507080703 73
    0x8501994030000700141603440f641801813421149070b0041d181810100030300140e025007107502042648003032000c5e0410807808000422118058010058001e4020001c4c07000e801280c001000210746404405030001e00070303a0f00044619024000300d007004413030b4061640540c01c20641c86a00a0a0fa104c13a01c04c01004104010b00a42c88000f02c2e00c9114204010701680d02030300105981090703c48000c1c80380203005007407001e00c0030b100488030b0a540150a211020404821881460014240b119030481c0c2070607881c945189000d5651020400c0e01903c00b402042d07020070350b060b15803546500700707141c070342e0040030a4a549890b0540c2541c070114000f04503080303002c90700402c07451440c0c800c01c000541034a480e101d065a4402c003c0c807050f014000481020551074411401c0d4800080c030407a800785001d0030a068031880f000c1100005010b24900030340c00349040c2860b000c40d255018040034003a55205e41c016075620455036040b8035012600002401ca030007a82e600040c0340c00c0001c2d16408807441143e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 217203830 1250 217202580 217202633
    0x90506010905060904050a06080a050102040603110405010c2a0b073305040519080d0c050c0309010c080403060c2006041703061504180e0a0f0b090118 66
    0x80112028030007803007410b40002090107480c80918098202076440441c8000008040360340325005458840585400d45180c0d500040610100394140285050108110140d62820740341c940000c040e45010300014040b10510801d09000e0440980552040c20f494445012050340b10303402420f0650107864100d80c1058150901c40d42185003a1081c004191800c100111030707172100311900060b002c0144121703030718054550784400360448001d42450040c010340c906d54440c4050504403080b03d041450300814410140064480d0000010484410310800c1c038081c400901c071440c02c0c0350035001d95040140541d003000c0800b603280d0390000101c180072017140e99000000c0490880c564503a10182c038003910010f071003c24500c85105210065811070000b40a0b86c6034462581e02a80c925001600000440e02c010042412039039400d014501c408106d200c050500070394959540458605000b6000741f02c1254140024408003007035001c040030344400c1c804014407144a2400100340d5015480c00e5501c0307080003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 217205080 1250 217203830 217203841
    0x90504050a0c17090a17040518010302090a0f020c0d030207150203040c030f051e07080c041e090201050f07030302070b160f050f0405121c0503090a02010f09050612010905 75
    0x1e0142c000c14146585620458501102e1100c101d058010030200d010301c10141e20000140c0c800300a00c08040110078501e854600308400c20503040d0014010842284083d80140b0142c0d444018550304060001c00001e0030741d4941c40070347c1c042e01a40c4800c0c942401400f4818802039019002480d41d280303d2407041e07040309081c1c022401240415540034018160b81001880002d40082004180c24042c408550401020282550052100540c07002c0203400c0001c04000d03e038810020025480c008450500c1001d502d00c80c0c00c10601c4120f4060b01c00c5944407060001564000c104445080010a00079681c6017403030306005c0c01035400000200d0380018280e0002d2a001b54100c40c000240b561581c0c0d03209044c00b0310000706d40303a40188484140c8240200070001d9190340d01c841100655040c0c43c05007045007907644115920b0981c0740e040b032051060400411046800c04180442c1151382401c140d8100002c1c903000f15508811604201e03004080001d802c04154512a80b850488801e8801404665920b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 217206330 1250 217205080 217205101
    0x20607230403061d03070f0204020d020d0513030207080d050d1a06070b090d030204060e040c030e03040311091305060f04030c0c0b09040b010f09032306130311010b0f0103020c0f01060609050405 85
    0x1b5058040c2c580c5440001844c01850240c0043c010058100c00c05810880c01120348400c0320020307100b00014810860540c0708040e014801e400080502c04050032014900e920040e056110b10036030303420115039504c0851585881c10142105801021305105c0c0c84030307035501c3c0c0380c0742c0c0c1802554486414030070304503800407852090088034299849072f5200080d800d01c000174400504510744513102455200c0841140612003003000d00005c0d4012001640403421a0051044085000c4c02220f07415902d094240c0104074001800358200000b034540d88150341e20307801d044800e605c1c000300003020708400c2c0b400081c0f0000d029002e8402c0d0b11007103c040200b1021600190f44118292b02140041266164100042003050446240d451042c0b071410405984680e40c450400004413488c03040c5400303040a00080c59800f014110b503012600c8000c105d69a0828001004588042041410150005091107481d0018410000d5000c0071030020b10000e40c54500290940fa134500415009602e0940040c114005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 217207580 1250 217206330 217206337
    0x506070f1112040b0d0605040c09030213020903070e071b060504020906090708010620060405070e0f0c0304060e0f010c020606011412010603180f0609060b04050403020607230403061d03 81
    0x208403030b072500d4140b81030702d072500641220005681c0c06aa801700003960f529035000d00c050a14460352003440d0982144100320100b0010400ca031552881484507040071b480003d00c1405503a1081008000c42d03031074640c01c0768940e40a1241c5200c034510384d10310f481040003e42155021324422158411b0540d699028000b8202d4101c91900016005c5401040031030f005d0807a2126100d4a11b851400800307481904a16298041d10304854660000d0020482c1c6040420119008100c50900480c2400c1000000078580400307400035040b40d540d00c19010040c3c50402c000540c0310f1080f0000d01076801503201c06901d0b0b000032116103001c680340c40703501c141c02c400510440300b03600148100700e0f54517428400108c000300080c0d5469018512030150700c0700400c901c40039a090301841402c000c50f07031440520300744058500a01d4881e001e14217000500c03002940108100d46d0019003450006540c862100300d0f145410140084071103030180c006808424020b454202c00c500d000c035440440340c070351a1300c554603580340b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 217208830 1250 217207580 217207603
    0x9030912021818070e070801060c0f080a0c05100504030305060a030f112107060f081e0a110f09121f0f0b091602010c030203060112020d02070506070f11 67
    0x50304241d00100e032880000d45942c12890100c0c1c415403800b8102036452138900c03250000012a0444c034100026075900c243c6950140100d40303020f04041000e690341034140440540000c04800c00891030003402d0748581541c0d1945900b1000300d071548030050641c00020710b800e8038294002420040000d1050801d400910116503000b85254078000c03840e1142d0381009407a050303003648038071a18100e00000c07011058512456003000081d251440c503002024000a50040c181410310101104006641210100e06141074080c011082c4036540e407030504034000c10324107948981210021810361110281000500451101561400c0401e13401104140daa07100500380701800c50110b40c20040c181050360048401507045000120b4010b01e40400950b4400003111441300141e14010110200342d824056032101d030009040441c55414070000007014170300c4200c0f07030020700d5400142c5000031080b41d90481c0c08103600070b420b40d03a003800c18240060026024000d1440000c0542d20314901190020480080710b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 217210080 1250 217208830 217208839
    0x120503060d030507020d0204050124031e0b0a09052e03050c060d060801060605030405240c0703020f03030c0c0f0c06030402120a020d0813060801051c081605010903091202 75
    0x40007107030b50440d059849904100d070441075501412005844500441d4041c040300ca0200300300f810040005411403040740c039600d0816041c050100c0c082d032801284544440d0f6071407004500c941c08440403400000040c4c3c002c60f0300a10f00f0b010402c407100100c880d0081440c4154107891003020383c0c2c492001c0d00f9141c0c00050810703042000150ba01d45440c40017414100300e448000301d1860f54801400d800c50304d0b540c0c0900046075001041000304a014000308500789110140010141240030003d01036007401081d413204040d00080c600306050007003060380c00148810080302e940c3d10f42140d03101000c0e0040e000514291154050a896101c804281a210310001422040c1191303031301e40801c0404030704001081c41c10700a82c004500903848500c03c4ca04c915020b941c20580d141724110884c0078008a40e40301408200300b050052096554010a4110313041c6043e28034410800d46d07040094040c402c0c050005030403401c80c00c0c04002c204064000107401740c06600c4107403980d03a030380034948901080d007040250302 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 217211330 1250 217210080 217210099
    0xb09010f1a0a09150b0307020c091609030b060604030c3003050d0504061e0c081620030c030304060c0306090902010522050d060902040506100f0528050712050306 71
    0x310340b00b0381d220410012540d107440324496640e000b017185035841030381d000d00144c10880580025041c6104c2090b0802c000466070380c0c5400340303103000030985451800020701140d103480100c1c140e0b0ba02c900c1540c000c2d40c0c100a00030f03003455840c80800b12103030840d41d00341c40741030301000d0a00d41c41d07550031441c541494241c0c03a5145010b480c2509c4000800c0c00500c02c4418a07524814680c0508100d24800c201d0301000c0c80000309004039142c00b501c400e8006007041c1c282c403543c0413031900442d80b004c5108141c0b092000c07640c55511a58500c1400c5000d554140d00280c80044108402c1c82403640002c05c00c0c50003a14208542d030b4950ba02c06082c1c40b203801020340814030030010001206a1015600100c0030005034030515152544005102024036001c1514101c0c0c483c0c2c2040300354600791182350380085045a13801c64040107a4000707007412240b980e0300c2c018040b011400b000c045404030700c40000c1a01465580b0031346003000b4405011a0010207080c0e42e40c0f4650059040c203540903d08072401048003d040701403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 217212580 1250 217211330 217211339
    0x330a09051b0a0e090d110106081203130f0c0306050f0f04030c020a05062205030f0c100926010c020c010915020c06070b01030b0c0f03061c0b09010f1a0a 67
    0x15002a8215040d08100011400103101d054020724600aa0402015059131a160383c4000c018011003940d41e84580d2408c1c904000c0d03c1e000040070a9403114942e415500c2c0d50303d5400b40c0801070f1604001825410b001c0c020081004103258951054a01c58402081540c407500c0342403140c2c1c8011074504428903004c00224010900070081c80c00c2d100c0c4010f000d0126242c4071400300d2180e4001818182a440c41d0495500703214ec400240755014010079001081345140419905945035900e00030940a03844411200100500c2440c00402824840c546107400003000e100d040b40668032a007480c0080d52074100d076880994408641000e00b194141d42e980c40403418a05070301c0d94a103610b44410700f0351040c000c91714131075140d40d406001035a0154101a22a6156080078624048020512806000708200120004c01d51206581d080a000da8080c03415000d0415039a1019240380e030041d00c003032441002c00000301015080004103001b41d0806100c08a81c5a5240d01c1d40e0220288660b4040c04041e024003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 217213830 1250 217212580 217212613
    0x11e03031b050a060e0f0c030a02060d0209031009050a03110a1205030c1c0e06010e070804150204050613080d050406091406071a01090606080c1605330a0905 69
    0x140704500034800c1c1d429840e481c0c0e45441c212003054481d0701450b0440703921044440418059190102c0044d07010b8142146180e0003d05144150500d56011303c1d0302040d600c101d61001c206245075450344e83e1082000d80040c0c2099035981c12030142c218005500341050000e01800800c190754401d5000f0000b06005080403015a07564100074000207400d402401405600c9108900302c0030581018040010703104940290079040540523005504001710510078001c1466005901a03402600301d0080360520101049900282c82140d002e20782c401d8020460b862107440180c0a0380494000100322885c88980b24000d45031401035100c0e007004100c2075142001a4103141f000d903084040000c00c000d140c0407140d034074400342c80084507504641d11000340042c1302030303003892141074007622240c105104149070414118826224030540c4a040c203190076040020444100170800404014500c2c01447c06007000500e0180c114085c401c1c0900b01954000c0740f034054007407040310f64164101c4003508625002200c00c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 217215080 1250 217213830 217213877
    0x12080318010e16050301060902040501050403060b010203040f0608060a21080705010917040f080c060a0e03070504020409020a020c09070804030c17030109020405090a271104060b03011e0303 83
    0x2a0019500c1c2c240d540c00a40090002c1c2e81007076003010400034050f00303140c01e142c00c5440da508010301040c810401030006a0f004810754007101e6001e10085404000180106c2c114001c40e801194144049580400c03802d401010503407040f00144c0301207010700d80d5072800c1060300b0030108100702566071340c01c480c001245120b00207140f00c90050740003003203070002c0e648d81505960810b840da0b002c0b5800441d05110302041017880ea0003c0640b072000b031400101c0a030015a240c42042c903410f05001a10341c080c502a102805180002c040041c811900c455031900f059020394000c0a1860040c01349251a00381c40c41c0001c005070103810180e0301c0e05801d50b00c3e680c090322101c044c0a81a03859049120180d403000741e516000710301811500307170003585031850081401010140640b00024960500104100c200c90043d1400c04003031114183e070036425058184000800c0c4483c41d12500507081040208441d05500000d60490706a0880c3c5400140c40c52280e140490003400010001004010300f0242d07907001c801d03c1d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 217216330 1250 217215080 217215121
    0xd1e111602032b17010f0b0706141807060302040f0509070504030803070914010516080a050702030f03030f0106050c0a120302190804110114030a09050c1302040f120803 74
    0x1100d0000b60b00703c85159140402103102d210510100307401c0c0740811340c0080010f0348906500f80e01e10455042610000075068180a100040e001c0810103005029440d00800e01c003060320103070800d1a0400e0010492503003030900300304500340302c4d0207030004820348203100300d0f400c850205504600080c01c0c40100442440060100030410a0038040803010907074007070086003c1c0703080d61a101b8409240202c8450f1003c804083c440c140141885156103840c20780d0060302280c1d80c4070a0466540880e184140c4441c0140300d00a0340510590b2012100c240c1e000005601600c000f60014100c1ea80c0c5031000c848502c078020034480d007034002c0401c1a000030304068200400718114140035040c51095500d84c0043c0c07040804600000740c85078244801d00155081100d05070b00c00f0701e041e04e110f00340b507003000d1050322026040c0e00d0690394844608080c0401440086031402e8010600006903480345a03003406904140102c01003624018030002c0e401000c905044446644200d06a007165140e22110b501100d550b5003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 217217580 1250 217216330 217216333
    0xd08190204081f0c090b030402040b0a080d0302030f0a06050a03060504020d0605090c01080a0c0f1412010e0115030c090605071a0a0f140f0105061e0d1e11160203 71
    0x404210064180b240c0b0060903840716054940c203ca20701040203a80c099403100741484540401440001c0803801117942c0f05405031f4010803084074102c0070400e8080c2540c42200f043c01840c0100074100c3d41a0011406405090001f1400340ca41d9201c08007100e0b464403c0560010403c0000c10000d1c0031f9421550744140000d017003181143d665118001070b2081140c00d06140d402c0304299100660b00218065002500604208160f1000070805000c03111204000801e02c8840c0b1044c0380c819803d013044803160049035603510b0465948000c0c10020010a02843c00914005103904c3e501c0e070310170710681040355001d030741d50040d8a10300042a9000e03400307840c0642c2e009081c1160610780343d12102509020740c403a00c5000505103180d0300c40000f180c01c4e0895034038000c0150020320508c0c0c0c403070403141410344008403135059544014440412921410860041c1d8052002c180340c020948981e008c83c4880450400e1740c1001d0490461080c2144e40900450900c00c01c103100d0200310049032203c04258500c05030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 217218830 1250 217217580 217217587
    0x5040515040b1812161e090c05070b0906090d14160c0f05040510050f030316030e0f060a020d0806060d0203010b07060e030703020a0f030c1b050405090d081902 70
    0x140005201da011041104031020741c2401c0c41100d050090048010701c81c140054a407009081d102c45c0580b0100b4400c407002108052104071381c88031301c01181401018908000c01206084280190054012640c16540d012201002a04542d004101107205104d00b0000d41038988101c0c100b074451004500003a600a54144200301c0c9105003108560040341c000c040d6030700f40d5454040700c000c0507000f68100c18043d42c00d0100340010400e0700030780142610340c100c440c0d146d200c0c014001300c2c4c5180500da0319007640303110005a81042c1500800e00b001d981d00c0a0f900b00400883c0310052007014415041c10380010392103000d45019803403040840036001107004150074901107003d00c14100380d030002e801c4500e0b0b191000038080100071440c407400540c202c05c0c030040c40c03d20b200d581300692500d201c15030280442c10341e0301460003018030a40040f100e0340c0d03004058034440c1291111100d0300e5450780c0200b6001d54036080205080c9000020303441d40040c400d0752648280d54402480504a100c41c2440c1c4290035000e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 217220080 1250 217218830 217218839
    0x2030303070207091b1d0315130201080a020f0d150f03050102031f060915090b0304050c030c04020301080d0e1201111905090d021c06050c1305040c0504051504 70
    0x91000310300405265000309643c2c2d082c0391000781202c00044107a0360f0008000c2802c191540c110020851030034100520703011203a2170300c000c40c1c01c2070200c08002448040640400803000b050541c0c400019000f0380ea2000c0b1990740a040208921601303c080d17100b00c00a10001460001c3e54001310500366805200d20720495441049092071840b81c0c0040f00e00365004010071a066844000124102050307950984c0018070300440075003030181d030b402080309407489400500d8600380605d0b44440103280b45002c441d43d131318060030802c3c0c0f01c2c3c00382c60265110f030148010300031079480e2a0084d40e05840001016100e40910010705680ea034802d20403050b00208800c1d94a200f00400307105070008001c483e0704480e521585411881c07184200201c0c0d900500c4014042e10241d521510034071381129905946002682441c2e04440300d1982d02c00c0300c0140098140001c0000090488002d802c0d1755036240040816184c036482000180d400b40c409180008100303100811140ca8041c1d43e600206103039104180c034280d103d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 217221330 1250 217220080 217220083
    0x50721120e01140615030420190602010c030e0c010c050c0d0302010b010f02071401110c150d0e01091502031003140303060a140114180402040e010311060304080304080a0c0203 77
    0x100010108a0350f60f12200c0924000d00c00d215640400119030301035204c01d084c043c10032203001c0134001a00c41d1605c81040c00c112581d000c054207001c2c81c02001d090802040d005550840c1c0c046009000055090bc0001d280b200d002e40100e410900c00180507215003c004001198001c906c070380c05031124881d01c44d88190640713600e0308008409000703a0010071540c51007000545000e007401c400301c0842d03010300400c1120f0445107c4c506c624010920388060194500c802081ca485000d2040c0c0744e201030315041c40010b40008600a00c1701c809402c005014a070940071060b8201c4214400280c1042002d55000140b11450b50055a00140780c10610400b903451303031141c8400030a2000303c0d00307607a0300002c2030000390301d0409811002080c000d0102120703440d1f0400001c042490384400004030200201f6070b008200c59006010b000501d0240085494076680e02003510b82d610203202c00d0f07400d0400c030a00001c4034182101240c0c4107903003000165113140c9507070384c0310285030344018506003c002c58103c8180c0181d80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 217222580 1250 217221330 217221341
    0x30c050a021b042703020d02030304080304030f1110060f05030c0a0b0906120c0403060b1c0b07091809140109021e040906060e0a15080d0302030406020d0c0f0f05072112 74
    0x30715441210300e07109250113480c5c2004001f0000a40d8002c0c030410000402110480f5801070b8185004a1640888041620f500e41108008045401190000024441b0f1940418100c1e550400301e01c200f540d85005160702d0381c8100d6821a0010b510310b0f414858581070400504100304050140c41c0b9010204052252000c000e803001011b500b00064100280500c0340102d000e96002244c00740302c540c012198248a5041c203100003016500150000b4803894014549103000f810250400c401c1d102d020402c00004201648040b02e071400650700c4030309094014400c2500c801c1e40131f0400c2524028000f01e02c80a104c02001940d840390315200d005001030850300644004002c070380c816900d241401c00d031a00c107407001c0d20300c07032410511500000c100344a00000d540d07007051020305006035603031124209100a84075030009009035604140002c11040da011042242c41d512641d1074215405c0d4161045802c2d00c036846000d0700d8886100400f0a80036a043c8101c00482c00a081c1b407192940b0702550013003900c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 217223830 1250 217222580 217222631
    0x30a030e030f070c2306070b06040f0516090806010b09061e07121106060102030d09020d05120c150601020705040f02070f030801051905210a05030c0607030c050a021b04 74
    0x1100c030380100310005d41c98464002000000070791901d025883c01c041000c6029000020740030601007400310721103442e5a48280c03181220783c0d00900040c0740c1940300c2000f540013070860b600020758120340020590000300e00181038811221420b0303e404604420081150030180141a4001024100c08a42128403000380a0244a5410050511a84070004d0110a045454003010b504401c4c10860b003a0390120840e04402d0080ca40003030b00700c0700c50003c03619000c1c0042c0014140d1049003284880c0b03404900c064142c44d01e00200b1140d0680c641030030901240c8060710900d0142e440320300c09010360328064000c5151000d9620340142041616102d2060384040d0000070740100310a2801400a4101a1a48540440307803201e0f04c1511440d000100310090f0008440300070f0b540c1d10100c2d000805900380701c44a401d81d0070408694407030030000c582d10b480303034016250200400c0c5402000c25247d4003980c241d03046105030b500a8541c00b41d502100d846030050050740d442d0701c10396503201000804041507549141c031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 217225080 1250 217223830 217223843
    0x510050c28030c020c0f010f05070219090b03071203051e0d0e0d140403020915030706081608060d02040e010f0222050a030c03140316050a0209100602030a030e030f07 73
    0x184a440e4040c00703d8160480c0341d4119003000b4150541c41e103441003808a031403021301c0c01400c0790505c0e0b581121907026042c40294851000c551a84084403a40300510988159020400c90300841030100341da900140d03c5101a00c40c80d0024074400702e4021030107803d0780099941c01c4e40c080d460000c40c0340e249510090302c4811310360381c0301504a0401c03010400841820b0786c41c1032102044d030f500003060149028502c4000c2c82a1004d8001562060071441c0141d5100300250440e0701d02501e50502502c0c1c000c0071580d001c1d01040741d440070400a44104a09802240f01034464840d8540710340070301019000c41c54403400c10303640304d24140a940761341e032005042d0b4694405030b540884c018543c0c2180f49554680c40743d03114051303810090001c0b94661661508580d405150801a00c2c05042c0c281d0450149405218034041419056014031401107842140c0520132075102d0500d0740c54a24030080c41c205070058070010f038024001c0c02201800b0b83e2102c0009040c11044a0902d691021810752990042104441030f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 217226330 1250 217225080 217225147
    0x50c091c0c0b0f040b0708090909060403120b0604051c0209070f0305090f031b01090c030807290c090a080708150f13080a17010e01051201090510050c 66
    0x348289001c505010304a00740c029407424500c908074400310301842c06090000c0000058200c10400d182e8111b852203003005d04000e2080c54600c090f151181402c45040e030214003182d141ca0310b012150302c41ca100c42180284410b00306400c000600c94010209582c51001456440c103403005a62104100343c860151995107488080922400905a400240c04c000440d17024140005107440f000c411756408021110303224210008082c0064098104140040e0074410a02d2010080c0604070001344201030003a4040300d85000c03441c0c45000c0054070401124195041003011402d007131690402401c9180004010548854440e6402406c14240380e000c1c42144d40035580e444138100d06228241c3c4c1c0241c00503070300909c3c0c0c07421605140d81e00128220041000c50002034928860f401501410141c03902e1088480c0c2ca50307101d0720784460052003800380d148180130395580009403880501505e46042c1d8401d002d0100e004e041818600030340400343c42c07104480410b100360700d0a030748071883c89460300c00c252001e44407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 217227580 1250 217226330 217226333
    0x509030c0c09160c02030709020c0102030402101b03030f09050f010e060121030c0c12030f1101150e1003050d0302040f050109030b070f02120f040503011406090406050c091c 76
    0x180c44401c6460368000d40002040240300c03104088035200e240000d00741008003040d54070009040100b160032039400c4900c0400c40b000154015409103110710310031f54800d0380c4400111001c0d0303031001e245030740d01d51010103600300b0300300081c425003081c3c4030400d24074030201d1142c40d159070701420000b0054000703000303a5462012151801c01045030500404140a01c0300380d85055113040414208007210140c140034242c07030440c041250080c405801401280b1008181001c54940204031307a411151000c0020b003030440c1c0950340501803142040c18401c88840010107407903c3e07004054504010b00c01d904020880c0c0740000461350078030249041c40c03a02d0b40e005130340380c4c02e044c5200c900460a0300100d040040300c01052000585204020350080a40c0c14600c4000c003010000f240342c074044c07a0a240b44d1404c0440e005400103100006042680c808600921840c2c0e04025401040175003101c4095000c40e9542c0441c010445d154170003508284041c520038600b26000002c00c500004c00e6000c40c1020020040000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 217228830 1250 217227580 217227583
    0xb0706060f03020a1a040515030406050c1309110d1e060801060e040b0a060b0a020304030c050d051507020c0405010308030412030516110a14070e1503030a08070c060509030c 76
    0x14085000d41c14003030340d007550003240b070b80c6005014410014510400d5401640c0003c01650700404c802001018505140d00c0c3c604ca03190019503080390741608000118103e860580141c07149000309510f901d2400345880005000b9020f980c1018103240350402070081c00b403403980210007403081001340180000101800300307400c40c2c045074080d10681c0d150160a0140301c03000c00003550466040500000750f03485140801c001024658044a03007080000f8041c04141d8010014004030ba0190840d107181c19600c07820b00420300390294005205822100485000440d002846500552148100d4051038171000100741155401e8209503844000801000100310b2041c10b070650207000c43c0340c1400f40382014a084c001c82040003880800f80090001120b00c251030400ca0b03080f6441d00148294108000c4540e801d07100d001901035031240f2124000094a0030340116121415540040c0045207002404241203c0c0c0d08009041c0c041001610048280440c450380102d0b0702590704030000d10750345c008002409 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 217230080 1250 217228830 217228841
    0x3030106110f06040803070c0827280302060a11030d1409011e0f09050a080304050105221112030d0c0f032003060303070c0609030c09110901111002040b0706 69
    0x1011103a10120130031000400403000c2d03d410205509161101210b0b078a4004612300920021500366249003680001d8040b120780ca01014200c1038402240d841441c4e441c0100c0f0300784400120400d0103541001f00014203148004120103041d80c40c101c00c540032070625250456104d001c11003070498690003100b400811440041d40c02c03035200c5008001145244410003035103141c04516040b6666600d8080c0440e0302c8a421511080b5800803d0b0b4000900e54900040c041d04150380c2a100c941c64607001406114801e036040031394801e0711416801d00e089680d20b852201c1e40d2990310a800c00304250009203410010030140411000408000c1035801804c003006201887c690395603000c0504044500008001010070914400c0403d6842c665035130340d28000c6440c0d8420010024002e140c100d600142c040c1d400042c0380b040c0c074812990801101e0755583e0f6038080d030f100c100b400d0300d407428100480000340d0b010700d100003200c6021800b07880d21030031600b4246049811a034407140a0440014400040086a1007107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 217231330 1250 217230080 217230103
    0xd111801080601090f1e0b1c081909080604060213030c03050a20010c020f030c0d05070905010b09100807020703060f0b0f0406030305071e06060303050901020c101413080303010611 79
    0x100100e0200441604221b210720468004541c0d446050b011203869000c0d21400340d094000c2d00a942c0d00e45454015540d52007081003240703118003500320704000c074810740020040301e171010014100382c2c40315142c5030002c3d848000707070b05620b08000e20300200203400c6024800045000e00042c00140a00f402d221250600c128174054154940100d641040d0ba00041c800e11030030340603202001c40800070b4000c1780c5846070340200d4a074007001d40c154900070031400144a1040e25041c0c0010311080e660380700c40b0141c5024603850240c2c400b6405955109031442103030b669510016502c102c40740e4994903111407003240c800698408500e030b15003400c00c2e101d081101d10b01070700c048155010445985182c80080c40ca01130400c000784003120402a034091f101c40d04464100c800e82208080101550f61301d00a840790740031000d4103000d80202004d003642898000c030903081c407818a44480c003105411b4130341c40d803450b801116507040a00c0000d1020440e4081000030314080d02c0645c86070403850f080038004501e0032102d10013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 217232580 1250 217231330 217231361
    0x40303051b060f071b120f090911040302100801120b06010519030b0103180f030e030f0709091502091305131a0103110306190b1215040b060d020d11180108060109 71
    0x10b0a600081041039001d0000340e1a1411f6128100320020440701d0080552140342e00505046040c005c0c180707a81c00070001c503403086413644840701e00540b090b1500d0f8000d11035480c0e0003520000071000704040088450707001c1d5052410030b1034280f0000e031803c0c81c00b90042585000a6807000713103e01c036513050312070068203055041e06c0b1000003d190b07550800480c801c1c1c0005003048425074954219440806c000d00020304403005403019151645080c100401100200742c60030b607c0720420700304081d014400c654000074050f2031014401107000c8084086c08d00a07000c3d00c103010040012030049540500b82107113003429108002c5c0c2d01e500d98202401c2d0382000c41c4041c0d20036000030040c01140805204c1c80d071070341d1800b003c0210305500e91300001184d4442d2803082142500a07010700c0c032541181d10703540501c02c91103000d403920680c03922021300010820702ca00094010011602220101d0b40100000300403107001001e0002c00344402d08201c401040c207a0003518254081e10062144407214050020526106c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 217233830 1250 217232580 217232627
    0xf020a110706140d1d07030b040308100b180105160803060a050405071b020d06020301150807020f03091302090d0503041a030f01030b0403021e0a0204060b0f040303051b060f07 77
    0x70000c00303036202d03244c0650081603507280d03030b00c4541c100a080000281c5082041ea04800c3da07a09020701c402074204c40490009038a440009d001c06000c0380494142d40390508000e0030041c0449a144d40c15840c580d00301e051103824058000481500045050803074070070400d00c2d849051800a204502e0302e1a0400c034400c1d4103201c1000102c5510201c0c044880303012200c1c440f1010410f0000c076100c941c95847c068a030354000000425a050340d10402e00e018022580e42003c180c5e07900e00c04076151a1104402c4565070420450221540392040c166000050764040061420105000040004840030012610b60308013080c1000074280041c5455419207519900a00d146802000b5110400341408001c29900c100000308040c14402c1003110581840014038112160041903026503d000d1040100d106a04003540401c001e00108103540c080c072840b91655048c1420750794284c2e0180c00514151020505803022040c206600700415801040c508010b0070640c28030480081101c2018851003d00f41180c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 217235080 1250 217233830 217233857
    0x90c090a060b0702092d04020907020c010801170f1b030709050613020a03150e0108072403050c0d051005090a05060901060e0307170d03140c07080d0f020a110706 71
    0x168103c80c00a0741c101c2d01e804036651801c0201041c200c000f01c081c5403081181405410b41006408101e00940c000c5564a0043da18400c04a03501c80700009401d0000300401d0041000c20099001004031266072000d076002002c0740f400080c58860085e030320142102c20105152901d00702442860003500c0305440502c03142c40c0040c08903803450708440e03818074996030025035419520b1195000c041040b450040c801c02c1280e075008100315020081c00340a00303a005203880040c29074852180000510585420b21803462031206041c6d0007813030000c01c8070908240401410001c4515480341500c18071009800c58165420310050041c049001080c1031201e510744400d00c00f480c1c1d60044a64111410791810924203040b510201c2c2c10000264007a1306001d90301090881210f50216045e40c2c0c038091a40e04002e0490f00d98102854100d0a542e1301140140420020003c5178507d4020030503400a03800128600c00410910001c0340e000300c0031030b40000e4196618031505281407143c0c130000c0c40b140c6415030042c10741 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 217236330 1250 217235080 217235099
    0x7060c140a050d0b1201090c0510020a0b04021c150501050604031a0a02040f03030c050d1e2709021809190203060a0302040c0f02070501020712080705070e090c090a06 73
    0x20070094000b0b20201080c0d5403d500c405400072282d00c0300180c01e4401c41c1070403110440c041d0001f9482121540c40c983c10205e413608188995101c0c401d00c650051864030360546030410f10600103441039802402c44070110020000c1c000c0c017494043e2051440000203d00903518104494040c1c1102c1d105010070442000400d10f03149020549600445150071907071241da4210b8004d11881d486000054110100001416000312584610b94020800d4603034411080200b210240c3d410384a082c03032043c02d080f2440f4203511441e9404c400c15400c4110400640170301005e041c034072500c0e5005060440e000a4402c0d03000000c03043e2a108408159052107581c00c0900307079030704103100150f003005202d5804000104581e944e0400180150f401410401c181c211045000304114100c80d8480c0241c401e400d07000400c0d51000070710b101203480307900060480201d20b6443c5041a070080c0016100c500c1990004982113801c3c0800e14014021600202003200e0690b0a103c4802c000500c4404920316011041001010707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 217237580 1250 217236330 217236337
    0x1060b0a09090f1d010b04200418091a2208030a0f090803040501060608250e01030f060806011503050603060610091a030f0609041110020705031207060c14 68
    0x80b40c4101207090f644009803200101024403034402c08107888920b11020742810341c410640303048155801d10035140d1403803610780b2111410700702c03000c5100100030801c10701c0142910600030b5014400080345040c2039403140c49503114002c031000d29021920b018402c54001d49420940029111564802e040d141516814410b010040205040710f03110152806006540e522540286521034240b60700c03802e00b8103082e40248521b000d1140880c50341c101140c4610102c561590b43c00f40e54407180340550280c00403c540107080070344068145a10340040c4846036100f40a1800a44000001080c49600d00b0a203a0403202a0000a1041c14502014052141c4000c516a42d000704152182140061707410000c89000306070303504c046d68012403401c88801500c0d60000a60089140b100300a0464075203908014010000359801032618021741030000350341c141180809212242401580c41d042e56420103e070429113003070720f250b540c03400024001c0c0410055100d0810408403a20345280c0d1a80e810900b080b0511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 217238830 1250 217237580 217237589
    0x50102160905062d030607170403180e040b0f0a0c08010b0c0703050303070507050c090601020c0f040e0717070905040206030a09060605040c0e01090602030a090e06040902150a0201060b0a09 83
    0x1d460744002107464561582e00108a0311a2059611028000004c503607011604040130380709004e4040425883ca00c50600180d80804c9200400c9080c0c903a5542661426072001031078000b03220b040400038041020541241c03007a40240c04000c0c3e145481813114104050003486418140e143c0201e2005850b848203041e81543e000f00b8440d9900d800c4c84520514080c004e0748010b0480c8000401c1144045d1f0040141c07807602e102c0e0081781e02e401004020003a00d20411100c180c016407000380400c0480c03408000320350b98164040d00010710004403044040c02c03d4281e03000624480103d030a50180420200075580051036070400410041c241640014142e103c0038040e03c81042d1102d484009003d00e940c4020001d0a0041c0204546030030310b10064481c00d03d00040d58085881c05000044950000c0200d503400412039554128040c10403100c0344040e075006e084103170403e81d140a44070068582e803110003401c00f0902140e5032902d1000d10000d0070344006400c05401c400c03045c8070320b06046401031000380035903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 217240080 1250 217238830 217238849
    0x2010908070813090e030f18090103050a1a160302030601030e030d0b18040201020a031206050301050f09060f07120c05040801090c0f060f080a0b122e02040b0901080709120c0501030605010216 84
    0x4158680342c801242e80c00c8c0d10b09503445407601d00000100200050300c4002144a05103200507406c4807602c401404408a640c0c0d01c480c28900101c42400b803081e4021035121a050600090041c01900654a55003000c2d40b485a00ba50302c20408800e1f181c480382e030b0300754540c4501038043c0920f00341e0300003500d6182540008040c00b5410655868107407a03034020310b0183c28050020050b07031900c001203244110701511202c00500400003c5510305611060b40781c4510060744900185243c0000c5c004001c1002074080020000e092101090800003030080000950203442c1c800313286814406040d8982c3e1a51303000c1000d10011518261031141c00c020030b640d200e040355500240d0520420082400800140c0e816409030294001a04549005c240300301142d0052183d039804103100038800c44128411801a40380030001030120204a6200f6610301c0d034450b42d640750001d03045984111240215004074812200e142d10400c00303000c10359051141100500092000f469500c010b40305c166040812406000820b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 217241330 1250 217240080 217240087
    0x3032a33040c0308030a0902010806010c1a0c12091b06070b060d0807060e0a121112130e04240501050904060c051b0a0b100e1602010908070813090e030f 67
    0x10322020070072800003150030000700f55072851b105c0c8058000340746c4108100d01065201000c00e040e548900b9800c0d01d02544541d42c03008641d03800036602540c1340300074244030400b8810403032182c1c107400c07064000303000e60450001048906071704401225800c85680003a402000c090012001040e0101d55280e00b003078054685c0246028035041490755442140c5002d0101030400c41003d0490303900107400a469809000c1141007030150384011241c103c001c04a8840340d91040c00320941c020190380007452000740d0402c0601e002e031780d1112200d5801d2000c0741c09480700e4840699130504940c06114281020310b144604000a40c100b60003c0c124001c042c1011301040d43d2110702d031001501800444603400c400e00c485520351451307009040c5c1c1e0740345088421038000c05007502103030001c00d4040103032083d200003079010300c40366458001d002e45222100301c01c0c000310344d00d41c0b00d5200422541c0c40148007450244c0f05035603032103000300c3e1046d002c801540d005051403864080f4000c0d41c0b078004815523034565802c0440903075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 217242580 1250 217241330 217241333
    0x10201060906060e0108010512030d020309030405030a0c0e10050105030109022223030111090907260403180602030409020c01150f050913080d0b03032a3304 69
    0x1406039401000400d03203010408550301350040c0c3d25185001d401d0340c44181503038860041c41003584c080400d034105544207003c40e41900100360060760748200900d044a05141d0340303200007450070702c40707840544a141c1c02100c14440c001400ba09143c1c0082984c4600000d41d1520000820501c0144a07003841c842c4d022402c20210481155241c030749aa6030400155601e4442482030607501070783d08203c2c00c0b4041403100c01404d04042c001c005450300425800d81c1003041c0601841140c0e0f500400d00020811041c55080e040c16440072601400d101901400c02d1a1400c0d01d8003078008040320744112414a1413131010084550b000080310260307421502d0160300c4094030301040f4050030707030f4080070051040141300109040c411001050111082203880c2134094a0b0f012003c0d1001c540030f0310203000d080c020040030841d485103400c26403161501800300d80c42c0460314a5103016042150100705090440300b24084500038040048030694404004559001d07020461001103119050800c0250b05441000040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 217243830 1250 217242580 217242583
    0x1b0604052d01050a0f150317071b082a0a03060f1d0c030d1b060b0a05030a060608060606040506041502070b0f04061b050a06090501020903030a0201050603071508010b090102 76
    0x1c41188080000d02a9040c84221000501400300310036444910700242c405100035601c0604007183c0c3c205e1054010b00c00030003803080541d481050243c8840d500009520450320b200044903008159940143c5803910340785850030344c084060380c6054206030030500d4424a5940d02100780048135403064001a81c80380600610bc0580823460300d4a111402d10710040144507404980e02640d801d0883c141d84813921550307000d07904001501c0025483d60b4941202c00c000420690140c8c2401000800d040d40541d074401c0001e00d03200703032500225102e03070311a081080240340411402d600101c04131101d9092038100400b0681e030b4001c5200d010002c2c4001c108007102c65002744941800b5016064040e0b68a5a0f81c48006c50250301c039100b180002807084000c669194045400982010b90040c0944014102602c6480250412000950b00d03950300300908052558100024003400006030000700c2c0514081c4105820f0031650352109001200d443c50340b100f580d9204000710b040d650708100440c1c4442031240100e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 217245080 1250 217243830 217243903
    0x306150a05040c02030c01050a0203010f170118030c0b0601080105010e1e030d18060206041e03090b040f0806060d05191b0f14030f0c010e0d02040609021b060405 71
    0x102e4215140c010701d450001d074088010610300c5002c100a12940e110841c0d05400c901c001d00c1040d20401307903a14103201e500c10140040d40c4c054405000460f01310020f200802c8515080c0b00120040f40b06425502c0c200a00295900e03030004003400c0c1200d096142c040060224040d210106210741d280c011440d100300405002c04561420190445036880301c031031009009038450055252907580001c000045aa10028105208d1940200c4030020245141c403071740e0f421101000203c060091502c400320f42c0c107a222024200070045c0c0c0003554030092030315102a0408001404090003403440c00011404103000258001a40d03140c075041841e800340504000a00b00e54042e065040c1c20342d4004001050b030704580d103c406a50101e0081c4a184640b101016981e40c0031f0401502c407500908601000c2e98014290801d5040024040c01414580d941c0050211003068000075800d45e07011481c1441820100007810983d12408010030003410291601175603001820261425110314206207000c190816442 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 217246330 1250 217245080 217245089
    0x160e010206150d050f0105100e07050a050a030f09080a030f02031302060f04080a060b040e03070c0e06030705060c0604120924050d051302030f0109030e040e19080909060402090306150a 81
    0x196424082005c1c0071502a2200303032005041d90b94035810102d800c61b6001d030751038090716143c0c880f140b4201c82078005480c00d820180c0031070240760b40e808031000c05441c0d034000c20610350322500c20385944580b40e020260440c0e0842c04042903461040c801c00510407142c0c0030581034030750125035030781d260b40100481124034415600622200d00a18110070b0030030005811a0f00c414404403818040300540c1074620b5074038000c949000e8044010482d0800445d00c031685541d0b00100b026090358291030321200498810303800540b001019904c420308010034000e9040181030103944924050242600e001e4480502140b54030b12030b10382c1c2003040c3c82d00034800d00071021130b402c0c50003a80090155103030500200c40c0c80020800306030f01a0050302c00403a00c1202c107103d480001a80350300e03151414240382007404000d014290f91540c00c1e204020701840f201910b6049004110300c100845079030382181c20280300400101826903805980144440c04860382c0100d074069002d90404102c08a1880c20310028140c03080c654003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 217247580 1250 217246330 217246333
    0x118081e13030506070c1101030b010e0d030804060e16030b0a0b0405040f3305100308030129090609061e040b0c010e0705031f1103010b03160e010206150d05 69
    0x1a004022800d10204500b16801141914000d1740c640b04142c82201249038002d1012a604460500d1036000b9409141045030600d4109030400070350020494900d080314041e4007247d5050304005c20002940107185000c0380300800f4050048016170301009031aa5400010440180c1c400043d002542c50b41c0000c45180004000344102d041c036041c00803801c1d40d8000141d41585e00564802004070700c241d0134081c03901000786c44150082c0d416182e00c004ac4006821703418810700000002000c03400602c0590301822841c0c90799500c40722805203180320182c0042503010864010f01c51400d15036500001e40e029124282c801c1c1d90386000c1741c020140000c0780342c0d018030340e8140041004078401c10510050829944e8140080140c050010075055071681030744a80c5034160301a2010504417040321500d88c030b40309509000420301540402d48501241c02c00d801112056038007004203c41640100c4c0b442c515103180703061602e2442490b0340000c0d160303034004040c0001150109443c08445c1c07110b5035060102e980200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 217248830 1250 217247580 217247587
    0x15020406090e070c03120e0102070b0a0507180f030809010e18061903110f1305070f090501030c080c0a0207080a150b220b0105040801150302120118081e 67
    0x10030180070071580d07000c1c1e040d184090100003031000d0300504005440a8058550701205a00355179004041c008944102c403580d5028051980002c0070500c60500070950290041441d10b00321300000d001920040a040c00155000d004200202c004815001900d400c804119a600e2000005854a107504c5441c0303600000301000341300e8604e9150001c2401013038100c45451508c0120341c1c1040d0f91740c410b0300028100044107c0d6a450610b01507849168050340038192400100da0b00080d40c0440c0d03812a00c40700881d05044044a03540e0f840201e00000e00f4090804010040500d28000c0c00d944c0010006908442e00181009849008203c0f85004000c150106c41c0062010302e490000c14807413600d580c01540c10702240311307a03034501030000703900180400020760315000301d001400e4094400c4041880c1030113001c0101080c000000c1c01034184555001155070080c03031643c8184251416480c0d050074069240c0008a1580d00071034100c90f2546402c246601d844a1341030b01c0703100825401c440340e0101c005000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 217250080 1250 217248830 217248839
    0x70807060b09130506010b09150307030b180901110f0d0b010e0d082a060a020f09040e010c020c010801061b0525060e180402011101060f0b18041107030c150204 70
    0xe09402890300c614183c0d04141d80c2e407c1e880034540500043c0304d502503199294018000f403400003840d03028880d8a40070803900140340c00b00c3c0b01d0481e06a4100141f005100820245100034000d5481440c3d241981503d4800d41440400a07401256800c80d83d062329004e10744070b01d80c405c40082200ca100103107981c150302464035000000b40d00c0314104928882020070801d29090070510080181c4080303401400c0c0c96550004800003e40c0320280d0048070000511412281e500c4600c03803407052542ca44000100840000d40291a000e08256040d04100400300140030543d07000d095081c00c0000361043d44d10714401860000e0a10013a81101890f0308400c8007140d02d2951034154400889103927403161110028000140040030602c10a10b82010952602203801940304c3c0007400340083d101c1000186a64544100c0c00360b02845602c101d45004000c245901c82a0580d11082c85002003100c00300500581030340801100c2c001d144018090101c207140c1c0d40c0600828401d14407070b039060a8421581d441d02c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 217251330 1250 217250080 217250101
    0x82a030a020409060b030606030c161a0108160b0d0c0c050303130c0602060c0910020f010e1b030303010e22050607120f021204110d02090c0d1b05070807060b09 70
    0x1a20a108080e0304080c00011017000704000c0f680550300c0580b200d450369443c251030f64050780c0146010741941030514140804103c00d885d40c0b1101070582090348010f54500041545021900f01050b2503188005208114040d4620b0032a0107a0038903030004292908414030940d083d02841001510700c0c000041003200014411065444440c807030b164510469440d00012651404200e6000e0707828102000030560a18100d456040380c0c011a1044655031180c08030042e0950f8034060240701c082c1c1c0a4000b09584da00c2c0e05440f43c2515005038021030856140c02102e0b00b0010000e0408090218110400468400041e0001946035041001c40e80c035810415801400190941d60b650b000c40d141c492a86954000c50084400341e80c4002c42d002c50310388880e1074110700341e44d5483d40194058002004040140c0300d1500d002c2c0308000c03425106440f000300f8400c1030280c9400c060300004000280d00c0c13988205401100340c0c2d070400e130043d044949075030b05071030498018054190f0142d807014001040004800c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 217252580 1250 217251330 217251337
    0x2010f02010917040e0f040503031f05040c110601171b0402070f050309010f0f020d110f0f0c03010c03060b07060f0f0218010e0405070509010311040e040503040614030106082a030a02 80
    0x3040561004581d0303006c010040ba04401d40740106035030010404036100807103480c200d0001940822501000c581c3e1000068101c0c0c8000c42d90501283c0f40148505e80c01c1c5041c402d90740181039030b180d507010b0544066029500ca245a4100c80d05480c1e2203040040c0c0d82c2c459038127540c0c0742e80d401107030140500c2c0c2a0a116541c2c0c0c1007505881c1c0024080d14102c0c584601c90191039062103d6900102080c1600789420ba90b80700e6582c0c0061414850022516000c000c10440040c080031081c1c09800001c48070303400e040c04d580c0341c1e00d01c440a050401e032003088002c41c01c80480c0d581941024000441c0412500c081000e000810b441e03c1010740003150408180b101e5004251140034244c8414180a10b0702080c44280c500840e07400d4003080061041215550282e0420904040001800c5151545034580545049000d070b030161a568400700d805d00c49180c002e440002c01d4090020b019082d985004002003114000501080c0c07507040c840741040e00c0510062507244851041c420554980c038060010100940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 217253830 1250 217252580 217252589
    0x30a09030b0a0603020f06220f030c15080c03090c1305060108060901050a06030e03070507060818030c10110d11190806030604060b1f03020a090b0c070302010f0201091704 75
    0x200c4501162032802c96201d110116503020300300214910f52001000312640044244400385051440d107200c4010000b01103c01030000d0b0718240001a041d424401141d0100c2d40220040e43d0310620500c4030103401401c01503202e0501c0812641d2942c0d13040e22181040c1d8074549564100c040f00407102c1087c032642d04003034411102a600e00390665a11001c0088481f02031040382d400c0040e030baa0512245209804c62421030f10940101c0f8a0882d0315650685044000d6108000192032001842005010a5403041c21520202c0095081415500440392501c04011001707440a0365415007400c40e4100c601a1044000c41c52403c01c000000a0300780200d5138050b002003c2da02060542c80850540a00c1420f401817a01400a181c1690786070b8680b17000b800603041840d4094507207401e21303c1325185005207140600d0150703005610742c0b10305240600400c01a42040c0d1070b0f0384007400384032440040014414103ca4091900d66000216800c0c180d0042a841c140a0010000031000c4803100ca15600188100c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 217255080 1250 217253830 217253843
    0x3020607030f1407080a14100303030c0801060206130f1a0a0b010318060e013903060305031911010f09110405071b0314070f06050610230c030a0903 65
    0x1c1044111042150f503c1200b0350500c4020102103200c84e48500500c035880580c680002850000c0443d422000e1081129420030302c405200c414400c041d03050194100104580c1064855541010800b9403140070041801c80c98841d41030005090012680f41d40c0310341500041179010950314488000321031141182d1002e43c8a061940001d00d951203032194402841308100386018113007040e650040584910241c00d105503403030f020194402d001c40000700300d0414440031004801d54141007040346000e07004144506051400e0020400724401001301e458240c0100d400702a01c44120b00700b0756001c100b22906007000d42c41d1855044084000da803040710301c580580e00030a205c1c414801000141c80044500300d00240c2503140194200d0202044610301e24440d04000750a5005ca40004007941c0001605503046200e61081000340109481074030741010b003d4a02080c40c2060900141140b6040d00b0121503515498030f20304940260301040d92003d12401e02940e599500040c002400100d4501003036800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 217256330 1250 217255080 217255091
    0x90703111b0c0f0109140405060d060c081e010e1909061d070905060303040b0a090503030d06051206041211070e04050f0d090f0b0a05090406090f11090f1212070302060703 75
    0x46601407140c04c000c40b014400480c0d0303035000310001e00014290180c881600a0130754003c1c18006092f9006409400c041c69407403240c24941101306c0d801180c401507088112509400060151340007003080c03a035001481860100341411141000d100038525500007504081c43c204c01c1c010303075a240010030112184194101d8210b1500c5117075400407180c0607515a40d141e802008100400d11003903001e00400407940c1020b894042c0e0780e0002c07a055a010910140c8025500c0c038092020b89001d40d00840039120030f0008014601d859640c0c024458102c655100a11003250001c82c0a0f030402c02ca02c0000e80f003000c05503452410b05107429681c6004014a03a25180a03091030048101d100d4a00d440486007030401d0340c41041d1401080d0b0079507600c000920700800008000c03143c080d0301c42d4000c050080040520010765100342442000c1154079503149503540107000c04c103480e1250f40d0200f102c0015002251708100c3d0140c03044210340307040e40c903105984e00082c1c00704051081c5a00030504a20a145a0318140074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 217257580 1250 217256330 217256359
    0x603050408070c0e1602030c1e030415030207021516080c01110c0303070f0224190905070302010801080d0c0618170409110705030706050c040f09090213020405090703111b0c 76
    0x2100d02170235241144c2c0c0e03446003407005003162800340c00080a191080c20b692030a5200c0107a6549000e80044200109800040380021407c100d220b006407040050340040c1890181c03400754224260504000d0180100403481c114111400c1d88020300d50101c400941d5510105001c4140d16608200c508002080c030100d00702c203180f030000c10f800c01c0e140503241d900b03000c0c0d08507500e07114140034016003440341107182804e0140390f200440c4500310400d0700500c000c0074410300d14030004040040503003112200ea08945540e15415401035004c8035540c1e4001d0340410a0071351440c0f5101703d500030410280c121225111100e00f0044050700070010740300140030a00c068003584504080503c50198000c00b80c0d4010031134040425255401140c000b89662030840c941b950300c04045101982d1034001c140782c02d546040940441ca48640c0d507070700303a091560041d03040a00d400001401c451005265806050311200b1400c00892264100c681041036404155402c0d000608020350310810554418001d94103007100c0403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 217258830 1250 217257580 217257583
    0x31d0a0c0801060f0e0a0603060e030915040503210c010204030c090b01080601080a021305060a05040f0509040201050a0c030306230414040803070e061614070f050a0603050408070c0e1602 82
    0x9950418441c5080b04d8509903421005201c0141405c6c1e0720341e501c0d00c0200010f11203014031023080c48091700840d100c255013010402c82040e40d442d2211652410482005592004103c20782c41842400558288881c40241c0800364420407c172100f5952002401104001b0350760a65000d8664601040280b00d064100558510005442d4103010402d00c038001a10300c0155001420529065050604015555400320b101500a0f0001c03502259000c10107000b080324180c24080142421a41840c542c14641c0000e00544207050081d400c00519001500905010341c10240090070070191428001903c001c2c0b041e400091612206d20440c1480c4000d0401000c10345900d0059401000b0245586c03201d881c25203030341900311030198000708240050650406003404c0b201c803581c021040e40402031044480031f403c045c4a50030460030108104002d21240d2a40c0c031610054400c503003400121a195400c0c040036a0040b100c0007000d01492420105036810600e007610f00070b5010180d0b139004044104801e9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 217260080 1250 217258830 217258841
    0xa0606020f030a051602030a060c111b0f0103050c1902010603020f0f1e030c0d0f0c060504030c03080d0e010f0e010606090e0c07210c02010206010b0f030604090201031d0a0c0801 78
    0x1c00048040c00318140500c004055000c405c2c2c030050490f4202031080c3d848205845482544c48089110381c514007109503001d11403690340d804a040038101d46100c002c0010881890000d4142c101580c800001e135141e00b0300022925417070b000d01c860b4030241d4202c0c44028003070003550004034011900980c1840990400390707902c2c88004801000c1d0092000c4c000690010403408003a0304c1c3d40340c0301d070b0341440082e500c1e103c2c066240c05006d403401255412a03420095942c2260303500c540700b0040c04110400c0465444240441540e902c220781690322034200d6603680140040b5592908254681031a103001c4180c03547c442502052420000d0010560384c2e80c05483e041100c2c0b148020403a40d25000842048174580200140d0b0b210b40c0310010352500d00742913510966030741c2150a0101b4405c500d09015903030100005d0b401404410500c0d0328010f50044034000c00d00000e442d1038061619900414116800b90300300e50a0480c1c4240d0015080010700344003030740d452403c4025a01541c0780c11011400c5001800f41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 217261330 1250 217260080 217260097
    0x3090901031202070b25110a06110601060507020306040f06090b0a0e0601090e0c1201020f27032d15070203040f09180b07050403050106060306090506031b06210a0606020f03 76
    0x2d03a02c8008064400300e1410301c0001c59003101040c2c7e0a40d40303a80d0b01ea840c44080d14607903640c440102c40502e0f90078075018042c0c0002d01400f500303004290040c0c3e40003035002c1e800f55011102240290b41c1c2c0c40c200c0d01a001440d0004c18110550041092424266215016104c00c28003120100c1e60303140e050004481e05a40012002d8100c01c00750324050809810f1000301000c0d00c1d00040c03a009400b20601c807903400030b1a000f140344041c0000c11030f8403852080c00c0081440e046000c0d20010b4170b0008814818001d03003402c02012903050b0178030036030720030248407401880c005645507070414505058025102d620601417005400c034541ea01088076000c80c401c00040c00065504115030395015119100d40741001411602044020080030000810a00402d0010401510046403450601c00c29800340c1d03400900d40e0340030f5405800b02250003d80c0307902d128410f00064400c9907407003903c0004205800d402d02c00c025201c429030401c1c010b0342e1803075501c10021210707660b0030b0301c910411407648140c50380f062500c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 217262580 1250 217261330 217261357
    0x307030506093306040902070201120501050a0909030c21030608031c0b151c1d07140d0c0e1012050715030e150106030e010e0709020a0203090901031202070b 69
    0x405049032207075000c40441641c1515504110030030407001030744e1035100e5000010705075008640070086503044080501180c01605050015604010210b116443c25104552066407a0000c0d0420316005007140c8000325002001802e240c450b41407500c16001000140d00d00181c5800d5001a40807004801e40b80e000d042201000b401d2089440c156010b81054103c5036401241d00b004041811011001400c2e90078212429200f44422403a002c0c044591207080000650a460280c00d181c5001191140559454085800000240d400490b500002810300209070749041030000c20344890742090036105001094017400460345a0312050400164070340001c02c16480035000f07100c0d82880d41c52038800c003050f5140024a842d4030307a11040c604411101c2e043d581c4010340c401803010300d5040c0604a120410300c002404154528859150744003014441c800840390b001c40c040009031310900480c4c0d84444018041c0d205940c40b401c001ca8400d050241c41000b51041260020b0050500c1d01030ba41e5600c618030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 217263830 1250 217262580 217262611
    0x306051003200c160e040302100908090405090c1c17090105031b070f120e04060f050103090f061509050609070e010806040905010c02240903030c0705070b0a0302030703050609 77
    0x82c10781c00e54110f00316414050168070218200c0014000c0f8040042c94001120f102e90704013803d02904220401075414142803c0055550200760480100c030003406e8265400502540c40340132650400c0000f040c1c15130f000031002c458544400310540c848111601239240480f11018280e00ca62052003155445404120140700144100d601c0c11414101034070041c40151500e001a03942c0382c441c620320402181c410174110081c860740d03a84200e01c1455030109a03401c004407030a160300c401d03e4841c584529810103031900440d01c10800e4040c441500301364800001d00400c1078552030400007200d030340603400c00186800e00041d06440d100322101d014604a407203a00380716503504011912981c005101072b821980342c8040900041003441440382c10070007503020308440307400c2d0210412055502180c00f05400d11420610a024201104503600300c00d682d040c5550f241c80c030786080790410202e030b80a400500408a24410700c1509034000b140300c0c40c00c5603005c100b1503032020208000d81506440c4d40c26040041d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 217265080 1250 217263830 217263881
    0x1d030d0f022808180301020304031205090c01091403010e0f0a0b0a050c0d090318030b070e01050310140111060c07141504060f090b010b0c01060815150406080d0306051003 75
    0x1a005003200303c1c4d5410000b8000e001080420b09980c0255400c4000130703410090070401c80b10070302c101c40c0c104515002410280525100080c12142203004545600c901405081403d5a09500815104280c0004e68941d00d071940b00d52034807440000c806864050456000969003039079403148a1041c090b0200e07450804c218900d030b0000911200808406001c0a030030305034000d040c54881e0200552199a003072403545040e40e802851840019402c5040c03202c10300070b1102120b850640d11003a02c01e0060189030f01c4140c8401210300110200ca004182c2c09454140501d545501c40203044132801740c42d001c0480e48184540940c2c030207030b1030b2081c154242010042400201c032a0801e4118221112011920684646451451180030382c0020300b40180014044804203080c050800204040c2c0085c0c00f41c2422800040c2e900040100344003003102d44404105103030b80e01d80e4000c2e4041c1003818200c5005034096000540142054041c451250384d090340c500b902648a0301401490804195855041d9200c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 217266187 1107 217265080 217265093
    0x14030f040303110c06011520010b011b02030339030c0f0601030209130602040b0c060613113007050a0305060103060f061d030d0f0228 59
    0x300b40491354408070003140f01411560743d120042d00240072280e04036255540d6400040c8070722a00000c0003504001580f2902c0b201400ba01c5403024121000c050f00310006520100a50551040100b0214030003009888a0380140103400c030130401054800ca0402c015145801c5000c80d0300c00b0644000340c480411203443e407803013558080e1005504640110710300c12001000b8120300b840680c01d4008100d031990441e80140605000c0c030313841c1c845002c0c103a5250901520250301c150550000c81000314240d100e80088903010154032441c200c0c0740e01c40b11140040c920032424845821301b603a1004209901c0d032880c8215006d41da41907607618141d2026040b520302400d000e0400d8640034003807006503a0441d50009403141414001d03c0108500d0410441c00b0034402c4485e050b0284100342c0740b4454010740e449003e161030760259990000091062241000181c5144681c0034034080c40340042901c = true := by decide +kernel

theorem cover : BRFrame.Cov 217086330 217266187 := by
  have h0 := BRFrame.cov_init 217086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 217086330 ≤ n) (h2 : n < 217266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
