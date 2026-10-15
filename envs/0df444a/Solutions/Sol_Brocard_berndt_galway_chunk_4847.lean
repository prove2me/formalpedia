-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4847
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:32.611884+00:00
-- url     : https://prove2.me/submissions/dbc0df99-35b8-49a9-80b3-f7f35aa5c171

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 871582733 ≤ n < 871762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 871583983 1250 871582733 871582757
    0x30d090501020706230c0c01140405092205100516020703020307030609030203160f06240302060a0e060c01051f0305030f090409060c08150d02090a1a1f 67
    0x44022605000315801608038040030030182d401091040301c4503040a03500383c0f418a11001407003407504104d030480d5160b802050807403141d50300459120540d08000c840c142c9000c1c1004082545580d018004c41c0b12082800c802c0c0c10b24844268907040c5103139018080d41c29075038882403407002a00f01940d440c085c04044030901e1584a000290703042c1113980c00750203841c10a00e952200760041640d0001901980020842020520503030038000100ca4410b0b59020f10070340b1242850f9044034428007001000b0030200ca41220110b144800f11011a54100c1d035050350b55400c41011201100c2842448cd040500440c00c1580944103400880c4030341c2c0660f07010b00508800d0090200c903810284006006504104100c9c141c140c1040010301d00060054000303e80c111041d0b44134811101410f0303035000002c1c40342c0140003080d24007920808035108200c4848011b0742007a00064111900a0701510806550303084c600b010b031280001c0d0f1180014001c04039682481e80540300c0c0440120710402c8800920b07030050341 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 871585233 1250 871583983 871583987
    0x70215010b0a02120c0102040807060906021e06060409050c041503020411030601050703230d020d0b120c010305060d06140f16120b0d02040e0d030510150c08070c0303030b030d 77
    0x550801d64443d4000d01c601c0f0207800c582e000c02e9026180711035040d50208004103a500d81008040020324140ea0f61071216803504074020b05000104030880c0200280c03c200d0501d1550028290ba000102207400150200d414030300189001100000c450b005803c103200040b0368502c0c1c070300f1072040302d009480c1032100c018a0b8501c482207100494142d400324105124510200b4031560f10074403007000703200c400b41c0f084201c126411029089551030289d80ba03000104601000068054811074400070b4504012014107c03c02c80d840e09224801c103810981d81c0c10001d007a42d6906502044100e800c09010020046035040c40145a01b0031158004c0340040c0c6070208030044c0c0703c100c0050a204041d5204412980c4080d09100a000030405203a4009800c2094401507520780c401d90400e0040c000042c9010321882d400038007a240000d102c0040750b05440340400444a10910700d48114106161650010144d031826886d01d000700303900a88440e880384008010180c165200102c03a039401c60860740240000041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 871586483 1250 871585233 871585237
    0xf060c05150f041704081c03140606030a020f090d050a02120c01051207030f0509160e240a1d01060e1e0103110d090f02010906080f06190905070215010b 67
    0x7580c500401e003000160100303520b1141c4c02c00b075002d0b1019841c640b659a2610619011001103034801c2d100494040c441460381510a070b003121940c2c42e2000c000d80c606000010698040107102e20522900001d410b0f00d0910110101d8a025000a04111040c1d9490608a82c2c81114801c101e001e000041d0103001c50010014840707002082c161b4410786881c2114079140f24805026000c10305258580c020851b20710058003426104031041001003061141202d60303040650302d81e0b88044a010110814842242903600d191202d511503203143d11808907020b4041094000c0e2940046140c40076031448644214021413200e04a0708141c2c1c440c00c409280a0410001c20184000c074907002c0701005a11016500a030822180c280d00d034034915082410320b402c41c0c0c082e80c002540407a40b05900320070600c115a040a41708015103460703d40801e03245004503501c8a5104040d210303611076500c02140a80009070014850090010080305200d20308058202a5640b000c910046050000c01400400c0c08941041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 871587733 1250 871586483 871586491
    0xa080f12040b04050402090a080105040f110a0b1b07031403030a0605011b1113110c07060e0109090e0304030807080d06091a0d0c031208010810180b07090f060c0515 72
    0x80070310f000d162008120013984407185540d0080000c1000240c00700e000c1c81450301c114040c0c400349044207e81e00c0c0c06813509903580d010a1180c001480c09006203900700f01500e2140c4550441c09034002d0022241910300b00d02540010071001c1c80d40640102e030f1401202450280048407014082e26450b07000656900104c501010414541035032801e003c69020400c090010b600508481140c0d21902c2e002c10649440c1d00755000c4840700068841c90301d003020000c51303009096520707203550300321404130000342000c029108a005c0b00341c0f9030011461408091003280c0040d0340c451481650740c030461038261010380203010030700c0780d103490844001000c00d140c0c000c51008444d81e10503000005080400c011001301201e0342034454a00d00c040120004441d6400c0c102c6e90781451300d5500b903540c941a0098500081050500030311070400d07082015100310200566426940040042110356620404a0342d1011550007141690484a4000b03505c0385c0010801d8040e034041c138281e65200d50916108042c54606407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 871588983 1250 871587733 871587749
    0x1a070201091121070f050f0303120f0a0204180b040506121c050403080d020301150908030d1a040c08180303090c060c03120a0b0a141503060604050a080f1204 69
    0x1800d1000c3d140502c10201072403020b5008188034450451024941501078020a0500c0041c2d602070102d85800840c4100c3d011044000351701d0520b801000100c8040702405210341024004003090800419405030750141c04103109504404048010100250440786000c50046140101044040c20058003c0c00340d035112000401410020503c443d81180d64a40000300300001804040001041d00000b0040d000c4a0180580c0f01d505104044040310940300c0c1c044140a00081c007001084400f1068400c1016030000001e4400304400e151454403a64181440d4403628144505080725004010680151508c0c03c4e514501e18603401c4040d5a0712090f0350788181940030803001c0c030031490041c004000940866041d40c0c02c11012214039201e00b40140c640a44042c1c0700d03110202d69040c0200080003c040090100c5000d501c4000860802c03095040746c82041c000010010f1519210700044070000c00014091b000d5150703a03101c0c0300b902c4440001c1030b12101e000f2a0202056202084143c0d02500c45074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 871590233 1250 871588983 871589003
    0xe01020a020c010e04060503060c030405010e190b04060207082208010b0a170c09160206070c08090f01260a0b0409021c0c0e01330c03080a02161a07020109 68
    0x1c01d0041d0740004c00c6400256101d40c4512000c80c3c56102030088a0241c81c85001c09900ca04240c501982540e11414407001c140d40961180d520021189100c0416a904603055040c01d0f03d079400c1c00c40180c45414806000107100094610100f01420319105007400c4501c0c0c1e100b03007a0b4444110034240c50300c803481150702031440c0c0d03000d2203a014249100b4264880140890f681c2c2260400400c0d1803031421240041e140e0040d00303445051030340521940354841d8207442e007202c5601040e0b40b000c01500400405c1e0f8010440b1032244c2613180d00071485421646200080c507030422100803000c6005c104100c0f0200300745800c21408028074100350080002c2541c3c0202440350900c2141c403c0c03548802c0708070b010f454000c05000c0000b41c0480e6609024083d00f10318540c6816000006040681110904c854098142c0141c0c1c08030289030b446003010112550501d00b0032420f0704da4041500290080c10002040f1a68401c4904100500f000c8241c00c8c0e9070055802c00d0f200e54588405908881e60741102a000b0031071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 871591483 1250 871590233 871590253
    0x8070b01210b0a02041e0603060b0310030602090f040f09030212030108030304020105340b1b1c1b0215090601030507031e0c0605031f120305070f20040e01020a02 71
    0x80150210391043c41c110340181415900c0ca0129030450f811410035131110701c3c5900a0161a0781806440c018050348800d0500d1802c0c00741c4090401d000c3c910019000c29404035032545a56a011603144812070300401c18441400d001e440d420041540c0a002c0f005846852107811040d0b40b10000d6a04032504040035504503695500159295440309000d40c4500e0603e40300300851907024544c21549210514052451001a1604c0940c1c1031028003550500900d034585003c541e8090702c110741c20b0000004000e0481300d61000b04001070a008206a99000039043d0f84c40201540000c030011084c500225402440e113600c40d44a491b03120a01001c0c0c040d401c0700c903051000c90180054400880004c044640f48403119441d8514000d003140c1001000403000010301038100c41080c1c04a980301d0081c003205a140c0d1911340306550a640d251801424041d001c079151052007804a201410660020790f5400480240c2100540940301c0d441403511581c51300844001d071802c14400da6440c08a079400a081c0102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 871592733 1250 871591483 871591493
    0x60905030f07170a200907030207020306070e031f2a02120a0c2001025b09020a09060b0702090c09030f0a05191703040515010308070b0121 61
    0x102c202038030f00184100100c000c0011400041e001e58400d580807248981c42d11301301041403006001c1e0808003098014001f20000d82d80c040381140d0406000c4c2001202481180f0100c3c4c01c0400841c0f5401c00c0e061740310344210300c00f012900000c5800c80324800c8084c09100b043c10b580f54008e8054002d20060f8480c840700d00d07504940718000c0c64444801c4c18020813070210781d41e1354007003e02950400c800ca002c0c001c0c880d84003560100800d51100707101c1078003e400b01c1c4525000c030602c031000d560b003410b0080c16002c00c1244240c60004032640420a40701803c28600c42c500031501405801d68224040c003d01d020002c0e06028030b02c0f40b841916800641e0074030304811902003100e50000500501c40100c010043c6890954042000c0310705040c070300c03024020050030342c05c00710304080110058411400c045034182c00011006a644030750740d012486501c0e129240c030305005d0300d805640c144001070241c0c0d01c3c00100a004500c0044c0000c82d02c5a920811283c1e240c42c501d0300303452080c1c400c0305501c8144000d4200024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 871593983 1250 871592733 871592759
    0x7020906060f04090c140c030901020d0e030d0c0f050124091e3c1404020105030606130914010312020c0f0402070501110708130e0702030316031e0501060905030f07 72
    0x21100b1b103410448100c00710b41c817041c9680041c102c0c1c41ea035400001d403c01d60b945c0500004c8002080c50030300c03c1e0070328003240100340c60f09c000001803410003468440942c10014060007554190b45c101c8000c00103c42043e4804042032011422901001f02000e00000c01203064001e0307000d05110201c52501030000903ca0b2030252102400045248101086c3c10758101006080d08500c00155005c00c15071100d60300c01c3e54100c0d80c2d46004049100020723010040980d0b00700d4112600104140c950980d103514440c58040c41c020356408c00203495050411500810207102c01150583e070041c403141a0081c421481070780d80703d68003260250040401c0c00441e845240c9940038000d824022000420600400350310301c2410f610403a000c503482c010116000b40940b55642c0d07800003500c035000021406086c039405c060755074000200041ca0020824420310300e2184203410414036001040c0c883d9044420070006600039100c01d0080744002240d440000941d860001030382100c03003a00c1405003000300d042000d0343da024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 871595233 1250 871593983 871594001
    0x40212060919032d0909150b03041e0c0501080f040b1f1a22120204090204090204091119030819050408060703020403151e0f0e030f07020906060f0409 66
    0x200c1004080803211112095a1081002016504c2d00b2038005041000d4154000d07a0480b04246103441103081191000130700350400d603829001302a0300c950b00e9282140540b005900390401c0d00214440c44810480e40318010015180d090301d0f0341b0003569503200100000302c1300311809442c0505000104074200c0f12210300124001c030042116108175240e12408114140359410f035803050b000000c1c1031003100041082c4100b40040b5084c0a10081e2810758400e081558401008e07110f140c1d6039000701c04655407035105075901070780a0002c0c0078103c0c584c200280e410f03000d0140c1d1030160240c017030311a4410695000600540303510015590803c40c5000c10140a02080031020052101c10400400c0c00602040300300d02c0707010180d4000d41d4403403e61030101e140408240d03c029000741003601a030385090f80325a8a601c0211035900c001495210780d000302020301081101345603a03000006c2c551106e10b00c800010640d150080d110b14885444250030300145110b03400c45080c5903031090000b40301e00c0502d03400c26200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 871596483 1250 871595233 871595237
    0x5010b0702131a04180b06010807051c020904050915010b0f0708070206070606030f170307091502120406030e01111e130503060a02030a14010b090d23010504021206091903 75
    0xf00018240414102c40d070280e00001c002c04000c8444040240302158507500981c203280c0507490382040540600503000b00441c0c0d00c1900088011801551001e6043c0c801c0400001c00600803810403c900c40d4070f90600075042c031040c101b480004110b040880d000c0b00e0009040d5906586131503076544079503107981c20100b0201d0784a0010408000820010f01402001c2c50140030014110141d0f8507020380e054004440f403111080091007001b80c4190030800c030300c0c2240d000c1d01700c001c1008000401241130682c143c000a007002c0f404540403a042e580740c1d200d08290513195008015503503c0c5150030b943c41c011500e8854032510110f00510034000d90402421074011501c4010580c00e44690000703044c00400c84042e00c04a6002c4104138071410940203e100715859100352036450750504c503004031240b02c0c100d1114007a98000c115001041f180e1840c080d0010b100d0203000c244c0b0f0040302d80d100c0c042c9c8400e6505030700c591150500015601404520700d809000c0c914014550010104584003401034404810b0381 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 871597733 1250 871596483 871596521
    0x503010614040302210d0309030f112a040c02010203060d0f020a080106080d080f0603070e19061403250521061510090b07081b03040b04050405010b070213 68
    0x300503159051120b1a0409850900c20171032021103201e071404100c07200343d408041c2054000c20200307809c0b101441c07040b11207291001d10074075002021403510f00d8030550400c003002900e40000e100c0c050b900850169110481d82806030b000c005100724240d000131303540346034001c011220074000940420822089188080c05900b091551404800d0840c1c600703900c80e0351990405804a0300072940030042d00d80c4100320325a2801142480d40102c0d81d2100780d80203120620440c80e000c20b1909024400100503960700d00001e00003152503090707139000f0301c0c400441c01d4001d1241c40740003c40c04c0000e280d240755907410303825550a294580010005c0c1040a60400f030500c800001c0140d03c0c02805126452080307040804241040f401807052240c01819182c000c010484907020034071103010000300b2505140c0e00a5800ba4a0f0b65600403241c0301d00d00b212860780346620000a0000300c0c2c010180c0038100700c910444041000340e90b40d6100c0307506c41c800e0490003944800040c102400111050b0f022810325601002c0e140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 871598983 1250 871597733 871597739
    0x1903090b0418060b0a0c06110c0a03050c06010e43170105010212070b15210c0f10120b040f02040806150a0e18010c031b0e01050301061404 61
    0x89900c540c1182028852000102071048030701e015000090035404d031014075120840000608061000304000c000607200c0040512402c030391b4046d40c0e107000249064540301700262030090603507401b000218505000b14000000c0303040254800c2440f500902c207080020003185903459000300303449461040903018458400b14803070845811440080c03100d4a9148000044480401d0142c174141e01050456000d6140d00f8180c06d109819604010303407124032a4032940312100ca481541c01d040c0c203c550007540000c3d880b11b0b00d0f4012441900a9403003102030f148130400300300c144808014124013507500201c3e1644502c8503a481147e010210340e158040014800345004009029940c20720744040e40c0300d8001c14240007006090243c981c100f0070403a85c1032010040840802d8030001700784a513144c00503030000002c50381180e04524140e2140000000c01c12140000005001440341600b0540c00055880785540606d0180c0041906108142c64a90441e0701c0d1600440c0c958240450250364900148000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 871600233 1250 871598983 871598999
    0x9041401061e06122009060403020402031e09060408120c16050c040e0105010e0604020a0912080403030801290306060c0a0507061418040504060908071b060f02190309 73
    0x107202149582c12940d04841c54201d00804613100e400e0760300400d5240280012504d010f9410400e10902d254604544802e41c03a00000d0103030060f80c1c406504580004104044440042420b04658950302e41c0c800e865162085041d03a220801c46008080707560401150a402410600d15070780011b1070b17032805103860001e2003900c0d0b04440b020f604039407a42c407900882a05203018000c86400c028424020089585400e10380030303091501a0895018a50004809a11a00c5031940c4401f500700354038480d40402c1c1510344140c06901030700c800d0340025150f400100d56440414041180e07450445502c0300c0300300c80050300d46941e41c0702603e41039010f88204002c1400c0d140c107103c0758080501400140c5101850b0000107032500d500d94800140402d0208005203140e5080c145002c803289058400203055901ca240040c010428441d015100308404a807441c20811130010749000f5004100e618003c0b641d60359003e840701d01d200e000070000360700b1000c443c241001150034401e102e00c0c0a450302500c61540c840d05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 871601483 1250 871600233 871600259
    0x1060e12010c0e0a081605190e040c030b060109050d14010b0a09060906060c030203041203020a140606010f14040e0417030403020d020c0102070308030601030507140f0c1504020904140106 82
    0x2881c4046610400b442030f0301d1810f181240000d1142a01070b1010f600b000d0b40351010650340d40134103031060740d00c10b50380300c41e11076891504405410f08204031501818142072500540f1001d01c0212000000c03480001c00b10351085440c1011240003070b04012040703041d50b640c030484100c1c80c1c0c003040b510366039820708000e190350310703002c0a0040a08007000241030b401e003102c640c01d980250b0010014000c40610301f200003980082110b0803940d03028101030a40c00d0070316089040c0b15000070003505800c034840c1d01c030f24040d001280040c00303007001340c841108415641100381e03813081c0c21a95115003117009100c20459011003008142d4040e106128060422040c9000780030b20360415203060340180e118410500c002c40c3c040240a10700740b000d0004020070751030b6580d10003561000038200c90405480d1030200780d905000e141e800450007001c1103d00c0d210b0002c00a0074083d030b0003c9040b200d00c0d104c0c05005407025807100701418041c40c0c02030180310081d60741d51201c0f400c840411411880c559664070000030400140c0c98 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 871602733 1250 871601483 871601501
    0x31b050f010c0f020705091605031b07030915021f1a10110609030313031202160b06010201140f012c0f0610050a08010504050a06030f06090204060803070b01060e1201 73
    0x4070514840f0f4488002441c02d00ea50700880c1c016541e28007408061a01c1074422041c4907841e1070b00c60b44d40e5484d0680720781007104029800328403000226007113040607041144481900e4810f00d0b800400303666000d0072686d401070001604803801090144900c00380341030704800400c0d000d80022015030a4240c011132145141c80d420034001520350012101803403414001d0300c0d000a040002035042d810b10654031607418070300010040038414072002480c409003803601070380c403248080108030043c02143e05124020303031000c854040c01075180c01c1c034100340d00c24824807180c065a0703100c0341030820b070782001d04c0441c003a1280d540100b005500c010f012400013000d40200d40c0700d071001780b00c101d11900300603013803040b18200110190240241440284140c603804a01c4504446040300c0124013615643c400000414a0707800c094001d03580d00300103500340318007500a0b2140e0f0307100f6a01006031507a200d0b0b0464490040e00320050001041c0710040180e6889901ca05c90710410040207090380e2109041c9407802c50b403d00d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 871603983 1250 871602733 871602737
    0x10b030108060c0703050a1b0f0c0303140c03090d060209120109030f1b02100e060706240b0414040b040c030c020111040f0b13270b030a031b050f010c 66
    0x14001c00c44140026600a44014149420b241e0130365409011801491101c6040005142d502580c1c03004265503000895000300f5400d40030303400e40c01e104650760a80c0c0401e40104003c1d12285c4110201402125501c140d428051801c281556003004400c4110312000d440c981d0302031200e0200780d078840f0b4001c0c0070403043c01c2c00010803200c82d00c0c025040f107540310f4920083c0015000b410017440781501214030b8640c1d0440d450f0584180500080c0c0302650689506600302c080410100208001e039070080c502c0f1808412050b8042c165140000b1000d0315034000c1801001080c00100f1046104403500300c0001001440491940700450120f001ca07440301100100203522031b25501404c580a02c24803604042444485161a082541c0012200200d00c50446a158009841090288107144500c01782035442c442d107203600c140700b002c4c1c1c05a0050f288c480c48868035124108846240002c1c800aa4950603201c4e8489500c80c134500e11a980440c4005841074060040068040c850030f100707d0b04040015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 871605233 1250 871603983 871603987
    0x8190207030c06050a20100203180717150a02070f0f1203050408030105101403011707090e0d08061206190e010908030a02090a12050619140105100207030803010b 71
    0x541450340002e0b1031075000b1400e0010802060000940c0300b006541c400d602580306680400071501581d2800f40510b014100c014404014800100c941e8020408180102c20440c1d1903a82c84403a101501041ca480c0d913625507208810f0b14410a1051b41c1040d4041883e00006051503c2074540100305150500b044400c07a5415085000304500b82003164040d006501d0204074071728099030f4a00320380c4818002c01c0d214495002e1702e0000b0902c1850580c803895040d054281d125691410307260f203403541201c082141400303041000702d0a2a0304d40f1400e0103200d02d4a008090a03c007825064524003409040c9a400140e610405c2d840c004003040300a0280c0900c42603403c00e4012055040100d451102084c0c1250341003e00000100d5088001c0d03d40220781e4110040c0d440d03a402d00002c00c1e030070b4154000e000b01d601e50600c0c0420701002149252080c0944ca0071410401550051401103c001071181d001c000e9240340140b082c0e003032816601c0c81c910000c5c01220649503d031307240e1800a0b00247c0c8242503803c80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 871606483 1250 871605233 871605239
    0x2706040c090c020105102904141807120911100e1509010909020a05070506040503070219060c0b0702010623190602030d09052d0c2b08190207 62
    0xa51161502c12038580c4020031140c100000d080e00f41402c00e1049201d140702c0310001d440b4141c0225600364008100c010324940d0f565880c001c4800030800164480d1080314040890a103c0c0c2d0701c110345da849100f6540e20305181c9004584140024142c100781503e0141058000c664142c840c0746024000040076100c039504840441b040100740344105000020f0070005200da450503903000420101924600701025860f00302c44c0b40d0440d00c81c0a620b0000d0180d02c00c0c80c05000900001200500754640246d50150040c100c11558a11840c0709200d06e2001035901050080030484442c0300603040304075803001260144d82c405080900039081c115001550540c410a03800c2c070301d400c040c0c82e584860b00d480e43c885c04514046000e501c83c05010f01907686d0301e440d002184100b0905000d0010a04080040594410000384c6c9614aa02d05c07090200a580300e44a503d00c00303854014014000e860750703401d0151100e000400c0c51112901090022100d44030180b1060000d244524070601c09040e8503402002c078580303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 871607733 1250 871606483 871606499
    0x121020714062712030c07050706080f010518070f120f0b180906010b070606080312071b05190609060c111605090123030706050408010e030405092706040c 68
    0x900f40c1542991a036045a070308010240461540c003400c0322695640e8407540c1d510b000b03a07070510032000c00800500031058041603283c1c00110b060700505103080a041c0036030703c81013030014100c001e054008111903050300041c079a5100d806294004100c40c540000800f40d115800d10507500b507141000742891f128981c5030f8003401e00c007059444075050030900a0041c240b812019031591418010300d07080303500000c1d00c80c0c14044190000401001e440301142d0361084040025110000d040d108040090b541d0b4400c031907483d4108100b1080b06410102904413007580341c03c0200b91038001c00c011101e070303525044060045006031042c1360303100348152100c400f119042198a0704280b5641184890074052100600254071000a01410364640201c0c0700e00c00a080c01665410035605214564113204114020900580c413002420441e120107000b0301000d080d0010882d1640594000d058100078800000b604006031b0002134000c0403940519050940742c030b41c0c9007508249003190f040e1317209140c04504020002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 871608983 1250 871607733 871607761
    0x1a040e0717011506230c011401090209090a0f09080409020c0c18130606171b12150a090c0305010203060102160b1b0f0109031d06030105012102071406 66
    0x118040000f080740d82201d81c10883c9910030f5004000c1001045991744440081c1a402d07550340141c401c00481e11345200c0040c8034080c194076850381c03840c0d00c03010000052002e480d0080c0c5059040081400800b941c1d0801020014070508080410407616105400089100c007001007020341070000e0090b80d00d0100c01400b5103000f20302c0800d40d00030101441222141c03520710440d95004543c1030502c1101c00308c40e04003000500025000f540e00b00015040c5034407031800010340d4148014001605e000c04181d10340401103000b46130b40000000341c2020010080031103c40e1501070f40841d8210000944540c180c641c090b500029400131030f0183c4d40041230204135a0104503640d0860311944410300310b030307060142c02d200901580c46000030365100e070360314501704010920140400d0351040b4002c0110f060300d41002000500d0006064105090007001d8072040e040032000c407810703140180c450440000c0000c1404000320440d00b48081c00700d5003400f42c68002844001420f40f110301d100002c0c826810132610b07580700301c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 871610233 1250 871608983 871609019
    0x40602070812090a0909050c0a08061602061009050a0e12030708090303160e01030f051609080d0912050a050a20030a12030e07080a06090519080d1a040e07 68
    0x1e80010303c8084003580d900c1c060740054a48050f004610845c55103409450312107280c650682c0704ea12801c0100b07181e1000103105101d801c00011102d00c040110009030307103504042d215144a0007402c07000f030203203946603080070b40c210fa04c216000a0009201c60860304280b04214212088d1a0000074440c4040d8014902d540203941b14005c0c40c0745003880040c0403500010b407109002449650504e5100f660300944c00010484403105003442030740b805800003120380c0b0082e032100b03000c0341103140d01186600002846400003103c54440d5041c0078140840f1000d001003001c400c803a14800c031604c41c00015030910035142424800c401020060391600040304581c00b40341c014500075031102d50690082040c81c0780451070407485040000c0c1c1d41c00424041c6040201c16001071070030b4407032184840c1c100140c0e82d00070110719001c0d070103850911030052940c0c240e9002d000b10180010000f0711044015a40c0d44d031155402106e10245045500f00700e50201c0e0682d40003070300050507600b00082c100b000b144e600d0800224 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 871611483 1250 871610233 871610263
    0x90c0c060c0a080a0f0e0601080309130509070b070c032a05090403020606010305091615030623150c010f060905090a03080114030111030a02091009120b060a0504020406020708 77
    0x4102c681d4600a140d10310042c1030600c0755494901e094a22074086d444100102120070640b29150b03110304d1140d54035072150b54401e016500d0044071a50400c20352048074082c5120201400102c1d1411542742c80d00d810051069030030b14210040080000c070b400700c0c1240340c14441150505030641031040d243d403249042c1d01140c010f11450b820800000d9010a01590013402400c00103107680794103150618104030401c03841e405e644400320124258034595205900074095650520240c0c1d101c150510844100d101c0e408011401d40345103800c00d103491400300814070700400c2d20340d080001d000340c0642174030040c9045090701a90f401007441380c0c03c29030003540da002c840500105034425450790018030030001403140704140d451220006c00195403c0d0000140c0034a45a8181d85908044650360001d50003a0406441740703051080c403091341340c0909007c1c402c40d110b00703210000c8140f003903c4440045400400203a40080924000306a5a0395031003c2d1001e00a1507009200160400543d14608880140c241c2d007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 871612733 1250 871611483 871611487
    0x10e0105070b160e1005070615210f0b0c03090610060f050d020d060b04180c05120a0902030f07080105060a050d080f040b03041a150f0d02030705090c0c060c 69
    0xb01c0e001d0503030709030820181000300c0d10800c2d103200c00b21500c0c0b0721038501c5035100c203001e90340c1400945d10070081d14040f030080000700079a810050044201c0030951146a0f84800b207800517815004403103100148140c010030070860000c15541c2c1d4600086001c6a80e106980804410322900210800119a200181d801c070200b205080c4000588403514001e240c6081010002d03100d1610321581d01607800e606403030442400060307100c1c01c565143e44c01034003070f055005181030001486200140101b2905a43c00e465040c0b0f007903071403103d0181c400001800550300c191180b41d4500142c504000003031801003100d000d4424603050600b0542580c5014000754443c50202c9400e0180d0b03030701c0c507003011041684400390f07542e141c0f17aa2104481c54000c0b03500c58005c407e008001c0006021040764013524000c004480d82280d9a03c10406561406042507c81e8000a07030100400460400113041c0c42000c0c001011541015a540f00250445200b1200420f074410041203203050b00c3c4040121680100310600d60394 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 871613983 1250 871612733 871612747
    0xf230d1a150a0909181401050112110d150f2f070318120201120527030903030f07050705030d08041e02060d291e01020f0d02060105010e0105 62
    0x1c4000081c50300380041200001041c011a900920070b9000425888106000310014410000c20501c122641900e18203100030700180282d5061007024161003030100065907080c81a190b46e41e070214030703007056900081000088008202081128098510f030b540020540b02c504509807000d031102d418030401482800800d807400205072036030b02c0424482901c40070361680c0050500b15000f441040c3c40ca42e07c0c0302e00300e8001c00d4042c0c141c80c00410241c000e807260b0020300ca111080008403002200c4002503520140b40c02207410155644001c81c2051610803a410700455100107425544603402087c0140c9002441d2010402c0520103540240022070103021722125000c00903114560007040104656114407003101810140f0f030720100303001d801501c40c41e00c500c408050203008001201881141060720042405040326152a0411031a806080300e4480d94020f151440708920300200241503006582010081c03500402c4860b41c0e2807050303030080486500d0a0009417a002000d4051410070a00300908 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 871615233 1250 871613983 871613989
    0x906020705010b12031812192a0602030910091a09040c210507020111040305030a0905062502030c1801032108070c0c090f020d05090f07060f230d1a 65
    0x703820b622009441d400e00551f80d845a081c18a004c03a14800310109965800d04140b001c0b66050380581514558200301400a8440c00c500c050380900c2408010380c0100300340304041c10401c2c200f1440e02220304095004649541040c0700c2407032901c04603911010040740b4400146458000e45a0070b0120741840c00b01e100d854140c490140320301d61404000f098030b5002241c041d610075440160100203c203085915a03840380f9240d902e9922040640c0700155031841c0201d10b519002c3d08464140d03c00d074800512240f21800051084401101c1c140d0381402100744400b00c0d612004003010f407250701c031030101c0d01030341c19460211807140611040c2c5400380120030201c2e40031034220b04103642090040c1000701c1504141d1030719040f141c0c645d4200e0b401007030402070b40d01d1100c030803a006048020040d0b1401d02607650384150445e0380d05d0740703040c03440d006520068003044802e00942d10f09600b0700c2d05203412600406405200304a80110403040e901c14200080d183c14080594400c4000e0f9810300b4018404c051050000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 871616483 1250 871615233 871615267
    0x91816230402033706060e010206070908101112010b070323180402071b1a16030302090310021801080a1401030303020309010f06080f0c060703090b0306040906020705010b1203 77
    0x11070400700031660131000c445a003088004401981e0050203100c0c041d201c450060081e5042e184140c05031150794013040d2180d01405405056594060080403109504d40859010f015a00000510420100801c1a1450380c092080703000e08010001c540d51028149402400320b10614540031600c01b4250b07158001c000c904003102c680b20a43c1400413000040000094000c0c40f8050008018100a0610b1051500050a00011951190310300d4500041074440349006110b04281404074161000800300082e000368003614a400e00a01181d41a040c20200c14013203a02220005041c80541c41181ea0103681c092905030340915032071010b00107002c04c04054691a04103000013018141c020001504048095000d1420140f108000380815595400703980c2e1140a00250b035a800d00940600031124203203a411500c0b0581d0560f14000ea03285082405040e0b03420260400c0d51058450701400041281d900250030501d000c1c000005046040d00200500703400d0f25803900809030005d01049860b0355544103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 871617733 1250 871616483 871616521
    0xd0b090f040c0b0c06040f0c1e0e01080703051203071107060216151d01021f1a0102010e0d18151206061416080904141b040509181623040203 62
    0x1041e200c400600703241c50540000150270114024840384c0300120144c04413003441c02222003507003656150f42d8980c030304203898014601010b0081d0b440509200707400400040215403141840c0b400d458900e02d1503500c5818180d80d503000300300603404185004d1440c613019254000403c5911035810444221300c01c0a030a98504d02840700c1c0e0106001101079203a4003d02c6150f2907034040e42c403201d1040c550402c01000070720f07100c50020002c0f05640b201804035401449841d5807045a4002028904070040c0304075803c0aa010741000c400311700c44400100c40d0100b90728050b41d1019903e81e1601501c0c42c0074a10222901a4080c04c10800c3c440700401150340300c4c4003190340c0040880c400400c2400e0500784905c10b07215400c0e40c1600180f412120150000c800c019083c000c12a4188540b81c0401c4c140b642074040c00b890255541c03112004012074410b000395000300c1c10380901c0c0c03400d50300d0000032504c15240f10511a800f08000c0c040c825050020350740d01265441c0b5106040344c046083d41008910320141082d006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 871618983 1250 871617733 871617743
    0x120d06140a05010f09090e07080f07030b04080705070306020a0806030c09190c11071205070e010f2c0f01060e040515060705030c07030c03030e030d0c0201050d0b090f040c0b0c0604 79
    0x1307100881445000e206014000340c440134405001140707441d50340c1f410188984a024001d442c03542c0c54014000c19010201d03078114800c0c8a06445a89072021a5801641e04480f03a114600002001403002d0000d000e5400d903030b485514013850070000703060500320f50b1551548207546130b0080141111842503252100280c1d0340000400b0f60408405640300c180402d20019544240880080c0d0240c070700000307141e030303d20543c1a1003845990707049004010a0a00a40204100080d0148119450624070119281107502031040070b079882c0001136085030f03040e5068081c100d0013500500029401006440f00c051042d1010401032806400c44200d42401e05545071084600240701c5042c001c1c200240c0c0c40303600300c0d0b06c1074525450741c0340340a44032510280700803800300c1c1b090407a000e4a40f8021811017080f400f680c0f9a8583c031481580111032650100c8003100e1070959500b00301410f0f0300c40740c80861207014115041441e50503c0d0038032680054041e03000000e2018100107805d60010b0220f0126041076100b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 871620233 1250 871618983 871618997
    0x30a060c0201150e1005030d0f05070303020f0c070f050d051011070c08010606030513080702191d0114190e0702100c0509011d030c1e03120d06140a0501 67
    0x3565049001d80710911000c5000c0c41c01c0702002c00c04c4520401001d025980d107160b4441000c0c0da44003415140c4160780c111a003c01d80c036040c10700500d406070004001040c4649401850819014162140c9800001648100c0e511450301805608400c1800074003410085800000d04400755541581e07030a014108801d40b9074403007100c0c55100054200740ca4103a030744405049101c0c3d403030b483c0c0c0c28004c1a85104660000e401c080100e0b01c1030709540d800402c516001015189050090303001d10566640041d140701d00106a00c40c00141c942e00d1b90150a030042404145822030b5151514500580d110f1052040c4200128800382c070400c0d26111041080b68054500b06c07035196510304080e400c120a00345003410301803e151884005070350050003000314050980351055010004003800014141c1844115090384c84091503141c10314001500021030700890304500000c04140c80400c0c00c00c84506545402500302082400681029010710b501816001251a0503c018540001d038070002602c00c41c1e0511000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 871621483 1250 871620233 871620251
    0x5040207051509030a09050604030f060e07052110110301030b0a020f030a0c080711061302040b10180e090304060c0f021f09271112011d090606030a06 66
    0x106100c41580341c0b6808007102e00078645010300645a034002e4150b040041d2002202195510702001a5800c1d00e82100d150099000180d036150f00501076407400c0c507503078425104001101e5031030b640c28181c541200310204c14442e210540c80c2e40380c80e0b022000000d030107003800c910043d10000b0005030780c1102c0d0851004889503d54a0b50300b80240714241c030b4002c41d20000002c001088910b50401c00302448980c0d6151020b82d1200c0f422240d0420040072141c854120707130b0214001081c45e040c50314400d4002040041c5800300e17680041e80700704003a00310001060030708080841d42500b20341910f0003040610014541403600c4986a500c91081d0f0003200184160400560141700c0800401900c695000d0001c401c1c403082410f120712a20000103075400050b48000020a9212040f01c2b40100c401c08a0000d862600142e070040700036004039076540041d410240320499158a86520203402480e41e0401890840d1800443e03004580c8000d203c001e483e031040060011548001a08501c0913800c01c400180c0110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 871622733 1250 871621483 871621493
    0x21190314180f073f0b1e040506040b0601050409050f010f061106240d24090309181104120201021e030a121104030b0f090f0a080304080906190e041505040207 69
    0x6501c1203241c0c0441300e44d61081c04102148541c0b6005900114111400da40c20324a50719528104480051141d0403800110380001ca50801c0240c1126050608a040c26111091182106c0c0100c40130144040902e0042201807180c825903800341031246400040443c110040b00d50382c14001e0070000401420000200c03001844c1d102a00d20840300412442d405605820b042e5000ca0300007404c10443c0208241010a0160b203108056089034103403a040d013110310b0074007020300000c0d0504100d1340e01911510060b840140b5180104081c00039540d00e003607088202c0c00024501404240350b4030401c1c44c94072000c91b40078000000c0d125038014624000000744202d010f03101c0580004268102c40340e030081408000c00c030000300500d200b0a0760711000300361030350740c008001c1e5a08000750901c01103421042e00d51000c81c00300e070001e541c00f90007465002e207001c82c82008106030b644241551000c5a2072030224980040d0310116900104404072018042c4a42e501c070240d40c910000c1c03240920070b950000c2d103081046 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 871623983 1250 871622733 871622819
    0x60c120815060a0314072613120801031407030c09090f0510060e0903030412050a090e040c05040c02010501060f12290321190314180f07 60
    0x141c0003401d0180c0310401240068085d01d2581e42800082d6011400500560b10400800c43c0046e100c044030403d0f19002101071040b1a8081c10042061000d640041c0116419100c8802c109543d0b40d100c10301c96145040225800368581c0750b0340041c0e00920020008500300b0700c201000d81c0c83c811400034a842c41441c101d0b8050142c0f0b10010128058604186010046d83d071000c02100c440c11080c1c0c070300e17a440c52071141d22881704540c020925900c11420021080c4070310003408070f644c81824400e6040d9194a1007110107502110101c4030302c0b214150074003250405010300d0314880c010340000e2110b541018000f60003026549120b108000e19802c14012410481e041745032500420107a0020610800030380f80c803a1144415080e002c6e00c14038041d480a0310451445000340780d40725245508080c040c0103000a3700d901a0f514070304040c0ca54140d0f0800501c040f01541c02805003600d400c088264a842d05804e1028039408142640c214100421188654840c4c8685001003001c44000c05202131a40038906 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 871625233 1250 871623983 871624021
    0x312180f010e0d05031b0a080f0714030d0204092910020321100b030408040b070c0b21010801060f09050a1e0b010e1c0b07091211040501060c1208 64
    0x86103107a6003c0b014403801000805103884000102a2205103050810741c1d5514030746002480080300300140040101114094643d40d031040105e02040462504801d203103410182104500960002d01044040d20701e03c01c03811900c9204083e41100035000501a60b064003510031280201215148003181c0c9109008a8880b8100e01d0520341006801120314004100112135140e0100841d000204140c2a13101c00d9902c610740c80990b075494203003003100c803000f140c00000c0112120407503031001051164094020301114508000c034082e80007400c1ca020380031514180d205888a9140050902c100d07142c145d240015034095940110f039503120300000c0350080050040303041591120501d0b00420103142e81010640c508240d8039942e040207414100403040d02d07424505210038281074030f24000148540c000e039a128041d414089045a48c441880b44500c42c1c015044030303025194602c0c0815480d192061601500843c60000d04206880d0781c1e19600324510300b414030920540d07800145003501c90458444072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 871626483 1250 871625233 871625239
    0xe01020a030e0f010509030a0509060423150406050a0e0303041e082b0f09030b0a150f0b030c0d090f0b090c030f0309010f020703200312180f010e 64
    0x34030804410010000c000d9140240803e00075100120b124001c14084c0c40c0c01210500701840c54090f6521042e60107510440405800c41400d000014640504148504c001d01d40140700000b40e44c201d03000c100c034110704c0c07046a0508150a000600501d80c2c01020745064503468109050520041c01c00079156004943c404803911072404130123131052111000800445a0b99011101601300f0945400c004035946c4d0b00400c0e10b80c03681000750882500c00c0303000100d02c1d140350914400c3c071510b0340c8a0069140d0122080c406003510f60420007a4039a140e40070030020305001d01a000301606200300942d0710720018203200c2003107030082144140480c07207074401603e20b41d0201ca0b819003035409241040880c881205c0c0c805c010700507403005004030b00f00400c0703203180325045402541c54a90004015139812600c446c56030211300c07800c500800018001180e6146808500e2404c3d81a80347c80800c0519040c0b84140c0620b00c1d40060051700580a4904001c3c0d58031101101d505c00700300714580c01268030394900001140c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 871627733 1250 871626483 871626487
    0x18031d01090f06030b130204061b150f021305060306030c0103021b0709090606051e04020c07051e041b0c080708270103180206040b0d091a0f07030603020d150e0102 72
    0x40d001d405605c551003081050381d40c294201324100b040000c078040d40c407490001c9404070029034510500e071802c9545051248801c010580f034858040c0d400c50368141c20003d0141d0b130008000c0c2da072030321081d4160001c103011107003646189010000300b03440c1c8581d146030605058000c03030005001004d0035210203240c641e58040740d403032564400b55034024040c0c82100750380c024504600401d007410003018081d40c00f0f00ca1712072800c05005542c203100083d0300001e8540302ca40134100e400300c1c090759805c12110f800c00d206640c0c44035030001c0c6c030108000c40c0d400e90942044031800f9140c6e06d03034090b0000ca00e50049038001c0c940070b840b25647d0900c0c0b4518450b81400c1390000744842c2011042001c1950011034207142030741c00b040b981c1c0400400c11401c0100f03d070040d620100510003003000d81d0190005000d2980d44040c0850303038070030595855a000c00c080d0982c0300319411060401c4801811b5040265000c055850306000fa00c1c0703140c01259200e0080500504008a07070b0080d803070624020b8024018002c3d10380000c40d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 871628983 1250 871627733 871627739
    0x1a030a03050406120203071d06090a0e040c0b030f160302040302062a0606030a06090c08060c0301180605060a0813080d090201110f0712111009050418031d01090f 71
    0x40103507105004903c089101448062075030318071442031b0b9104132215119058040301402c2c501d42078084000300c003a40711004220401d400d031070304070303640004050b00c0c1254291800d291074250401c000903040311a003414240104071058402003c040d4010020030002419448041c0c01180684140c0d04042c0d040740c40015000300c2810101c14a501c0300340d488180c0388802c04a5481c0d541c0720a02602d80300d03859886038404c64049036440c0d000070309103032140341c44404040c1c1d101109070601c0d40440308044a41d0340407004000750340f10700508140141b04a48c0400c401c908001c0021a180181040c1200b0401c00e50000385500c0350b904001202c1540280c9140d40311b5030b22651040c041e1030015012030000d144160b444100c08000100142c94503e120080c1c0b0140d414442c800005210001003540c840e48a00101641074a60203150603043d0345581d0742d0f00031203040800348416118a408440010207414900202190b8003018010b400181c400c0d100c00c02214074401299080134640000326034008070701d400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 871630233 1250 871628983 871628987
    0x905010b040305010b12070b0c1603050303041202060c0403061a0415050406060903020a0e07091805060907020d0f0e0d060e010f0b01170c090105160c1806080309041a030a03 76
    0x1d4002c40740f050340244031918400041c48081100503503200b2440e4403000050000d07540d050003400742d005003807003110a40d980007075090b2621001548199415080001804140f1840c9001a503099100380010846405c0000c4040c07040d2007244030140040b545e84046612100d03003080260f01d40c000091040c0014a500d8a80241d0300c585480b41c2c9110b5482c1c881c002070300c1400380c4200343c1100d80051000d044146801078001040d0b0b8024260340070451a0480404c5c0d100383c84001d485c80921100c0300103102d240c00e40900070003950152040b8150752102282c40d18141d800040d4000e0031015107010382095103184040b581c4500d04800003024181000782c001d406810541c4010f13141c05840c041031104220310300043d03039209840d5441040b07046401c0700141d084071001c8010030400c0410302d860751902001e1101d00c41c030407040e25000c4489041c0404100000d5101003034021900300e400030204a80c9182241c256602d00c15186d50a010310380390f00715001000c01110403010411005000e85030100d01790710300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 871631483 1250 871630233 871630237
    0xc0c0e040506091b01090308070201030e030a120f1107020d0201030b0d0609110a06020703030318081903050c0a0e12030c01020715060f0e041b0305070b09090a020a020a0b040c0905010b 81
    0xd0300003203110b24800803c04c6400c1c51405488941c068503003010940c19030325100c640340c1c07159900b40e0615854138561640780304204001e00c0400580e5550310640d000078605807050b2980171500d01c8080b0304050190804141c41c4080351245941180e10f1107c1458600c0103070702030002001e54650201074902000f0030301c5102c0c1c120f40b205611510000b66005d0b00142004038200c0c040c000c100040c2e10154040c800170740603610a851b4074040b13081c01c0a02c82480d984280f0582c0c0712081100003102c892200300080d0703405010f4035401c1008021082d061881d01d0100906441c405d0000c103200f5216081e00f440e11690900817202d01c64440d100a540d6614281000d4070b0000c150014844094502803000070b03411400d42641061300c101189404594585844651546207403200303450144524480020005004100310340040080c0c07007415444610328801c106030410020a003008140c01044003405240c2e022035654042580901041c60584890401002da02d00603003043c840700f490100089060300c20000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 871632733 1250 871631483 871631491
    0x6040b100f030b0d030509092e0311180c0912100b21060a1a120106150518010827070e0105030307110907020c0d06061715070c0c0e040506 61
    0x8060200f40007490600000e195585070140000702c00313011300180340c40c0c813401080e00480214280d00e0034131300280000910b0020915034808403000c1e0a403c000308414446208811a0101c1d210f40c403401003600c4442009000511078051507a00081070005542c490390480345407500f0b14101ca19100400d55140d005089428185202c1c0100300c03180300c0e10800d806d10300c8082ca1152800791035940c036180b000d680a400c400c0704840303d111244c000c5050548a01c107810070ba03c1f10341c070000704e40545011215621804440c1c0c0c0c5004001c410481c03040282c0d2480d1851000e83c0b400e2800e44242c0c1e4511a4040c030212031a1902e2a440c146942c1107440c1c8a00000e0310400d980c02c507800c021141e6642c40416507288070300c02d0300078540800341800300c19515100b1011544512540152500814281d00040d8601c41404003201c115903118424040703451141030400c1e04c5c1607d40000d04800d54003181158002e00006d100c041000880c1c7e02c14000c00035004100402401309203140d2000d81003600d00991a104121 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 871633983 1250 871632733 871632737
    0xf0203010b10050909100506070c0303080703090c0e0709031703040201021c08060f060904060b0c12120a05040303020d0501090507020d03050106090e2511010e010c080f06040b100f 79
    0x20034400301900e022a20429202c4242e240c041c03038040420203010501c100200245052540c600b0001203580b2420002c08455100d01080542c85080d45800b07000d0a0000d050007042620304070b980350001d0300c04003110090f07582d901060060f42e501d0403003c0314000c4881c0c200502d00301c4403214140e40e80541c98080e50095100741c00341e0b5072100c110a214024000b080010100160648000ca070560810342000394001402518003887c00d19072201160a40d0b240750300001440d0000900d0041e880c06c18403049a03055101d03c00103242c03221250340420403020240c000d10308a0f641d840400e00b010b002c2d9040b03a980c0342c26544203000315a503800300140101401c0b201c100c05405290b80784031825109110b118162111a110115010305045440602c0030b0000c2c0301030724509000c4907102c1c0c01d0481003522046c0b030b5041d039102e2888000c80382030a401c0d40c1c0c0c01201444c060303041c00086034400f85c0100c1401c2d80040c1e0b510082c5c00035074036400042c0c0079120546016802c038030340c1c103100200d40da800100202a48069 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 871635233 1250 871633983 871633991
    0x160315050409141005070c12140c0a03020c0d030915020a051203090d03092102010e0106090c09060504030c14030102070f06020307090806010e01030b040201050c1903080c18011107120f020301 84
    0x5545030b00075070300d086901c06c00007071061050b040051040e020b030107140c0c0b10b0303450807902024011170f803141a030740149502c4242d0307802060414101a410004500c06a800f5251859901c2c00741c0d40250002c3d816005092003081002c2d47c2c201c0191080200c58101d03070f00582101e440c40310607242c1e13050503801528090b54900903207545614072030190184240c03069000b21060020041081c008850540c5642110115507e42e191800048424002c52000d002188800256040349140c064542440d552100c07090040600c001c00100d01d1070502c6404a40d500c0c0b50300c2e240d804a68001070b00a20503030300b00501028482c40d000042c0821035000e10302c240b83d02e8441a55142c4c075007401c2c0741d99142c24440c118070072524800500c0064950100c9030342003407040c1800c0c1c0c00e180b0380c10130050414100b2050001c1c200001c035142003e142d0311009281d04141000c640c075140445044044410400321901581803104000070041e540b281000442e00925041c900230301950202c0c43d18121840509030140d119600b8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 871636483 1250 871635233 871635253
    0x3030f090a0b04150507020115150302070c0f080106151b0c030228050d050a082109031905040321200105090d08060a17120c06071716031505040914 65
    0x5101b00d01279455013180c070031040e514024810310f540343c1880d45a800c02d5024882180050200b0034060043d0000300307003a460749401d10380f026084a81030b611241290420108034a0100e40101380520080210042d03014410418240040b1007610750380300070341100a004027001202c2194003015140242d80440f03114245d81c51007006032140f40a0070180c050b401103016600000c0c103100003012546001041c40305000c0c2c2d9035105016480c000c440040c0e080c0c00020b00240f000c4065204040e00300c105041c02400e05045807140103142400030790402407210301c0748000503d5401080071030032900303210f410030b40203017120304945000c2c00080e64072991034417031038444000c01c07802130f120548901009000d0700c40f001e103800600500040100086641801010021540700e02190010302031541c44500901c0907040080004040380602d07000c103c1c0604907a02030001d01000300d0301460803180c9501d0045402c50440040701c05407a529403100c3c0d0311615007102a4104205a05039140d13081036041500c020180c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 871637733 1250 871636483 871636487
    0x4060606022d0f150106030b0a0f0e190507030b030606040207111c0f0b1e04021003111201030f02031b010c02270103032f03030f090a0b04150507 64
    0x36070940b4000b80d44036101d003035400b0410072818000703020442401c945100c4080200d0f41d08040014910602c8111441c005008603905405103905481041e100c00259614184001429401e03602070442400e4040c400718860221300030164003076151200b410012801c0006012b001040b0405040cdd009005803000592280791034030a64114a401c00b0513224088066001c22001c44001100c00c2c5201c49030310800e4001c92859050800384d40e100d10344044840c18070044c2040c8001c00d04a40ca048541203a0400005849038401d40c174105285003008114000d50b48141911401000b191181c1d26403200c0001044c418800e100110300da00a50664000304505a620380c071001d0300d005aa03020400216456005003400000080c0720075008840c01c03003191104000750000c8000380d20680c00900d080e10705a03a0524028120f000156030300318114012143e40303290944074000188204603c803c804000345244c501071040da00b42940c0200d420f50245021300d45216110380d0100304056081c50600000e031968 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 871638983 1250 871637733 871637743
    0x60e0c04060e15220606050a09171f021b0714120a150204030503130906120302120705281b21170a120b04090305070807020103060308070305030406060602 68
    0x10004048a40b840c0e40c1805000603a031510300c1c009440c1414442110354a00c4d240720b0103000e014a87d0341d83e550b640101200038018240743d0020310707070244004d0000c4803180c40052100c07544011b005107002c0080c4034515400090050100700e4807407180301c2c105500c44130800304840040c0d90400b051501c81d210b000003801802554001d8010320359010464050100701c0030b901000110109420251070140c803907803650b0a40e04080c0035070f0800d1144040620213001139000e2103015084400d00c9a00c8496079807002580c4a5440140d071411780000100481444402d000c48240d82d4120440c20207440c51318581d103032035181d19550a85404800b000c20b040c0f06020500068112001c240d00c14219810803840516034501d00c5604030348403504d014144070b072200c011019040d160942d03198501c4103048130b42020203032106000c40034403031803401d04140c1c00603400070142e91140303401400780e5445916a10042e0010440303604050211a00418914105648a8010351040d407203041e00f807160710b540e0074085c0c0c3d1b50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 871640233 1250 871638983 871638991
    0x90f0501210213021909051002121b0d02061504020a12020c0114070f03051530070b071208071e02011103010b031b0f04050904030c060e0c04060e 64
    0x240046000201d0089034460345010700c50008180b0a8207004009a1108a034045000c00101c5400700f001d040d8403e4021001100411042d00c4607980ca2180000094035640d800441d00503851001c10041000171144540f8a0000b03841c200b00c079444415558080e5a400b0102d80350401034864807940c0090381054000d8030010026074550101c5041c111001c0c00c00394010304101260740d940e807010803007030410801c00c4030f005141c280c481403100c08880000034140c90000b451a4200884c03603038031f0400d50300c03800c20302c42c00c6000c0f944805044502001c071046c920fa010402445840c403449102042c2941e41000030034402e0b100310303000105032500c1300341610a010704031008000300d0310403003c4e040d00b400e4230200d03103801200c144000101c20b200010010310700e070020b820112058001104004034017040025901b816000d6003917003400e1100400c0c041f60580700c1da008850150080c280410b0415008000103d04198040c4091180e4942e607100f040e41c4203801a61a4801c608106002030980d030421a11401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 871641483 1250 871640233 871640249
    0xe061209060a0903090e0a0b030d080a0b010504290705012901020a03020a030e030a080c0c0a12050c151209150106030c0806041a090703020c07050a05060d0c090b0f0301090f0501 78
    0x1000b031505c86c0400304010020001007506480e0041c509242d9402d02905c54a02461786448405040800540040b6032000c440a4103220040009114003d441c6426484542011a202500074070301070341d129480c055090018407030f40c00c00c100700f8030320400001841440d400750072820301c44811405c01207955640c0c002003d40941c00940c3c2000c0840d2050058051114014088a00400465880041039848814284a580c2043d0300c8071030315140c07845103078000b0004001e405011219a448081e01d42c0c0c440c00b6000d108400000681c04108955070550b050007a10b07980d560305038900300400c1c41c1c4070080d0345a0b1017410703105e580c0003103000e5009203e200b2840d49160790301201580c85200307002c010641103020004000f500d40011302d95503503641b50140f15115507600581c5131400792606a180154642000f0301c03d141120050010703880b41da003a2201c010300d0740d10215442da00104192440c0030f141c0c005210031440041c0300303140c482c2600002d504840124004004000902e0081005c9640a0280b041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 871642733 1250 871641483 871641497
    0x10608100b030f0924060906030102030915060319030c03030c11070b0c15011d01090506010e0f121c091505040501120f0f09060e06071e0e061209060a0903 68
    0x5003d040d1407001951120304042190140c5da18502d100000030903504c0710b800d4506298040020f981000e840c030703d42190303054000354103500f000682e1a45a080383d10388030f000c1300d040d20700003142c641d4200442c032811680c3e0074282200250710706008011400215040d000b00f8180900b21b01c045200d070700c070b06889501c25005865000d09060850391035600034100130f80f4078440d13581000200080c84d503e1500078605c503c0b50350b030501422050207544610580c004000607192004000300350b60040205d03040f101c0c00320355510190ba0500300258022031681c004511920510512100d440304001c5c1d4114086001e40b1a031601c240d0720768256852101c0315000720001442072000708040c0d4010040c182c065140c0d40b4000c034001c0c2100d40311104807280214000000d584030007200d0103114462049141c07850320a40580118601510003812500940f00e03040d003611054600120380c1480703801040c0f11048002e03d00b540c0d5a02110f41c090644100f0740f039110050081d00c005c201080f441d8441d080c8a0b07641601c80807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 871643983 1250 871642733 871642741
    0x31b0317070c1e081002090a0b0d1b0f020114060d0204020310091e0c020307020f120312090706090b04060f180305160306110c120706140f010608100b03 67
    0x46007500828001c942e206070b00c82c40482c207004161000c1070a1140003004040940c6890300322131910701843c43c0130401601c100140c801d00e071159070903c01900c0300390100580d200400c541c0000204502d600600c008600c00040f5110194014a046250300160b8000d1042c0040480c0345414550f05403101c070ba0052080b85103100505058000d16444102c81081c914182da99a02030300a6604815000091001c1c0920100495082d40300381a00c0c00c0c0180300840c03c004455010400840c44503100710b2003045800c901c08040081002125100d252070b1412013038900389901c806a8440c454003c078400f080a140b404520401410182c408980d480e548030401080c40003c01d50300322050180042400000d00404000f0031010000b0b07a00c840d07520b2040400c1e240c91403c00b14101d0380058181e071a8480c04100184509900007041100342c000b02505690300e19141c50041c1c020152600ca5041d5030380c040c0708001c0d08090f5029240e0480d4010744825055a07180c10414004901c18040c3c1c20003020140041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 871645233 1250 871643983 871644023
    0x21060f0207050a110310020301060807031505040f0e01050606161e12021506060405060d0f0b0a0b030708010803190f111605030708070b12070e060a030501031b03 71
    0x1552249410590061070107034191038503402d110314468199403004c030107541507950f810100a454000c020324070f000c5044d5410710100501c2d420340a13004800b0180c6403000c0f0003030201c80c001050000c0600403c104450030f80e0640710405070141da41b8644282d40780c80000351003400c00001320f03034203401010640170141005503600d0000c0c8480074009906900810440b1000074085050f0300c01605c03850f00140440c68074400c0a421a90000303200c00c7c01210184401c0145484040c10307a40b80141c0510041255180d140c0f0300340061205041d41e942c080200000000c0d210000c0c0d00860280d10385640ba414075030307200c4100c3c42c0d40b44034210b5000d01c40380040140c210158801d221143d42e80840303251665649002c03d03907882c40c2c4038141000154507021a00108620328041205800802d4028042d10840380790403801520b50007005110302c1c0304480800040c0b60140300b00803600c080403000b0b0075182c64140301c1c0e40c002c00501c000d000c1100ca1072600400e10285100340a0480212030344900348041184031003001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 871646483 1250 871645233 871645241
    0xf0f030124140f09010b0c070306050a050a050a0e061b0903030d0e07080303040c12060f1a0f030f0a0303021e0706150b090f0f030a060504141905120901050903100903092106 76
    0x50f06041d4052324002100040240c000d1902a100b40c2c40302040904003012610121840609550f0b102840e01540081440001c2401c82c5c2c0140d0240d50700f500414614501c011130b00c10400c045505000c00075031440601075a0307002044410a0608645441e80c44034400360762440185c4000d05121100d207010014042ca010100c3d80c0303036114000200d039040105628105481d5014903d400c114800301c00c07000b03141814150044102c40485c02400c001d640d41413466201ca00450004d410142c00240c01c9029016419524409429003960181d480006050100044c08000060607540c00880170000c3c41904460039074144401c02001500401882e50403c940943e001001c55014051203842c0b80c0803030b12501c1043e204030300503610000514001d0344042d060a895a01c900d4031054400d6004000c82c10000380111079a01940d4074070795500301c00700140d4140c000e90f258030f83e042c03280d00c04854100313000b9001701c503000d4030a0702e614010b43e07100d40265442d1045010f40d58610131502202d60080384990b04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 871647733 1250 871646483 871646497
    0x1803080a03060305010f0905100c0c021c020a151806020d0c05120c160602030c03070b191b030b0a080d080414010c200304050f0f030124140f09010b 65
    0x74009019a50399484600350350300c41c4542c410056a5401150500c2018450740804602c0c80800704100b129403100600a0614000c1c040d015400700328a04c802b594249219480064000349007440d203980d0b07416002c180000c6413200c030002a015020304c2c000240040090030a840e92a00034010f4044800010ae1b405140640140c4e40791003223001c00d20f5401200c00050540c8900d02c40035000e130040c1c07018000c51400465101c10110b50040100c0c086182c804826191413a910218024468440c441c0c0c016415200c0c8907100803540c68200100d038180360503031405034403010b40e0300c043c09902940420401d43c055107200301c00360764000506900b2034621a184140d0311500c02c4a034504542d458031001d508480d0554012404100c01c0b40302c8a040001d40b07515110b100400000a529190410005c103000c01d6000c5506030144041d01c0c00560300e9503082d003004500341d10414105000200c0c0f0081c003400300881d4800d50841f0748540300d00390894101500c41c62409540507108510b103907c6c0000c01c0240d980112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 871648983 1250 871647733 871647737
    0x60d142a070f051516171e071202030a050f101a0a14040605122a1b0f0105061026090a0f0f060e030c061503031303211803080a 56
    0x14140302599980320341180070707880c44c024080c540302d49a00060f200c00c12001e401036291070b02c030042224280c0031561f101d100d2948502c491541c2d444442041d601c2e40c4c40b10070800441400442007004d820040d0303000d9481200d09040c038004036105c00c100404808654028140750a07a480e00030a002c0ca46c40e00204607880240c6864905900e014010300c8858216810800002c4c8000401e0100000450909a00840780b18203844c0c00407030101d0030b00c02a008140316410440d001255404240a1892040410700344607015a00c0e10035210681500030032048a102c1c2c03180440314250b521040c810b00c040401d01c7c0910140f0f81d0402195200e030420308800a025180314483c3c03014000c0051102a50b40310311300c0c030031041ea80101c03c1514060054500b9064040110340c401c1c0705000306240d00244940e00200303c13219410a6100da000400d0961040281d25401048403a00000811113089115110710290b1880c10815045883d811140f00c0c210601620048000d54003e0011035200001441151114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 871650233 1250 871648983 871648993
    0x8061509030a0203061e0c03090705010c033018080301050d0f051b09011208160602040b041d07050910050f1213021e060a030506060d142a070f05 64
    0x3d60020b40790101c2202c0580c200b281d198010309080300e240440982180003840c585003036107042e89202ea56000b09110f440d04000c2150781420915008061081c040120b400e01103200c100c01c1d4110722503005d842e40e488000c1d0303850511b210040c1d40102d54008a200d62100c05107180d0f03441c0504000c101083c0e440240c0d090202030001100094041140d03201006aa8800c1e43c400085441000791801059110108145c0c800500400055500c01108c07400410404038012506603410501e000380070341d80164840020018021030710300e07141d5113400800b00015030041d220f6030b141d40c0100c481d40205003074982c01a45041004a00500030030142c10b540108580322410031202e0409030995400a503411820f00048602c1c08065050040b10010030f0b8080d50b080342048020b0a01003203292160320305540c10140c1e141c01140c802d0761048100c03462444424000e122410f0b0b5030601310b802000544c1c40140c400501020143c0c600c81c1c1109181c40b1110b0040f0031810030a00f40c072081d4100103079141c2181c0c24012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 871651483 1250 871650233 871650253
    0x3180607020a050c09070804080d0b040c111b0907050c0f061005011e0203090f010c050f1e060112080a1803050c1206100504150306020a0e100806150903 67
    0x80141900c1a085507005000c1060241041400c103141100d5080c050502c080030440e8543d0020285c5030019031007001c495941c41441c807004018140064407941c006d003070251080905a015182e404109010701c1510346030360070301d0980740b04d0507203148049822450040000314003c0c0210f0281807a4a00c10302514410b002140003242003190031902c561082c03001200610843d46d20030306140c8000500c407642c3d0202455218040d40d02d001c0e0b000c4851054055204440003644149100d1640c250301008543d070545074808050b032500c00d1050400c07007401090581c040c038210009501c604070340200c81d00c0202c03d05c903615040310680c084000e030014001c420316000b0702540c40328030040045010714090321b40d40e0300400801c10341030001825401c0c1580481300348242030100c000140e046072030840c0c0005030400c0340142065400d0683d40081c113550700c046501404a500f0411224005204480d20000104114400e4401600a032001d0390003101d8280f5034042c030b8403140d0003815005030040c129a03000c3d107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 871652733 1250 871651483 871651531
    0xd0b0408070308070201090c090e16080d020d0903120f0e03030307030f180308130302160e04110409110d1b08011d0c011202031b03011205100614040203 67
    0x5058508031120600062604249503011480580010300c6200900413101c031503c90401c0702e29140954549140d03240180c404d0340700d0800014014003124254086c445a8915141e078607200d640c002c41001d4000c0c0b16030b580680344204c2d24582a203038040ca2000110f2110342003190481192007140050104105040300e240d541000034500c101041c0d0340c046034090346007000304142c0e60008007150983e660707648298002600130300920740c4404018212903403290681822445c00600d43c00d014034018078079001003500b240e1000400c0c40b07a400350000c420010b1185062004980d000300000e0130a540140c2581028a41040c41009807800b078403ca041c46200e0704c2c801d12030032070183d1054526a40d600900000705000340f6401c1170306e6042c1c0001e84010011100007030024a600300c80807402c540c0c0000003c0440d0403030700c040d181e840700c1c0c040305945030b40c0c44402001d440c01840c0c1003500d0380e100b861000000e048a6004000585502121240340d0029032000e02002c3e41000d4008440c0e9400655211810741d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 871653983 1250 871652733 871652753
    0x8070f03061214010b0603161b0f0c030b0c07030e0d030903020a0807060e060f1b011803110f070f090e01060902070606050a1a0a080a090b0103061a010e0a030b060d 72
    0xd0103043c0b04059201003203e4603085a50f13041400780520814010802411284602107400c100300d0704014140640741440d094a042d10b0420091114000c011081d0500211101c0c14003079a11402205a00f0388030704641c00028001e020004000900081c60440181001c80d29004012721034140b901409442c0d0f4001255150742d508802c1c06940011410271600341c2c841c8016040c602c054424610700010f81c2001d4200e403180f032451072032400700107246d519801d0007541300100d110910707468020820b50500e4000d00c0007084c060868000d119001d00b9164581d13011403200d08a40f1046010303240d00d8a00010100941500740003400c003950388010000e54001c0310700042c0380c2103201d44e80c001142400c120810031002d1081c0c00c0f400e80c190300710709090345240350340040380c6074585682480101c0f42c1d91206c50002600320b00c1001040000000b00020400120750000491400005046140c1c035100c0801100c092035112a00b070b9100d01d0503039080000c41c11580030700d60408405003000040c00690b8603408095 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 871655233 1250 871653983 871654019
    0xf0d0609030f090603060e01031124071a1017010914071508130f0c0503030c0d020105160e09070e100509092d191a0312030708070f0306 60
    0x200d04042e20300c0e8840e562007201c0c0c0c00a040355007800c02509040c80301e1009074000500008040c000c1813050081c1c2a40d1700f0800031403603c510300d44881803101d00780d084509a0480c8100315010340d0601d5800800040026a0030302c0340440c07611401c1c6203403800303061001c0c011030820540c0b0195a074602d141d0101e40f0403540300910081000042c0b0a9510380400b080c451900c03c0700743d6003040ada51003803040f801407d415200205070001c500d0421040c4c80d041c08075681c01943c0c000c0f0741c075200005072110818004501480302100580007044180d4030382c07800884054610f2040c8000580c10075000c0b80c103103402d45815411a0b0a4540410704140d0140400c1407120b031400d039000420710108000402d4030b0584a547d0f400901d40d0001d201c641002d40c4952800541041c00b1b03031002000200013050300e006024002000c60300030200344134230442080085043c800d032501c4c00340a8060a84894101358088040328058000c580d144a221b5662030030446980e00032138100b10415441e40000142607220407514454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 871656483 1250 871655233 871655237
    0xf072003100b10230c0106051c0303060807050f06030c120403050c010c05130510030b03011a03010b0d0819020f1c08060102010614060a050d09050106060807020604020a03020f0d060903 81
    0x414002d903020880b11100100014080010000f5840c40d1048a0800d0100142c003190380c00c0c1c0c60380007000d003041c00b60003560801d6410401c07002105020b80052443c03103000714001d40f0100302c81603da1150a890b1680b90007207035003145e0161031842c04d604201c801198480041d40420f400c11003620207241101ea404d8806600244c80803569008581c001e02c0740030044820350910714903020317062a8100d4209040c1c420030b8410324042e1110f2403ca07001e038010751220303c0d000380200f0400e04c455220030b048908002d9014040d41ca020070340c40241c1030514003400e071141c00003855820030000f02042d200c0280d03820391150460144803a581031741c94007000790621207003090b90140c006612070100201960710080c01386046a0505504000c140e20068041240d58015512280c1d41c9070070303901c2910701d4070400300801441c038036100354001400419400032084d41d0301c9a5801d01d1a4840c03d508a0b512081918003950100060720704000620b4580c0000001800c0a8220001d0121301c0d2949022240c0c06201680 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 871657733 1250 871656483 871656491
    0x703030219020d0906110a060e0303010602010e030405031009081213030e240d0e191b030308010e0612010207060903081803040e0c0c031903110f07200310 68
    0x340700526584424030400c09440100142060004000c0150f00d1500c42c503014850380389401401c0e4403051007500420f03908a2018000e00c0c0b8640d54144d80d9030307c240b140d0001540703083c001660410011044500b2510000c005000c1d940b03103040b00303a00903d030345074049902c404108104111081d035210300a200d020501168641040341d401d0140440440c40700e924400d0341c9080d01c00300c0c55038020000b0011021090401c0e0380359158406d03040010660480c456060b0b11504160f04184003491000c0c0c8420340c458211202c0701c00d0102da01000b011607030300000707011401030001800b012108185141d441003000b4000341c500c0305082802c0d4226404410180d4100707803621300c0101459084020b00e608440076082000c8501c41706503030305840e40290b001e0701c2032000c04280810144940f000c01c0d5181079a02e1010741303035158198020000142d036496070301d2010034204040e1202515034801556066a0342d400000c3c9080540d0395102007100d9060101090400010540354481e2000c21052041a840c048005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 871658983 1250 871657733 871657747
    0xc0e090a06030b0c0901050307080423030c0d0302131e1d1006080105150702030f16150504180902030a08040b0c0714030703230307030e09090c06030c09060d0207030302 74
    0x805103010040c10111308030810480c0d801c107641c0c4081100ea000e1b50920300084591207920b010380b680c00b071420011200d9080c0f10076440b141e590220091150744130321400c0307800441038108190242d01030707a03084c42519859101e041101c12100c1c83c4542244010520007045141c50300203081030b02c00c440798606040c0f41e0f0b90081008040c80750500c20081c11060400400350b600d84170004884204401400c0c0b00742002050304811500c08101d098556120b131000c1e144448a212080b001403503161284403a4110b001c1c9501810074000c0e000c03034080d1a910000280e000380d4500c0d10601628100c81c00301c0c2c25119406c1900003241101d4043c0028102c60b520003035541401c0320f00b2034580b80e01a0840d200200da1460483c0f45540e0000d190030032664031200c0445e49402200c44401500c02000111030540030004154041680c0400d00a4001d80100c6962002c1d403941800039545a00795040260004010404620201c8001015101844000f0b044520300180e5005000c21ba0300212030840201e60042142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 871660233 1250 871658983 871658993
    0x603020f01030b060f0702040207020603011e171c020313031b0e0631051603110702150d020705010608060a060b03040b010302040203270616030c0806040c0e090a0603 73
    0x9030202400d01e41841400701d5100014030b00d12540550012841c2d00003114000c40d1101e8040d0340c20140c00030041d684940c1d4840c0d040100e590405402d000070070a001010860095004010a50400365002060028400d02503860181c0410704440c0540c13106108041710140c8000d52403000d5032007052104d00701c0640d5422550f031006a9008000c0c142d14103810400e1a48403030300e0640e16091403001c0c111031640215509241d001091284170070403800d00301000f4807655201d980b02000c50071070785e040040c56841030b146802c1d801111130007036207c10303c0020000d202104c003002c1d014100001c2801890006240d50f07080c00c54004d40c0c84408141c00040400c074070042d061003234000030300b40f00482518602d4195103040c0b03a40700c1400001d01c200c0d80800030441942c2c9504000780c650b6203c00100c3c0280400c0e0141a9403402c00b2100305130040c0c03050f5071504c019072007805980c41c00000e5844500d0315032200f004100150040c60b0480b4204140355200341341e2681e5541d11180111002c03580090039134110700703007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 871661483 1250 871660233 871660249
    0xb16121a04060609051f050735030402010519020f03040303020a050d020304050310052a090f0f030c0111030c03130609050a0b040e072c01080901050f01030b0a0e10060302 75
    0x680a001e0344c0041040380b911a40b441517010f4000019050416500004c1501c55015454000c0c10650401d0f0241d42c440090326017642d410107200c034540b07050601e0210403003440c0c031040710700900041d004e0241080551420701014a202c0c11801034400b21060041000c0c6503401590095006910014850040c0070007030041c043e100c1c600348055894242010042540c42403050401e04030180d440d000900303002c3c0c20000000400c0845a114540c5618240c14912140c125951074ad1041100c0750320340c051031804903581c00441001a018000042810f8015221000c09420301c9406010800040840c01405d200030020302c942808030801d540e050650080a480550304528003440007400c090200403065804c1e01d088810080304410690707070f40c1c14110303510203454070102c4080d000301d00c04008844544007402155142a44d600c14956201d05800b800e0b24000d45610750700216020061011504003000759512000600022903071032003200c1c00c41e00c0c0101340e518203542c007540d0b80e8040c03045280c0280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 871662733 1250 871661483 871661489
    0x30501020c251a0a091a1b060601080c07020f0d03080711070302010507110607120809190c171603030819050702070501030b0109050d05010c090f030b16121a0406 71
    0x1511010a400c0585038641c0f1088848822040c140c0032808103100f611a9585001400c3c0000c6101819400800c4500f640e400203241c0d51202a81c40b0019040300c5d00c00181d0f64400ca41c144d48001e007680742c3d0800382c41c095001c220140e0f0022200c4800410989036002c22100c190306c41d507105c0881d403a03c400001d1038245030009946140e04184010000350f82d001d405d941c07003241c2009485110030308841c000f640c0d41c0310301c8400801d00310700c02080e420b610341c001c4860740c89083c5490640c4d150f20880c1c2d04208a020800200820170518481d013808082c05405560203580604802c850014040094442d140100ca030303c102c4c009010b64080040d00da92490902e140301070102801d000b94285104040c2d2104441e01481c0d04060343c801c11102103a105000420007040040c00344440521942000344c060002c0c010020003003010040001488081c02d29441d044a40184460340c0549036281480b0510000c400070700c041044d03094a2143c5030342c40e88601010000041200d5503039000400c05c0c0001c1d220313164 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 871663983 1250 871662733 871662793
    0xb0f01080a0807031224170f030d050901271505040b0a0e0316080c0c100f0503040c242d05071406102904060305060a030501020c 57
    0x7604110001e050318040d01c0c0e1481c1d260400380b46251441c010400100040c224012103501001000300d1000c0c00144a40c098562414900a103401600541a0348840440c0604400d43c020130065580005950002d070b088824040042039503480caa8800c80d00003150900c95000130100003102c010000e000783c0345228800a080184101d1600340c80d18502c12000030080720300141c6400000c82c2d0355405104803000144840300b50b2510b080d140c01c200010b07400c01c483c404040d200b103105241c1e441c94444110b9489107210364402c035407002004000c8806400c00741c0704450f0208c103058086400c0341508580c80300e65801c1c0400101c030008009000741080c840140e1343d0030907070551000c459801c00da206500c1f1600181d080c12a40c0700c20320300d450b0003500c043c1c103408026805460b0904c80d01c44c2a00c2d401004886d40201490180c0c01f84c0010048403008241402d20351800401082000310700a4001d03130381c46071004101000d940c1c0e9a807600e50036031b84140f0401d4101c2d007081c036401200c0d0210b0700700c41c0c0c1104164 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 871665233 1250 871663983 871663993
    0xf03050a05010e240301020f13170a1e08070809030c09060f1e09130c0b0c06060d060b0d0803060a09050f04060902210715020f0d110106120b0f0108 65
    0x121820784005907015010581301c03031248905420031407010014044000d03014000715640c0300603000390501500003803c14101e1136100a000580c603152002880d1121031420701a000481003542c0c3d0750b40b1110342c80c40356000c2c59502c1650002062108001c0c0441c0ca008200965a916001302014140070181403501d109412a000b4841241c843c50301c2c0c18860342003070307400303002c1c441d108084501d00b0901e0224944d8040e1281042020604003e0700c4400158496410002e0341626220180300a01076008152600d600000000c0c02a281c180702c070304031450003940c001480c001600c0109aa8074035640c410750b0000400014003010782881c8400c0401000246d030104841d0410b6000783d5581140a40064103c1d40c070b07055880b05541d280444171070034211103400e44002c15450540c446d214129481945968403458000000031400800c0c5502840c10400103071400000c246015a0220395001d143da01540d6141e40114000d00c50110340031400740212080034032464008400c4c07203480b005801c50106a044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 871666483 1250 871665233 871665239
    0x50f011d160e0a0609060b0408060c03040b1605090d0b01081b24090d030903120302210a020d0204140a0f05090103080304060b061b010f0e120c0f0a030f03050a0501 72
    0x300044040c00d0b0340c1011110350a6440d58800b12000d0704558103d178011a250100000b01c1c49a608006e00803035000d0310a5079503940d82c610500c0042d01048401909801d0a1000100a0504070400d07402c03801c0e0301e06240c0d0404400601164401d03d00070030860300038141c1001402189401c005a0f03a6809032140c0d980110794a08002c41c07000009004440038402c4d03109103100418402e481500e140c1c0001074084c1c0c82da07028605004007907150920095038032138100540c2e60481032203030080303440d400134414511400c9000140f11a0400100800700d0803c00d50a114451852260780010f00041445d010300051420100040100c003803026030200001620005c0c04000549806104038112130300118815100d6580b4100f090140c1400c1100039400000003914180c0c2150040d000f01c00403090314003c02c142090499090200c0d001d04007041c01c01d90115074600d0321500390100921a00440d01d050f01e81140702210000d2400b14800390407004502402544000c4560510548d0785c004280c03a010300031545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 871667733 1250 871666483 871666513
    0x605070308090322030314030c09010e010c0c0f08060c1e160804230301050c04120204061a0702010815011d03160e010f0501090305060a020306030a050f011d 69
    0x10400200a080c04200c800144580030148261081c20115844000209408540d0340d400c0007100c1c081100443c2911908446041c103c0003601c1c410700c69209028030303200c1039100556103800c1e1340582504000a00a0280004071640c000c0310090490380c1385030351034501f40703120241802070050101080748420f00404281c180b81840c4113054007440c0c00e02ca9620701208610030807001d0031500260000900040001c3d49400d0701c102d00304444071300c0c410a040d4141100801d4288e170015501301c01d0112041c04180610406480030340291440108001140e0380e44040042d540000b00d01d01c1252248040703180010340d42c11101c0c10780e000360340c144d902403c2c17054500040c040e251000c200344001c60554100d00503d032010414280324008400b0300709150303951000c880e03810304001d015203c4401246240010b041d4029403819050f694041c01514140c1c0d10740c40640000e400013005503034140310741c2d20200041013090210300c08802c0c00200201d409070354041500786c241071140c201c0d2181d911050403804600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 871668983 1250 871667733 871667737
    0x30b1e0408042702070302150106020102090f130905010f0203060f01020d0c23150108010b040e25051507122f0c0406090b0a080d0c1b090507020a14070605 68
    0x14080d07212102c0c2c00c02c1a00b20481110009000083ea880e01c00034030030713040c1a00040c0740c41c6508280c2a01070311a07130b00e40004a090b0702500c202c29402a0505010034601e1070891121000e80c0c1c190400000c54102c1e503201d01e42580d90034442020743c81c0d4008280300031410910022103204100b07000a000c4400109030050600b061f0100240802a0301c200500a01e1114600c41f02101103060440e011030b5180c0e824880030708000c0c42611140d600c3e080e60400c02d030501d40100082c0e40c45200c09000107480401b0381c02c0d843d1900d0449102503041e918000724165481c64001890302c5106082980c4035513a0385082e030304120041b160b80049c4040e14500c02c4a40300628660b100005030490b01d040c14914400090b071605100b024500d90150600c500891450540d0340200440c9004850702e55203683d0f44c81c51a0740700c01c440f5075000000380000707400317038041124400d42141d4000000001c01d0f10503520f4808000310340c2d003607401e5001030b001020000c081c0b061800446031030940142c060300c4458030f004c00290141c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 871670233 1250 871668983 871668989
    0xb0c0c0d030515060703110624120309060a0503010e06150f09210a02090f070e12160306022a0c10030e1903090801060311060304060213030b1e040804 66
    0x64940c4006001a2408014059003000c041c3c54140c50b48154a80a0140060008007081f14801c07100051228910503d0340d440803500420029400030486090002d00c20000b2000341d0300f44800c01c0260030a03110714004140c1480d0665446d516541070112100c01c200b0044c0c03280380700b0000d1003032419060348003008071000700401d1410240e4503103111010034120b00c01104100200020007440c030044500200707071440018402c5400c40c4155440f0f0782001445101580c1c0c000010b1f114045d481140d081c6070a81c05083c111260403200e88000341980303020710050395003084890b42e07004a503070303201000d103030b5031035950740c0305130f120809142e1005550365540d0b010900800703100d078054103503000360b0500980c03001c1103200c002c40549481980c82c0040440c04a41050120b00046440d1400030b41c0e064180305000680c0c1d400001000340341203081c10480e07550000b0380709540d0749900b00a00b1801c0c01910000c2c07402903101f121080740d44e142c6481310030100c07c903c0e030a81c14091440307020440002c910108903816 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 871671483 1250 871670233 871670237
    0x40c060f02010c021f0e0609010c02010c0c050a1407080102030c0901030606081303080a180f02190b04030b070314090c01020f12040b0310050d0804080601050d03020d14160c030b0c0c0d 81
    0x102105408001400d9407254840d118010314041c040d9032300f0190454540008103800900c110398070520110340700c0d95240c030050400d42001d508500041e500441f10303154400700000710380b10940c0300e149040c01c990098490421030030b00000c00341010350700350003804005c000d50b040c40d904600d0100d001d0040340d0b00c0c1460003030400c880d5000240704640e01d40e005108100c44007100c5e0100c3c010314a42101c0003000f0850903403240d2030740301c0c0051100c4c21052201d810b44008542a9003082d2469903401e6409070003420078400d16850b00201e46030800684040c40c42024544014400210487e001a007051010014800682c00c07002d90700c02e0442e4410122000c135011000ca480c0d49035070302d00c60003080440e02d4010540c0801342c1032005050100480160081c0c4210740141da0345a642c40d01044008450b20b9002030158201c41d100042076800307058000b000a420342c4026250407007624164107810412202180c0501c042007050003805103659501da0b0207032500d40f00900d00380842048590b1900102c4101c81 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 871672733 1250 871671483 871671523
    0x903020f060906041811210708011413150b1e0304030203070f0503090907020303060a0f05060f160602030f04050c1e040902150a12112803060b04030f051504030e120a0209040c060f02010c02 83
    0x210146512405080c0c11482400d20116141c0610240720782c4440130fc800603c2c0007004920703208007110106c0340500d80c160002c629003021561100803800079281d0030741d02d9020600907408030351940c0c500140b1616003076016540c1c9103845010007008030740700c1c1c20090071918101014070982c1c403034104039074042e180c80c015030307407074400540d84481c1880030694010040c41c001310a200c045c6e1400180c0500403845141a25500c44051041c404542e0302c1d0482d892006840020005150401c1e6002100050020b405007015042c181d03001107281c0d02c03041150700020940d422810500b88a88554041101c83d00380c0180390892040b1034402c100540e1200c2d050400418110540c0140203620010041c016011115111a0789041c51454101038810540d002d000720101028030a81c41100144101d900d03468a00c80701c10b540c014000e0450010700081c56910650501a015958040c00540b01700d108021400ea11420994014505601c103260801568101000c141c6000d40100c1c800002c2c110300442c0d61 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 871673983 1250 871672733 871672759
    0x1e140103120c29070906020d0c201f2312070912060c0905030102120c0306010c0b04200114032a0a0903020f0609060418112107080114 59
    0x32a0321110090f08801c0704a0411a54140304031403900d403050545440c1d4080540d52000d050f42c40344200084140080c0460440f5000210b040f05a13a07002c1c2d070304020051031004c2c080301065055200c4025007420f014901c40c1040001d0b03004562130341e6401644801c1121980460541642d40620380c014104191020001902240300361900030052441e10388894595415080070402007850181c2c410005071903101c041040e0a05000310307220b084030b2810504582d075940304808565040505410b0410400421540102c2e4440d0f9070079001e24085c2c0102960910280b5403a40203801803800c4034140201c0342c03540a1144c4d01c55050300d0303002e00c03000c14100e68008041c0d41d6400c007010300300680800301c40105079100165031101250050b80d1007940d600d281440a80100840b41c06014021340c1d101100300400e1140980349035a8449400c403034100032480c400c204030f030b00c41c540d00220102165108060010326003001c80d000425040b48003424141040e5042201140c44072541c0301c45240614860103202d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 871675233 1250 871673983 871673993
    0x4110105070219030c090c0c060f0b0402120108060f0103080a0806010c0f050f011103240a03020a0315050105010e09130c1e060905030c030a0b0c0d1e140103120c 71
    0x1100400c1d07000384184a0401406107102c3d80500a00080e43c6040d59140041200300b114850100d01500c56101e4051801c503665407200a810b100411220907510b80003c407400752654005401d207642c54803800000f40d0f0520240a19050006140603c0c401c8440c0c0100b000c43c440204407058040c03245003d00070780c0c0e03545e03005940d210301040c0018040b40394001540d0a000020032100b088101110003440544042c07490101d44d4001034a410709880c910a070f003041d1000440070000406000a001d20034080d9907a0001000064503500541f1901801e440c42101e07018140305250141a00342403058801010318003080c02c02c84002e003017003450b50350707a441e8000340900ba0407960000d0015240222410300002041c030901d07181481101c022610900e030204049c54042010104040050000e0a00c000c0300d8680c07002018000c0c2c000f90f007550003003002940114082c042c490f0210000c1d000728801c2d820b0503604000301d4101c002d29040c030105050047c400104034881d508548c040e0341c41e008850114134140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 871676483 1250 871675233 871675237
    0x3240b0c010912050711010810150201060e10320904081c150b030c0327030a02060411010305060a0e06120307050f1606020613140d121505060304110105 67
    0x102600200500341001c0003541c0c0300d4001c080301881401c420403907040e80801035503440015034581b27034240100ea0051088000f002c1100081c92024400070032007907501c01c24018039013170075100070092a06908062018602181184e00e000c4507c00103461088240c3c213a0002e1845082c07a424404e00e5003030b0100b010310001c003040d50980c500a0f205000360292001018000740142410080540031061000070f078444070703400b6680b1659214a0540c46c650340ca085200c401140c101c0c3d0000d1210154140300c81081c01040501300100c2c880d0020f0885013890304003200000c618049080c1098102000c22141d034031440185001c81e4500c0782e0101c81c1e6110b00d000a05034541c0440f1404951201050400500100042c21140c0242d548207944c405079190480c20051101401548056030107880810b0904202028a150281c0143c20098120400400e26030504891104400004204081c000320040e81803107841c803003c02503603108010504d001c010070601d01009202a014844582205081e40d02900c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 871677733 1250 871676483 871676501
    0x18070311030705192601080d02010605031b041e09061104081b2103071103030a30061e210230030705011404030e09040510060b0a03240b0c01 62
    0x8030910020003108617442d0340d51401d210320215031061000800a032401803145005481003e00900102028504003c218800d240b14160b0480c2c2d850842d1070504200c4005441f810400c45008507561001d81418000d40b11004040340485900304000c10524200060030040d104a0075114000c1020b5140014070002540d00c04401e00d5102c41c448526071240030005003d403601c510001414142c039001803698900031000000007188031200e1140090058030000c0c0f00d40e064039900125412445800c000584140d80d1264452444012081450048981014000e001c0f18614400d07030044070700030300707004a648e03040107801082007090b44240d80700522a0a54881e8a0707101b200c1020301013101182e0b4903400302106072400c0d46441c68000c0a0081404814062a00b544c0c42d81041e0483c0000c0101800000d0011990783c0700d6096401c1c0341140900540c8000c1150284158039401c0419003d0140e4120a0450100c00c024a508201e003000301041101610b4165030600e4071760803042d00307460040640741 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 871678983 1250 871677733 871677767
    0xd020d09122f03150606071704031703160c03021b0a031a0f070309050d030b030c041d0d05030f070e030709090804170606030706050f091807031103070519 68
    0x4540d103244a1403990031800c00301c010f8088880c3c2c5010840c4189002c601550001e40c4100d0030090074022a0700007050340c881140701c41203146042da4030790b01c00d0f602103070711104004038900c04802c1042c42d42107040044141901401d05440390b805590300291542c1c5881882040201005003c02d015180e00350080040d65000c01c49418452003007c14030f20a0204a41c0036006220020002d820144240103100c5990360020042282c4201c41106401604007004684d0701441003103a034020710754581c055a524074803202901419240700200260030700041c00081ba080c0076040062003504a9000082a071040d0b4514064400181290010741050b84e141d20440e01d6034140710101d001e0100c0e0200810445210050a0302000d40260505032214001c0310741940c150001e00e800c0152a0150b40102a01e9440205892130200d51400081d400ea090403200240076000c002000341c5c541e01842001c0708445034141103420b40c684004002d000344100e078110f100c04400c416140b6040341c06425841903444802c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 871680233 1250 871678983 871679033
    0x2160c09020d0b01090b0901050f07080d0c0801052704050a12030b0925030b12010c1e02030304170d09121814031902060405040c0c050d020d0912 64
    0x140c240400650012035031911494500b008480c5590f028071203030811501103d141e5800c040700000159001d4000040300e00b4103000030082d0700c0009446030005c0c814911680f8000a11009115008001080c1600081c2c000c4c038541031001c0950301d01c0c00d59030b1105001c071908200c95a46a103441400c102c0141002004901b030a032140c1d05c26a01a041548100740540d20003606d07540d1100070462050590020200121501355440d4030580310350412031080c0805004045141c2d45500b049003111980703941c0b0800100703c5190580104060b0701200c06003030a41c4019415403d040d240c20283c5034222084001c90400001c2d41200e800352a0000490250050102c170008444254041c014010100d28211803808928021805041c1c1c0d41c0c2000e18001e0283c02004826003a503000204410516400e0303034885020302c0001030a0b5254058502c2d5994540d40e10412400d2a103000c2c1d142503800310480d025500441c6e400e011061384401c2c01b004803203202d80045a1082c1e18140030814001c0641742c040741c6240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 871681483 1250 871680233 871680239
    0x50a14100924060813020a140414100b0a0e0904030f0f08010e070516021e19050907031d15070f020f0304121b091a0607020904020402160c 61
    0x2550100c000711124000240a506a400e04400c1940c00c0d0400014071400d0500e41480200e200d5110145d005e80114020036044207240c000402c0c4810a80c0007100c000100c0b00002070500301740c002c00e80441c030740d004146845d00740b940c5003000c5060103010307410f415500452044001846103981c0c6110074400383c0b00c802c0c90304090a00800c0500c8030f404840104041e400352165452040c50100d0407500c04105096550701d98410841e50340d440905140c0d020a20b00d1032100142e940e106000e1040d00c0b00074020b41e81400c190080c000c141c011045e00c401d2080b0b00100c02c00c00c540ba0382c480650300050915000424502c00c41001800e41d60340340c0080f0300b911411002c186610403201c0c02a028882c03a07100d19408070103043c03003260b0760015a24541f4003034100307000c1040703210510b0200b45e246903c100400c0f8640d4203030708a00d05018500ea03110388082622807440720042202d03102081302c600c006407845450584150041130244102400081c003640c1c5c001410650440281c20b59031042e036100101c0400c86903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 871682733 1250 871681483 871681501
    0xc090204031b05060a0e100e03120a020105011706151203030a0603060516020712050f031204061401030f02010c02040204080d05030402030d0c020d060c12050a0c0807050319050a14 79
    0xe0b0340504850803186040460300303181c0382050b1105400203603034094116410350103228000550002c043c052100c0060b090f030141e5024842540d25001c450481c949864102400a003902d00680c01144104403c0003101020600801d80c281d0050b1203104141c0007500c00070200710520040715025505000100c1404948071090b00310504232801350000780282d8031100420b130690380007009100090791102c030040100300a180c0d504c2c09254001c000b510b4070038010451031407c0d94860f080c586911901c8904200c02c210f05885201480390000d120b60365290704664940c00c1c1031711080006070510104560078421565a60100c401400103c01131302d14201003404054890b0b00240c604034800d001c4d180030707410124071540041640319001000041c02c1c0015403076000041441010b42000c02c50f441c2c106000b0150ba1b0f001ea03e01805548000150015640d54020490003015186000b00041001402030300703000c030410100707180789100780080c054641c101c8000081c030302d04100c1703946002100c003040740981d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 871683983 1250 871682733 871682753
    0x3070f060c03140c07030323030103050f06010603060303050d0e100204090b011b1e06140408030f1806010611030c010603030305100911160227070306060504050d0206070c09020403 79
    0x2070300c02d8403002d10460304030b035000c905409804c0c50101c3c29030082c041040400c1c4904051150103031f681034100c07119060302400c1f0590364801d0300143c0e041d5000240400d080c1004208050052809180c00c005460640c0d800807d00c1c8200c05505c103110b9107a901500c01c0080c180244c10404e4800b250071559240c0d1001d000d80644142d1001034007060352441d9407400d240301901c3c0c0c444201d5000306104031000d426407160340015041c000c10340700d2039034510f59640c48040ca514260301542c010200145c503440d260b0b000d2002001c0007448040301d454001d096290107840000caa60545e1442d04210100101c0c450b01c00e17266000d040b000701f02c290f090480c000207154040d800603005080980407501541e03103401440e42501ca422007221041035041204920200c0302440c0304c038450b4401072000c0020722140036140b0119100c580610f0000c400042407068480e090700c103a0004007803905000e401d2502d820000340e159010310102a003d43d5000550100304100480c1500c0075101d2440c08545a94507403c0000c012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 871685233 1250 871683983 871684007
    0x30e0a0303120e03090d06020f070507080606120d08041104200405040b011b020103050c0d050a0b0a080c090a0c11030a0306050102100b09060f030304090f02131502100b03070f06 78
    0x81e0349000442c0f06418008030489002c0320f8041c10201605006036500d100075805080c62070b40d001703420701944001036000d202040080480c0c1c1c0c020509030800b1010094920440c0120f42c1040c1d000312000c000040c2c0081c402caa1068102c0c0e89060140b0010300440c4c00b41841c502c41022200c28008108082003410b400b9000f0b0300d0050350200221200d40d40155041c1803151081c9001c0414500001c1c0158401e40010350b0184c1c4040b541c0381482a020031560540d042541c2070450b10b5250030702d02c40310b800c1180c80900185003001c000c01c2e813441450089062043c0c05040074825035102c00702c1d83c484900480d2035806824a401c122992611083c0b401001820f15005981c014040c450b584013502d81603010f080180b40004100e841c06d62100c10402150780c04c001c19540d0140014003000035020420300c41d0310010001198050703941e0783c0010380c03086500b416030007012400f807448a03603c03c129400180913400728520f0000140002180001a1408005e42d0140c81480180c16021803840da0121440c440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 871686483 1250 871685233 871685267
    0x1d1c1412090c010302070507150c08030f1902090a0605250317090106050f010e0411030c0711030105041101052b02070323090f060d0e030c060c0f0d09030e0a0303 71
    0x10b403650900110140d1051074000341a6500512050150110490202541414601301000e9103a40b076030300c0440f183c00440710010740130002c03420805056010344070b500e20240c0f001011482d00030908000740030101d8a000346810030402040008400307c0c107a402000a03c0d03001c82c8030051440742c2c540200300c0e84c6010841c0d180d448148010814a00c014001c504c1030340e400404820ba500b00000045481d5515072800c2640300d5114442c100155480c0c40003107001e00580100c59503240d016052131f0545034600181a802071b0326050030080400d01c0722048007032031031091070820f40e00d0600c480c09003045481940071315800c1c00f101051180d8003001da0f00038802c00d40301e03403900030a01c2c224034845882007000c201d101d0f11383c01041080d40a0380c60300c00c2e413044102400030076040c1444403410f840c80484002c200c130400d0f90791002401c80d06505080090580c080b4610300c10500d8041d1609020155014440310700d11980d071162118010140103036030f40340c0040360152410003a917540f820000c001481e802c950042d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 871687733 1250 871686483 871686493
    0x70c08030913150512161401200613210201050f0105030d0915050f0409020a170c041514031f17030415090803120108011d1c141209 58
    0x240e510b016000d0b0641003070a060303034180818a00700a0011010b0b003058040381600440c10f44201800c42c03041c00101501c08a203d02c400703013110b200050503019480c1c00c0c01c0010803824405824080d000524940d0103098142911218030070b5150201e920755454510385400741e0100c564240f81d560551250b4131031642c0c0c07000300000e6603031380c000c3c1070b00c80309031090301d6000550010092142c40c000c0c010841e00c840b03484c5011454400003000f0828503804c150010226150002602d00da000ea000c1200510007581032400c03c49405d198444401e244124840c1000c003800f11006402c956002c1d1403180424140746240c0780e602c1c5407140c1c41014507488019154010242c41c0c00100300c100740c804101c1310070003c11004500d8a401e05c019046002b1001016400b0052904e4002c0380c4010107201500e003441e81e01c50110b940b541882e030707203a003541c5002d010704164a144070140c01b0074400c0042c0350075450100c407440038071407014000c1c211a40c8006614000b88500c000444451310280705002c24810a003203000e0310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 871688983 1250 871687733 871687759
    0x2010e0618010801240305150d0f061a211f1b020c1c06200a020d0c020604051201110f0c010605120c09070507120f03051e1902070c080309 61
    0x5c60b00b10100c1c4550600c0404580c0c4081126000f6842a50048104400c250510001e80001400910840c00441c1c0d0035440c62100700401400d030084680300c1030f8904500329230f2042c10303000c102130081c8030301d1289038002800d4510b5409041072001c1c985900a00c0c08100b0400b500345944009840000200c84200440c80410258a480401c109451001c02003852281000341e0302e1000c0145003040d000e80b02c280c0c1d540340e074490712203022051803100950032010941310321801c0006424502c80421002c180700d50200014010f0380c0304021203082d600300700c42c88a0714415007000180140040007030030359400c0340083d030074608090920290010040c207200070301c95581c80b0014842c5001c001d81082d06690300a85a400161030490300c2194000c4040c5001424014a51580c1035481c00d8a00d00e2004a09445c041a1505a05005982e070200d9100c221200d020b412036000c204101d0010540a00d8040315013403c0842d80740390301240d60003600075008070a0030751200b94486d140e91242e484c49204000c0f003c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 871690233 1250 871688983 871688999
    0x51221070f1808062706150a0e060303030402220e01020415140f1b1c4e020d02040f05120c100e27013002010e0618010801 54
    0x840d064424403006411035480350303040c4003444800103085e0341240c0080030303482c6070140302000320340c5c4a42142e561103280d00c0c42080c14020307140c116401c400360a010803000c100442d107000044a400c903605840601c81030420602c81c58200118242440c0c50701d0800030350401120303054003d070003a10140792800340030700034900c1c0c256203840c0568650780401d8000c0c050301b21409a504090b054407001c03298a031020785d8104225604081070b8100f11f0030703135620308004514207a074400c40c0d442a80c1540104c8946203c03035800f030034112051801292403d102840d401650040e10f288813144110320329a0190f4070f132610303410001d010703401c1405920a10030340c860300000d203854012070600b20843d0010150480d05a410280803d0244201c64031046c044181e800c6c00c07150701c0707034040c0300001c90880254039100180c1182000c05000180d02989110580202c10380040002400c00f40d540385000c1c902e2410400c0e1440181c603030744e100620181c2d20580c00f10742d61100d0344030081d50304070750482603861003046e030b072102e00c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 871691483 1250 871690233 871690277
    0x1006021002120c16020303070602070533040201110f031b010b0d0303050a14090a020a05040b031e0a080a0f09083408011109040513051221070f 63
    0x410ba1400c41000400c40c0841c00c0c1000f0007101010003460300c2d101c803068001c20314581c41020704540c9542e000541d002844018072501031860818908406080f04c4107980f0500340d03110407244d0f03100036016404141160300600418030010284002d5900411000100719282d402019116100c0c920044100b444441306219105504100804e120000c03083e9842c01c0380240b0008180d900b49a0356000540d10000000e8103051292811100421600c0c04501c10700555481952010b8005da0030708242041c640d802042c0f030114070b004003940c1509840000d005501c2c1c50507202c40504130490020b18074110f0b60b404040d20541c1c081a859002c0c246a0300c04500343e4542000002035440c007802c8100c02c1c08540b5486010019003c6a02c005841903100c141041c21101208d072428a003190000c1c0c6602c3c0342c00c2c180107081d4010680d01c41d45405000540707070f0030380718518440400102e0b00001028600f4160340340e000c44049260248081651034000d00c007400458004c180c110101742c0000c5242c82c1001042c0c1c0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 871692733 1250 871691483 871691497
    0x216020a06121b09172803030e0703110607080702060a0201150e0f0a0f0e10052a03130219090504020f031617030c01020d0b040510080715171006021002 67
    0x5101d00c4c42c1450705007440072103810080c000c002401200340c0d02125014a07602a4040d45800c000c000902d181e5280140840c0c400503c034420681080c0382c200080360301041851081941603601541d10405850142858861000000d40c05100444e41d0fa03503032541540180d1310300a406c0050988251156440100b0900464440b02411182e4002403000c131901e0f005600303260b14650000c2001461001c81506102c5104c00c00b540c066594400c008010b40701028440718140307030710500303400010186403071196480028450400900040100c900715111118040c0c003064081281091058442020300041d1005480076071140584076460011850701103070b01040704102c0800024143c2c03400601c440350a51b020304004044c081072104000b611400c2c0010021440015800107040750004100030480e00d01030506860b00e0f0500100707124240d40040c2c03842c2940d1f00c3c051824801c46447c1070850300d0380e10880703640c044140c92000303111211710664120f4087d10380c0358080e04d0071024505011402c03402240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 871693983 1250 871692733 871692737
    0x20d02040e01051807230a1e030c0504030834030f0f02030d05100504060f0807090204060203121009060b031b0306010c03120621030e040b130216020a06121b 69
    0x10010444882c006d406400c003400203a0012807801081c000c0d030201c2034021800b0580429040802070f46090440d10720440c2c2d000e40c41c00c0402408544800c0104203004e2400000e05081c4001100c28440405008010f08100032b40a00481d0b0022040903000c109400c920450200f02501c02c002c61050155000b00c03150b440c254002c0d8107201e0041d22641c003070000030348062544540f11802240c2e030744440c010030014108055004071b0705480c28a01e01d140c60003076840006064418001841007076400b20850302c00c0700c0b0721000c816141c1c40d0454198070980c4103130f100400310b038941540007030380c2141007019611030340101420b2001c1030100000d0783c0300d9100407591140000c03a2018a440000e0141200a000f08280303840000c002e80c5030032405524041010346407210341c02d8103465074105503220721070141d0058299002d0002c8490040402c2451070b42c15801244190049644001094002c9d40240c003550024070f010890303995014090001c0741804008810141444140301c100700c2850100c441d01c0040d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 871695233 1250 871693983 871694029
    0x1c050a080f04020103110d090215030606040b0d0b030a1103190b070c05031b0601180c02070909060f1406040e150a0e150f011d090604110a030204020d02040e0105 71
    0xa010050021070000344120f050540d81d0107000030a00540d0083d0007480fa9008000550306094010883c0488800d040600007204c01c0041120580303030141510115498084041d0312195a0740d840c00141c0098200c45405128440c003680503c45074081c1c4038080c54050301034800f0050404100211001107983c050400c2040c0d00100d86c1a41c440c000c1f203003050303000300e0580b400c3c024485004143c400e030030285404180e1103c401482100300c0c8030500541180f86038030070071406000340c40c007940f14000c0d807040101c40c95482e113080041c000140c22248555200302c50800444920a240c013898403000c2d24040c1c040c1d40341201c2c0c1c1d1410031001500ba000e80000300b40d9011150b07110328410020789400b801264a82c01542c001244036075101501c0ca0054400c00181c0b201d560415148280003007500c60194050507036038041c07007070181000c01c4143d003090300801952018140d01d0003041c5007200381d9000a4200d40b00090100030300d81b4550160099580e0112810016642c8008021040d108100c2d002c201c5410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 871696483 1250 871695233 871695241
    0x150522050c01050a05040302090a0615110c090c0409052e030b22080a0f020c04022106150a02100e0a08250b0112020f010305070c1b171c050a08 63
    0xe9400b801300b480365450403900e404c1c1c072035000ca1504c080648210001c0307a2603110a0090051185210026070014500b25001030310103402c2a550306d100c041c1c40ca014903490000701c0d0f00200c9a0088074060324040b2424003040c10314000c072040c0c143d030308a20388505104104030000c1c0b640248000b07100700c0303070001034807580303915030003074101c42c5065941d01e9907402190300440320009030409001c2c00540c0340945655403111403607000a410445900b0f011407041e4810040032410060242803c0001c8000c20507403109a9500d0380868229400c0c201c002c800d0400105070600103503030024401085031802c0c00d06000400d41842000c1c0d4841c4500401007200900740040514800348194001ca603103204d83c000f18850085484101d0065004e801180880303003440388850a50502042c200e11000c02031800304481c0c80c0c8283c000f004000f84100c001c0221030000c40d40c20720420f2558031381e40a800c440090303143c80360000f4046562440301d80114210405c0000b4109101401182691144d8419443d03044103640c0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 871697733 1250 871696483 871696487
    0x7020c011202160c0303020a0c1d0412030e010e0717030406022806051512070f0504110903060c0a0909020a020309120a0b180f0123040f150522050c01 66
    0x14114520300030b40c102c510701000c503c4c4240700d60021402900138180400c1c40742000000d0046540140720100c1826841c080c2684884c083d9a80c403030341003240c00381400c2c81008110050250815116140e41c00c09980b00485070003c00e01c0c1c000c0b00c07591811005a102a482c8950701c0340510301c140d001507001341020b401031001c0d943c1d1100f108800d1065800d140d4180e9a106400c40707809a5950709009488108010f8604002d035589102c0c40144000303052003032410040034081c1065000701c1d40038a031542844011101c0d80b1341030f40e0340d040c80141500d5032441d040505d200c2940042074094001460280006102d00d450707c210358100302d060703000e1460f1482c001c042c881e03108801d0a48068038400c100914000c220400102d5000d5070a40104140d00c1c8215880340745450240581c1400c00d034503024400b810002d00c030014003e186e403003440c1d04040369240c3c1016044580e20050140244002c01da88843c0001c40e540610312540038048018020700c3c40108030b4050396603200006101da400341c0c1003154198 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 871698983 1250 871697733 871697737
    0x31a060910120207061505010509030706230316020105060a0f270e0105060307051e09090f07030809041b1215091107050616050f0a0203040b0304030e0907020c011202 73
    0xd00394200b800d071190800d801441260701c01d440c1600e000b0f0b07481010801036030714410844010f00c02442d2160411220100080d03c84003d445031130180413907a03100c12012286030030102102d2150301c4580c1e0b101d1600103500070f606240400181b005529160002d16140ba0585401e810740f0401c81c05121000d05244201d800c54400e071801c48400c255448140030400c0b1a40650342400301400300104450034060b05152414903603401c580e1249042c1c0c2801031459078412900b002c0b40004440484040d203d50301828100711140d074150740c0c0c0e4003507100084140080080100322100040c0c170204a1000352000e41c040e009051000d82001800006202c0c005d04001c0c3c010350400d50160381050108ea41da10840070446100c0302c0c200180101c042a01c400b80001071010681c014a00c1200d10010740f212078005225200d000886c01d4801008180a0b510600c2007041d0b4020300849283e4690b01d0034141000380c8400401005948240c0342100041d040318400305100c44001030603141c00c0030044c0e0441c46503000c2c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 871700233 1250 871698983 871699009
    0x160b04020316080a030e04050c0d0b060d0e0d080f0705030103020907020f16182d09080409090203102903120403030f0807020a0309030809010210050a0507031a0609 72
    0x18418290810b00034089406039000820010004042c00b846919000d00b142c0540807495120341e242c801000740303c4c45508100c407841800d4080c0095100300c000001120b43c0a40b944e00700c1c10700e1030002c42d0741d804c000025003002c5410590321103601c10b039221680c8d0007541800715a42c01c00074505000400c0182000c1e190950040460300540b001800100074041c81c0c03000d82010040700c1c0c402d001e8100103050391114a011481c00c4c0c01401d10580d10851035041d50640d41c1441e103c400003601c0407442c041011035004490640d0712502443d59265150b8200014014901099100c2d00070300002e503016440314427540000d00315024890800420b2003c501c000418140d1202d501800382b034401c813102c8164003000304007440c4a52118038200507030460040c041d5000074502e0055500419114011a40040140b822a079200044582d54510000100c1c00c5c0b98a195000c200c0310709200c2442664540d90b0401441280c5640d8200000b041e101c2013100c2024800c100990480d004020300012030404103a41c4241b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 871701483 1250 871700233 871700239
    0xc080303060307080c2b0f240b0906090c07053720040b0604090203090f06010305150a060b1815040605091329040b1f031d0a0c0f0902160b0402 63
    0x440d0305951125600c1190007e81110080c00c0711196201e00040b01d145514220503400d010000101c00102040c40024040c05803440703803188400240390380c6040f00c120b540242e406003d64080100d03069a00714883c59110000302074640ca082a00740680301414a141101d410a10001203005030344050b40201081c0e2407882e0300a901d85400340c445486d980700500041020001c01071350380c942594040d040c0000d003002d0a80c1500050010404210700113200101100c1e004e41d00c4600d521050000002889070307070701c85000c2c0c000114140044001c488808810000b0654064030b2581c004c1c545c0c03020302d205a0059401003002840207044504107205113103006901c85100050021a18409410110f0b00380001c5107003083c8007140040c0e50270113016a8031f042c0700c00d0741c0d2032241001d0242109508504002103004156a034a903120301c051010300c41100741c2d04140306445003251603080c1516690807a002d0f0700d002480c0c46500140483c914401c441c0c07090409000c05240b80001e0ba164400c80c0300292050f0f034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 871702733 1250 871701483 871701559
    0xf030509030c0a0f0605090613080d06150203090108010e0105031b0303090303070f0c0e011505031f0b12060904080702011805040609050a0b010e0108060103090f0c080303060307080c 80
    0x4070b01e0034104201d80710180a00e0b03180d0b040c129280303055025584002c2c145985504a0011b0264240c02c00f9001d44003d980000750035200c1c2c0d81d640704003004110a6200480c80314108402c10803007030700400240325064003070341c410929a88402c600c82c039610081c410035401d030740a10041014180a03610841c15031100805503840c00d28064001783c07641c2c2009a09803540c000004402c0d04208800c15921700a21082d0a200003d40c50840030300c510103001b98608051080010000b0074584842802c03107108a0340c1260005200d03100d05440021381c000c1ca6009581c03502d041c01050300703407915556852040394080f80151510b9400d90046551706a607d26800ca40b0f41e0045001c9131a546a004400140548030030000300d502d01600c001040d221884005410b014513080040c0d07544c1da00c0244036901260a003001710b03d45000c1d1604418803a090400a050072000240100d1240c80c0400194020715049085804450301c941d4190b480d44101d9071070a500140005058845500b1128008680c0200d074071690 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 871703983 1250 871702733 871702747
    0xd060e04110f1011120a0e1f0203030c030415060311040f0501050307060311040e5103070e1003030e0306010b120709052e051204060e1c08090c010f0f03050903 70
    0x580e0742c0181e00c1c070f0808240702200d40402030411301c0c0c164440e0b082484140070320301e5072300307901039141e200203030175500c10701e00000c00601807040c03a10ba40d01d41802c80260401c01d00380d072070503c01b42402000c44480d12450030074180d403c07041c035140104e41c142c4500902901c40203150400560050503502c0a030340e140380e020701c0006000b0b002407030458400e0104000c000204609144500403607441000526409403d0112500c0024030702c1c07005005903a003c40f4820245036040d00040d15010392680917050281c000c0c0c007000355070700421400f0707402c680c42602d1b1040e4200280d000c05450384070900072021112010b02040e01c1148814486541000450034034003400c5440300080b607000c6074160081d0320302c058032003d00038040c402010b018003410f4842c81c2c01428510100e8000c074401d24043d04c0a0855900c541c20001c0f0303a001071010602d0101c01040080c815554004c002d8113000e01141e610065010b903001c070302c0d030360b5014822421400c0001d45d640712582d845100241c004180107044410702c1d1205000341 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 871705233 1250 871703983 871704013
    0x2091206090106061404260a21030c17150604080706091706040201020d08060418060219080c0d1a040509100f2309070e0118060b070b06150d060e04110f1011 69
    0x3010305035141200748406a19500405400cbd90803000c442c10411000105110900d1030402a4640080b40d61003a058107241040005180c1e0003141c1142015000c1c00ccc10016429410910301001c40e0039050001e04800f002491442c0c90f5241201c01a0141c0c00040380d1040c4180303e240702c1030780000c0003840014400070030080040300888100080b207145a00041840491401c64042980e2140314607100c0c01900e8018180c41d00d5018268241050686601810100d40424048025000d0300507104014514201000320740c1c82080d846484900351400c5501003c0402d54019142c140562952071104074011005401c030b5600020721284540c058a80d000c00e9140085072958000e0030107014000c1128403030013004c0120b40c503035800b444e52043d082100d440041c580e80d480310342c0000c0c21160015888a4040032003028403c0e4688002503a19211002c2166000d21a45501950060660383c16891100c0244000e1028000b62258001e0f180c01c0318031815403048084120b000610015a01042c200a00c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 871706483 1250 871705233 871705253
    0x3070f0b0708040b1c050603060709150e04050a06030c0b0a1b02120a081b15010b0f1309090605130c090209060708130815010e0a02091206090106061404260a 69
    0x451a030b0f00341c11700400b0b40350b2401070044641024048000d004142440c2c44007410b616050300c5120b01d40100e6070103a054941c0903590300c83d0328a10150043c80207103441c01508009091034002201e203040390341408114007054900b81c0e02800c40e161200e80f00c038203290f04445c43c1081820000c0b40d001841d50b02c1c0d04106442441141e034500c0c0310f840465212598500c2da246c5800c40c0c03180008441e4072901c0b10347c080301010458036046a8020000c2a40c4142d088008085442403a01c030030f105900000000900f405564003c1a050340583c4080041c0d44070088001c48000120201400650082030300f40312441d182d50040003c10001440c0500c0c20b41e40b50754204081e0810001d0a823a000d11076010409290240820450442c0d08856050300f5030404041c03075800381c1c0c068005041c1542c003082b00600d584030380c0d8450310342c2514031045510b64600302c4882d0303010302840e00600c80060501d501c90405403003168103583c03c2d10400a038110441240c00c0310b134050050054100865807107507945220206c1c100100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 871707733 1250 871706483 871706497
    0x40c0f12170d0207030923010e040f150e01062312222609010c1b050603010806161404030201030b0409020d0f030e06071a09100c051803070f0b0708040b 67
    0x240c2e58192841c01d9100250000d07d800e48441c03916203521341d8140b981e4443e51041d00482e040f80c0c0003038003406102c1d030340b4020f00e41d40603d005c840c0040e42020405000801441d41201c1d82581c4401540802d01b9159818240004003d0b011a00c2403042012840c6443c1c16254810b0304c0f003114909680c1e51580c50b0310361310003010b400c0c0c0e030801a5600d9414860800000501c1008071100903074600b484030000206520240b50024142d0040c08141c1220310888842c080000d0400400240e1a0b5031100d17201e50b06c50b43c0030b0f50b0303c000e006c00261184212078041c4d0300c07814014290400072070901d807031500154042d00d5031710072580d84190346e020844010795a60100e040700c640500c0d0f000e01104160714010b0100540100310a1041900340101e000003031811260340610100004200c10503110140390b00e180c8100c4000045045052080f01c4015603441b10241c0304503c00031645407000045042070646980703d900800119442c000018001c00341d43d02c0003030081d20301c56040546841d9650000740800c0d00090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 871708983 1250 871707733 871707737
    0x10818010c111005060105030c0708190e030613150e0a060207050106030b0703140402011409090403080907090204031104050403020a0501020309010501180e0a0201081504090803040c0f12170d020703 87
    0xb5010410b464010001c41180d001010002c00260410360b0000c1c0440c003000700b01c1000c004001464008002030002514041c03828074400600010f000300020380019840400306000e0b2091b5400500c420070300d068420034885e04440c2850040012602c0d2034003410004010b92005e01c039038000e10b0002411032000701021401600005946405c40c9440c14100704081c120000b01800d0491000c0c11041a2185603009542403d00301000401072003060f009000304a05030350f004040c40100420315400c074031420b22074040501a203420759203070041c180c200e025600001d400c0104404550300c507810f155000f00c5d00540280100c501d1042c4030390799142603a000700c40300c00041e5142c03001000702c00c2e29103151800d0010003d8050160f00480404541d0750303212860080d042000d00741c007003006030115810799905100040c00a01907084030b42400300b69640306840441d208003141c1c00c00121958211501000d446c4017002014603100e00d070310b03000c0000b19420420b614a05081180480c0c6c0038a605c01454524460f03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 871710233 1250 871708983 871708997
    0x906040216080304120305090706020322031a06150a0c0f08040b21010b0a0c0b040606080706050910050304200105120901050411100509190f0b032203080105010818010c 74
    0x1680001b825514060240c2142e80c3c882c040034001181c0102c20703203032741c22031a52030004040f50034044c0f09030340c541552007d0170694506420942160380d001040d032080c5000d5811500b14241701300c441c042840361007000300028048000706c100180d460282c6482c0907001711141e03814240c458002d84800d9001401c04041c415600816042402140d4041401004041040fa080551450015024101458004011406c01d900003820400f40c0d0f40848085c0c40343c80d0481e000c05850300400b60060303021802851140f45140b0414120602c101700301c130710030341d8001801b0541000780103904050a450f180b00505022041c4000c00e101010508440c0c800d800440000c601f0b802c007418024040e5540d02200c9014025007010983c481c2d4000080340e0110314141d83d90410102d5041c40c0c0054a440ca0704040800c01248400096040d02d21019500510b06072154200b00c0c00040308170418502c50354001000b280040740104070a42c0120034690340b003301c20b00681c02d09514036034049d0844034000902c602003166 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 871711483 1250 871710233 871710263
    0x618210607030513080d02090a090c050705160b2b050708010620030a180b0c03030402013023090d030c030e0a020d0c03050a060f0b01020307020906040216080304 71
    0x1040c0500ca13000f0702010f66200700901c075501c401045118251015110680009080507582c40c2ca4107108000d00d070380f003010001d01414200040c4940d10825003910180300d03a007031419500207500c900c50102d1362440c40541c0f915401d04580d031522407000d0245411031100c0f00d0840b184070030f83e001d03151107410a50350340301071581054805032135688096100003010250520031140700e0710000882e04540b2850038210103080700300254003001d0546421a040300c540200300b400c2c03031242c00005140618402d807148003a0b110b15403000c2995400400305c0c1100d14001482e82110800303654024140130641c1242c0d01a204102c0709240c0c0b022205855503003041d031102110300843c0758036120340e14008125140520036030b100c0b9003506569071101580070f486403003a80584400c0146c0320080e40700850b4001c003070361980005401c20400503d9501040d026860070030f41001515032011044030b43c1d05038000c020300a90b444250500c80250090300130903000e42091500080441c4e00003000d0741c07155220341c0d956071000d02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 871712733 1250 871711483 871711487
    0x1d190614011b050c01140919090e03070507030f08040b0313031103090307050f19091a04060501051b1f020c07060c0b0c07030905040f020c01050906060618210607 71
    0x451020544001c81c82d00d8100050f80100c0d888050860902e04110403c2440510ba44c55128100031250320040304c8002c82038840e8a400350608496046100700010408222000c0c2c03a880386140080007500000d0341400010800a100181c560160b940641001c1d160341c02c80c1041e60050b103015030080000d0544d1010903500414100c4403c4c0b003113014508240078040820b81d1003210b4040c02e8812444250301c540c494844130041c0034030180004468903043d6503800c00741b0003003404070390203201e05000c00c2c149680c80c281801000120b55069450300c1c03038040004411403544d0644040e25006024001c1240e402503013629007400340028002006a03101c1c86483d503070303252101c0c0c0d80c0044184006411514041054001c2e043d6111450f005144e551340c42c0343c6011500480c40340c011079401842c000c1c01100b02c07800c0d503001c1d0400540e82c100800090300c8203c2d0b13065585008944441c0d11600800103d0b00c20820b90800c2c1c9922080a0003615441c202d10382c207401d2100c040d642050299004204014000b0707 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 871713983 1250 871712733 871712747
    0xa09111b010905210f0903010b060a091503021c0b01033b010504020906010809030c060f0f091b01031d0a06050912090d03050901020c15030106020f071d19061401 71
    0x60040000c0c0f503c44002100b04e101c0341d000d0181c0c600b00d4102d01140405940d1003e40105421a800804040c1e441543c40406404400710340901c0b02e02a201c00942e540c028042e20882c1ca001c917040865001100110042c01e01400840240e2810140c68221a2240d10714000502c01000b61820701c4065240010114010140c0c0c000071000c0d5580c1004188009611010f80d4550400e2080c6020b40b066078400381514554419080a801c0e01c0c0310781030030880d040200e41c40300c9000e2134441e8221072094950703010440d0b40f070340990000f400b01c0510b0480007110b980203900065202d050781003118160014800307442c0c140f41d04100c2c140c40d52a190410420200400d001c1900c84640c0d1500c294240700c900808202d00f00028140202031140c0090054116030080040f08085c400042407806020b5029840c0243e6800a201d044058480d50301900040300307000c11030b0301c00d6440482156020501a0055034110103004e4400c14040004c0203800a064038240140310140c60103441d214007417101540010001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 871715233 1250 871713983 871714003
    0x30e120a05150a2a1b0b040302030a03141e060d06020309010609060510080a09230f010506011b020904080c0327040203060904060903050d140a11030103020a09111b010905 75
    0x20500e070180c145800c0d0225070b02150703900d14a1401c1403d4940413440c240c400302e04c171240a0710b0004160100810540d0000003047d00c10030650b402d2204c403603965241c05c030050040d2070720385500c1440d4020100040e080c55142d075001070000c16403407140c0040e0311101c01302c1c0d000761600c00003651034010500481841c1d001700e800800090350b000c4440d6451000092904802411b4034442503150020710091181800d45490034540002001034040f0906990a90381c2c456110a80200c1d424030000542a6001702c8801c10607040004890303051003da5820080b458400078411515400c040c0040c3c9090241080a08200080441c801210311405645d000c3c0b0408112001072240c3d00420401400f6102e16031800c0d00107500c108081000140e924081c2c0d954010f400c201044c2519200345610003c2d0803c1134203010304481001006001022003110006100901000e9003187d41040b0030007150525900c0581480c0d8090440350410300c0751040ca14000c10f4960001150307039100c0c43c00c0c10900c6000c0c401410a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 871716483 1250 871715233 871715261
    0x20d0516080a0c051008010605030a1b0215011a0a0e030a060501060c060e0714190b0d02120105120a0209100e0a0203090d0810090b13050f0121030e120a05150a 70
    0x114000e8010011b29180050203030100300080403000c2810030481c2c3d000450508a40003440302c80034070a00c4002c0d036840040c2002084080f1000c00041d44c2ca485c11240880c1e81e8190b071b0702500d0058030314001c1c0d07941d907409125131742c151141d41c840078041401485103030702030708080c1d5901d4200140c90600205540b0200700c101c1c0141c0003c4020407031030755001101d02e0405001c0e80c00403100c4030912001e8580004647c0444984480020314507040b00c8994010604034050304540c00103039880f80140440102d0109000c0e0301039109813104c074050300c1c1c0b4100d4280d020401000c1e4401507500d420354580040e9056410b5080350b60044140801d140081c4190b44481421789418800340c5010040e000b40c09103144568043c2c80d130f0f901c01e0000c1a48034a8062400c1d00350102083c0406d040c000e0b103040c44901d0910550705000070480080088070070604003c0c22050f01540c0c0c540b0121206002c00911a82003212048540700304c096203400110103000c05402e8090314840c410035481d2003464038040c0c40917140d018803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 871717733 1250 871716483 871716499
    0x3120a021507021c120c0906091d010308070507080a0503460905030f28030903020603100302130903140705030714191119080a020d0516080a0c05 64
    0x440d503540062444440ca20128080d13003000c400d800c054074150841001416214140360040f40f8154001c880328044842650382c41003129900e00d80790b0302003000e82d030101486012800040020840c83c00141c500e032401501a103060719070310007080340703001c031040c030121040d4201060300981c401058200c07416280c0501108110604900d203818801102400c3ca003405000e0006969041e40c85001c0020180c030014040f04d0003001c44011840d40d421018500707010014003140c01d201000d41c1c0e80307041940598035480f440106401d5901708807080d0401064007140381c0080c2400005a5110281007200543c0c43c00001420001401c004000c202000034030034505808202a80001d2000011160620740168080304405540240c0c1418030001c00e00c00015404285d00794001d00100c101403c0c1d03250170446004541d020101206204105140300d80140e035001101100c000d4200549600803192003030003901c0c002030020307014a9210348140c100c091a03902a00918007005005591440500030486240c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 871718983 1250 871717733 871717741
    0x27030c0506092d040903050409050c0c060c0a020a08070f0b09070614030406110c060a06060e10110115171203090616050c0a0605070315050114090a0503120a0215 71
    0xb12002105000102060f0b00c000501891031410412042c50050081c014080030843c0c6c20024000d41003400b0f1011a14079020100341c404c118001102c44207140c0c000a40190740c2c0b8210340c0071309500000601c405501400c0003600c0020f4521000380680c6214640852154881c2d00349100c0b0741c1030007080f01440c0e0380000c0c014007000d90810b400300c2d10340d010440c0d81a501e03130743c81c90400054040c510701c241303140e0383c00b040003413021300d011400034841e450720345082100d03076a1460200e42e00c405002e0a50341143d00b03000d94038252481040d11001d078010440021610804031003084441d00e0440c0e00808a03007660003006040d80d0b009005501c028402c21398281c2c00c60410380303401c64072590040c140e20b490301c481500307111480e4000c0c8142c1342ea40b450501900ca54001905010003c0c040456062000902e007203002d2140e03640c24100d1034203990041e51002c62806924901e8141a0b0007a90304c21f0b4000100e40001580c1e60b02002000060b0301190381d0326865060581020b850302c40d4529144030443c140100b00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 871720233 1250 871718983 871718989
    0x90e060f060f0d05010f2f0d02250c0807050d0b01052b0c03020f240c07030c3b04080a050c2a0a0b091027030c050609 52
    0x380d40108044440000b030162100000304208000400240b0300d50905440c0c0c0c04204841c3d000f0104101904202d01203d01070006516404028018410808005200110300c5c403615a004e00001403c12200d032040418907035207141060341d2501c0c11030707400c55511010b11558009001500003014180c40d142c40e00300c000d90351070080c0c0f5014003c56000740c000012030300c580c901024103079411315034145480d081d502290400398a40c50450001b13a0040400c0d0112002505000d00503441001e0101d2035800c01c11a01d1003441c00c19400030440d50418494088048007040700325010100070500c0c0005c02172100508248007205951402203442011141c00245c010f01c441d20b0038179036000740d000d18000e07a1082510301c16122400380025813030152050f0a60384401e10406566010700041080d400142d0300c802100700050351f009405005001d0070b080c09003180904246c2c0d40c0203814402814095450308442401d080301010032458201040031f5990200203005046682101400003a200a46030134160408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 871721483 1250 871720233 871720261
    0xb01020303040807020a0302330703122f03090c03030301050619030204030b0c0a081b0d090807210801050402090a26030f040e060f03120307050f0310090e06 69
    0x240070b50324001011000c40d1b44000140000d190700500c041d0321088150212082250032940d88200c0740c10b8003904000300c1541070140e0310310039030581d00c1400040d0b0000740c800c081c154040c42d2400c900c1280c1010020b1521400c019010040e14210b216100c1c6000050945003441e10404240240c00400041c8075580b01d00084a214143d002c4c8400e01484010408400910496001038203508140c820f1250504a8100030101408513075030f0141542c540442e0f082c05520241850b0074024010440130302c9502e0030350410004203008002003030502c06191103000d000c06021002c0b003006001c1031200a207080c0c01000260140809540031414107900002169140c0e11501485004842c08003444003840603c60052005200b10000d83c1d4654003e046000c4450b00302d0300410000980d4900058101d04240710085d0300c60500500609501814058211071948040d020a04100d010842d0f0101200d1020045004210018034114058a0824580100c030f91040000c040f03500700c0d00500000c03542c1450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 871722733 1250 871721483 871721491
    0x801090504050604081c060b07060c0914120c130b0111030903122203060b13050906270304060206072007060f091e0306050f07051e0421060f0b01020303 67
    0x805e603680b09400d0021450300750700c4c48039a0003c10700308080400c0700b903c100050042184100b10900a000380c1d0750007526400c0c0140a00300501021204040242c900454141009400f0106841007090f990000c00c0ca482944680820411344403889000596844160b02032801800006181841c0100e0002600c6081201650750303850301c08a04140080d8122541d40c115520b00c6190f2511140d8030302d02070b000340c1030210032144101d140340540d02d20790780c95002d400c0c82812800302420a0f680d03581c00f030303418500d01c00041e402c088500380038080b510403040000f08050100354000340450303d0000001003002c00c45030010b600094030000b0341c036041900003d60b141170f10080d041c941e0f20042000021642130725190300100503134034042144510034003d803c80d0300c240c0c2d000701d2052100340e86000b200d0a450300151408800648100104000750018807811000485200300d064681550b5410070411148004d804140072402c100711401040300d01d11414404081440703052041105040c0041e442e400014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 871723983 1250 871722733 871722743
    0x6092301060c1523010807050d0c03080f0f0d050f1302011707110307150f09030c0605060a0e0a0c1106100e06040617030c0c0f06093c010801090504050604 68
    0x800341079000243da030810118400d07640756003c0c41c4400d110035602020028401c0d24200d009460001c146410120948890190081402c3e001e00c0d00e103a9841c000c03a40318194100080c0001c0c0020400888070f0380007080001d030144004100340c1091445007031180c1c405880400f81c9030540b490000143d8200001001031204142d280039103a0781d140c1e068801c2208101d214a050000003508420070204420b00c03450b81164840401c80c102042c1d200c4401c80d40c500e03602a0120301c0c0784018200040c0c0c181c0100351700920181103008015a1820b41607145403040e10218a00b43e02c40046181007948400840e00d10f0862200904581c14201c0d04c0e51341e005d07420b0180d03050b09103012001440d207440d250807240080500350548900354550b503841c070340c0fa90440184903046006020b48551580740904e85a002c0642c010003d5261800072010001c0f500b0a094180007081801002c0103128164402c004058101e0200400c1301d00316403070300040c0540416004040060b180105000106200080b001e900c40ea2003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 871725233 1250 871723983 871724003
    0x51501120903090314030d1103011a1305040f0c0e0a050901210f0c15090f05040c020f0f0304060e06040b03010e04030203190e040501060302090d03030c0507050106092301060c 77
    0x2424100e508070f450b600003030318590790600e002500007000401000700c3c2c40e00480030841d501c510944c40c1464030081c42107080000510842c00102c450900c01082c0c5600c8166090150386d40d18800301e82521202420110402da4580c0000000f9801801002d040703030f0110b43c0201a641050b000403035035103042c01111008191200c01040310310340e80003110003058102002400d0303150946060b0740b41c00b245000d0310040c50320304c620984400f401010010155020300440f45d0440b400c0806100041000b030015104601c5100c010880c602c50500840e100302000c200516601c9080c9040507004002480b50305020b004100010032000d0080429241518144400204543c480d403d040f4658010400300144055440d03900c4040c8940000002c00308260036501401031342c0e6544410b608900544c0782e2141c200c50010781071303400644240c0c05200104400c0c00c045013001e081e500d9803400c484582c0c11400540d0790380d40380b982600c0c0190078044501d14021009440b103605041005010305907a5030020a10200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 871726483 1250 871725233 871725251
    0x240311060d060305010e0f0d08010509071407030806041b0c06180c0b09090a020a08040210020708030d0911030309010516080906070501020d0c02010b150304060212010b07050105150112 81
    0xa014101d81c140001c0000510500d41c032400c20034000d2010608a11981c030039001305004c0c0700300214411109240c60345505416a1130032080c03003034404000b00300c0b9081040300c00016401c44007040181c82194026a51540c0030315100e024001158160384441e00e6083d40107000c01710b502d6214007280c40850f807000000c0b402110844040500c41c8441000034003c1c0071101000c50900300c8031018082991040b641c00800d43c1b504080e640072449400b14203400aa000f2000902504185c2040e5009864a04c11114603503680c0b01c81030704680100010000b1940c80300440c8040c0500c1c2907c0d0095130a0803809075241c1006100060a18812429240c9202c0000f0a618041c842c0394016500701078009044140e84100d58a0190300030760203090b00e2a4414509000e4005043c0f0501c1914401c1030003518040581c103c0d84c500041981001b00115503540d004c01c01405442c42c84280107000b000c1a2a207642ca6207060700e011400d48100070060b0384e55903051448a242c682e40200c40326845c00d0324000000c1c002d40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 871727733 1250 871726483 871726489
    0x82a0d0f02040314070905060d0201053f0903041401080405120f030f0f06100e030316050303100608191a1e042304082802030706240311 60
    0xd52035903240c6600c04100003044c414018130405400c1c2445082e103d00079104c4a04208030b5030140c5016412294581420300107500890003040e180003092070740080c1d110401c1505085225841aa0f500d992204420a0207400c4a0b540f043e080030580002e11308040c1011068118940055100d504010324840410140b1805000380864001000082d0350342d51260400304450754801d880b04900d020398080060755911049105d40c3c02108020180618000d2042007100d0110320018030343d0381400104810030180d0b060b1444500d00c076128802468692400820080e940000d6901c40420701c1000410440c030b060f1100c0d14800d0b000000400014600c1c0490b80c17000004a024084542044e1a00112682c00c5041a900b00c2c4032134007200c042c4085504250f1624180e0117881e0f2070424661510701080005030100050103800c18042cbc00956615140740d20003004141030b0b02028096000003408070b0511900c1d018841034280d003580c40038a003c0081c42c90340308030a1240300c0034000c05481d0026607900d80d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 871728983 1250 871727733 871727741
    0x20f090103200309031308030712050904140108010c080c04030507210b10032102060402090c210601020106061b020d0c0f0b1206030118060203090a080316082a0d 71
    0x580d400b00140c0320b203004240c203940eaa200c482a0603000b501c1c00d10000c0c40c9040001107a000951000b01482d03002603180341a01e00c0e8101d00106079010b92100020309003005213803001070007040518004204290550b01c05000c102c0c1c003400503031400743e0400c4140081040000e00d07904540c1c000c10741c041d8903d510b100c1080740f000c1445001340081940000c0c04143c01c800001301d0305580c010400b42942d4841021610b0390310b4490085000503801070300c0020054a0300040e105ea05c41d0707642011900d0404101c06503090368424510360300b0380c14040030900026590910801014121a042202c0d01c2c03514131401307400c4130110380e10091190022545a000b0008072904480050900440800e003446d200c00c060040303a00000040e0650400800004145140c14002c00346d5880b08014080441e142a403070311030195100408086031842044c40001c0050300700c50095220300d0088155501041c00a01c0c000c1030a00d000d041c5201c10382c003140360300383d80c400401c2d2402d01c2c010752600c01c1d9a03140c1001c02250701074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 871730233 1250 871728983 871729031
    0x27030c060503090c090420040c3c0c0311010b0112090507091505041a0901060c0f02060f0d14010e0c0c010902060304051f060621090b01150e010201020f090103 70
    0x100305041c07108225040c001c40301000d1050740c0d080241c800142c148800c8074141d840e80d100080044941a10300807100304411910340ac00100e014086440105000410301c10060010014480200c01014982d000d01602d01034000030b0f000340300d80c450020000703040d500c0d9180c0346103030315a8560790002004001c0005000400d00020148508840b502000030092420310800f40240e04061803001e030507005480c00c4140c000f00074401d04003642045011034000b90a0b003011a412820344440c0d102685d80e94000e06420081114590f948107c001035031030694520b101c8851321101c540c001032081c07022440300e5580c0100c41c0383c0e1036a00d4405500205002d0305410304082d4110b00004244400c2c0003010074001a002c456a50702a2238400848100c2c049800f94490703800011041980c200c42c2c0c4aaa160410104803003e0012074010015200e0300301002e4203071321064441084c10710704400e032a04145144100b02c824002141080f082c01c01d0b100c55803040012003810907546401e030441c80380030a8200002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 871731483 1250 871730233 871730239
    0x7140112020a3e0c03060f070c0804091b0509012010050a1b090807060f0e0603070c060501090606050306042c03030f060d0f3027030c060503090c 64
    0x100c240710b541005500d502048000c50060500d441d14000010004200b6007048001c1c5c0144040d03a03401d0744103041080040d0000c2e00300941d500004012940b06006000034082012001586041100f910307181c1c66540c084260a001e401c1c07200c14142d03a0030200c0300c483c0850440b05514603480d000b51143c10404450304a450581c41c003024400b0f428881c2d40404401c820018403500010215441a07504030344512810041ea031190b00240001c0344142e03100400d4400301e051a120000d41540014450741080b40c4c64800910a03011500c00d110990084038014030303181d0340402209040260050451100400f1903004648945070201d5107198045c0c1501d545145401c010042580586429140d50041d1604a113601556001c204c03d0724205280c5050f00c0d0b4000041c101850a41d42d0310818803445400103680b0350170015401002580c14a0481c2d4500147d0791903021180c0402d4207103e900c420751000e0b00e0903896502040c80054901055802a2603080c1000d5440390344090115203441c80c8003a440350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 871732733 1250 871731483 871731527
    0x60a1a060c070311120601060309033c030e0a0816020a0b030a050c040506071e080a05071e020f0108040f0f3905010e06070503030907050307140112020a 67
    0x1000c4000841c2e000240c070302c580010303003010311040e00300003400603520001d600d0340c0c00113001008854000d9205600c11032090500c502048190448400844040660504514040b9111102c420b031480401c802e207183ca41020070182d9510301ca40c0340e44505001c4000c01d03c03032001445181107580700d12000c0c0e8041d030080c2417690040e2141c000f5503a640095480c02c0d016410320011443f40740007401501c05898016000c0381c20710100d6100c4070425080500518244100079040202160491000740f100e542203442d4182e032a03103586405d81e900900c00d0740f0071780e200310b03000c500070010f03070f2807132031040c80a042443d18882540f038a003080854901b00c80801040d5001381200e00042004030b82d0690607191410b900320880414100303403c2c4880d11010620501d942110805005640c002c20940b111038a004d0a03244c24550199140340c510f50041d1189c1d032031a0322442c0200024502045140044d102c5000203844034a140030019105a4681400095030341c0c01003442825503104259500d480c080c0041691 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 871733983 1250 871732733 871732747
    0xb03150705090612130213050402010e1e0a06020f1902030a02240a020a0c06080709170c030102070c1505040821070614101e030f020f18090c0103050405060a1a06 71
    0x140300300c1700b442d001324010b050806d00c80841035494402c03d44226010303182d40d0f00461800c01081031a800305400001041d140c28601075243c0c0317404440001514042d002401a0100c9050003071900d40c041d048400c1e1650b135507540b400140c801140d0400825070580b1100c03414501507a00d540164050340700c0704035020000c90200c4010b03a000400c80c2c00c4900402080c000d0300e0326070f401154060320807039400f800b00c1c007984000c10107800c2111021449510840560f04440100d100003402da90001100342d5044158072801d1190081e00c14203650b800396203041091410b4980309c1000e0311080c01260000703c54a4121100042c0d060340030854612a601400402100c0c41030307030340c1584842d0151343d4510300030501200801c440304410010345414040d0b88c0c03111540b030f185944180300701c848480e013282c101050b94419090360f1035002e4401c06089520740349111600c0d20480c114070b041c00d03c10307c5138101410130b400d100110f14042034035908070702c18440c04504482100360703000c0900c0780b0058141d00440006418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871735233 1250 871733983 871734001
    0x7060906112803021209070f06090b0a2d0e100e09070e0a030b0a0203091011040e100b070c03170a080f090a051606090b0711090712090b09010b03150705090612 70
    0x1050a40e6045140c0e48a02903c1305d2046441c80c2850140400010b81000814048dc1c01104a82400b645c07990200d004c283d0080313040c0306443d90740a4141b0108141ca40b07004814906800007222203a107600e88523140b000ca1400013542e10101401140a10644c01c401501c1511000c0c0104081c6401111450050504a100c00c00941c42110421118010400e01c882d401d1400e0041c1c142d003100c507040036403e141c10302c0b0600700550005042c1032000300303606000141c13016901010f012654000c0c0222800b59285013440d280520445000c4c8440e09410414a106940c02290564000000401034555a03940300480b038541064000e01900070701c41c0c41560420b4540701100d880030f449135a91140402542c40781928880e006d500c400904104c2168510300300c0f4205005125800421f40c50310032040d0540003444022134203400381c1510070316601010003615100134085c5c941e01450a50080004110a1009064509002e44104204040010404400e94903d07040d6040f0050091402c0781034100354000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 871736483 1250 871735233 871735243
    0x615030305090f040902060910050415050a230409020a1112090102010e0604020907050f04030c150807050c060402010e040902032b0504031203110c0307060906112803021209 76
    0x1082d40308a41000c1144800c0c1020300894000030350107400c1c942030548520070025441800803414040180c10b001c0040e51903a00526410b60031400e032180d0382c0e680022540140000c50400c1410520300c80c02c0411f2002c42007000c211000c5880f1400c0060319109410b0040b0394030307060081c0d88082413150055860300f01c40940c00505000900360020811000d03a0212170341c403000111406540722642c200040c501ea4010f00040110317950301c800c00c9107415100d64520744540e8280d0003003070b5403a07003d44404906540007da07554105045003451400d08190501065480e4070040000781001420310219a003603ca40e086104160340c010255204460001712108130300406207035440403145181c5102001d207008200b10b40c26a41c00803040200701c402040c1c10740241112250803d0b1445080080c6050385c0002d00203045200e1241202180c40760450030080d080e10030300384131000d5248041011400000780603201c0110040443c02c1c100c2d20050841080d402809002282c049140300001007054170003020417 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 871737733 1250 871736483 871736497
    0x303020d14160f0206041118010f080607052b06050a1d07030902130c0c0c0602030c07081204030b0402120d05031e01060e0906030703050f160e10050d0615030305 71
    0x201c04000b02e014400440f1100c0e218403107803001d604010f01140120f082440d9004550101a1030300c0c40550713290b801403009075001d90090f0140381c260313030042c44401024045250801068a031a40c00d01c0c0c1c01450000c00800210401d0041e070b8820001000340d00d0f01070300035400421001301141b0800d661800c0c011885800e09000240d442d20150004889501901c90100340940244c003000f244100c404400340200252803203c5c041c065903207042070000314001c103440c010704060f6019589415044038910f10b0308c0c5542d00a10000d40001020069403151350058800703c0e900845066000c2c0c80300d001040350801c1840c200d4542e405103000c5c3e10703551600000290b025510550703015400f4144030100d003142c150300f0300426001440c0c0c10784216091801c02c520070f801c80b07802425910100da903503444500e0051815484207650304400c9803c0c2c1001d611403401001001c0711008080e0904d040c0780718480d074206d603008035071041e10701120203414001541e0001620403291000c0e040050340342e04003d803407504444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 871738983 1250 871737733 871737751
    0x711010b0301060e04140a06090c06020d111f1b080915090a0b090f01060609050307090921091e0e090a0b010e13020306010b1e041a070303020d14 64
    0x9140e4580360038144120011104d03910b081c41c8240d225a80c81041c04040c0e1138482d44c10348901c00032000030031440d1040801162058040407801490014049d0038555003400304003e00a650781c0820640340c000c1508000e0700101d8003000380b0611213403030403c0102884000402030b0359581984030303805500289028001e14040003141d9404000c100c540c45929000c86140249400003450140024403c1041c00d0708403205a05580b8402590460319013101d4207684800700103080080b0400007070a0a004810103046424000d119200081e166140c4088207150b021802000364119440958400c0030008003400c1f50f80c00989040f04202c03401c1e820810a4060002c0c3c00395401c0100c0ca01d6000090ba0070b00081c0c0c41f030700801c401e038030313182c400001c0c01c80081454406440b2020700320300580c0c4c18014280070b0711181050365255454a000350350040302071003858881c4075041006005590380307000540e82d05030102c00340d29a2240ca0346400c401030701850b092041c0040c1403032400b551550310a40198401d200c25 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 871740233 1250 871738983 871738991
    0x40b070305090303010b25021e010806030d0c0b1b0f1c0c021906110c1f0204081b06040b0d230c0405040e03070804120b060d02012c03010203071101 65
    0x1000b210761a88403e03c90005003003400c0081d50400b8101c104a01440f0fa0a0000e2a021401540200d0100c28182c503140ca00b014002c0b01e40d041d41d40e0818061908480b06038003c0880360081343c2c001e0081070384480c028024070000c1c1c00088261000d03c0b20910030001005150307070ac0e444842070a050369007180c00402e0b10304c0300700008081c01084510a00c011042107600508102d580c4d00700e00c80c01d1800c005800e0316056200c020040c507131091070004109682d2103000401214040d070421000003010720f2040f01015004120402a1040000d080110181c202c210303180c14007a03800001d01144540e9101030180a004943e10682d40d103564000402c16180c001111000d03102680d8002139802c045900d41030618003480103000138245540503102c952100d20440b40340a07065260103800d90425801142040d0380e6290341e034200002803c081d40c01800542d01c40600321001c0c0e002030013502c155060003e159012004407607803a6414003003040301d134502030000c56490500710341c010142c1101c95200388207503084c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 871741483 1250 871740233 871740241
    0x13021c1b0806010e1003084f080c10020a061b020d03091e05010204240908010902060f03130b04350307031107060507050702100f02060402091e040b070305 68
    0x5884e143c900c40e613455904000800e05503074913564160000d42070100003403107902c0001548204105420000c4845440300480d064403d594511030b10690045400b65041551042203a2800015400b2449808803103040000340c851000f289481014103000c0c1125042c41e40106070300c0002e09400e0f219419517826540c60030384502c000e030305030340076924000c01d40e40388482600b60074001c5808461030070344205c001501e015540c24000b020000e004140300100200e03104402881070f00b1406080050200900a00c000081600003a040780109880010103000000003d1921021030034030038200d5600c03501030031035814642811050106c01c400d81c055041500000005801040c1c1426401d040410a0702c91565952500840c090310600f015899040c90601c8404001303034090040a01c1008180d80700c1c0e840d013915004021444411032040010f00804c5081038508541c0410074944c8680c054074103811649412401909038800c12281210000c00319040c0003c1140e159440c81c0105103030b40d010312864907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 871742733 1250 871741483 871741499
    0x7140306010e0f0310020f040e06150f09010306030f050120040e011e032003010b060f070311031e090405010503010b0a090c031409010209030f0613021c1b080601 71
    0x841550164003080003100749020502e8a80b4299445200190a072501003803a982c01c48140c0c0c01c07040d268074200001150a110f4808400c81d00d5501139001c03101800c160103403c05048030b510881500c1c808500380001d01d540a40d010f034000303a0041d64009079250003900c1c5405d08900030448089450b205000d40b5450380000642d1b4400d5606480329030360b41c0c054692a11004a1003000c99114001d082100e00c0c6000020507400400138280c03410030091480c1081041e03040600312031525046500c40c0900b400103c202c04110026510311680c141000741c0c059030180c0c4031902e1030141d1451140300071030700300707031038a05090b00c0c1e01070049103900b510306000c140d88801c201403d0310441e503265504403080c42c004002c00c0c50700b900280c01d040a03e080002c1c1c456081d60356061000c40441d4017042d261340020700c03400d41d400e08000515a101165001c2c00031030030008040131012212420103441241d00e860560341450854142d40c10b007c4e40502c151900001200c00c2c070314100194480d80005006000000802d94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 871743983 1250 871742733 871742737
    0x902100305060609040504020414250801140f040b100c060f05090a0b0a06030204060f03030210050c040b0a020c0406060c120c0201080f150a08011d1f0c020a06140714 73
    0x4010003c42c00c1c00140d60500006240081069a04c0740e00c4110b183c1c1d4480141101301c4c02344080203843d1300100f506036510405800c00c4820a42004022001040344000550031412000390884a8500e40402c81c00005d0250003e401c2d502e1740f2042620481c82040c1e0488041d01c0d4031481984103102d85000ca51002080b204120f81090f401d070000001040080d084d540381617444080c02c1c8001444c1070316074003c82c0c21225650041115036200440c1842415010880c078298094518000c0c8001d107099582c4c5030f014003d03803003490b100d094041030284c421402441040c1035014013610400ca00ea03034500e0024002040000d040e40c001002c803000c4000c1c1da00c610390021841d6010786500406031240361842c034180000803c03089440700f220210034442c1d9100c01000005040a03000482c2e5141c400c238843c00c2b00d0088850021880c0e00480c100800b52500d480e0a504110040b60006600742e00404203030304141070340000910091070302d00e00d651004540300350301c0d0007000389590f443d08203912101c44840314 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 871745233 1250 871743983 871743991
    0x1f0207051206060f0d120e090609160e0102030f1305010f140906070f140f1c08010e0c090d05011a0409080730050403020f0108060904121808010902100305 68
    0x607048040002c0305070502c056a01c1303940f80043c000400e4015036407102040700300558105000a411090850514586044081d411040403500440c60341031003c04443d240c82c03690f07480400d012850070401c095a00074015540b0000c24030f029603503514441444440e0204046c00f0f203602042c0014004000c3c20b20403402030b859a4003d40909191101d403e040050383e42054404664001c2c004620720b000800c2100301c0e90080588030001c04903955010880c13420902408403041d950314054400410040d405540030341104d41002d19100700c1d488403510029144180d01c2c8950308113031180b000e1401c03c001544401c2d80c040300c41000101141e8032204010980d0401c16002d00201d2007840004041800404070b13000384014400460440410002d48845850101e001040480c2002c2410001d6040002d80300c00218000d11305040b0500c3c2c82c10000c1d002c040b001e4000b0746090748881031007013003a0240084003c021070a842c0e407804940c1d42e030f60b00d81c083d215220040340640e95603071100303140501030b0240310f0017 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 871746483 1250 871745233 871745269
    0x13050304090f060308040e250207050906120d0503010905070801120813080d031a043e0412030e0d0c06030209061303080a09150906031a1f020705 64
    0x38251801e20300c180904501010008181d5840740004000350102000f80000c242c0c4000a405610709020f0f2800a00d150098400c1155003901300e030480f80354042421310645408491441e000d4a619010425540781c0521410042c450135108005994002c2e010b981203450504003804150707179409007240c52441c00e100702580c8400b20b10340c410005d200d141c0542044d203030303a4100242965542074501d02d814075880c142ca0110b0f070ba80ea10072060180d950000c0e408081c0a0381c040c010b42d00c400c0c1e0314401051030740d8151088129002c6141c1314007507698800b03080f0b00080007022900c0319107400020100101e0304c072080700460814070901d8040d050901c80350000711340000b10304c0070303151404600342c0c00b962181f00e425900100400810900310302c0d079650a009103001d0840f90b0346407502c0b8100544901840e402107082c149006412402150340802a0003d44d5290314010487c000060031012070740e804480b1b0b40382d000b2021003034413803070800c07100d11805003164580c201c500e0b440d61501801540300313000c545944 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 871747733 1250 871746483 871746487
    0x360c0203042417090109060606090503010b0402030405070b03061309060c03050f28060902031e01081915020d02070b100b090612090c030a0c06030f05010513050603030c070e01030b130503 82
    0x2c03406003c4102980c0b02d110b100c00412a541c280c1d8600080310344582050010581a02c0c0510560a09208518802c0c00030788003185036050640310f1607519482440307200c04048000000400e03545444100c140c030050b60322001d06c00d6134550325000c006071214000340400a490440003030300c69451544100d02800070007010006007000400038242e04500703120311102c40303601c40000141000c1700b40b00451181400084449112000118442031f4040c10b070b10580880e80306181e4010f0340c2d88a4080c030420507902c0510302c820583c030303500072030041d00402038180580c07031020841c44140180d001c03e0b14403075408984030030441780c0c9034080e0030280e0003400700840e080300003407041082400310149074980041c048800c80b04c8081035000040c1c40c0009a60044600701800a010800d8035058040d84c1341d1071809071410700156046c2004a00042000300200101d651990301103580ca807001d00c1110f102c14580c6098808250f103070309000e07280c0c41082c482101d03a55001400039201d10342d101d00c8801041c1d40280698 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 871748983 1250 871747733 871747757
    0x204030f2d0305090f0316140a080d080a0f0906020f070b06060a0c060e2509143d120314120f1005060d0501080c0406360c02030424 58
    0x8520705c5e400e8030303040b6003502c00c0300d03105118407078848241e034002c00120901c1d03c0d40b00b8060061203060503440e84058001d9200518a0750302e2600030000c00d1740a002c00c00009003c8004051103005000203e00250005200081001c24040140300030013106002c0d0304c0c034010545802040c065544120340080000820340302022000a850360003003815003019030101c980710f0f055500100850412400c261484040f884420010b903081ea016100c00780746114059805440c06800c080348411504400303140c070010b040312035907000301d440c102400b44080e00e107014400e4540300d00c15180040040e403810313404900c500108400d9244480304883d80195190f10300609a00d807428607001944025241d0f414071310720307410041010b48910002d0003040c03079070341c0000c01c0c03c0d450100741e00d04184a032020540a5410842c1c24045440f1003c805001d151007a001c4110050700203040e07448240514805c41003050509241c2090300742c3c000003074800d403080c0f460f0707207030b030140c10345400c940090790305250280400c007401c920f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 871750233 1250 871748983 871748989
    0x219271401120b090a0902100c0c0b0c1608073204231e060117040813051504050102070b190f110a0614090d05030c030403030204030f2d030509 63
    0x2c1070307840d1650310b0102d820840ba00000300304500c222001c0345410754900040040d4508100c001d02041854103061400c462a0303140c566403a03413a40141e0641090001e4000ca8550781040084104513201030803900ca251155444d940320b9405104008200050420442c0048400c900c0b001884190050303031541c03081c065050001604d44080202d100c06e51481c04000b07000c0490f2581803203803050400d410f845603104800c00001e028050070003070400c4850b00700c40e181100015a190b400c20740020000c4c4d26082031054a400618150b000650003007c0c200e10300c074410b48010040c00036075109809407648036490300203601d594010140410425200c054421203414040d00440031244c46a1034003602590285103c1c81c90610440001c40700c00e6503c60724240d04212251080340c20800000c091301c61070080510040440c00098641400c458000022404042c02070341150000c42e405405880c42847c1c9040c045d03070320000955030044e84160388010381d404a030b9004a42c03082c00e46c1070704c030941400c16441c14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 871751483 1250 871750233 871750247
    0x50f0d020c040c170403030504051b0303030406090c05030307032c100305040804091b03060b0331020301050403050d0b15030a020d06270f0b0f090a0219271401 70
    0x21400600162a1680500d94806884e1510980c0640c4001c2a10b080501c0c0170382c6040d004414800342c07803060700684002640d01000b101c0d001a0400390114044110b800d0225041d0942c1d4402585072200040380010190005103400040c041000d803413408080c00c030410310b6602d07030340c409065010200700301380450316000c0d910080d0040c1c0503180e09800d06880f51010412107400e50300f05030000d0500c0748681001c2e40d042c064000940b072038142407415400d1405080728181d21000f88150341380c2e11400641e88a107803c1d0103010003070360024005e102c6810581005880b9520a01c1e00020260900700c04c000581400c1c001180444500860a071860351214003400080d0811522040d0494588400095160308811001c0f400d48030100000032007560500001c0448500e4212103440300e0070314072049416558500140441403050340c80202c0b55440810500085c81143c00c44070300d40401580326403600347c2c08000f0200e9007942d80c000c01880480040e50441102d8188561070034400c205408006652150303007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 871752733 1250 871751483 871751501
    0x31d0a030f0c082b0e010e130e03070b041b0e040303020c1e0c030114010b040909080705031809180d14040e01030503030604140103080405090c07120c050f0d020c04 72
    0x5040b400c103403140361040c00d00107030803c0120308445064a100c480f031540c0c12030b40c0307058507207040050190401c28000b808501d041110b0910130007007038050505000d15070300b1120039814644103403542c942c494a03103812080c5044e02c0941c1c110000501484d0a01c1449076a00160b07000092044890740d01c5907012130103035105190000041c090604d040b113558140d400c84002152b82c1c40d001d400700942c080c042c1400c4910000030b076900c050224004128540200e0200c8c2c090b121601400308560006091003030142c402d07210010002d120014950040c03868039400b41c841140d0481e0043c0c1641c40d080140c0c0302c01501100c7c1304015400001740611414055a4401284c120307030035410303080555403004442420700036801a40c036500000b040003070034540f9205203a12042c5642c542c034465411900c541d40c2c240245c0c02418001e020700c00102e540326280714240e520880e4072141581800103e00301c001c0101d4031052048500d8450010401c100000102c0d0341c0741c044005030300400407488000108400303000010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 871753983 1250 871752733 871752743
    0x1e030605183313120207030510061404090203250f14010e0d02131112070507080a030c0c0f06020a1202192f031e120403030e01060f080a031d0a030f 65
    0x5010f90002685407800e5400c0d0583c00d03000340000d20f01e90f040003400d02174a4170039039281600d071441c103100302c50b1032042184405005460009070341506102003890a10701c29100425900d000800c000540d41300060541075826010140320780b96664143c04010700120300b216030116403820010f201c1c0c4d04043d0070f90240b03240001d01c17448440d4071585001c0300303c41c9050141c2000c81c40000303603010010030000b112a040070452a05514025141d29403150602030003001404140e2142c448200e19803241d89101c1e40d02d500800d00b90060303402c80c50200d000f540a00822404105020032400b0014014401e0307e0b929445078013010542d0403050402c07140c4451101c0d007500403102c09641811506982c10140f110a00710328021a0740302c01d81103500d40032144a03645c0306070b82c4008100c003d6600001400c440c1d001541406c0204241403100752850140c84180c00401f0012034101000601c610b00084217454a070085e115462606d00710700c01e041560412034a503641100c00c170a020030000303209101500d0703824000e07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 871755233 1250 871753983 871754011
    0x8030402041e0917040e0c0a020304150e0f010306051e12010c020a02130c142d0d060905040503070b060111010c0e0406080105060306011e0306051833 66
    0x22a000c0c02c482030a440c1001c24903640d403d101c408001a800750381c3c6a40000891040c101403a181c05a04030860051221111007030104000511318001c106680c060880803000318030322081d40078010f2004400421480c40741d0582009881e103540071b442000c09480024000d00e040b160aa002d044e1189140500d05800280184586109072401e01c0f9080d081c03100e0707602500043c1203d00420000e0500001401100c602c0d0400585c0c41c0c0341c1115101102e2146410482e8031429003016200300c0c4143c0707074290301c42075280c0e081d00401120b2a90040c90b409000010801070031303849040c07503000c0740d0007100c008116074810001440800c0f50194407540c0a10140f525071801810301204900b0340fa10310348031001040710a41c00e00960b160a00401c0042c0421310001c111510b0004d0020781e8032201072040c3e400d008010f1007550a082c00030f8001c0006542c00170414092800d0000c4101e15070104420002494000d4000c289804041d8a0340c40d129500000080d4911f0041da03034000b0826000545280d429081c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 871756483 1250 871755233 871755251
    0x4020c102c01091a070f180b1908090a08040306021e040e07020d1b0210020325050f010606090e10050a1202040608010c050d0203090705040501081b010c0b01030803040204 75
    0x108038082411010700798000f046000d942e1070310714036841140803000100c800041c1013140440d80503c085007880340c1c0d45010b4810b02510320103690641c8003600480c01c5020700181e90380e071a0055882004000c091907603400c40c140e4880c0039490711900b40c01c4004240741410481040841c4043d0040c2556500c0c0e8140300b490391382440c418034580c2d8455032004012003110400c014845405000000e0188140d0824981981940e100c0104031180000000c0c0703e11a0394010713020071072007001a105d88a4442244162220125032002c100740e0095030b040700c003481054032003106004180101404c0b40d845445242501d4180000609003000c010440c4003507040079400004d0541d0388030520700c010300c030400b201030b0300b0070060040c07106403902a0041021681007504900c00c5640c0300d422140440c0180c4001a1251520b8031903904107a902e40c00540e0050a22001054031000410385d0328036801c004120041c1c40d28001c005481c0c480301d150001e040014803000400c00f0440c4c1000070769015100034000aa1140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 871757733 1250 871756483 871756541
    0x903030c07090606081005061c0513050f1b060a0201020f040b030106081302031c020a02031c021b0d060b01020a051e0c030102090333011d0604020c10 66
    0xd203246414560024208000c07048252190501501007442c4c80350152510000020003440d480c03045c079028080006000d8407005030a00c1170303400483c00b1002444581004c803038945008122071003da44038060b100c80c0160708031000610b14000c0b010040c814a41385264002c200e56600000c2880301595003c1241440750394100e0020000781c0302c1c40ba072880e200e5041030802044104001c01c4040721014445c80440565000a00310410345418040c0c00101010000b0890910b01030600082d00340c07141421540d42c008c4003000307045442042d9403c81d0403400018004020030059112501d80000008160002003074040d08044411001801102c921154a983d8240703802c030700032480c600709100b000c2d404580690038032030220001c101b20021b40c203005003640040c0d1030350b4003044c20325880103160b9411900318a0800c208148185044581d038180c4d03130349205009140b80c6020041280c0500704000800c00d2525109459589202038014442c030742c0704c07960f000b00800401008030381881e01ca48040c01903035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 871758983 1250 871757733 871757737
    0x5070c081f0221060f13140606160b13120206060f1203030c0d060b0c1005070306240203040b0403060f05010e1308180d05160f0506040b0906090303 65
    0x1203840030007030182205807001c2010140020403070a41440c01003011040d54034a250b02181480a14860f094694403881c00040c0700480c10b451081d00001c8003055980c00c4c02d1964406841c144014100008030341d034100c1000451300c201c000050300c4031140540100462103400456a00100184082800204c1c80d250582c103d00c116280d4001a0300c21020401c540c102801c280e205c1110580d21551003264040ca21902c03030200603d08890008080340b60042c61510360040ca00402e000035560340d44071030350442d80b40c0301c00030f001c0c0304100c41303003088040fa140714030a01c80c000481d0a0340d0111210100a001d5070480c1100c13007401181107210a2001181c031035070800003880150f01c6a000062800b0303501411070140c4e04140d0000000d50003010402c00c03400041d11550040e00d511a1009a0310104468100f24503416002d01030307080000443c07900c08001000581c201c80e0b80480306260040d90391036620503d11400750140642114091004000181c0c68001a0a002000070b214500b86000b1034040b032300c0d607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 871760233 1250 871758983 871758989
    0x7061118030c0a1a0f2101030c0e0f0f1003060507090501020111180d1a070822021f02010b0910030314030c04420e01020a110f0105070c 60
    0x1000c400200c0e00e41d2604204410000c0001d0300da03280a0303442c100c008056841240daaa0040400010303200b8160252101201e080d4aa02404400304120348038038007041d04024002111056100d04000c10301d2400d240320248035003040520b200d42e40e901d52440c400505406099000940200c03003000c00041e02c14080e6a02c02c0025507900c03030016107480002429100c0c60388003080c07566030420548100d00c240d103125404144060710340760160030070351800e07130740c40c28203090784108514103001480364940d0700c80c0489016083e0302056080110306038a00000c095080240294040c5541000315840810003091040300409800005034200c11580400c1c03401100b25a807090781c805405041c4101031b040070003003c50080c891036403825442d2030440100940702c1c03406818003505066451503034070008280341703a011100d541e03800c8007000340f02c5e2820a00a4140c0410201140d442c0c0408182540b000410682141d084503018407008400d0013070008500002400904202080191001044440c0d00b29002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 871761483 1250 871760233 871760257
    0x19020f09040602091504030c0302090402060c03040905010302130c0e040e0115080d02060709151d041b0e0102032505010b15070302121c050a0b030d0e040b0a0515070611 74
    0x1e42d20004c02001501054091003480803c014082070001c908080018400d40b90306850f203090689032030001404601812603112401d10000030003180c10102908890f0481c2d00c00d842501c0c0810380d005e40d0720203a8400c0443d46000030020b4680c840f80d86056000300a1004130840001801030440b100c450309401960448009548103502000704903504004003640300126240070191141482e038211400e140361001361080028031045e90700c81d44034600c020103009100400c1007024000704005010501c4540300c01034045850540560340710350001c812a102e8200d809401c40c401003d02000c40324040000c88252420b40d6030759012001c1c0c0d215568020750003000094140e48481151400901c0c015446503841c0103043d040c000800c92505451104191101103e800710385a42d43c00030310070003403444044003a8544103540703006050300d4010303090000500d81518107102c580310480512000c850030f44034242e000340d40c2624000c02c1508400207486007074031804010501c0c0e140c11030340d1102604400903580c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 871762589 1106 871761483 871761487
    0x1030b06100215100f150f02030a05090d0c0515030907080312161701090c1e020a1b0504020d0218040c0504090b130f020a0f05070519020f09040602 65
    0x4c0500420341c5581851a030716244101054851042d64020494011905050328400310031034000d07620036100d00d454864070b04c1c00d0155001c2800c5003501c9420300e5500115040e40c50210703140c0110303801d003443d40e100d04041400a042228075484030115a104100c4142e40514109680c0d0b4443c0040080410988007a0070079182904000c1441054105034000840d138003c580e4000010315001d0754485004010f00550320340c03040c43c040162400b40c0d10403900000020440b00f004d610000c05004030250302603461000c50283c1c2c0091380841c00b42a0007054a1400f204504030210200360122410310142e150208041c2c400c1c0720364001c180520b40c4400d448034007a1100c02581200c01d1180740204294401034801e50700940003c480440002d1480c210000414480c1c015240c0343c5811101074403556030195002f4005021100707080381c00026030b8940145503510040c141d80701d14000e0102607 = true := by decide +kernel

theorem cover : BRFrame.Cov 871582733 871762589 := by
  have h0 := BRFrame.cov_init 871582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 871582733 ≤ n) (h2 : n < 871762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
