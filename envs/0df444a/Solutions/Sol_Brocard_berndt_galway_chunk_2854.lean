-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2854
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:56:20.930684+00:00
-- url     : https://prove2.me/submissions/e51c2351-9c89-446c-934f-46579d3af931

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 513129496 ≤ n < 513309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 513130746 1250 513129496 513129553
    0x1a010e16120b060d0c0207030510290109031a0412030b031e120a121b0507080c01110c0307060501080a020a0e041a01030303051501022b0e03010c020609 67
    0x200403000c1e8955058028811840008144034101601c400d10b0300e0072141811100070140c0e0100e20100104036080c030003095a0b100719941000390741c0aa210520803901c03480021260b080050418821580c02044050041c40d0400d035049075013102c07060003030903520098a05442b054011945005050710a0091f80351110010740642240343e130b2465989006030303a5100200d483d0044680107145101c211010349030368001540c4101ca5014814a2030086405000c05025010b40c2010b074811590b8111088408840d405501d0300c0c1e8464031384044038010600d400580010004c0080c8402c0000350003c007408100b401150100903e903a0364810694030400c0b100004d4114005c884100040101000001d500074001d802c82c1002540c0741d10b102e03124090981040f404280d41d030003881003014440060f0980c603070003800184801200310441d10b40e40c80f90055804295a961011060418401c54031030000140c00b500a000b0040c08a070b01035125001116000481c0c800c814078014040c2c00380c9052800c0d03155 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 513131996 1250 513130746 513130757
    0x1206120c0a05060c011b0e10020105070c080d02120a0b03250506031902070606030b060607151107060207080702040506062127010501080c0a2607031a010e16 69
    0xb50a040c000702d90030240400c559550380e4002c0401030300312040d42200f10007242c2d50790419016050104020003060708501d10441e0314100800034101e8002190541058110001c50340302c10100350b045001e031140080c4604441941070078009000d43d29003202c514404214290b820229825008151044c800c00143c4103a80c0c5980d030401c441d0130020f0055400440d940700300b225100380c005404041c2da0149400b01d4110799075541c2007080c005031150103500301e402290500d1038404a9210442020b203154032135182959205101c0030114000340440c1c07051607104500750345406450610b2031050300419400d0f4003943c10710001400c50310300071040322020040c1c502c43c04c04680b40c0745440740c05080010200301440c00110614070f10b41c3c40035104203084000c00000460a9030500c00b0084c205130804485034010300d2480c1c4184021000b0548003011001e0700f0440e880c0c030b085171031625440c0c2009944013814441c0c3c1260070401c08800560402c1c10b807000d0252103034054039950b803017202001d04040007100240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 513133246 1250 513131996 513131999
    0x152d1a0607030309200307060c02010c0605091906060306060b09010504090c05070c08030307020708030f04091104090903020d110a17180405010b09090906070206040807171206120c0a 80
    0x40c0603405440164024980002c8280c250703621070701d81c10328401400c43c0d909054a07104403586010082c0d040079000038035229180d01255400a0000c0b04540e20041a141e217410010388a03010402c10050b240c44201403a00c01003910b420b154008100320b020a8a00900f0281e001c0390108004085410300d00c410303940c561516182070b0003100140360b101c0c50001004020000c45010403d245500c102030410040a50703624201a200a80392990561104101d90000e002460310621200140c03411103040d0300b00480c04820410508005105036040540000d1800c221842415070001b04200c00b5520350325030080301d00c5028a21642c400d03d103400140049040c58044440c0c40c03070744014140d0f40c07410030103a09501c0301d01700000c0e043e91003d070450a10700b44003017101000ea18005541542007105070019006030300302014000d49844004001410380c2100207241c404002504000b1413514074131200f41070326022812030846c0f2604065a22074401c214800c0c40304100305d00481e039210140001000701c01c109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 513134496 1250 513133246 513133249
    0xe0306130213150906080c010903020609130e060a091a0f0106050901030e01090605150a080706140f0d2333060f0a03050c040b030103080304152d1a 65
    0x418548440c0c2c10b050707100c002e102c030480720010910019203442480814606d00740945640b6000c11014840e04101800c48100090707140c0c01c04880c0c50200580d54010803002c810740e8140a4080c60b104a2001c1c0318080800084100a82c00140740c1449207480002e00340348010301120250040c0d6404945040c050b004012417030180e4001e144148060401007141c0d069020b4a5003120f0340c55a050f07680586510030001d0040002c00d99149030b00d02190300d00074260401604039643e0425000c1c600c2489045032030035080b8018030098480c1004100d54030740d51a840078280001034100e00055510038006c813000d0700340604198640a11070701c8100000b52621b41031030804007450f08034a240441d2004c06560041c0c0b1515900c000707101105400980355904d6243d0b50000301211070042c010009843c0a0205000129515048904481e00103814586a45a0307081880780f010507040b0f00d4001c40c1c5441e05072a0403400780c48041080e20040007856040c1440c1e02082d07001c1d03841004110401c0038904c07032112500d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 513135746 1250 513134496 513134509
    0x2090702060123011e0915050c0304030f0611030a0b030607031a150c1b1005090102070e0a02090a06020a0b10050a0608182a01170705032503020a0e03061302 69
    0x32040f05240c405524900881000d1046903264030000c0040c011100510080c0085610f05141c64610f107042881d01c0a0300c1340382620381c080d90000502c44403017202c0131030500007250400c00c64049034050700c6a490074800c02000092001d400510b0182c021000000c192602a00c60401c1e006130751b8070011810300c0c8400811020f42104ac08481010105000c2210400c60402440395500103160303c1000c14410b82081000c000301a400b90b00c00c00c0b80070055032401b0790340450387c0c0080300c2481815003616100c01c850305001c1d01455000e00d4201414000c0000d54560001d15806042e001d00c442800c151203820b20440000750900505030459200f100800072a44241c402130f621404009a82d020301d01d402c030016080084c584440c072100c0345904058160440c0d00c1c0e0810394086400d08043e1650200076006102d001e030000c1110080c810003200040710500c02200d801d40800b441d00900b0b0f04071408a40c098025002010b0f07400c0081d06102c0c410506040c000b5206020342038180089022030f84981c2007000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 513136996 1250 513135746 513135809
    0xe0402040b012307060b0604051f05160b06040510081c03020c03040311090c07050712030e36060d320604121e0302092b020907020601 59
    0x403c00d51000c015012140d030701001850b07800042501d9030f9014282042000d8600c1407024034800d6004000401c01a0380d0050220411201500a000e540b1100030044c0e40502402d000000007440c502291804c1103841d040f550f10441088a013000781c0d07142c00e9110001103949010b038540680c84007801c0c0841d07595400b402942c0c2040743c580540780540f94544281150041d0b4821119900d04102144651408a903550307441b445954403030b0708160303440d02d4090f070300c007044c0c4038aa5010159421000038103200d0801ca01c20381002501c0205ca071004107d0700b180e103000154840e120075000c0e2507107540100380c0e1001d00f40181002030075448410b0140e210f80d00101c2c80e00145c2c1c0a0800c2d2665408405140010000300c45c3c00394202501c2289003500b07100380a696014005410000c040981600c0b42c1c01320302c0c81000032900380c40c0c010784440c03c80b0086007044d41c6210120482070710402c01d0601c802c09803100c10982900c2030f80c80440940360383e002a41d50b080c1c203000703441d401030340320310301c025007008400c03039003c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 513138246 1250 513136996 513136999
    0x80a050c19031b140105070b130804120c060207050f03031c02041802041833080f010209100305010501080c0c1501030311010608120f18060a2006010e0402040b 70
    0x403140c42e80c07661044140c5940701540411a100d208003044901c110120400d400182030815519186031a80c44090564008151640341c0c1c601c0c881540911030781c001594007800030741495000c601c141c0e0910300d005000500c200300061280a1010070103040411180841070300c080c0003141411840307686c1504201c001540c40ea9055801d000000752450402d05403c1115401d4100503074940c20440740e01e88051641d00400d0b901c90600300200c00c60504000072103401400c81e540e12001c00e00342c0401000e0300f40a81d020013400d12462200300c250440650050400c00c508031088817074400c00301010b034141c520074801c582c04541844005400e01c1603c00060407144101c8042e035914074041c2c00030404100707082e001036001940c2c0d0040000850f1091044402405c5007400500d0000040650881d641c030078001c580601c800d021509045e505c00195075032801c07e1000701407075121110140010130554807848002c0b4200442c2141d44862038011840c103050721317001c0340042c115a865409101c047c0c003590014a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 513139496 1250 513138246 513138289
    0x7061b06020903190f05120f0307080a110c0106050123040e040503090d08070201080609061e0f03060c190914060a12140a0b03192604030615080a050c 66
    0x3148510318940d10414050310075000c0801c00c04032400c24070300d4151047ca070b42a0f03040040100c24020380c4004141c9600150524105180da036481002d1070141100c0c4611403100d10001c1000000c1801c103401803c19901c0a030781e04d0440e512110000c01030b0009240b44041210010803040c00300c0f600c2441000d5000d03005408a85c50814002d01251003040078050a4481c030901007048000c56921114a0b0b4001804456481c075904080740010710541c681c270038501c0d246d94100c4000700191500e50b00713030514a5000302581c10900c0d1070342c420050b0780c2c000d50304007007804000e00200851a000303c02c0141907525000d04150058881c10034000756a0050b9490800e000c00059030f992414114014008035880c0c4103d0300380b680c10442480d00035507080261451080c0c1080034520a0602c100240e10101c2d43c00100004026005211884041d02c070344640006c02c0f80c0014011080c0282504400316a500360341810f081d0b190355407501074807130041000040094011044001c4030b4500340c8607180d20602000e03100d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 513140746 1250 513139496 513139513
    0xb010c0f0c051c021e220c202505030f031806070b07120204090e0d030e0309010c260708090a0504060e0703090c05040c021005061008040b0703060b0d020c07061b06020903 75
    0x1a0618082c1d521a52000d503440d55640390045603c62140040000c01c0e01e18048080e48408d081600c2c0c280c22103c10b600300100910003e04030b458900301d800140400b0b0240d6803d2240c0a61240d00c81e4008400c014040d0790103089841c25040100440381c003150420300c00703111510349103403c4036802c0680c800c03498595024031000c00e00603000d02c03800020480c0714008001c4807000784406015a20400084405038205000344192640c010203481750960303121590700d40790143c420080c1070b05481700c08880440c42c0c01140c000d04003c400c600420002c03604a50500d030043d983c2003048140c3d2941d00640c14626051700c08140d109000c0d400010700f0382c1c0301d100041890340d15000030600f00c5004c82d0a80c80140c1c0b00c0e01e10b0f00f40d611007604c619a08101305541190440301e0f4040c014140040142006104102140025861502c25484032001c0c00c1488100742e0b4039a00380303a10740065084449c0d0400340d070041440000315180201007a8070240600040004003440d1130b103402001707422001031140c040c041c2108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 513141996 1250 513140746 513140779
    0xf03071103072a0b13050402090a1e090b2d0d060c0c020411040f03021005070c140f180a0207050c0a0803031e04050705040b010c0f0c051c021e 63
    0x60301002000b0b03681440726103034150281420b904102e82c0700070001c00080207110415a2070032071080c1a14011f84002d80e99000d01008100d0a0119030310901d00d02a11604450046004d6000001128800c08060045903e41c9041088000c0344c0c8034051010034540b0b07901d1500c0004902c0080300000f004004125014164803130f0000e032480403841d03030001030040882d582149418030904010006207800c590800742040c2d44c1c50906000d50102a01c20f85062070054141440b9900b2180910f50112492034400e5403207104c1c01081080ca000030b032082c43c85400800a0b414108502e8110000444910b02180c40e11003029009501c890000d03503650041c118a16401d443e0b400c0c60200504501c03004560341d10340702d12519020300b020303981d07250300001c05024440815400540c3e00300740c90b402c030f03400200c00c2d42e6a00181c50038544580024102603644010034148040c800f520403c50741c045c1d0b20640030010241d0642001d0380e0a010003076000c40d502e84115000a420b119840c9200b101601888504a0210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 513143246 1250 513141996 513142013
    0x40e0408070b09011b020f061f15120c03022106120708060a0b0909030a03020a090509041103010b03010213030b0402030304081b030c011e1d13050a110f0307110307 72
    0x143c0a9550340e444035456280344210a601619078075092000d0000c44103400e2156480b000050070402400d0358444003a00641040c6014800910450440c0740d01400030042c09002210b810f40c0c0407804518010500010901a0007218198481d41002c03038181c08544c20051200c2a014200c10340100702b810b0304901b10b00007040600060881c2c03a000b00700300d01c0c016030b0340f078117075100000030a01840101d81071203081c80c2c0001c04c1d104001c00c503042c0542c9a1140e880c0c2111814005d6001d00e80c007034241010301040c083c0c1503480e01e1030a00140e009001700e01030b0200307042c240e110b44229580b80e51003200c4100003207241e0b0b05100f600944000c1c19281362682d2210058a0301c10348600c481541340700710003180d01c40e00c4d040000d22100c280a0038000c280f546421403007121a0351100c0440c050000001c85110b00601038035059980d80f00040500c1d0160344c483c0b403035100411088800820b071b00c4c40e0140061000e90b1a03401e6500389240f2a00013481d5903115039048031110b00907034018010f0b03c02404180300144262 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 513144496 1250 513143246 513143251
    0xc151e0c03040308030a1a0907080613051602070e060a030f080702280503070311010f0c1403070501060506090f01050a03090605040b0609130201020304090911090106031d0c0105040e0408070b 84
    0x11350800d5203d05001054904071284802c0165199121080210701526502c40d065400325685c10410010354401c004039814002c0c85010368002c0e460501044500b00300c0040410301d80d00c042d4200d56581d40c0b9404c0502c4001401d4810640c00700303040340c0800018003403440440c40c0f41c2c82216840e0034544290b02180c502c1d850151041440307085012012828002d030715070300c00107200860003031518603d5a182c06200f581602e03006030401500c6518180094050b000f40d400480d0b1054440205402c007184590f02c0750041c1c0000c5426508141d0300241030301e010000d90302217110051201844d0b0601c1d400556207907000090813410f168039007e940020409034414244103a000300c400414903d4a04100800c64070020010003103a107510312000e0240c0d90010940302512121704002901c0262810049034150454031340a030700c104d0150001c500940d06401c110503600c056030081c03100ca0020860350b51550340c000c03007140c00030300140420400100b8202200c0d41042c010440c0134a4403110b13403182200700608 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 513145746 1250 513144496 513144503
    0x30301050102120f0304062706240b0301061107150f0f030c08180c06070c060e0105210601120c08010f060309080301090b0f060c07080c151e0c030403 66
    0x44010002540c042c04640c00b40b41c40504040d02d0b00754203104411540c00040c0010305943da0f1031b440b00c0d6018998a48107900719687c80c04142008100703140c1140179124030001103c203170500b01d11903043c0d442c412400400b030300c00946105040d44c0c2400411075154036003140002652080a8000a640001010664550251b40d072450311454620002500c0849010008002c051408980d0600d980d8001c4500b904030414445580300308030450b4502d450600e0a100441c1d10280c001814410084d0900303d83d400c81c6c07015210b0900072400c202c01903d8901481e560000b500e246120030100005482ea200d90f4008414142400700000d034a1009040303c540910758008076a80000500809694911640040c1002d11301440000340a995251080c00b040c49210b10301034031400c42a02560b11301c1d250185101c0043c080a4403900001607080d80d880c0244200300150044200c00c000904003100928840c80312400381e68030b46004040341c404110084c03440d140419105000c0314001460500052008600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 513146996 1250 513145746 513145753
    0xb0a0201142a03090d0c020a0504020f0d0608070503100e01110a0c0b0604020a050412081b07090501060e0105040509061203041401110a030219060608030403150509070501080c070213020c 82
    0x290744010202e82c12100095148000c09104201c003420000901d8407200c00d05140200d0b01d01074610108005030403a820845e442030002c85c0035004c0c00600f90150200c401c01940501c8003da4a082e0162142200e016207601500600308052449940da0015071001040b10000501d004140c1403400c203903001200c9050020341a0740806050161222055400190865046180c800e107428040e0042c8940e00c11003000c071840c00d4031841032000410586000c0c0c036414103800c03815034000c00c11a4580384d040c010003900314036150012800340d10500c5a500b00c0c580607103c480c07801e0f041100300b100c5800000d01c116801012803070340c400d80d010144040c0009103421806980075045410005d048002101040c98450344904103036000700303900041034041c05655510000704451581454809802c540c0c001c00a5407000250010070403002181002d64240030040400a50301c50340b04090b121a20f5218107030004540318003040280000348018640302c0e00c01404c0318040c8403c80480002d0f03820040c0c8001ca04d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 513148246 1250 513146996 513147031
    0x504060c030506130f020c100e070902070309170a02030109080a0f050f0f1308011103070905120d11010b04051005030606090f0f0402010302070b040516080a03090b0a020114 76
    0x1424051000c030200a401c061006107412404214503442080850351960344034403040c0350700900fa50403034900c0c041c41d1060ba6988081c00007540040e241440c0003010301c1c401d1314800a030501580c03003a11403040c0d05a903460304081c50080c10003190b603807680c500d500c28014540c0d88001a9400d12409960a1094004035114610240064018080003210300d05000c01082078140b81c0f5800c0b401c4582001d0010002921540fa1245d0a0300503401900050404e610303000c3e481e501d000140c0044c0d840340c40a0350751400803136210303828001d42e540050050501540726035018103609020f2001624117918100001a00088041c0050241c1d0f2041e142c2d01034030b2060b0103043c440d5040602030340342d00240595004045081041e00c404e185800107103040a0030418001141c1160b100f501107403501608804108210704050610b9615580443c05981d9201d00110300080d2007140814108503060b01a103d04100c103240c8011903100e90302140d80c500c11550b0302c0c000c04064000c0c8085186c025402c140301c903198103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 513149496 1250 513148246 513148253
    0xe04090609230c210f150a06120605070527120d020618030d141906060c0809060910080f090106121415150a1703030c07080708030a0504 60
    0x4005951002c8100000d019591103810001444031030704442560340014480c00010351a030610303419135030400c1c0750040f0000400c900000196040f46940f18210943c8262140c3c0001000c8956910034040c80d1800032066201068490303104546c03206003070030000e00c1c3c107a14041a05e580700420042101d070120f4544507941d142880e103010b00721102014001c0406996005c00a5900c000007041d010170b18441c1c0030f842034581c80c14015a1803000c0085400d110b007090090581e500303610121070302c11100000d506a142d000d2280e0003088225049520341031400c1c00642c880c01016400000b5840d040982003201489649400d009030302e106405644010003820400c40d071904100c0058030f40411a0704241c07044c481040942450440b495010821614511021024a0614502600e0307056045c10040800405404c010703200d00115004507904607819848880240194018000080540d8004d200007001c0c103000a00402c0b545014080080c03c02c0050340c1d503003a95520031200301b201c26880340d0521041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 513150746 1250 513149496 513149513
    0x9020703030e0a020d140102090924090f01260d0504080723010806010c0b010f080d0203120708270d030b0618060d020904050103210203040807060f0e04090609 70
    0x90030342c98006003100c1d20b442d80009060500e0a40302410405820300b081788007440c04d43c1191840500a444400145042001c0c034820441400c0c0c100c250310081c40d110310310384c0340030f280e0b141c41469007003204e080381d03401d10685d1000303c103240d41c0b0410640c10688240701070990421000072110090750380c456032181041c0070241001402e611010400c5940810003145402c52440480a030a081c604040c003a07480500490b00c11031600c2025044042071000803482c0980071180c0e030207881700078085400c00308100008a0340e0f445100441c55402c007440001c540d2252041c52070301d0b00100d89440081508528003801203010700c0ea0005540c265001510b030104003601401010071030a01150991b00301840c0c03a02c1010041c03003807c040d91242c400000c80ea144425907a040c0c52050354054000c03c041d6131680b03402d600c2c1d02d4a00c025003002c40210314400140f0b40c4000200c5041e280c681024160040c41c02000307441807170301820000140246400c51540c0ca444503c02d5490150180e50b000c5582c02c00350804404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 513151996 1250 513150746 513150761
    0xa091824030507092c010b030d0c08030105240c150a0612020f0a0906081e010207051f02121f0b0414090405010e120a090617041b050405010902070303 66
    0x4109500380c10008502c000c68802c0454002901c00318a015012461100324100c541a00a400800780c0d0b9200f00c2241c158400c80c90020b0075000c440c000b800c880002c1d515601400d500a060071010401030001d07003000c030103107106010f0040128400b48408110000c40c7d4204400d00c0140c2e500c01141ca40d070801c00c00e0606a040b200c0084104181410603002c0d5403401c0c3c0c0120043e000b0b41c2c0c140031542e03c90304c031051000c0041c03d00d40800c002103034460710103644801040c421440c00e080d52141d11521560107108848100d42c0c820b006283e0b054000e04040190207804500680b440d03820b100c111105001030741c3e428807440170742e10200f179540c480c40002002c040e20343e040449040c406110501400d54050083c030109a4202c0711500243d9451421030301520113078401500b14002c0402070801c191a0001800d6180f1664998485031500e40204855001c41c2d1480e400318035101c07601040105c0c0c20340c2032008045509107080c0303030080e40b900086070903030300280c0c001c00c0082c8d80000c4010606034107100e5410b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 513153246 1250 513151996 513152051
    0xa0f05030402060403080c1218031b100f050d02030a0902190e070c08090a03061509050408090f0111010509032106060406050f1204030302042303120a0918 68
    0x50031400c1ca0380204055000da03000043c040c440000b01d42c40c01840c100484440c24519500e81a518a544c0b803446aa06429980190003449501c500412110344000c500d038240d80080c240c90070307015981000301c8048d13900900716002e00204200c81c02002043d40015441240c0013100810082e0302c1d8414803084100d5408407140c0c0d00c0300341e0000d005a010108440d50001001c0c500004841c2c190704240c010b034825004402d03072000024030000100502904955280d440c010030200c400c0e0f0b9115081d4003030701d0b4203c3e0000c0000e08104107104583c98041c1c50000309042c10300d002001500001605421240c040c1c4e682a9503900101c1d90100405882e056000815241502030429041000100d11180600d02502d0188440856846c001d030002d04190703050203880c1c45200c1c0907402e050030050700941c414004c0c91160f4021075118803001c06445d00c01d603004c0c84d01030020400740c8403080d0254850b400c43c8000100b000300c400c200094452401001c1c012400d0312a000140c1c1e031445091240c00800b9401003039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 513154496 1250 513153246 513153257
    0x40b1912091a101d1519061404080114090d0e1c020111060a0f0b010e03030706091401061412010b100809120316031103060f130603050d050a0f 63
    0x1103002489003000c0a1100481907000b807000e495100883c0d20342c000b01d822209080d00304000044940c07014401440c003480c44c0e400700c00140fa001c40f0074092030f4081400d0740b804580210104000e654414117454040c000c2100c41c0c0c600307240e2a81c0c2c03480d0a44079202580529000807909001118009001580c400216030610754408543c5401140c44020710a224200120942814500b964040c480a5100b0418a015203100d4a0025401001003e00c840c807010001c1c81c2070181401540101101d0b024104002d005504100d030703965603072000d042d2088007195100c0f82528480c031104000d01901029200c003041c140d401000d231070b040c0101a0080c861000b55a814040c1a8020781c5440d0081060344150b41307000c11180e51103004951401201c071007282000c510000402031041c1700300706549840c50156070140489078141c400c03581180005e9410542c0800c034415030210920300418075845803a1200f0020070480c0d52912414180828084050301140740014810b20742540310020048001c02403c11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 513155746 1250 513154496 513154511
    0x180a1a07080105240c10050f041101020d14030405120c0318040204060f0807020f0a08120702010c08011e0b070f0209070201050c0f07031e03020a110601051008040305040b1912 77
    0x8100b5038002e074424080f02c5040004d40c01e01030085c02c1c800c01d036071710b86415814480b60411042c2c000344240205c2e0143e50200246d015a05251f00c0801c6c800b1042c100365a40200741c04101c41d00302e046038405403045605200f500d0200c000c101d0040c0141a0214070303003001c3c5440d146492506000703c101c1020440c415441080b0a021076038021001c84001b0001c1c2c54204819520110181e2130004507509540c00b6200d5480f05808100107040200301440e006e555100103a2500a030907401c4e01c010000400c04078078031800501c4a03155840c4004034540c1040c0403102c17601e03603600e9021940e5001d15026070301d074404070404100b5800c044d50141e420504500c0200182d28010b04064a640240e4005030191040060300741c051500c06c4440c042c04000780400341c0304804486070090001c0d400203da482c0480d4840469820511010600c181218009801c2604107448103a0845142c14020030481c1840820311020480c421000040c01c01942c0c9505140845401300c400a441c510070048459011401d0902c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 513156996 1250 513155746 513155779
    0x7051309200909010e1009020f030a0f0209030a0305030c041a0d06050303030114010e040209060c0f0c040c090b030406111c060b03040f0210020c18010e090f06180a1a07080105 77
    0x2d0f031078112000028883c0c00b948a00c031004002c1c115039404140b13132074004241290020078080065004402c00a002c0020580001b1248107a0160580441c1d040e003018a11a010034011002560702c5280c40109034a0b10b03460f45d0040612040d501d00d003500d400350206120511000d14420000640412001142035600d0040c0c1c8000c0c0c00c40c21540b060410807000c5443c8055111070701602e40c40ca900814058661140214184e55460801d07820049449103071201c42090803d4400d000315000c1558903c403201d0b0038000352a03055031010300101c459079510020804206c0d0510050100400c9204007213100f4090040d0700340513540700d90001c0041401c01c1041c0000141c42240000e80e10b075040e2404004400d404c0070590401804038880c640110b04000803400d4910300ba5021030613a40586215203040c0c551405103590b42ca030410400d6056804140400c8590010a8103a402d901c1c141044a290100740d03510822000003041502c914004e2800c28480340700d800003000e9000d044266a0014607071180318 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 513158246 1250 513156996 513157009
    0x2031207051f06031208042f01050903070906030f12050301120f060e0718230f091f0204030303140c0412051006151202030915070513092009 62
    0x484160a0003015564805542c616008200115005415a20010404c00e005020541c04607001c65030b4241c4030340400c0d102408a02c0003400d8030041181303000c45056000054038141d12050301c46500d440f90780f00000342584607006000c041c51185000700340035003942c98046000c60101c45c40034248901480140312890031545140791142c4c1000307200600000c64107149004000303108110784103004840003c208800301d407050303401e00c00c0d41180802c114544060f168001410714084000c40440107800f0440e016038903080c01d60450031000549415001c0c104003441011400160b186809401003020002d042d010b1080207150711150740b6072269840c01104000040c030840c0240140120b0f50050383d0244407042108040340310360040200003203601c40c100c580005000e15040c50005046e03858044881200f4001c0e68007640d501c500900c0c04280d854800110500000c0004081100a00140c8030b0b101c120a80940188101007000880c0c1c64560600d01c003200301c0000510250804100c0c8401c6031300c421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 513159496 1250 513158246 513158263
    0xf01030f0f0f330902030a06050612060f10051f0302031810020d05010b16170d02030f01050306010f1a0d061703130e0c16110301020d090203120705 65
    0x5505000180500d00c1c2c0b26100700b04807000079240801c40d5118032094034403076010031040441114404494403107402c0c0b09041d55030200000350142c1041500e000061002e8010b1034000f40020400342e003903810500785030700d84802100c13100c480d40c54840911031003144035118003014103403e032208076010300d56520300200100314240c8002010781c000001800700076502410525000201c01360741c42280c101d01c280002c0d40125400035100e031b20303107000050114004001c861800c00e10300704141140480e40c0710f00b05115685821440c451100304191900c8249070b00c002c5119601a484c4401194141410b1518003e41604210b1101150000901409019001c21441900d110290b40d80d114140013606002c2d0071164858406105450140d02c12440040701805000f0a5008844482540c85a00d90165081039641c3c1e040340d0010014004a402a16200040c40b07015080e032182c0740d00382002190032680000a0b69982c0b5942c0c0b00c0000451600b80045429003426108843c01d040254480b16150250b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 513160746 1250 513159496 513159503
    0x1120608030a14160f33150e04080304060506010f05070807062a1704031407020f0a1403011a06250c0b0306040b03010603030906181505120f01030f 65
    0x1646140c48450f418800c40300801d070722028200c50b901c141c5c98041e0b030440849404a4201c1c00d040316102c1820080c0c0c03103034507011000b006086024201e0f0580c46000340922903001c640080a00340100d03030400c600d01014010f42c418100c0f582c2da850726081c0300341114005000c560401052103980215103503c40156000d5a07003103428599188524608403004000525088005030340d080c0f081441b02180c21696041c003009501d654550804040700110901c40442c3c0040101c1c9280340e01e1594482c00c1806440c80e54409055001c1d505e04410026400048036030210440d080d132881d03114120700f030a01803000c42203c0040c01c0446440780e200050703140d00a4031001c840f100c11041c0b00303902c140c140d40511041a41c200342000d410035203c40c0709039003a6100300c1d001c1b80900d0811048503868241403007040c04880e095900c0484450800a08540c200807648043c8025500e030000070a0324544c00c1c20800000500340c0351240c2c0c0702030f0300b500507845000007081c84442d20b220000420100340c0310342d145003403a9070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 513161996 1250 513160746 513160757
    0x30105040f090c0909050d08091504080c06090d030c091d090a1e02040b10020a03181d010f0b030405100507110a06060609080318130204030206030a060501120608030a 73
    0x1955203900c03000b460710002c0a002c010324143c0c0024004c5030395202d49510f900407425038843c1d002160080c0d6105c0301c1581c00483e241e028081010501d800070355503a070850301c2203990514000818080500c0c010098a0f0440150031061550414039010311484901301d4079400d00e03207102d030b2030241404070703001c41940d0221405040d00c0015a010704180018149154025010542e0403411000c074030f402240c2c004200d000c0c031700e07040b6054190b10f890111100018225402817241e00c110b41d50440d01c900d41c40b80035280c0600312503400710369100d51030b0040d60600210a114800d6601d4481002140005079010240000c03003002400003040001c55202c0b28000032101c04034498880240403034038112003084510450040030300c02ca0400001e900120101c4003503030b0b50601c05e240c80360842d03502c9105002c1011500c4007101c16090705410101190b2800b09040745005040c1903694000c80c502d0390013203d603040810b59803102480b456030468074124044101c078804100700c034206400956244100b102442c103020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 513163246 1250 513161996 513162011
    0xf050c0405242107030804050405060a123002101505060d0c12020f0c0f0c030c011112030f0118020a0512060a05121e0102090d0803071403072105040803010504 70
    0x3614021030f03034540c1c42410466450980d02d081c00c5010341c1160194a2103141404040b9400745046401e050070b0f551885800d810030051990303801880c505140c0310b103018040c03000b507900d01c070410f5884001140304103402428402442c0c10014045601da2107101d00c80c0d00b450001445030741c0340c100644031003901030b9031300285980f03844d803098848040c0d4a900680503400000ca40c038000d0111400381441d83c20400032140034140b89606039450741c0307034200c40a40685c005031000e04136621030507800b40b008419a09480340c4030500c8903d240c0a50044805000a0200710010004468020f94804480002000031810006071040080440c0b0800f444421062180d80228001d90381d1040044024840141495800c01300e0860321622a660b00200040c480d40c440780d15200305c5018021100c62080040100000c1c4d003440da40c0700d41d00d070009403a06081140f490482180480884025400350300d850b124005103100301300030301004c1e16900c07048a40c950709150600c4001284d002c00e40e03055030310031038012880d003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 513164496 1250 513163246 513163279
    0xa0801120b010315060b0d06030303050601081b0706020c03160201020d0804020306070806010e031507020111040f09050403020f2b0203070c0e090102070501050a060501090f030807080904090f050c040524 89
    0x141045c0e0000f010f8901d0002d0761806e81c21148c0c1c82801242d00c2918240202e9840c000107459894045400c15521180d811444240c4401100280606803050000600f03100603003072840d1660f00848511030882c07004403040c005540c2c0412000f401c044d01450080800c2c58142d000c29290200684103c050160440200d1416030280c1400078680e203018003140c0d0030304105003480c01151802d840c040c025518005a524000242a0860f02916001c034440f0314514940b400c000c0c0100030082c0190110b0060400c1d045807111f0601003240e078100038200d55401c540360544070401d25a809c080500c1554410040c120005055600c00030446013004079410751661148078150191044600050442d46018200306180c5200c0d4020015140c0aa0340c840c8810340b18007248a43d034040307000146c5403580c18000d0310700140c3d8540c018003002601810200700d42d003c981c0c03a01d0b1150b0b0800000c898039000420018080c1c04c09100780d03544001380e6981042e40a4131104c0940c007140c0300701102401400124210100d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 513165746 1250 513164496 513164501
    0x4030615212607050a0606050a1d0604090f0b090d11152502060109180201021002030a18050d08160e19030812150103060501120b0a0302090c0a0801120b010315 70
    0x190102002d04550b101c030fa03498019110011068211811407508801080d1800d00c21000320a0700c1450490b02d50082c0c017141c08851488000340325984c0181c985180303200280c401300354114814441c01040040313042144003075051030080c104400803c21720813141c2d0105d00002821241c20500820103038107d4580d0a03030302c03000d0b1480d2005402c0c400302051812240d9980012220b040f00c50900c010440d9880c611820110b5643c00031011740143d10800c03844160400c5a4000e5030030000106000410010010745c2e4002d40f50500010394144d049900d880e00040d410014aa40c0400302e400c00b80500e0828a402402d13860001c00130340d00800070348403150342100912800401450700001e029840744008030b0500700507401240e0044030140303005900400c550007405484151541615420070b00c18101690400520f05d240c040c5a01125560b40040541c9501014a000d81c448107000750340c1c1c60b131010000d03280b900180d10002d400f41c501f40b110070215000000c1c981c1540d900030032072200307071707440700440c001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 513166996 1250 513165746 513165803
    0xc030b030319021216120c020a0b090915060d02090324041502040305120c010221060f030604020a270e210a0801090e0a05030403061521 60
    0x10144000590a000216202c518000d050015401c0310404034100320315241c20b00601c0c08002d00942e400383c0c98000188211402d0412280030f00d804a68640c81d50001841e201d8203511150481d88002070940060404080680c0d228154581d901c41104d00c5002050082c4502c2c034000c0384496002c1607149182c0d5050115100c600c4514206640c901c01100b00008030b040c9c00d8030116000241000c2e0074030140700600030398003140e40040140c803a80b4120540d905580e4801d08210410b5582001100640b004041d00500502c500d400e2541c96880d241041c803c2c0d01d0395159110f07100e60f0040d0304010059891050541c2a9030180e00550b901d2813180046610050380c015000301a1170034a0400e40090800288070041c0d40c00070214a04e1031120800001000e01c62118180c00140c06800180034001e0150003a014134030101080391b0700a150340d222581190030680084606940b04c9082440c03205052100d02c014007a5101c807ca64480310450348c1c0e006a0b050340c0003c001c030401403a846c6031501e03005900385 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 513168246 1250 513166996 513166999
    0xa0c1a07140c010206010812091005161407050102010e1b06092e050703080708100902040603051609050d031d100c050105070e130504080d11041706060a090c030b 71
    0x6410800e6040025102c610080e0224018401d41c8000a00e1960009021212510214099181020701001d01850608100150041c05410008001d008040780701303808009005a00140510400780c141d1424015031b54850b6045a0500902829012003c9000400c1c1404018044000700c41c90001c00c4441c09401e014584c0500e00c1c1c004112030001d40202012a850304140b442c016407550441584e1a00a030940640064800c800141071540212440b42d04440160200c03031038a0b80d10318000303007030381c1c040e0b000500081e03210014032410401d0000e040a511201e030405821050600011482810300d010002d42000560841a40c0c80c2c00704040b51425803201500070304030078201000c007400c001c4084008070b80315807030400007400b006d1160b1294054680000c0c400300c01d4182a20000c1c01404000d401698400c0b010440300c5e5000780240b2a07207428080d4a01d001d9100c07440e000a04014140d07100401144e90461020094181c1d42c1e00e1181c0195071091500051406080c1002c4008140c80304c4c025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 513169496 1250 513168246 513168263
    0x27031c09081c15150503040204151e09020331050a111e0102070b0f04090501030b0708070806010c06020a11010f0617070302060910142701020a0c1a07 66
    0x3030688485846100c2c050011604103001c6000300d40074040e082001c1d440307900c410303003401060010007070f11800045800c1400240701281801503616283c4411655501c5180c0d2444d0a0b0690310310300124010500003025a04021401c505d00001c0b046510780c0b000e1081c6065000703840810722044400e10443e01c5058000b0103e80e101c2d030f450300c0d04112000c14212618800c011480d014020910350390344a4680c0700041c0e029200681c64080021980d4024880c400d821000a00004c01e107803180b44200c0b4001c60180300344040c1c80c1402c1401400d540e501920107420001000e0070400d50b40d801031015120306900c80e0006950b0301d02402d08580400c104c1341c0000c01e81d402e003641038035091126045541580c3c1c43c8124144442d640d20700c0c0d160740b610035110081d04084240002c5425207000d20b940840d00256041101014410303220015465018000c10034003e503402e40c0c01034280383c11130f0203816aa1400e00041070447c041f52240c868051051280c656118a424044d40940303c0380c10076201c2c2c841c5d02840c0d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 513170746 1250 513169496 513169507
    0x913050715030f0b0d150b040e010c0e060a0801060f2a0501110903100f0b0616050c0d0b190216030309121403011e0b1227031c0908 58
    0x1008125410300c08007000190401441600251452250b0300d400721004080000340301441da582180401401c1d540e001803070356495044900d460b03070b0040040344102c000c000580c1021802c409440805540c04c4180034a10a104000155404c0a40d141c1900c03060306190302042c01860044507050b51a50490303103001c601441000e1060012031940700064072400003401400c4101a9650b2603001ea40310a541c1540220000315284a4541c0702c24a1209070f00340c04650102910042000d0341c0c8084003000c401e41c200180070040c808103101c41440d29404960644018030320361160300c10154080c10041d002c8050201103401039420b40e04840f13000202885c20b82890041781000380040103106000d403442e4411607c16002a4400c8910504004001090340e046909080400000c49500b6a5804201d0b000c00c0000c181c2d001b1170800f400320801450130407101450281951010903081c6c00d00c0800b48290030740d910400740300c044140d0b2400c1c00d5902043c0e2090301c04c00e202001074402c200010b400342d13400081 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 513171996 1250 513170746 513170759
    0x350703031a21070915050906040b1c0b010b03040b0c030a060e070221030f27100b0f04050601020318040b130606090b0405011e20061506030f0609130507 67
    0x103010b0005002c1c0c0181c0303c0003565600940181c558141d80a80c010041c0007050007a403070140f000300e40012001c1c1000400107903401c04a0541c02c0c1e50f002815a45881d600b116040000280400380508925100181541010b544107005004003808a00c101c42000c0001803542c0381d5940b191004040c2c481441e00242400100a5290754240c01020350612081e601c4180308940340d0100c07401950740c0e1861030099134400b021040d090360000c8100c1d134210344019104015540803c05034601030600400080c80c0c1344900704000248910500584c0121f0400702045002d03a004015102c1103085000c96800350410900058020b0041ea94419400903071605d51510804a07940300c10300380c890316103031071580603180c03102c2100b64081c130300c00d26001600030710b0303031030070400791400c00f50203c17031075820060181940d120413400e100d901d00301d5102c0164000c400300100c20700324801a076440700c0142d80240c0355003000004000d030044003d03c0c0314041c004810120707640d1a00034060308a0283c1200581d11401d8681c02c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 513173246 1250 513171996 513172039
    0x209060c060106111e0c0d08040902280e0a05060d0e031204110114190905060c0c01031505090c13050d0804030201030b1215180a350703031a 62
    0x81004400b880b1710341098400ba680300941e409a100c1142c0288101150001007140380200394408031520b407001e01c00007800d502d05001410004080390250410000c02041c0380c103004900035030b940100720f0303035151024964882d07142c204150b82d000d85906580e441240200b10292480110041d003078880021801354119006404038001c512403d81104520403000c011196010440221440840704000d80740f09600c2e210b840c29001240d5003003521007203030b4940014100781c101e0030080c403650b040b048100f011580e242c440d840d40c5d04503852604c01610709140c0402d8154038000d1040e003414000281c0d20107070300f41c035115080042400134900c402c243e50602d4424001d40152008034046400c0002586492608002c8207000f00300c40e8005001100704820b030031501c0d00740a4801c10b08a80400c03a811f00420052001e048450b00550b42600043c81030b80d052904c01c1030a03851180840c00c641c45041c0c003000e0940850340c0840d01843c0101d01654802100a803050303500d02c00c1d90380100c556425107503080508 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 513174496 1250 513173246 513173267
    0x4030c0f0b070506010b0304020d0f03020a1406130303021c23060d1e0309030c080102180d03021e010f0501030c14030f100c0903050d050903061012060209060c060106 73
    0x40c11011099841a4101c81070182d480e005009800420050019460704000345500500041c000000f061854840d411100d02030741d001c0d40141c2000310300d00c082c805000c0740303e46030101c002c2c002c04851609004610790043c81aa0040030590005000d02031034503820f00c807040030704c031100781000015400c03074007d00303200503c14407820120b203a2400104140b4264840814050b008101440c1c071459404085916005002d01102031040c104408000b088081c008000500003035030005907140190382c21801003112031205580b0640000311940c0021344d0108188040d0122a000031400b0841404858090b08484c000e00e02e800d4a010000010320040c2c201d400200d0312549075024090040006142d01e03881e05011002e199481025120f1640d0070316072028450780400d00d03182d081c0680b241c0e0362906103045400f460000a2010520f08a40d00d024070003241c2050b02400520719052401074019940315225001402d01507012134001015103480080315400c40743c1505a559a41e140d54000d801001e11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 513175746 1250 513174496 513174509
    0x50706090c080303070908060103020a0501030e0f060109020c100509031209071806030b010605120411010c14010b0a052403100b0a091a07050a060207060b2d0409030e01030504051204030c 82
    0x1e81b000095403040424940d040ea03030043c2821007543d08010054015040310602d03828940708007840920346a105020a038041e0198500241e900c005503000c0a00d03000b4200c60549400d40740c48144006800004200c44c0180001c840c07e1440d030781c03200e8040d4102040c41e1b011401e4030030411903222031400150300032000c1d24803c1e400c0c1e041e181d807102001c5a10340501891241c0b54081000840c1c0800c284441d600d000183c14540b08100c048941d0b00e50780034007400c031210412a91107107045c9005181011840700988401c0d9558000c200c3c00301409400961161030b6500f44100c00404140100e40000c41c00000d031001c00310041e80c8400410008086001030321840750500f038000c015000e20394210003182c00c6141c02c10000c00f0391100c0c2d503c90b40000e5102d070500301c6070306546592280043d1100c0c18400803c1e500c10907500d181508901e9410752007003801c0e00151085240c49440000650030001c480200002840c0000e078980e01c514040d45003182442441c1c0c03000c4004a0000100541c0c51184015603d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 513176996 1250 513175746 513175757
    0xd051201060828022205040c0f14071110081b0306060405010e03160b180108060901031e020a0b22030c0e040c050d140625050706090c08030307 63
    0x3070300c0e907040750041419035260307081c03443d0a0149820410146044003400142c101c0c01890036008948418421015070b540340401c4107501300c208064030f1306228035941c400e0720742420402d181c3c2e085401001d8a000c9190900c101001041040521500c0b6509002d0800c020f0700344181c11204000150184104492180607130303103280c24122500302c000c401e4a00400015100380d044c203040c040199403820701404000d8040c4104400404600040040c4000030b0859400303080d600c05481c020300407288000324141d4144820b40090044c10346960024034116500031811000400210f1807a001d40d0041c0c1e02d0180d440f8001c400c1c04180418108010880074584506148000381c2028998020a0181c44003400c10070300c03004100034100704424029445441006240141d903160360004544040d800000d03200c04150140c8003400e241c1c01c214060f006205d049003140c045201410a44000040401030000c001c408100c000400c13030950000c044041c0d0000c000f0b81d031940c8840c0059034a40086400e4400980c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 513178246 1250 513176996 513176999
    0x10020406082e061d0d060605090f010302220b040c0203180d02130209010203040305010c0c032007060f12050f16050f0a2303070c02011d030a0b07030e0d051201 70
    0x700c0c0a001c030700e100440b030310140980d07450000140da0541540401806900c0390b8040103105654624030b0301e0050f4846c2c0d5001a505007080103102c0e0b80c610080c000c0012100000050015a4840c124000807002000b030b0515544240100c0d00080c00129079120b420600700310543c82d909801101600003041c114a00304004182c2c80100200700c01d90703110103034003d05040704101140b00503400800e200036041c0102c91600d69039035251401c4400310000a00090b031145044010150321100c030000075206051817110f0000540c007000c1d121542c2e0b101d41c5051146182d01881e90740d0181c00c50400d200c240700401c00031b9107814030312200490b10440350400e80f5a020080385250f94050380036039a200c41450380707140c1448200f44047d42c00701c0007001300508030f040c203000541c078202c900ca0007188545120340d240a000d0720240b0002d44111609000c1d01004000d202c40001d40d9200083c608481e41e0f0420b110782c245c0d48032100c0c107400825002040d00c1290191130141d40c0c8081e048001400107101c200b14203113040e0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 513179496 1250 513178246 513178291
    0x15090f1101090e0402060309120d0207060606110d11100f06090b1903030f0905090c0a080106110c01030f1104150f022a15040602011d010e03090607051002040608 71
    0x402c20740101030080c0342200129016040ca00051944002c07107200316121504681800b41c55500040d105d41080b07600001d00c0ca00300480c5028000051200c0e0605d800d20081d43c54145031642c009000704400c000c0c0341d5030541c49110302000728800e2010358003c1004140100d41d000d101a02941c010021180d0904040ca800c03824101c2d448000b4100c075440d00000c040c290b541c05c542096808202c03500b081101c0101245076a114440d0500070140360f5015696031586140c00307402010168400310603c40c0c0e04200d001d4185000c129109241c0b0241b90010f00b527110380850030002c15041c0540605d06001260115088180180e43c6130141c03110b4623031201d154050f040407039803400484150914100369451040080c801c400602c50a804003d0050810002c0e806402e41d803034001c2d501010040c1c2d15200346d2212003541d4141d240000f074610009203e030b8254941815a28841c100019000716000202c94050242c14003610300c000740e0000c0190340c1c407540c402005024090590b000c141d620748055410036407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 513180746 1250 513179496 513179507
    0xa0e030a0317091212041b08031b1906050103020a0902072d060f061a270a27050105030312010504050601090504091202070602150a020715090f1101 65
    0xc07035140c2d6034102e82c1044240c0c0440c15100151840ca0240b094500e540042c140c42000b0348900302004c2c040141c1e0340b505040c00c81400401d07400000d0400350b11502884100c40101c02c0355400340040d425021500060307413000340f8007503511204c41c0c606800b0f035410004010b0682c100904030390080300d0042c903507500c50b143c95040380306401000704041c2400d01c0003005041d83c0040e400140f21150403400c001d052544918050b00c07441c4a00c0305119035203080500440d8a0410001207007019001c10b2030a003003002110080340322803032a00c6440083c8846401415a42d800900c00243c02802c1a2190500b5940b8400d4900001e00c94444082c40c1814008101420f00209640d260303240d101d40601903918110600c001084040c0550f810018403c00c00b003800d8035103000f810b82d00351144a12142c048101e120003410807003580c00060440d009402e1044414001c0c0c4901e45d00b080d82c0c40e0006a03902c1710f900d040c09002c2004101c0d02010350401000c4403d100062141c1503083d030095100700d44000b54074004540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 513181996 1250 513180746 513180763
    0x5010516021009020d1b03030906020a050a020d11030304060210111206040b04180c052b03120f0c050d0e03030108101104050301330e04260f0a0e03 65
    0x5038402c0c2d44140810040350802d4000a00240010701c040701d00b911421107070303910f0314030480032030150003010000c15a12000d402c0c010825803014204441440c0d48590300e0b400401c4003e0b01c5034020b200e1035024400040311102c200c5000404a03561140d81d584040c0d200ea074008480c03684240351820820716070070410120b51020300c2c503500c1c1e5185c59854804120052409440c03423500640e4850101c00c101d208110411030a9008042810710b20b440c0804008440095050380c007078400700d0f1211180c40094ad18840703c4200e41c541024800002d0301b030600c500500003001c0208056080803800e504403600300c0d00818904007003170820300c600603600c040517550344401e100300301c41544404840001a1120783c0884411405807107014601079841000078203450080a0b0720025031a68a541040503401114030303889455801d801030a003918002ca420000c4000410181140d402810001220f1404450802059038201c1007907440300810024450b241c0c21401d600c41c0440c505180d10941803400045050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 513183246 1250 513181996 513182041
    0x1006020d0f0519030e030f040509060d020d0b0405010e1902090915060d0201141210080705060306040c261b031005060a020a080301030602070204322d04050105 70
    0x1031034034400c3c165107107580d0380145a0780b0415558081441380f18034140000c2c050b000d940ca00c5203850314201000c10145d004c01a20903440790a8060512006031144800d00041980200068580b40d072141055805454800c4040b455030080405c0c00c010340e2a24105140070a009841806c0703641d82e104c00c865039824010525108825004002400518010303102c05540e5106141101000044e460300310380c81e41140d001403006103141010003054070038034008a40103000b04002802d55601e400c1c0800c0e007500c0041c080b00e0286454088184805025050007864410820340316200715110914a0301e01d0281618807104d4040796002141d40507916000b5240929001e84030700c400300c0e10381360400c03115900016800d01507020390951074000c00c81d0b94002c0e5000303501030000583c0e986058410841182c00d0403800c0300c5051406404c0d9041c1c191101030000f0020040410010b040d1a01c07040c40e0010703ca044144603100d56210304950700b0700a081b200c640102d01c100001d10040e19500214040f14860324600d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 513184496 1250 513183246 513183257
    0x6081b10081f051302090306130305030a20071a070207140f0414010b091c050d0804050c03011e05070f14210106030207020a060305060112051506031006020d0f 70
    0x2c071640421100da00c0700310b40380b00709101c09683da000440c403001510480000c4c0640c0c0846d0b81400d5040911045510140080d034034840b164196074003a24a02003e4401007440e0b664a180949224001e9211024108050342542e00c0b900945005c162400e03150500c803180c0807440002c5980c003400058040190b90020043c1d02081e00710390300340500407150030143c50380300d902e42c0c4284002d4549149564043c00f0b80c154882c0d5180041002d000b0354405400040c40604013064483c2c3c0450804265011485203c0c81e04261540300c500b03140d03180106418405070316505c1c2c210300d0303502d1030405080342000c10130008043c813160b82c0341c040c20b540107400380062401180382404150038400301ca400800c0c035094078260b0300c640c040c2c046513901c030501c2d8260400000300b17500080c00010340c6402400c610080c80e0358039040c0071a240c02d400090a40c0d078405020b1760f200d034030394002c1079007400804040000340102070402d5840740342504a40300200c20504c14000540900084200038901c296000b140002694596 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 513185746 1250 513184496 513184501
    0x120a0302090a0b0d1d12090303090a0f171515150a0302180a0b07081c050f0702010e1b040c0509040f051f060c0206070203012018040e0a03051c06081b1008 68
    0x540c00c1030787c0141e85103549070000b00140400c2da81c40c0e400d81006004004021140c160801410004600000801c41c450360300654102d1030050354841c940340d0004000310303c040981100c0011981e58000c0806513004442c0c041280244a83d050380901028010904128145d880b98414400b80c4103c500602d22550410400c00b000b05885c10014a0030503401000b01ea400d0004401d907800b00c54060b603104606041c41c07028045603d5090103225400c0501d440501291069070701d14020790314501300031078091901c2d5101d20640c14020019500c1804000d4402d01c841d481401e01d040080c907040380c108480041c90300c4640c0c050106d8000360f01c1035540799128410900c0c501d03020029103400c5560102d03403641d00c4060700807144410000d02c0707040c00901d000e4942c86003c1c1840103455040d500e11544c1c015841d00407146c600020000c1d0b000305d8290941013490f40ca142e00007185042e00a0030014100c000d0502c08002141c00000031a01a28041071002c02101210035080011a2017408200b00c00942040302 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 513186996 1250 513185746 513185773
    0x3101d0f07050714070303030c0206060a0501120e01050f0405010e0a050606011b020402181011070312030b030d090e011220010915020c15040305120a0302090a0b0d1d 73
    0x616a007104090400c01e040205641d07a1000300c082e211003007030b4140c2060408104040c1c15002e07020426250340094075081c40c0840104411400c18416541000581c00c880c40c80504c0303590240003080c0e08c0000a000b60702c0c1501a034001e05505407000c94180d8a410342c0c020031080b01080a8204551160240807036403a04001100c140b81c1244070050043c000240801c0140d030303541b0040c03600d038110906a1184800030410012541c20f03826081d0103000445c2c02101d145500401c001041e290701100e010243c1d5110708044000307006203045282c241c401d9000c4040e0301604484504212100d4a41c080e016a0b2200516080e110700d0080081c1046800301e0403000301700105080c1ca881c50701c189882610a551000d4088030001d1003c3c00201503080110000e4040c1401c544080d24404c0d0403091a14062861790780c1542d031103501907151080718001c038640c1102071003a01180c030501001030010031025114884200c40c0c0d40000082111107141048604a40504a04900d100411440600203c44010300c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 513188246 1250 513186996 513187021
    0x91d0c16020a09050103050a02040510080a03140702150417010b1005090d06063807030c1b03060e0c090103020319080f030108070e0a02090a03140a14010203101d 71
    0x28012a8808400d602c0400c4420452085034002d50091000b03103190f401500501c0200d90300602840011001900180030b400c0c00010380c5e00800350715260814280082c20f80c440b8050242c540c1c0294042082241c1244500d500b00c00344c0203995221182803070010024441e82e007200e02d1980b905400036981d03456008442c0c0180050a80c2c0c4001501001c40006240d03120380440d40315801c880c0341a61001d005282e000104502d51841247d40e01144102010041070032001d4042c01c88000c00700401084107070104081483c6074144031104a01d4200c1c001d84929140014215803818040644a06081c04040c0e2500c81c0c0341c681240c3d0080c014007503909040002c042107104001055640140c10032100c50b007040100010350080034000701425090b8108060b008650801510600b946070061000d418243d80e105140f80c11030b603010400e1a0701c1a6080d903854103040004201400300b4084440400712407030190011440b030700f01850034108454036030f4003d41d0701e40c1e140d58404102c1041e100000d4201e26070035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 513189496 1250 513188246 513188287
    0x30f0509100c0f050f01020c0d080c0d1503050703111c0b06100302040f030606050901060504030c09020307030f05130506061002070e060118060207061418041d070303091d0c 76
    0x183c0c82c042d0581503980341c040c9001010000c21a00b60742c0020300e0400c0010910513100500c0380c0e440c0c00c04160421980c90751940c000e45080c560700f5036840081c1d103080c802c0c2068060045234440140d5010310f603282041d504040d081e01d0428055101174015001d074180400324484002e9004542c0d044076101c2d48103215134211030100c88000c2c55030070000412454100715900b0010f500c1003402041003030400c400e00610150680c42a014070606120a2000606144009060711100d100050700d03551881e20440140c0710450034250740919040500003d000d203604021062401101110b035903031994010b0151003038207a0030010058100d1a0203100304890035031002c0d00710340145016901d400840c0a41c4150000541c0000d0260b400114204a15074210360003041d41c5c000c2c5400340e81485035140c40c8807452000d900c41c20b03104940d10908000031f40140162000044d000d1001c4030285520303407a010305580a20b002c1c00314005078130a03540c000c414420403014441d080e4080500d042070860b618006115207403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 513190746 1250 513189496 513189503
    0x150301030506070e0f120c040f0605011211042d0b2b09020307120b01060318241509050a0504050a021903050105070f1b11010e01050c010f0504030f0509100c 69
    0x710b9500b17160f40da10000080d280b403a8610290040c4c01844013084121240b44801c032074a50700740030003040540e0300004005080c584001c0041808848004d1100881c0700d0768000c080101124240d01030f45004900c00890002c2000302000a13040d00e0f80e81c191458042d64120894104c00510350301da00c4030151003a00e241c070310310240100321507070150b00190400030103410102d0040118005c130010310421111080c0144080c1c10200454003405080d4400003008042c0a02690005582401c10015544007100a101c0c201e50420035090070744004005840244180580d540c10940030035846981846a680500c0e402002050f1071a5550700748030041c45429011800c4001075400000030a000380900c43c818940d0340c5c3c4106402810441c0900b007101e520510121094605201c4800034015000600100400342400e8485017407100040303074940303d2403403440d0360303542414195005036503141c2089019030b00c25120301040145240040340c01d40282c20040303600942904442d41c03a0b9000e40700d00d6000502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 513191996 1250 513190746 513190759
    0x15040314040b09030f1b3604120f08010b0f090901091a0102151503100f09020a1508010603111303050309092d0a0b10020a020901090603050304090507021504060b150301030506070e 79
    0x51f144100741c6100301c540d00c8007a1059204100020003501c031035000741a00090a0101a502c50b1b480000c2882105000d034820004000038520860390480c02503c604e0940209098403641c3c6a401c0b89000e000e20710014504103003c40c0c2801e60940c00496245218110301e11401e903070383c1e15251804100c98800311201d03098000c1d95890500d610542c01003da10b20403010303020541e100c4030b10501c0b002255540c44031b0003a0416441c2c262017645d009081904403841407501080c0a10745c0121800680300c1d140b024012445116400010001d003c809440c0b030210445031b5102e1070382c8920112501a1700da804480d00241049030b0300380c90013000c5a0050b001004000006601e41c0090085004c00610402543c0507a0025541303504500e8451030503405040901c00500c140e5282d503680c1a600d0050780203485103645c0324030005260510800005003801d20a90202c039084c2094140301000309150008140100342c003080742c040384101c0908890489610500400130703640c2b8240111070302a64211020340c09013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 513193246 1250 513191996 513192049
    0x306210302060a020c030d2003070536121c0315060203040812070302070e0109051008030a021905161508090705101211271215040314040b09030f1b 65
    0x2045002a6114540a072210b40e5038006331101d903001401400648180c84002d01401e074401c5100710000c1c42528001c0c1c8081114180b008642410005440004003081d0340c400718a0507103030341c1a0402e5400c00500b10040c903005881d244101c1c4c90b442079010b600c985502920724800704034141c1000b08621802071055800700c035214007a001804030280d0290900e592110144441c000e031284003080140200401185401800d1b440a5218442c0343d084140f0890807a070660103001e02406040840010300a244d6080d070345030912a108404070541c440d00003078242c400100e003c10000340000035910010700360403814284840440d185041e09640c00c070702607190403c074140359207902c000d414408000086010b10300540c1d43c000c03040390b1800c5103103441802030307491000a401d0045400040700104021100e566600c82c14141d802c01c00031410488100710000c2c000400307800c85801740a0031070048007654882c1c64a03410290b41c4109100701455801d03540c0c00c60740405d2402c001d060103503442c10781c020054030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 513194496 1250 513193246 513193301
    0xe1f060b0706060806131707060f1d070b07082514010501060e04050c0d0e0a050a0c060806030a12211b0e10020703060902010306210302060a020c030d 66
    0x41e00020000c40e4001c0e2112424007640006000c001e91004500384806840b01694841d000b524110364107100e440000000d10703009008144c1c2008400100644c41442600e4000c584113406030a5100d184401c1d0091110108441255408a43e60682c105c0403580c00d00ca86548200303000701001c0c08206920711110740400004064030002150f20740103500000d40c540c540040941303880c5000340418440c600d0714003044241030035a42614030014801a000503a03c14059103140b401900034400f90062013000ca0140070001c40382040c00a90344960b44250f49610782c1814140c1ea41d82c0314100034a494034214056220070b1085e042c514660303180844481d40e0446c0003501c0c07001c8a049080d441400341c00d0800c40050140c00c02c80181c04d1802c141e07804044e60015000085d10340d03460b400003d012589514440003903a04c00e802040103480540324411400c2d190714681807810340501000c4015001320307000100000e02d13910070750300c00ea89800c020b5850800302031400801451280c540d0f40c130300d010342c02884403413 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 513195746 1250 513194496 513194519
    0xd050a1b050a06050108120d0902060403150207020a0501030203070c020d11102309130b04110301080102070204050a0b0d23160303170c0a0c02030f010c02100506040e1f06 75
    0x846000350702501c20140a400c140080c1d58058014150a902c5000c82203000e2010200300c82e03204044240004006409100082451240c3d80c0060300c4911100d5880c0e01c80c1d01a58000e00d11544200d4101184941da00015001da003c2110410007242c01603080c207002d414404d410380c0080e841080d403192094281e50005088a072507400301400a0f40c1c419203480c0440020485031b04038003170700354942d0800d003007400080c41618041403c0c0590546500d8042880e031120b410010350a80300640b80d175140c0d078440b19042d000b50441e00003a480346007032901241030003250303100c0c0000c0e01e200581130020a04031502d890703507540d10460018020140c8544486104041880503001203113034980b151120070720b1414010301741050040c2d2011440008424401800c100e9402c9400008840c10404480c1341c9600020742002d5403415075026550901a03245140b030b90109150000e403100100422180e1134440c2030008880b000d4544141e00e5010b600c1003200c50100300036210070100c060b94041519a124262501c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 513196996 1250 513195746 513195797
    0x50603132105130512060103200d06140f0103080406140f04030c0602060f0f13020301181b14090a050c04030507030f0201030f0c0e060d0e0a0b0a0c0504080d050a 71
    0x301c003c1070300c6202d44000c00c0c1d120b0062600b158030b00201801c00c414207803a51018880140000840700d04d2036403500c0d0384111015544002495454a0111804e0441c050f101880c1e150158850300000100035412000180341a01e800007181d41c10503042020558107064640601c4000c03040602c030120044508038000c2010354821000340000034500000a4942a4058034400c00203a00604110141c010161159402101049840b41e1100c0a001103070040c141c9034804c20080c0007102400b000d00ca190816904913219514011031a01c2d07460645240000340d108659510204020200e21564031a40050f5000b884a0301b2003482d1903565a141481c0c40001d40c006c503907000c038096610042d9a0140b00344180881d501405100403080844020039981a0f05102ca21542000c00c00520111090340404c0788249032004a0700001d4060500d003030341c120304403141c0e440b131805d00c001e544500c0c0c498000d440c22241030f003000f0000401d280d9001e49554101c17086a908000b40d400c45132044800e003210050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 513198246 1250 513196996 513197063
    0x603090c1e150f090103051801090605060102100e0c060901140703080a051806060d0303021908090d050f0a050715051617060609150c0a05070e060a05060313 69
    0x40001e0060790b0021944401030248203200c1800c44969071421202001030900c2d00007045ea66030796203204101c03000c4d01d040b44558a009907031410403542c8e1b401980204030903002c86100d401c4d5a140941a50080801c0c0110764111548071509801d052010700581d40d4141407010043e0540c59a81105800030203003900003c0c0345009010000c00e42e44181a0014460580c13030300d003400c00c4400c09503a040040c001c58003401c00f803400d500c1894860f6068402d039210301600080c00c4611402c00a00102c025140c3d10b81a008504003490040c1c0202c04494940d25000040c6042032100b18082e9080e810540040e41c40790300070980c0c5020004140310701449655401c49441e900301000100402994100c50b2850802004005015095a40758259404200101da400003009014495031903180140b59174184c89200d0b03020100108000841c060050f10002000240c80ba6035800030002800381c640b080030380001302040801d01c040c0390100312031840e50194041380c3c4104c00801811801010040030103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 513199496 1250 513198246 513198289
    0x1303030b0402280e06030f010308071b080c0108060d030801050909010902060a05030414060c0412050f060702061906051014070b0109020417011a010f092d0503010c020c0603090c 78
    0xc0103c203401c1203a00381070388402da80c90f0b0304515180e00381c2400554107010103403418002244070030800000070001a140c400c1620700c40c07a101c4e940c1e100309540d0440401c2450100c0c0e1194001030590404a084802031078142e43c40007501d902c0c14040c05004640580420525522080d40b01c0168803203d0040ca002c10450352000d40e00d18060420081d080140d034030040706500140107220800c0b0040c41076600f40c41c1da800e00300300c1c1d014080c41c00a103001c0d00b4446854039030244200f0800819004141103118940385414120000c81902c950400c48d1103902426a000c80a40400000c0d02e11a0544101601d119500c03140f80040c20303201c2c580890001d031b21840d10a500014140000e1410140e009050001380000340b00d41200364151400c0d00f203c00b4070035410007060112944249214100e024024019a16000b038401c5000b0b00065452404d285801e140041e10030b400512070805104142c14010242d02501c1c1840c4184100441680040c00b9003119201c2c0d030460300d00035560403c28051481070b44206 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 513200746 1250 513199496 513199567
    0x80114010f06030e10020a0c05010524191202012109020f1c1106040302060c0a03090f05090a0f021b0708060c0703120506010306150f020c091303030b0402 68
    0x3a400c00d030082e000a0304050402c00c410f1411500000d11006541c0d03407074030150702c4158401040301e00210320384000d0001d41c20309082c007603a5940401c8480300211846440c4e03050050407800d0100e44c1401a489008050600307804000340300400c03500c0e40c0400d20500d00b85100c030340d10041c9810b0284500301031b0200141da5641e07035011407602c54404183c034038003a50801e1a6002c250f003800e500808400d4041d0010000b4501018241d940104541c05154014080f503251200c031007855a60303001c0080d040f00821000e120200e40c440400148408461004019015550747c03a142d0b0701c00380507113070420030000380c081c01050b2115001c038a81c480318502c0d07103005100c424a002c80301890118068074101c0c00b0070f000c00c200c20100c2d50000c070140c0f551038402c502180b5500d940c80120000c01c0203a01c02d603205540e0130f100c480c4150b40304106d43c245c505150b007116001c82c0c1c0d0342c040002e81d08065840304030306841010007000103030180c0c024030896400207000500740380001486c1d80b480715004000c0340c40c83c0e58940e00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 513201996 1250 513200746 513200759
    0x21f022d0606030106080c0f1809160f0b0a0f2f150708010510090e070302030402090f0106120906060b04032a052d0a0e0105040f090f11030708011401 66
    0x41698002e40031002400b00a103080010381e1140c016625060294986500012050315400301c81310308044400800c107810328050101e07030b88a400c03444060285942412002600309089182141a9147c83c42401d2a02c04014010349000360070700001e00520450840d141d03100b64a40c42d005510140c2c28041402065002da411414200640d40800600742614148000c0c40d80c001c0c0080d0565905460b16007c00c0b05100c0182d41caa1001d61010103900c0c503410400c92103d626802442c000d510a8981e0852502d90340c001c500c2c000424014580007a1028003000032200080d044401341c0d07405500005291512211501c0441c0d00a40060303500b6003580e800a07030003031310109007040d11040d1040e40105844c10400020001c68840600b40c0d141c2c001072270b100d07a110300c240f80b840541500017000103002c19942c1401d05400c49092280521032440c00071001d101800a004094025038440d0760b40f00c06284544d00c541e1550440c0038041e0701841140030104425809104000103503a544249032038940c54800b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 513203246 1250 513201996 513202003
    0x504060314160c03021203070207090e0c130203150621060d08040603052502070f09090b041b15030504060b0d0b1515120105100903021f022d 62
    0x8105607540d45400c20444080d01c0c0c5030308a490700c6110300e0000040d004a0130228030f0404c0c5003144142c00000003080c00384064002490200303c5011074020312001c1440b06020742c1394104556465042050418000080300789940190f5214140b00000042d00704004003140a039040201e402136030100a0340366400456207400b24540c8240101ca0301c00c031044050b85c4030140c81c0601c1c425141459213030746c0454400400700c041c1c90010b00750048500c0b602c0c800000006d548100511500140404a402c00300c0c925455006196003d0f4201d00c900e400350306c4582e541d495605050f40300700880041c21401180c03c1000c2c4201c0300412405580120301401d00381421411103100c12400c40c81900f41c024508001500b1001d6281d0103000242c40c80740a00d081d0021450440412561114880000440c408480e01494030309051703c0f016120310340b52072041c0c101600c1452460002940c0814481400f24445051220308261840c2600c1519122806400c1d10448a0f580c0f2959074001c0c4d41d900302d80191603a040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 513204496 1250 513203246 513203261
    0x120604020903030a030b03030d110a030509010e07050114040906060908190308060108101a0c01060503011104051002030d0f09060b0f060409090201020f1c0206070c112e05040603 78
    0x121421860000c403103002a0752031060241c00c400b45511404401120340d014000d07501d5001d604c18080c4000032225242c2009075011500e080f01191a0001085a00005201d0030210f044110000c000b801c1c03c010042d43c03900c821464603682c8400c1003001040c1c1d4070043c000c0000508403a02c4100c88141050301c0030341000d074248019885a1a03544403000030a5105071904d801410a007421001070b100d00b0082415410b0740d401030512888a040010840640c2c8401001c0e24501d00b002081829200c4c01050b090311050404416908070503c400e1285241512000880c6001c9c2d0045900d8038000d0707404a07050f05e40c040d07410a0041d56a04404050007180d020325541d50300101d65048006140e500000c005004a02a294125039a090380343c0031a4020003643c1c21880300b200032200ca0b9608211300c0c2c1403080600c0c81420040c024600404c008900800b818000307141c0c06800c01c50442e1900c000e001d034614131019400c0002d81c100c0280140707141c0340452294400c0c440d541e910303555401d0050150071745aa0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 513205746 1250 513204496 513204499
    0x6011803140f07170d03020d0f0c0509240706020307170a48050417060106020d02070e04080306150c0d030b010c020d08090d0209070c0218160c0c09060602031206 71
    0x2d00c4c0910740e044011034103d60002240c01d00586034545c04031404c0c000c18403241802d80240c070746410b40c0540754020001c0c01880c48200d4940340010700c0440f03000c1394100c080d150110040360070f00070000000c0d090b0b00950743c441c03a1840d00010046450002c5080313080305075a0050002d0361990300c00d54000e1708260010000802d0b08860740a15007010040f005102030b28940302c40750034120301c10454140304004407001048007140581e81c04011099594440000303124520142c8104d00b29070314080d0002c103040b0111401c01090300d41c10340e9191980207080d80002c0801e030b4070400050440b40d408811001600d092130300000204081d00c2c2503103025007200c02c10540075040c81400d50803080140d542c4c1c0c01c01c03445146c0c0800300903160301040011401e05080160020343c840581c0e0100000f83e40d02114000d60a0b00845000342154652160b80000d100160346035103842c8a1041241c11050140c00c6621100b071044044410403582c81002e0000c8a040d40c021100582000400c1c0c0021181d410229811800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 513206996 1250 513205746 513205769
    0x711070f06080f070516030531081f0504050c1201020a020105092d010207020a0e0a1103041a07020a02060d0e060109022d0702030d09050405070e0906011803140f07 72
    0x400340e00207070080c00b42076070406000394202c040c2801c140c400e0042d103015a451f12204c443d101100d21503080b02c9c2d40054070305001641c091030001000e010008800300307486200c5580801420f00b031b9002c20003405d8000e0050702c2c6882101d5801c1c03901d8031200c260381508028200010b0303c0b244140802800e40b000035004501c1a40202078241c207070283c50050194002c42e00a140380b900b010b14640c0360290180c050f010354450800e0300300148140401d40d06602c10200004200480c54450008084602054134040e0402c43c400d0b40098011034a010020340001c3d160044a20041a95000070307500da00c48c90101c0c0c413103074030758000c500c01c04410800300303001d0320070040305600303160440703190101d58280c02d01c803101e600400100000e40758008bc001c5420603600a400d0f10800707880c583c5c02902c3d00310b0920441d0700a62512700002c80182c03007a0030504100400502118954441000464400034022803414500e600808000006043e44195a1080040c100a040280c03140f005031814882c0a0f402284d1950 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 513208246 1250 513206996 513207001
    0x809011e0203030703020a1211120c03040b060f030109020409051b030304030b0a0b010903051c091d070806040b19030212060c030109020d090203030c010f0609020f0d050711070f06080f 81
    0x41d008010390354046040d240058031078071810b0045981224041e0a4000300d840c1800041013003140c0001804005940d42000105413500350740d0222511046401405c40d89011000c20300520340305140d000581d40080c0003062050003500000d00f1610f01440403a40c0d580604026034012614003004400d48408070055030a1601c0d5480f40d01c05034038000e00078106255500781d29280c1368050041400955007280442d0b601c07100c200380000320f42c0d070800e0748080402d102d000300003444a00d10442104680101070404026107441000340e840c0c8101900c1c843d80f05444842c0c540781c0751036040104406400d0503040031142d40c0b460042c09001d03114044501031640003a420403200c419804200c0381158031003140140d8404840c03560400500c08510000e616000c00680383c00e02d00c1054120758400d802c0306a00300200d0707540c0c9600b0740c00c84c4288100c4401c000d5040c000e0401c51031899210766802002420410041294010707068140480781c4c0243e4142c5580d80400e110380c590000010340e10030307002c0c89114900e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 513209496 1250 513208246 513208307
    0xb030c030c06032208070c05040902010e0f0126180604020303030130030302220f06031802040c0908011103040f1b030b0106030c02010f02030615070816080901 70
    0x41103007000c014007900380040460400704208000c1c0500c9070a0700400010b110302c61401090540c030000040c0d070703103106400f40420503103014403a028800b9816101c00e1480381ca06000c3c018402185000d40e81444105010440b080c3c5105005000c08019890051040c1c035003030440c00003410800040c0d00c0d09034801d000700f000503100001142d041d00e5058000c1e10b01a41c485100311000d4a88090a02d00851112820340806415402801d035040030000c800754070840e583c2000402641601c5500140d5000303802c02c003d518000c0d4895000039641100482500c0c22640200e02603030b816110410002d8580c03c0304010350302003849108441144041d6861650429494613001c210100d41e001c2d0400304210150303041382214103411b90065a000300c4a801541c0d4440c40640180558181d4101550070304409280a10192085078401c0b90000d0454022141c55171490455411240c03003103400c0340041007041c50f5030702a00112400c561041803282d80da21040c0d000108505c100c0101e03007071030011121012501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 513210746 1250 513209496 513209503
    0x10807050d150605060a0f020607020d120e0109020604170709150510030e060f1b19050c120d050402040f0c0c02090a06030f29010b07081b0105190b030c03 68
    0x842d40000301e00300070740c0302124503500a1031aa40402e030301242c00140d0009513a00046030f405032018079002e036000d90b60f594906a8031621070b0000e400008202d4042e040c0142450b602a0074000525000014070f4441035001c2a4030754010741295944400307030b0120500020040024802501100c0c1c800d10050103520000e6041d0599801220721600220a030407001c60b00ca40c0c0103621070410351040361b50038200100381540c40001510b80a090002040e030150304aa030903400c80b840413292102c542c1c3d030311760f800d141141c0c00d80203524100824014511407009456019018003800070f1000c00000e0582840e104100c126000f8100c940003550524214481c001c3c0c000c1d12083c113194040d0391400007030b52074900c1d40c00108a40e400090a1085411010040c0141038540e40d511010790b6142ca01c11000601c20004001405d10480003072200401600c40011040000303840a1480d0301c00308002039514102e00350941d00119800d038402450030301e0400d4286014021034a4801c1c058010744256150080800d45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 513211996 1250 513210746 513210769
    0x20a11090613050a0c021e0316080403050f0f010501050a0501050313020a3303050108071e03080c0a0c05040e0a0605040203100c0f1112070f0303140903070b01080705 73
    0x45240e151001400030b072520b1403242000341030000204010300c0d203030040c11300a045021036040188075503e01410004e08145007090020003040056007032036144014080303d2940e84904a6010100380300000010341c040290130300c0408c0c4440580b05017036010344884c0c2102c01c1648664400c180100e010825660803400f22030300b003140e0f49055a00d0010900204251004980c0030005a6107042c1c201c010030703958114104000c000c05900c8a0a2411042e401c0b03080c0d640c20300840590f6001031408100105401d01c802c09894244100c45006580d42c4d1110f90313a0350030181c0300d0300d40350300940ca01c031007044450902c9002070035086404002520310408081c1e0f86201c0603c00810980d40c6101007815581c0c100311501a00207401010700c210f501d0410b00425030800c5504041c00715151004800000002040300d60040081801503400c04045445600314030742039034010340c00c0c541d96110510f46885160541442450502d0055665103454908a0000001603200110942052a0900642d51114290203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 513213246 1250 513211996 513211999
    0x5120a0203060a08070b07110f211903031a010903050c060a020712080a110c100f0c350f0f070201050d1505040608010e1507140309010f0507020a11 65
    0x10307120754030b070400305841c2c0c022500a001c2c18464540001420244070000740b0199210381c01d40c064002003802481501c41224180640c054444000d11000d126402c02502071004240111400348485030850300240c08001c8040c1c00003505c400503503145100840c0d01c1e1a60510070300e80343c5000c0d8519112a91555803d4150030701c6440c0008101c0a828420081c040103020044426141001c151038040400d41c412407003d00411080c81581800c403034045102800c80c0c0340a0000000c83d00088803c4480d0401c017040d040900c190460140e011400808007428124880b4503002d0364081c164081135040700c4103a080345000c040821080ba00c1c41074000c1943c3c0c0500c0700000280d00d400c40e92005a80c0c50060a050380c41c02443c0281e00760f041c07540d841e0301c0c01c1240c80958081003901e403210801401d8442c0701c001d00322141d1000415460402c0714001003a4030070f0300d41c94018110012881d450a0301d40c01942c0140c100ea4440c485502d03100c6e1356110b116007248845c0028001601159180300e807400160358413a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 513214496 1250 513213246 513213251
    0x8220605100308190f0f090b09010c080307080a0e010c2f0d03060501030b01050a0509010c020f2707090602060f0a0b040203010801020715060501090306020915161205120a 75
    0x141c41c196120190030003441d03000c0e4409072038003144150310001d414502c1e9284000f0310b880001040c0a802540e2040407035403a43d655081c0f0504140f47c118260780034904403810400041d440310042404c000181d0302900160740e9110050030010030803001d5846101091225915004058542c01d422440c501d1100c02075521007010404038160b0302c03044211100400354a40203005150281c56499030010042c0c4900b40c80411901d20036000440e201d014520700300c8046a010040a4007640c090000103500a1005104001d5011040d000c502d80e0700e400b680d004c507501c40380303484454000b00c0c44c00034135407200292618004031032410074000e58824003d8489902806403502040d888103d41d0000d03907200740098020355995a403090031038000e42c000e8030103441d03480740002640b03004501c501641e4222081650350114050954462000941c00800c140d40d020b19401e8002406d2a4048081d0058154030020314010359124109102030002c441480c60402001704141200011400c0700d03140c000d0303440d1100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 513215746 1250 513214496 513214501
    0xd1202031315200d110a0c151403010b04090203040c08010608011e1a01120207020307060f08090f03031b160b1006050702062502030f0706030b0306060a0522021908220605 75
    0x840e0900b09030006c050094036401c2070100d001510380000c4d9048805603998a00e014003031408462642c0400c2c002d815081008200030030070041650091a001030060000c122455551249682103900381d44c02085241d44400c0c402e515901c0314a8016504003e0302c80a01001114200801c1c1300d01254040c1c0f410303c40d02c0070050600c1d090355810340c2e03065540602101c6440c0e407540406410903004244900004024200149200201081c61090445040001c5046440e4410108004400301e4810400300c2c109010075625644040790030400540103044820082c10305000300710030010260080800e00c6001c21100c001a2900d00840300c500c42122404bd4038480c05001158080700e603210080c0d811f11232400d01402c401c02c081804400c450054804000c013024110901d6201c21080300c09943c000440d180c100070508100744006444010781122a03520b0400140400880c0c02190010390080280c0e10409903098000703668940141c010038079040035180341d0030400c01c000b11080e40103203000e40b500c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 513216996 1250 513215746 513215777
    0x3041a0a09030f0b010527011502031c02070512160b0c090d060507091e05040f1d0706020c1c11010504180e070b090d1202031315200d 59
    0xd00320155501ca4007148014100e030030304c102c103807100b070141c01d21501100300740d2541d11a1107103443d020341040c0318810069038601810004101003024071070782507010812181141810b840d49100c21070880040050f29030019040c0149094140603086003513a40401075000d00100c0007204509850344000994406d688a9030284001e01500c4c3e4070302e070002c00c80c41c50841040890b40103030f4070900c2070395100780d181c03079440064491001040c50340c24a040342d6007034188942d0800d41c01c002d80030b60014002003081c200700300c94135551030303151070809043d500300c0001840055418130006110f40000c5414101e850142c44002140000720f03e0001c00081c0c0581100116034010410744005280c000304041000342c40003070410143c060b2512070400c902810704c0100d84400c521007550400c54020b00304084a080340ea0390308010b4040bd0000340290301c014040704081011452183c0040c3c410800c1a4498945842000e042c3c480071921a200860f00301b03c2003604070710005290350910981e481c1910404040c0c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 513218246 1250 513216996 513217007
    0x1505070912050109330510030303021b0604050a05010e0706050d0207020406050622050315040803040f0219060f0908031c0612050303010819030f030527061803041a0a 73
    0x8100805c5e58600c0000740081d040002c0448845140b04800059900e000c451030404072402100c00d80b581c841c410205101103031095020b00f0960320b00c00d9800200f5214607012515001c4222400c940da54080407402d01000000e003d01088070382020000c0c2030003810705201900902030080c0740030580754080303001c0d000c0d50b84270380044005080180185d9030368800f9510800b5200c4501b90598000c05a200b800591418001003402500503c1480d00009458554a004140c0d00141060f1902903c40320120017617514040056200500000483c1e4202e2800710b001d041070b4040e8550005000481c039040044e501d02008803040d05002d0520030485c8401032494100030002030b04181c0708659501c0d50481001400802035041e0b807a40c1e0304032010f0f52a94000354154504a02c0d0081c006845450141032007400b0350400c80d001f80e40a04402e900020b066104070805211107801042980f0203010f0084041080340310000d0000d40d24059450241040408a804110741c7d051000e504000281256094401d6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 513219496 1250 513218246 513218261
    0x9100c081909140d11060105030606091b030106050d0b0d0b011a0d020403111207140616050a03090608010501140f030c04051203030402040c0914041a1c15050709120501 74
    0x7952011600f01040c05160340c4038026500040030403810030398800c40d100300049850481d00018000c041c00d95510041c400d64003c040c006030180c880749205640d21001c0b9002460180c01c0ca65204d5880e000172031a4401521101180da41c0076a0350380000c0380202d40c0c40c100c2c40d415103600c2081d014040009420207003940c8945850407200f5440402e02004010501c0d100c044000b00071500302c00c24405c80554203440d4142c0c0d114a00902c12007408040b49400c0c02c038007410145100c2862200c8080482e25401c0c1000404401100012000d40c0180501500400c90b01e01415081c642a4a02030380001713194854440d00d21074112980010001512503407401c3d00301c4000c0d00001e001980c201c8200c80d440c595a40041d00c049110310305021503004070798452003050007110b4688a00c3c10a0410180500008004008110207070750000e0000300c1c42d6803240d610010000c030f8980d401040b803907041c0c106401c0c1000d0227213844248900b040306201440c2c1c3d00c60584019103201c0d00004079035100d0341ca800c0d401400e44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 513220746 1250 513219496 513219503
    0x31a010c020d11030d08010e01080d080106030b03430605090111160312120207080a031503020415030b0901020909060108090703050709050f090106150e0a0305070e09100c081909 78
    0x2820117403030645038008842070498000c41d4010000d031b603d810000c0c0d261506040c054001840300801000306520982090300c0420000d422380d513064081c40221002d280d0450107000e150401d03c80c0490b001c6140c070f10028003080c1c5c00703c90030f4002c5060100040c01c600c11120441e04024054440c2d444100041c841c041080c4220700200400356568a010001100340021010208050b4040b0200b08551030086130b41040d440003520385001d4059000350300401941446120700007880201000503101c902c5001d1502a4100f98142c015146142004d02004000c10501c03250740180110f400580344d0f802c130030381c00c04802d08100c81503559487c0c0750351411045520281091261f0000094030015990200d4004c41450031003192643d5000602c134280c50303480c13040d0350400d40c010f180030220a210b070041580e441002040000019030343d0700c89a00e031645070740015000c810306005001200c08100600c2a180495074810b111044658001a104030001072180d844400d07d40d11004545071183d000042d00b560 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 513221996 1250 513220746 513220753
    0x204090507110d020f070312031d030c010b0f0d020d02060f070c0303030b01110d1d1e04200405130905160515040b0d020c01061503050601031a010c020d1103 69
    0x240144018440294002c0120351401400842800350740701040c04c0740c08202c41d41c010402e0342d16503500c01000507440b1000b082003564428000c6882c403d41400345400740300340e100551b103e940000d000c2e800c5602900c1818850014402c600300d040c0c40d607170030710b10309142c0495100100c070046001140e03042c45080e01d494401280028018100b18840c0c9070032003900d020703540030001d0fa003025006690f00407c502c0c8003152a442a81e10107106480f0700d40030101c82d0366054050500b5500c41c1c011414204003e100c02d0286800c0100c0c404280c00c2c188100740c0412802c01403240c0344007a0803803600440c8905d00400d400341058401c54080c00d800b680204080b40c0e40034044a20190410300b0032110b10196000e0350b440703000381002802100c51790340c00b51010740b09021916032030203564026010080d0312075400c605455480d48400108000700340c41f1060404020f440208003031404100045c1112030015200a840c141a0f0000c0c486036030107a80c00c40e0341541555241c40480050405190902070300440c07a40c54803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 513223246 1250 513221996 513222001
    0xb0a08061305010c030b030a12021207080d0e011506110703020a030f02030706050c2a031e0106091b031802040203090706030506091e1f0e1611070b0c0102040905 71
    0x8960110a80c0850b005000030850400401c40032010307102210081c5038140e01150741540400e03820411412540b80f0f42c0111840b18804c0720308942540c104030025035100b407000c03900500210150040c54184c0702d40c440200000211241145a40a01405408200b1400d4400804908400c0007014040c64005066000542c0d691410486000000703070202d029000d0703240c0000c0c003d40a0405e1b5082e0500c2c5d540585840c11a9100141c042686000003902210528801140c00e880a10000c40008994924649402c0c07045040b42d09441603540102100381c5080c652401c0301d08503071079800454009190116074100250214051890f024a010398401d10000c02c0c05a000341c00aa00001c5440644080c4403a640f440e08100860204503036800342c2c1450034039080031100c0c442c41c5803948948807849001d0181c80c48641e50840c410aa08034242c0480340344180304503800f8604d01d640340c03003070503150940740c8a5030f9214083e280c40d641e02c11454000e80c04a4840c0d440c00c401c2d01942c0162440401c10400c91 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 513224496 1250 513223246 513223261
    0x9030b18120705150f060d051507050903122803020702030708011e02040e0105041d07030f020112090314090604120506060910060c020603100806070f0f020705010c060b0a0806 77
    0x35400342c8002c507054401c5089901905065600390b6208042950501c0c04503030b201018400b070a20551001c540314098000e800d28610401d40c10b0300d00402c4184d91b46611035071500c0c189480c1c50b00060309404601e809000f581c5420307524900a00d03454516850140c8420000e01c000d070007034018a80001d40c140a8403e020491000551200d2039031180b80a2680300c40e04105107541c100d00c03c60043d00f0b180d102550040c407290601d500704105003440f0070300e2101400380741c43d2458104000d60b0002c41c0c05080320440308083d90b80c07000104a410140d08030402c41243c132681c020b4400041d1b50f07174040c898040811850f0340c035a9884241e40013002404050580003100c0c0c60840d4680304121007186c400c82c1c60001241c2500c01445501e400e460207520b400709408820317001c1007055000146040541110303113402042050742400068040c01190300d07501728034a00e054014041c00801c00c000c0c400c640c03024504100603a8400c1248081580042d03000030062887c102107443e04000c2e81003102144140c0d4240101c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 513225746 1250 513224496 513224533
    0x8090d031505090f160e1507050a210306060e0102060609092508191203050402190b0a0e010201020a1d3d1e03050604090b07171609030b18 61
    0x942c2d406101c040c2c40917207044103590b01104e407403001c0d41200482c1c0c00f602c0070064440c010601107000d04229481444c0c05d0340c070454401950b5842407803000720300d401c0c0d80e6580d8250064101a14003414034030a038401102c0000e5840e40000c040910601c0300201040940c0002c1c000d240c800f00402140c901c00b40462a070011091103a4032884060784600c1c2d200c01081c15150340b200030b500d544a070403074456880c011030842c06403d010708241da1040c001da641d0400ea0904000c658020020f804200383c8400036480081d02e170f20080d405650559004000c0d04480a90142400c0b91244400400c80141c074406803304070f610701464050f4011000a40d4980680400610300005c4008200e0005071410910282100d0300300020b07003091400401d42002141180c040e41109600030000b41001a40c803080340c5030740010300d0094a80d0004140c1500141c049031740c0f214040740c0d105000c0302100190500c280320060242c1003500c4040c04040589000c51080250038400d1805021108116a410201c0607440d00c40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 513226996 1250 513225746 513225751
    0xc080a020d1e0906120b030703060605030d30020f04270c20190b0a0f09050616120c080123030d0f0905190806060108090d031505090f 59
    0x11601c039800c11a842c02d0700c42800700010015640e8039500034900031060b203041e43c04840c1c45075080d4684450010302d48017000b81341c005601030107011aa10746403c1c10b043c2001c131480c500c0406c00060440c0c68400d01c0b010780c8503080c921170f500b440c41190107040aa0342c000f0301505800030b40390400080c00080c000940d10200d000401644807240c0d012021941880c00c6480310704808000c1644814000b4111411181079071100c0d01140c180c2d41100c5400300702000c131a400d17903002c0f00d410b00c1d25410f00ca42c500851184040308070048a0420000725907840340c541e1254010001e00e0309602c17002c5950041480344142403541d2031a0342e0240280004490081d29000b002d0240c03003848814000c42d02810441c82d000c0034545940a400f030641c1050100084800414201103907050000c41100022561a0810800c0c4c5096040d00020010b506103c1c83d6810326001500d56030400041c1c41c180040d000c00070030896110a03940c2000100f48a8075809400d4100c8541d01c45507001c00740c00200508980241001403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 513228246 1250 513226996 513227023
    0x3010b0c07060503090a02090606280306060e0d02040203060f09011d0a06031a060103021903020c010e01140c07050c0a030f020909070f1a0904020a09080d03020720010c080a02 77
    0x14090340d182c150448480c00b040303d441403980c0c02148940e0260601e1030100f0341044020309828944441007180d610010040d89000006500c1203000e082202d0f030510401c405001c952401601d980300b14000510204210200644100e500001240307a0360307a4100203002c0c6003030280180c00355680d101410717041860a1070020101204140015010358900e2081d50140c039030109046401a030403004024246000802ea681416401c000282030510b400c0034a50138030140c0d540c007581c0c61008060050a4406900e01001c01e0780c1800d0f5006030581c840c43d03a0170fa11144403445035850707500e542011498100e00740c20721500325807946004000d01c0000d0618070b401a00036110841652074000645665088034070076103071900c8c580b00c814031a0f421302e0358007100000c000e40441400c0c5100f0318006000c81e4010410080800c0d41070108102440c402d00284c150b01015003400c40c24104c1c00e8580035202c40b030f05100c0b49240340050852040503030194520010f4a030708006030640320814854003942d26014000c204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 513229496 1250 513228246 513228253
    0xc080403091d0403080a09050102220e10060f0311040b2d1b070302041104080601090513020f1305010b091306051e030a050607020a06050606070f1b0b03010b0c 70
    0x1261545151a0400300810140c40b2404240c1c1c480d182207905c01400b8000080359503c4142c00c1d40810030900107012000115003000107a02a02c0321401059401c0c2d900c406654503500041003141400b0302100c1c1d046030304d0360806100f48103c150040300105000e080421350311401040200303c8446070b1000c2d05585124644140c0309608443c0f81d100040c40d00d08c2e000134400810000f4407031102442d54070700961005c94080f10345154480d0300017402e95014440d91b11300c0c2c403404641080080c07c1004454010090354008021a0030400ca40070306410909034040d0055600c441e480100b40c03a138020245c4500000d041c01c000c00c3d611045000401c2d804124014810310b81018884e06420b9184100300c1211001811445400100c07007217812981c0180d000c4a0341b40c041d01c414840812400d001042c8036a40b2a805002804427500d0100100c4030050026401f0381e400327001c1032000582c01c004076140300750000491a82e288100403186000340d255007110b04880c40200001030380300b00035000781482055030000e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 513230746 1250 513229496 513229499
    0x150f1404180b07030c14040b0a080f090c09130b0a090c0b0f04050d0f02130509070f05180a18110f030118170d0c050a030b0102060601090e09010209040c08040309 71
    0x41401051081d001e019400e44038003180041e0f01035400030000404600b00120b4a109101d0041c4094100f42d104c1c5a01641c0000c180300c40c0382d07018042a900c404590031700300003803c0c03200207155241182c4954600030700c41e0758041461000c0314040000810360040300c00c191850554030800140221180840b51486400300128556010b50141c61464940406542c2092325003800c204c228582c01c3c00c103890203464204400c0158640781001c0b56a0403452401040600740005c40324a00f00d41075201000c50208200103106a5445034070309180602241405406919004400780051410b02e20200700140303c05114003c0011410141c00b40c40002c841d4403902c00600403d0600f611822401c40c130088075080340c0700c0c002a096204401035525081c0b152410110804000170032035500c0714450001c01c10108507802420390502481040e841c003840540b2090400b8030002c0d281c481b8a0240560030801c0c84001495140c0c25415134018207401041405030b200ca43c103018103c81000d903010f4001400b150700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 513231996 1250 513230746 513230771
    0x60309020102060c03071211090306040c0e10050112050612072c010f03030c080903060705091309170c0a051006030507060503070903020d02271e04050a0204150f1404 73
    0x940703108100c07d4070340040c16003a80d071140000300020000050754620070310807054592020403072903104a00c101440b440c564244001e6051180d0010f19016290743c0144050205980c05141c0c14540c0040b00360204d01600e0740c100180c0030a4100e03007002d801d4811800002100c882001400000301ca582820707841307910f0141161081c104c000d00410045000700c80003040081c8c0704400f440e08060141440390704050b1704000090030a10241d40843c0001c0f00802c0401061034542d080801d071a208201c200183c032129034888401204070104c1b9100120301043e4162034190903c90071041c0c5138440d00f55203045402d140841c0007021580010350b1544034000b80420101e02840c100e03401a842c1d80c80b4650a18a941d00300708802112900407608070303100003c0b040302418511002c1d03c5d41c40001d40502c5842c0f8040e14001101d001e442001c8500b11082c1703041c40082100030801000442e0180e80c0410442c2c1c0804400090100c1e0340c1c42991717103c405940c00a42009105002301884a0454003070016a00410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 513233246 1250 513231996 513232021
    0x907060e01030905071208130b07020a0e06010e040b030106080a20010c210302091009150302070317090a02120a1e05030d15050a030f0c17030a051806030106030902010206 75
    0x3d00040041e030024009025007440607040c040f0161041c04000d19191200910416038400703036100061340e03c0040f50b148114984031103094054080e0758080c041314503007100000e020399440c0d00a00d00860780c907020b100ca180c4080d00480d018000e00803c40d0380d50718413403510848441440721500f80b0b82203c540c2d080c1e465807150b0000c10400340c015203d4410b880840840c400c80740707901d5070400d060680c2080810095103d080074950a41515192203520914202c188240b00c500803050b0010944104140c00020b900408019007410031081c0c4141542c3c4d5540c4858070340007403124042e50180d603564844000c1d880010f2200011441441084004044804640101060b0080060058105100382d8580d00000d5010046507042043d50000b8036555401041e41c0b10010b03002030301d4045020b01c17500b00703201004004000030504512507000c61070541c001c40e031722030040803c40c03410000f002a41ca134504100c11000309003604018401c40c1d0382e595409000d4000d2085900480c003500138400019507010411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 513234496 1250 513233246 513233261
    0x12c0f0429040903020a202106102303100501030807050706020714040f140109090b100b0f160b01181410060c03020a440427050907060e0103 62
    0x5400412030200c071030351000b03091f006014140078100b000d519241c45660700e0300c8000314181d03010000d1480040b00441c9a9040440c01011303000426058401082030000f8000d02c00c403114030701003800180e1000d480010742000e480c03080c000220303801d240012061004500c001c1042c1c5209a0440c0e0800f0ba8642c001e1380c031294180304114103c030078401c00744503904050300407000c8162043e000181030b60050140950041080c1c0010740215542c5208604101441801507042502e03244040c404510b024488900e03031192400303082d0301d5600811000c4105c88602c000f0703c0d880364000002c4c0c0056864a0410007480e4108819a000741e0414000d10034440700c441c0d580c4c0c0101c0f40c0c0c0e4034140c0341ca070502200380d44032a0b000c00100e00318071510300c00d4400b00f0300a00410030f00403401e00250320080b0300f000b02c1326030104c03401283e200901d03180a04064042030800c1210708503411841c0000d48485040303040f05e8415843c6488058440c105000c0180b100e801250000983c2c60035115402c3e0701a843c4011011140031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 513235746 1250 513234496 513234503
    0x111507141e190f02070608060303190e0102010b010e0a051207080d03090b01092906090d060207020301110328090501020706060e010f0e0f150315040b06012c0f04290409 74
    0x20017403107103601c940211035110b0b0016045924044a0403c801c41c9500c171810352f400003031500894400c0f20740e4203006035a5444801d18020103064540400102d000005200f00c0c1d10590403540074000302d040a00801000b0004441614582c83c25110f018001c0e1665071400c6070711082c48400440c5040e814426040c80c07550000c02911f0401c0d01e5900d00052103243c0141d607034092418440f018045e41e823a442c0140c0584540009070302d41002c0d00c181800d64080d428a1940040140308000781100441e1580d480d01e00803110140d0241920480c5000800101101902c2540000340b2001400311541041d0304540861040c00307a00d030b0341c2c0d03481c012000d2035601405c1d0020000001040345040785180c403980110741d410451030314500c0600003a150170b84c40d00c040740808141e201000306021003451032030740c4408203090050f46d01e400060040e040c00041150741da01498225100c2001c1d4a035202201d030b0300c40f00a00304110320340c0640d58903000a42400103001d03e2070122042d4842d541002e0240c0c01c0900d03031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 513236996 1250 513235746 513235753
    0x60d1a0714040605094605220f150b030906070203090303070602030402031509070e09011503300221070305030f07031103070906111507141e190f02 65
    0x1541c004000c2d9004080810303121a00c0503080206c05011406103218031904250490140381c41030038000418000144c0c003e520500310214140140d40131045100003002d03105000003141c40007d4a80d070010184480c0c1811440e1b984000841c6540d56a002135000f140c6510441da11992344a0080742d4900c1800402901740d00284038000024480c0d402440d04644002c05440032102d1074032001c0c2a050084484c490700350b1282e031081040c0041c60400c15040407002c0020700c0148000e015840a026081c07000030038503004441c1070090030220040c18001000c050702d0003090038480c110003e64400d07801c90004010740e0400800708012800e4021251140d030306071900c1c0c5c115950900c03840342c0990300030a04014103440703c401d1018803200390000c52003010b241d1100c00300141880742c0185251584a01c140c841c0d0710080d0f94200c0c104d6081d0fa02c5500010603c0e0040580b0684541d81c1c186008144035243c0501c00c801001030641001009410b110580c035402500544042d10101c03010200d02101d0000b682 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 513238246 1250 513236996 513237007
    0x90703030e0607030203040806130b0a02090a0e0c0d0f0b01110c0a090c050d060801060e01141809120301031103160b0301060c062a0306090b06090603060d1a0714040605 74
    0x2c080c00039103c0280240162804c0c603540310340441c2005001c43d142e048004000d1b206e94100f1041c00074503600404001411810182e602c00812f0401c1c5590140c80394003400200003640b208403001c12590307182c0d01100140495407183c1314600c09850020503440c042040c00199090980000540700da01c01c400416a001030b501e02500d900040c11403003807000c01c0041c208080d070302da1400e500410005000341701c0002940d070300d050340524190006070030030050901030039a8042241d585c9654a01d240c501c0c1b40141140b502d03038168061425480d215203a01c181004030000007404518841c0c05000d01098080c0e5104901c40c0400c800b000100f0b0103007214200c010b1006020042c491990009224850a400150403074006a40040502d031200301510000c1c0a412005080b030b03044c0150002080305d91414440b4482030130004003070f03004107800d09006c0e54002c000201aaa19100c00040c001d03009803a017140c00b84c4603070207848003840c11a20480803903c1400001040a1000c0444048403aaa52a1401e01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 513239496 1250 513238246 513238249
    0x309090f0907030209010303020a03080105040e1b0a0f03050c0901051210110702130b101110021e0403030c03030c0912030c02040e10090c08060601051b010204030f0614090703030e 79
    0x2040240800704144640c0d4804001a21103010250285010341c0003000010b509240c0240381000580040d4016070502e6240703200034000180000c400741007100105455100c6902043d00d0324003603449408003c580c0c080000070b02c180404c41d545840429506080c0607a01c84091200344005040c5001041c0c0c84901c92072000403880d03001344506800205018a489200c4d000245405400e1042c0a0401d075600b007117500a1525900c0c10051518608042010703031a00704440b1b8940c1603121030401825000034480214446003454000d000a95a204949550322400c000f070150704074007811800f00f450100d05a103007a00810302202220628000d0404840c0a42e07400c403402440804c00702c1c1c22035110450510340000a00c8803500300b0492560004c0c1c10642810891500c0f80660f005010780d0304400d060000c1a43d000c000c54094205092640d41c20008841c0d84034020701c42c41e480030302419130b09490746082040e240c1084030462240704402e5450744a440800d5111040ca20008020414001132450715 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 513240746 1250 513239496 513239521
    0xc0a180f20130b18100819020a0c06020f21040b06040c02150f06010f031112060a0923090303070c02041e05010b04260d0309080c0a06050f09030909 65
    0x1649400c202e1403071199641c204540640100300c0c002c4001c501d003c4c00902504184081c00003c04507868600c0f458104494800351a0b4004022080d049030000b81c540043e80c0180403804400d580548119070b92480c88a0380301c0540c1201e0361100c2c8401505000801420780000c07601e000b41d811a1482c41c0f251907660410006040060019007903010359030941d041140c90b50301651007481840540d015524210000601801200d1004c0b000d16107040500c0949812180656800907801c0d00480219100e417400074400c84c4007588044800f80c1801d00e0504002d034003160303140510803e00003041c942c5d100e400400c0d4482c00122410702c00103891050303034230261510383c01c01426106038944840e00819202d0400c030650701c1c01d0b000b168100030001000c000041e009a81040e105202803000d8490160981e0002d07118a01b600e1028101a00c0c1c5605a041c80322a8049512000f1070008681d1b4120444c0303001d4000d0030044480603a15402c480015200d01310120494220000c01000d4410a55408164400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 513241996 1250 513240746 513240757
    0x906250503190f141f0306111207050a020c010c0503390105090c0604050102070608190c08040302150907030201180314030705060604060f050d03020c0a180f20 70
    0x69900c40030024407001001d00c80c4030740e0351550700030118094144807040ea04c100d50240c607a1881d1405410140c507841c040c00c01210907640c4c131841c04602d500010b60328058502500005008281840082c8424280c001d0003c144400f040d400351900313028189e00642c1c11403019240680301b500204410842c4c5946001c140c00c0c00306061402d1742c901d01d00034054540c068041d004000c020381d03455041c0401888200586c000300c1c407084a140d441c150a003070000b510b9030300c584540c0080c424441c0c00709605220015000c8920405032408010b0b01072652001032612200352410382c090f005440300c20354074810100030903110303046450052003941e146070b0045400703030485044c81071888548500400040c81a101c509400910000155100c440d03d00382282403000181c0450300c1140381041c01c01070800350280d0a030845a04a64036a410f0220f810181d05080d10303512180da005111040c00b04803442400400510a01c13109401c0041c0314010f6418004c0b500004030128400700300081c4090454003640042c01b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 513243246 1250 513241996 513242011
    0x60a030b03011d011a0d02030d0813060203071e030501080322031b0f1205072711040620030f0c1f0b10050a0804031b0c0305060906250503 61
    0x180e0b0440710902c50654800c0701c20f1103c45944460a207164050620010000703038004948450414200d50300181e0356080c80b1003004140001c400c0007980380c80c500d5000b07452894020106643d40e1818036001000c2003030010106103140c4424072241e0401d4400c0c41501c1c107a0300700390700071840d01044050420007604041c104543c9180d20160101c0012944880d800c105004401c000500504000100c0801401a04511200c100c942e44240104000203610750846600c4040c0c102e0303806d8200c10000340303800d10780300d84c803411810003039010050381c5100000c20403603142e50b90310449002c0c10a002c1c1140c0c402d10341882e103240c0c070620110162114110041045810000840300001400c403542240001d0303099400259540c0e9103540c283c203040041450030a500249801860004444006041403c0c0039101508001e14540445044000070b54090005d80c1c010440d000103690700d1400603a00d12040319414210700030b4902191036294400e540c01260040022000000360342d003042100d850304000d0518 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 513244496 1250 513243246 513243251
    0x612020d06200f0912030a08070e1807020606090c270111060906040318151d120f010c020d02030a0c06020409090809040b01020c0f0409020607050f070f050d02060a030b0301 76
    0x814250881030000c0c00d103094454880f40d214883c1400300405810001010b81c07070780d04104800c001c11940095219400260b44c02c10f0640250302e4804160045d81d8040d440303e0303c16858080c0b00d1203070b80000c1c1e81d9108650468502ca015a1142c0c0e091015021340c1646050b94609031496003400c01c5246030462644c0c0040c94440754071502c0355400c07032500900740c507092540c2d0003c500380403d0541c00700001c560305c2a101c00c80007865241511a505d01e1800a140004000010340175201080b006440c1e034540190040c0400d241300465902c0ba911843c4403080e004440d0301e02048545828000b08810540032007a801644c02e01c01c800310300f520201070481d8112072590b402c00002c41e511b4218462600b0b40c5009039012a103c031840c0b8280000c88900118103419588051020201980c4510221114110684022030640300300d1011411038018088014950b00a2580d15111b0080004000007181e01018440e1341daa95a03000f0310488038248200650403040c20030240c031045003c0d8020300076040c1c024000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 513245746 1250 513244496 513244541
    0x6190515030c130e100506040308310b04090f0507020607080910090b04050d1d0d0204151d0106210c0c051e07050a140907180b0d0612020d06 62
    0x702200314900b44c01c1074400b0071190003402081700d030303440d41d4401500d420b8904624243c1581c41e0003005015562101c0941d51450f1200e80300511161100ea0309981c03686101900581c4480201d00303e500940039802c6103034500342c1a118840301900616003e0f20781ca8025241d00d40718540c0440f01584000c00c0c030400e034420f00588822a2100f88510b030f100d503000700c0103444131313042510301107007068102016407040001c400240000000004030720100d4560440e113129a800c0a803010802600d20b0081c0340c600ba0410a42c001203101c0000b035030f0940e80311079140d84541c5030b80340c103404d0f140582040d2405240d00040b2914503102d0707403942e1140a1740704480c1094072612050343e9175103180410300040d1406031481c0744102850703014200711074006080219540101c55041044130180600e042110610a01692022a4400f4001c03804821400380e103260210102d1740340d0014000541c0024545640a8944640004d030507000003209040564010150395144c58a911080301a0411540d0340c02c10810700d042c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 513246996 1250 513245746 513245767
    0xf061d092a03070f0e010201020a08182803030b0109030f0204090807080d0c08160203030f070302040f080f060106030c05072004090b010806180304031202120c0606190515030c 77
    0x82c42c49888030f07030b03141071100c0c0300c3c45070081141101d80e2100e0f0540e0b0044c890712031507541100760241d0142002d05821309035000d15840c9454014402c81112141340620340408002607086012000700340261018030565000c00011694500e944c0f0000c1c0c40302d144580903000500c1d1503008607d80d00d02983d40e503130400480391105181507010b5000d691419680398541c1c0c440d10341110b174035684031900140b200381c241840f4101a44034480140210580e03c02180010540b50103581035401800e041c424035114142c488255a039a000f0700b18091100f84a00000020f40c14468003582d00c0c124116950b080c103040072079036a031450800300c01c8c0420f40c05602c6489407000f905d60f4031030f900c18240984125000303545001403860030500c01520b203000e43c00401128800092001040354222680b0442062441410b03080c22800e0800214403032151002c00600804a0700700000c070240501800c99204200c1c0c0400400383c5420005403080c0d03500104510b0300c580102c480c2002a541c0044e0a02e649841c0a00484 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 513248246 1250 513246996 513247081
    0x40519031206120c090b030a0803040213060612051b0a0c02131a0a0f06022802180a0c080103030e01110a020418031706030303220203070f061d09 64
    0x40283d402c81c22180c81000a100d190700e00e0000500c10103008022241c1d08101180c0c07a900784550140c03440c20000007003801c5407650454000c0410a0030740802515440d000f0080c02c80b0120081074000e542440c010541096102c51115628540c2100f003034075080202005031500041c140d0241e03030005a81000040c0e440c0c0ca8002c0394005010900307900070010b20b007000c00400417059000b06000d0301c8084020b001240d00015060000641c0c440c60498a00710f101e0300003901081a031000750041103460117981d03180c400200c0f85008400c0c44100780103122514404555042091001400281d40821405819400f42e04d20900c004406004e680c4100b2954021a080d03900d190010050cc59400c104070050503840310621620305d0f0810718002690038550002540c900001d03159000604007100501101c98040345d0140d092980a01621459a50b410205002c10140d204240200d03900344401e83c115200308060746015100104a2152034a504020001d0300400718100380100084d0440b010b1800c1909 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 513249496 1250 513248246 513248249
    0x4061d030301060306080312010b25030c060501150c0201050a050d0e0a0212030403030905040b060405120105060102010506010f08011703160c051903080d1e0903030b09060306040519031206 83
    0x4800640e500e524102c80103080700d045502c072a225800a201010440c007400556a04590b009090913440303003403400511107051810945601c40d458400d101004040e0420150b156023801207004000680e607404004d807203050b080c1c5d040070000c1e4640d5540030056000d180a080b5030825450003e0074101c1c0506004216040801c1c00d010550159818104500d0140c0002040003d000040c40c1004d14581c0c0c060491420380c044d080c800c2d600c070661641c0503141c0c8000d983c001c0030000c08030340744c04060080150080ca01500d80e1030065003080000b51a6502a021702c0030ac2031100e0b5a07100a40c3c3c600325100d1320030040c6000c42c0d18030b40420003c2c0e410340703111031426010950084440a010a24100030000c495940c440f5440151a40041c100302007071b60349054400301640310382d000c00d0402c185240031156020002d6010312052034001500140340d407550000d25040740903544011070b525000105961100229030003406130340f000d08981d01c844801c2d000c481581d80700741441c034050082c14000d601550240e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 513250746 1250 513249496 513249551
    0x303241903060c05040b040b090d080406110c030d0507020f030109020d211b110a03020603010906083c16090b0325060c0c1a030115050c0c090406 64
    0x400c2424024401c00b80701e01101007850703003030582c90503103403d00c08600c42c0280d2003107146022010441000c15121a0740d0040c945a003da15256a00e86651001e00058100d0381d440041e0302c0340c4140e103002c44c240041c1040c0851000c0d11501d09103002d0340e0070001d0b00c90300e00002681554880c4240070068580300c48a00341180b0500c1e40c2611030a0700d4000c59041ca4100c24003004000030b06c61600c0d201415040c1c01d0b50381135000200c0094a46a10010032603050096000940000380040002041e80300b550041c82651440001d5a00c070001030b8400300e01666214809880e5841480011403150300005c058020002441c42138461104005c0240c3c070354840e441d4080508540c480f070403c9014941440300c0f904c42d0386140c81040c129243e000e60356101580e28001c8106121f248910b68040c4500722400800903c26500c403807101020186c90000745400a110f401011b00402e10f4000105d400b0f8401e507a21441014010039441c41c110b020002a010b014100381c40030790752240300188500078070552103031a150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 513251996 1250 513250746 513250789
    0x7020604120309030503180312041b05060715090c0305060406140c121504060504061e050612040809040b03010507021f02070510050408090916030f02030702030324 72
    0xc240c01d00c0d6206889110301c103000c00d803914007000006500701050781c5c1c010307502d4400c050b803407841081c115146200c0c0b1040c18003400384503000c01041040b2503401540e90220095084501c564900611229005030710008103c48a084081c40c140f01565100c02c222900510b800100550349c0d1302c032103041120a032416510180c841407008400c1100ea80740c01d81040e0b02d1900c9a00d4982d40d80030422581d4030107001c20081000f050300350700765961381c0d400c2003000d044000c5c41000030075641c00b21311401d00c4240b0090f01900341005000146403415100707641501d07030180d00d098400c4d542e42c3e0366070316142d20039990503500550f42c40450b101500d0900c40c0c0351242906030020301040107110801002e010300380c00352064160041024100248001c1407041c1280c0384190003082686540c035028005024010506400000340c500308004440c054207113100c040f1160b00c0411003441184181000e91104864540c09a841000450805940303540340340114019600190300c481c0002d00058540100a40d0310400c100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 513253246 1250 513251996 513252001
    0x3091503050a1a10030509070b0a020a0b100305070e06130f0f11031012050a0203011b090506040b03042901060c110a12080f0d02040b0d0b0f031213080303070206 71
    0x754522862811420302c2440c0202e038007001001590803550140d1500c10107031648086500342c4410861a401740411050b49c8c3e480340302d01c280096462401050540781189220041160217024086c0c0a00b0340f0b41110240c1000c608025002c0036408010f4602500440e00d03951810b4004920300c2a04800072451002041c04618030100f03105445000e490001007580800c18000601d400d09101c9080796602c40256a8803101e904015080c115801d0002c0d4040d42010520040ea062204d100100280c03140c9a0f10002c1c1e803540b080c80042c1c040d900070782c0081102080414042214507840105014802e4105482c1000d400d400700d15103402a070002010401c402551001c000e02d600c004006654180c0711048400d291000c00c22040d15031030006000c802000076018001c80a40d411079030100e0141a0665803190f0b120103822183c0d226418104a041c40c10300e200b94249824890200403c200a001300800701c607551400c181c0d41c0c002c13869a9184140000c00284c5110203201651194540c2c1d0080c200a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 513254496 1250 513253246 513253261
    0x61b100507091502060f06100504031a011706160e0d060609020408010f0b061b0a0503190e0102030309070521061009050c1318181b090e03070206070309150305 70
    0x88070f0030300040e003590020020412031510200c0241c3d88910201c914002c8000604420303180d0740b00350380024100880505d00c1c44284900c40385154101d5030082100c2c1030340d03020018101d850704410385400e1746000c03007001d02e2050a44100f118190026004042102c03903005513403000126041a40300b041c0c455000304040003000c00c2849030121250003e8000d20100b1144d6000440074810300c0540d045c80d1007880194070101d001001003140582d8450101d90b564444503440c2c840701032900074500005623462040184952001c03098034080e8036008000c02071076003030808102410795240c100c0325400c03550f1038500b0000c05040101901075810218059045410514120b0685000501c002d421607003c024000c1a6960210b90700100d8252000c5403582d0040c6032203050181079000e41c031020a4480c10404000d1058180246c000326060202d004041c5a5408410049d14040c600003e0260070078400380015081c00802005083c0c0701c0d160602802d52510b4640b1206986c0c4000d440009640e0340030403100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 513255746 1250 513254496 513254519
    0x6070204112809030218091e0109020321070201030e1c03020909100f21152c070314121c110306060f070609022805040b061b10050709 59
    0x70058280b83c100429401d68001c640c03100f010103110344c0d0110000c00000c0b0100800d020b201184024108a1800d111070f4010340d502070000c3d400160b03c0b070300400b401080280901032400c4588004411050304102007500190000c0c002c0000c202c60328040c1c6c40d1845020604200000c1300a40c05440041e02d660001d001e201d04560014020980f000780003000340030044c0940803030b0041300e1800c1b018280e0889043c030300070003030107140360000e2107213869039031191212281340c0020702944c0302d0090040f040b01540000c1c0c40c914403409681d14107500100008c0c00802d038060504090b00140f80102d40f02c05008800c83c80880d4000c40360181664030150701e184038800f0074094600d85014100034242036080c0000003e00c18400c255148900600000f401c2081104c0ca80106040c650020503181c2e0481132609400c52000c2078100d011025410740343c0100b8546000c0c851400e500341c018000c1810031051030307201882c8200210758903400340303e2a040c40344840c0f1a4041c00e4455061030740d441d400581390403c8140c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 513256996 1250 513255746 513255817
    0x5250608011406072d08220312031a1e0102070b03071407030c0203070303030c0e0d150b190f0509010801140c09011106010b03010305060903040803090607020411 71
    0xb02e46003110008046540e0383c0d000e44001a03002960010f1040d40d4402c032860789164140e4002c800e0203168445400d205a01020300300822001c0c6644002c40c01802c40020580d66038000104180d50182403503800600c41d0303102c2d02c00d54200c002c5a01c10403100340000b0f003080785030702c2690340080c05200b60301450b564144140002403101c01801c81c11410414000b40c49481400041004420003140d2181070600c01e04080d0032658000c0d0558811986a050003800360840c0300c4203c012504229034003000c0d0800101790342d4040c1e0464014079050252450400c09049403c41d0141d20040014205030030b0a9a401e1340401404144560400d840c60003044c8008500140c1c000e5000da45441e080c00c0c084600e214081d0740c015628981a5500d22100005a07581c0314036820a01c4a407080e240081a0b032071f050001117060720700a0045a8841d91010141c07980c912803402407035025003041c0f02024850400070b01a204c528030082010405400180110305c1035008a20b00345404001018524004030f06542d4214 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 513258246 1250 513256996 513257009
    0x602070507090b030f0d0c1a040c0807060f020307060506040e061e0705120613150603091403040312030506030a06110a0314090703031110020703050a03050105060a080f040525060801 80
    0x80049a40d224181d40d0b046c0024844910801c0c0304215600205001041c400d845141a80c1041d05248131031074154000da80303641c824100d0200c0c2c0300b80141148a1031604c0303540154079100c06547c03413401420018200c1d17a042a00c40880c403411030030a0201520688014100f500b080c03a808103c4081c0c000040c10031028000b04004612003442810100c0381e0001d8242c541d43d8190000c5e4941100900d00318081caa00d44001850100c0c0c05a495040004220301480580c1264a14004400d86a1080344001090755100800c10b140c424000c1e044254003240c01025540d0f400d0541c0c030b0782d00c00d07500321981c151131010380090700c84240c9416115141d09410559440e40d218030f01300c2891541c801e018000a030610601034440d265030b8208000b400702444807503800703648480311480c025144d904a94008004203083c0400402c1604116080d40c040340050740c0c4540075030f100c1c08000040100060b0050380c02e4028009808241030b0864080c118640c229843c0c3c800203803074030354028000103060b00030780c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 513259496 1250 513258246 513258253
    0x2030103020a060c1b080c010206011703042105010203040f0b160e010c060917070b1e04230d08090d020f0c09071e0302030a0b030f1f0204030602070507090b03 70
    0x500150b29406820b10540d240c6003050006600a814507028404844140d404415140d103404030304000c020407030760710841c2d0230703000c13200c2c540d0701c0301090b0001c00038400c2c1c4d00046078414042008607109a100013900354500304000100f05289403141ca09a07403044a0507074001d500b46280d40d042084014a2650140c0c142d00c486d8441d0f10300610042036209441103c034100803400765400140100ca6011403500c580c0611620b061070300b005010100c9401c0007100f82c0e106113018002405051a40075100110400c12a4000f40380d6215650070311900310303091440c841500c0e000103180c40e032203042207200100c11040d101c104441c5006443d40c5d1070023009c8020301c803c40d00304a444120000d4002203280b40a482164286040c0d42d03090002c584e820400032000c00340205e0380d80341c00c8042e50503500440c01030704c00d40d4040c48000d0594060540e102d103444040519a40103102126600071801d2150607182e1881c08098a4141e40752255010b070380220303070192050340000340304008043c01c610410740c80880c158040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 513260746 1250 513259496 513259499
    0xc05010615081e0109050a1e09050c01180b0a0c0501020a0e040b0607050a061a031002131202090a0f02091216290c010603080711030607020319050f130602060702060604020301 77
    0x4114a400180310318a0907607251400306117140c119800c0320010303182c0c3c0340b11012401040708c030950141045034420742d094060411007038500e5120f5441e40d400002c100e45542e00a620f440117055603075100383c50010412a188401c00000b030403c1c00101492401c4d42d6945030440c0e040003c001c1181c88200c150742c4140020440c01c0700060021610700e0f10f0940040b000628000603400c01661304006441150341800746c0c02ca0004180d03c030303034050451011100c0004000c15254100b184198640c6c0802a500200040c00200003145640114403020720203400582000010404946814900c0500d01032607004003081e182140d0b06050904001e142030508492809000c0d018418010704072000412102030014244505900035040f4000540d8044074840d85c40125090070701042d41081409440b03400b410b000304040c140300105036a0039606441040c800042074400075140c2d0b52240d14030a100103418400c03040303c140d01c402950000e01c0f05030098091842c21000c000c3c10000010a40c5100b584107000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 513261996 1250 513260746 513260791
    0x602070612020f0c0307051b090c03010e090a120207031a010506030c0a2a140606060910030e030d14010e01080c0f0429040b0603040206070b06010c0501061508 70
    0x301c44040080c1640140c1da100c14100b4480140704130300d204840ba10001600c4810003800023401e44206202041c0008072800f4582007000100c0156452030440d00288011710000700443d12064000341028101d07001c4038401d595001d0801c0d1100c00700c00c0035812410040040c003400c07450510b41e91418992a46080d810500020a030b8003010380840440b52012903040380041c0500c402d40011041a140a035244106a0a01c0c0c801100c0110844084100f100e6901c440840007441c1400b07000c000f4442420441075005126490301005101810540c60b180031314811403041c4014090790003a440302042207995595400e15003030707040c5d10860306140c01d00e00411087e0000b10f035038541c0441c101c170030801c1e10344003500140142c2550903112216840741c4032581c520074958841442d080109075001c0c4080716040d0100051408101ca01940150341007198100207000e200015502010504000c80300c0d1086846060031541c41d600540c140b02030030403085078038507041000310f5802403141340e001170380b00503080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 513263246 1250 513261996 513262007
    0x180203040b0f0405152d130311010908030405011a0315010302063403020c0f06070807050f060a050a18020d11030705040c0203031006030921140d090c06020706 70
    0xb88800c030707160080400305040000500c04200101c00756a00600181420b090128000301140302e000030440d5402800e8101c141141c401da417141c076900d0048000d00140f900e00380c54004229035026869541d800c0ea80340017814034409580964000c0d0000907042850810414180c040200383c240300354498500724028500040b1001d0549905680294a4902e0f0f941540a5200380084003d0142d40810301203810406103c40d03221a18000e508a03140c40d4208000d0250a0f4001c00e10a0b070012001c1040102041e40c10f002419010300c11003c607109604100c2c001400c02c4000d542c0c00c90034946a4040c030908040d5401a880c0411842c440312300c1d481c0856000903454804148020043c00100824003102d550611030040103080181c814016001404d000039180d40c82218200c2107200c0480340815080e00c00e214001c111903000b01140c1e00d01c1c4011741a45a40c44030001100c0c00c02941c0c1c3e180c10001ea5400c8090402920b00b108080f0300b01c0118a0b1100854009030054000c6600502c0100205907011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 513264496 1250 513263246 513263251
    0x1e091e0305070b011e0603090f021f02120405010c0f0c21050f01050705090f01090e010b040e010b04030309122d120c02310501030506070206091b0f0105070c060207180203040b 77
    0x18180090148d9161a007070141c0002c0081c00781d031002150810519001c0310f01c0052000310b606909940c4101008124000c4034026805178900040080401000050400d50f10401281c040c0c00611240760b55a0040005e4500c170300c01110100b94107013004020031404201642502c2107650003031240d4170305440001c08038010703141400e00c109400d40c0c0304242e60340651005001340030034030600c40256841c0d0301c04401c103a0207842a401c0050041000056540500042c2c90550341d00daa0f610686038509000940b505008a00603114203a1060300151007020140d0b0110200924055801411440381403c010035510300c1d2000c41440000b03800900180d940548500c1d01d80300d100c141078114122035100300c4414503c548901c0549250800102c103001e00000c42600c504c0740c0c0c2c0d00701c58945c0d9071207080d29141c800304040380c01c0b0a000805000c0f00c510300084202455001031400a040c017a058451800b60341c0e00e944844096040910140001e003c00840c1c000d043c080304500b94998141076461191301300c0d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 513265746 1250 513264496 513264509
    0x60810020708070b1504330506030406091a0405010614031506190905040b100611061b210601030510050a0b090111030406110607031e091e0305070b011e 67
    0x2c4006480c002c1856072070400000c0140c0708005c1101e4040070800140b5001c9100020400300403049007051806487e4242681d03806499142903880316a0780502070400301d101251258001a9069041c81501410704e11560052001003000c03031501010701c49044003280740c14001d800c04220241481d8150740b1081d080310043d5104000718401042c1071440703a03031300e0700300100f414201002e20041c03140d81d85419000710180300707124034040c0d078990059401d203007161588680e682140c80091f0f0600081c1546150210028907441d180801c03005a41d10300070b400c1402d103003c1901d1902031011030751341442015070008802903106d14a45c100f4000418402881c0308038004030f84001160700303499100300c04144002100301c041b00d0320740740c5420b009806407482d2068000a4440c12001514060ac24094030384111110140c0021170310a030130b440800360607040c10603500001603040801040c40c03290000c0c0c903018040e0303030780c641c485071980b91524104106030b0203007030000010105980d0040c4468684c50440305c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 513266996 1250 513265746 513265763
    0x1404060f1202090d060209040e0a0b073c080f010f051302091c110d030807030c09031b0e090a052d0a290114150c1006081002070807 58
    0x703a0682000030f880340c001210b4010722055248001c0180f59005441440000c4509000c2c8201a0081c180d461951440240c5801b4481000c1032440c2d000d56290004520f08482072448281c107004200022222040016103041002e6065001c550340030041d16086203210110004551410b507a10901d0046401054410300344001c0c01200400164102c807c00a009000b00e00c52880c0c03500090160518868180c401c400d40c405040154540385002e03a080e80d515880d854210f4880b01c1c1c1c2100200768404901c4107016440c2000300104018552507500f200c80d03901c108010505200c188409541c01402c1c0c0e801071b60140510000280f03011585042070011000c520305500304120340b111b82e5102c1c6001c08056401214102d60621400ca00700740c9003060150780e07141c1446400b00e0090365a180c2407003460a0f20580055481e0207141145080c894004035811031810b00f0b0404264504181c100354440e081f80d5902c2000f003004e60b0040c01032140f4000681d03070460401105031201c1d8542d10035071000400c10607 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 513268246 1250 513266996 513267017
    0x6100b03061203040e100e070302070c0902030408090d1103010c0206090a060b06070c03050714010e0f09060102150f04050c060f191b03020703140a050705130b030f030a1404060f 78
    0xe0b01007058030014414a02c890340d10382040c0c4004007500c4a40d02480711542c0d01c0e0400106454080c2c001c46800c1580a000084150b203841102d100035000038108941000c0c003000381d2040c030342d030720380000c0f210302d02810a21064000d00420942107418816030744065400180401104080208005102c1d5802c4100401c0980c07540b4000345041c800e828008054120024012052200008000085c0e5903a07110710f03110321100c6001590804d12400c00590300081c2100114402e040900d00c42e83c110382d040c0103c40e000d801a0b40280000300c3c00322102c000440303d007403c0005000042000040414080d203155203048542c6000e0700642c8503807000ca82040f14000510f0784000d1083c5807402d03440e0076540e00a0050b0005142c02503d94142d4402614100003d95481c00180804100c56510650200007807d083d840c04040c070400c2c200c0007070034510700c0f90344840045858505000c400c214501e4030700a590348030b031102005041001030551212481000784400d000198000c559815240000d051192100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 513269496 1250 513268246 513268279
    0x7060e0f040e0c13050712020405030a021207050616110103050c0301150c0602030405030a0e0103020a020c13060b0c0706020d03020403021503060a08010f090c0b030c030417040803031806100b0306 86
    0x44080040960403201e005444e148074403566200341d0052007950f07104c00d80180310b9540d06041e40a5405002d502d42c01503100c001c0103180081d5204003031080c81c400d5a00356607940f4000f07003164100081001d0300070300344c058076020818a640c260008000034202000340c0d00380005480400d0105000f01e051410300c441c03070015540c3c01001d41c540e04030781c88a000e5542c0d00d001d00d0980d440782c100d013000c900402c000ca030903054698083c6c000d5031401c035440d90017070400024403010003000f5269860074644203030b070355203000c1060082e420003412a064010014031041e4500030b07009207854031000342181014030600c003d20050303442420f408901c188001d2000d449868a10018920020380d034403164140d0700e00342ea08241d5040b550019071855016012400341a56204006209440100c0300410b02003030400000340010101c0e8003581c007661803074684c076040a0700d805000789117500c00e48110807420f0858140f1250900c0400c02c03980d01031400d0007038910240ca05401200c00f40005002a0b201740c243e950b829030b12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 513270746 1250 513269496 513269503
    0x702120d0b030c03070506032a0c010506240f07050c0a030b0114030a1205071e060504060612110906062215140901030908040806040b0907060e0f040e 66
    0x1024040090a994101161405004180c4148028007038012504508040d00e000319040003140ca0183c9031754035654600703800208140044146070559107010380b0030049448a00302400040e03880e00700008042c180b040810030410000c2c0741d0080704854401c0d590103000c60301010303102c58590b40080c143e21035409107840e0741040503000c00940c104001135400070a02c000050007034103ca021a95900041c0410780c1416118030840070064060104181c210034102d00c110000e14906020b851100d484600d1070261006079200307040300ba10070b2a1034409000500c9660b100ba540107103592514031042d0841a5101c0301c008039007001d954030441185c80022155200c0030101c07081941c1000011079035038618520403011441b40e000d0b00280c54507407912151254001c0e192141510213031a100b900b0b090100e401180580b43c0c421781110042800d0100089164007041024042ea100e062a40198034090030624504602540040100040c829440da02781d190080c500b281801c007600c0104142050f100e03402d24 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 513271996 1250 513270746 513270763
    0xa1113030303021614010603030305090c0d021c02090c18010306031e140706110c01080106080f060103020403150507020c041a01080a0908041502070e0103031e1e05040303081f0b030702 81
    0x100f01c0c0417881c0da007826001035200c130003624070a8404000984504227250360301c3c0584841a40c10421070354440300945000c0c076029140040051102000c00310175800303d54100c20a640c0d841c07041c4c001044909424881c1800000e4403082032070100302d000c0ca10f44800030380a640075084404580131660410074003450f0300254100c0b1210200702c40040e036036410024405850090152403501510442010541c03066107028101e9080f5a9500c1072521111b00000710020040c0c0024181075003040000f000842c0b42c242d442d680c08040c2400a06440c01c040064203180f40e50130340038030451a2116094480745c0c04404000071310030a2030030142c02d82d140d00c1e40000410340c2020140603810b001c2400500301403c582002d803d0007090742925132007a55585030350f0b1159801e000c0200419554038400b074114000d40d802040d0152645080303040740c4c002c409407000c201981009100041c80006003030090507080003400b80c0003203102c060030244421340e07014001850120b0043d40c0d40b11400001060105100300701014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 513273246 1250 513271996 513272003
    0x14101409040b12160b040b03010302060a020118030e1206070801180b180717060a03080a1b0309061106060303160507030614060909010504050c01181205060a11130303030216 76
    0x42803e995450f0707055881241c10024600c004401d8404550403100d0300946084540212410b4110303404e40e404c018142d0084628070342159610383c00c4a5070030019500e0604402e0082d190810700003148000d002a1004140d0160020361010007842001d0707510410750740c11a80c10003001c803241d0b80c210514002620000003840da002641c10302854642c910842034900450080c1c0764014543c2280100403010710f800c580059020f0f12802040010176462402003050400902d07101c548103034604a00d40c100840b082c025000560700c52814042a50402503d0440b01b0900004189a21300000001c0d600d1042e00c001c03611040b050001ca00c100901000701c0405554000024080315440e08905003803500100c55191041c401c4901059420fa4180b041c80c3c0105d4000300a000d100708154015111180382d01c420302c98919443c6000501c0c2c0702180500b0b21000d21450240125040c107924140a0b01e0100105c008651402c01c2030520700ad80b500806011250f00d4107000d40c039000743c5031a2909222210750301a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 513274496 1250 513273246 513273259
    0x6090d0f110102041e060c0f02040b0418140f1b10110708060a060603020705031806040f061d090106081306060e040303020d0c090f051201110c0714101409040b 70
    0x300f912844120300344200251412901743c1581e5071801100c9007407010401908001844141501505041d0007094500742c02910105410820a80103220800300600581c0c4184407107003003144040081c00340350004c0e94000b00800140c442d0385c0c00c10503480d00c3d42103564400e0300c101500c04c00c000c0c01145101030310761f0305034241c0304d03081c2d0f441d480789849280440301c0ca0034031460040085903ea0186c42510312660308003008500702003030106900703074002d068050564800424000000d141d0301e074550703160181c03001d03564442b01e4500300d807031103008482d0034007007240300d51a50300051000e590f201d00c0055200781c41441110300d0200b02d00b0030000a0100750000b500b010105c10401c4189034050b0000c7c142140064010010751144143c04c41d848001c5000e420191500f66108001c41d11b4400703500542001c2d51000020310042d5000f11075410b0303010950800d42c03604400410402000c4c0102e409003000400d8968100c40700b9003032402171042c5100d00c00b00c1801c450201e00407900380c5950f844500e9801d000340030f9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 513275746 1250 513274496 513274499
    0x902041407080105040912030209030a1212060f0621020c061e0a0501051e0f0901170d021227100201291f14120a0e06090d0f11010204 59
    0x80c80e00a280484400d008100c0d403800000b41400e0520403540d89a8105c40c20348204101d0b00001c4019601445c8400d41c03500c122940321001c20074000c450580308556899017402e502000c080c0d1400c0d12026172154142091040c810803aa82d0050319002601e105d65004e4503076040c484200c10300074060074114140c2131081d2800c018940c81c02c02030341030303050030001c415a440d40e8031a01b041c0c0985509018441cac2003039801009150301070860041d003000040061856182c0c0500340041002114241d001131182000c2d1000d4410044040c0108266020075101030001e100444003a02010b101d4100507400c000c00d590610202e103e0200450200c078040200707010a80600b10500034083d0106a0302d204c0c5039010b829410044501c2c4114203211440c1c058a20b036044500041280c403988040b2120000340030341c090884d02c0c0280c0d1100101080344000100e40c500e420840c0c00c14044440540f550029580300f102840001d440008150304103800c1d5242404007054004001c0f10703516241048590b842d07001050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 513276996 1250 513275746 513275771
    0x30c030303051b031e0a090f0803060402070510061a041d06060d1a01030e0a1e0318030303020705070504060308031501051e03011a030f19110c0c150c0d030f090204 72
    0x14401c9000001381103060591b00c0d800750310790485842d004000c04140704520440002980b04000e942d00240080005003800c8140e200c440c100a0000c0a03060034541c0c0369401c3c4050000440310010645000c1c0f080b074105418030031008010846600c1884000102c10002402c17503031490111030300f0400b000020300050f84411804501014110301d1203010038188107604880e4607000418000c565046070b40340d60100030f2450050841ca1646009400f0010170038201d02d83d500c10503092600440c829034006030354070401d050040c20026a50025889181000001c0010034001403c2d60741000c2010b0501104448480040c0c6540c840d00c03101c1403041e410b054910301e00b0303045c5601860483d50510011255103418500100d1540b00c03c881581c1c800500301301040103107400c54040b202c4002c19103c001210108814003e441c0e0300310782c0b59003c00c1e902008601186081004142508005440354030303051091603030000352544a0154107904160303035a2805c02c0721481c5a00211790f556000b8204100d5050500da = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 513278246 1250 513276996 513277021
    0x5010f0207061a03030a02030703050708120108070e0c090f01050a0c060c110c0603010317180d0f051e100b060d0e03190f0c110f1315060504030c030303051b03 70
    0x5001241e44229005060b01d0f41c203000c41114000c0c66594003440c83d000c1076603000d0f2040c0c0c00c1400c8c00d07a444201802410403118011a00ca800707405490001c000082c80e0011043c0860780042500c201c846c0c05021809141e1601c491454400b1800d007005903c0d201e10320401c0312080da01c0c19000d400b850501c01031103422030700600301c201c0204c0640c0c03d4500000c0d010301880b01ca0301c020312000713003d02c1325005901c013061300500191052014001040311419002c4000540c111007170841590b68110103160201000020410b003c2c3c400304020f02c6013041004500700316101ca076000105110103480e007050038070325510042121307456084148100f00450391486010b43e00c3e005920300040c0c210a88400c1c180c518015210050560415070b909000c4241c240d030b50540e0440b08007417140e000314080010318420303550b855003000759100c201000101000180050308900240e41e00c44424801c00b0003060003c06c40c1e503d8258280ca81604021400b92105000400b21000204401c41c00010101c28270070b4050051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 513279496 1250 513278246 513278261
    0x1507060f05011815031205030603030d0203010914060910050103200408030c0f06130618050109031205060d0b0f150a080a2913170a0201060f060f1b05010f020706 71
    0x94004c0040040b0511502204100c5010242030800e581c1150035100d84943c0055500080103002d4a00b4520340030224001d0741c001b0303001000800d032140c2008102c1440d5008070756014104a68245040c14582404c1d8500102405001e0405840d0410b440750865000f101d00c4000e001140d180380c1d900c0d40c030b88840fa100d401842c00c811143c0140000618a104005a1180251b401c442d03c130300c00d0403aa9035030000400e5290890f0f141c100c10b0074114004241c0c00c1c414000014001d45400c8040030b4910b07004011180001d004c2c0d4440c08010140c14081002d60042c039600c088203240c1c5200c10707100c24960081e031010341c120a950140b01190040707a00d030b0012550010003881100304005040700c40302c2040303800141c00d035505410840280019120300f00441150080c0b03003d40d00112624480f4450003106500c4a80c0c3e607170150b13448400400154040c2501000103003140e10b0840c00700f44840030001d0000200140e10314218409180c0c00091000c00c2d440244000e41c5072030215940c2c10585400c0b809000035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 513280746 1250 513279496 513279539
    0x603010507031b0e0310090f0c05041b0804020a03080c0312160f0c06060e1806090a0201020a021e06041401080709050609062109010e1204051507060f0501 68
    0xc203804599a640a801611110750303040d00c1604000540d2042100c01000c0c082c0c55a40c10b05c80c00814907607018492147c42c001c3c6000d0040301d00c50a19605009c080b1f140f880e1312150095140829416195036060480c00c0f040d141490440896243c5000040c2003d0307080e00040c00c040c000040010000741d00100410304070041240d130001ca962000150fa41414110900c0b001162004c041740d012a0320606106503864420b0380001000d645650200340e04e00d0044034a841100c0c400c07901890050300412100d43e00004001c0100201c01541c0d0000352501c10301f0030001c2c0a5012040d07107420309a100c462251405c00003401c583e803201d994202c901c07928604040d255021a41000120b003819114101e401c050340c070064901403802d0382c10b0081c010594881450000c2c516140c40744c83c02c142000702d110740e00404041d400480d04800d48005070382800c0b011040c4d504001020401041643c990000c01101d107201400e9550f01ca482504010f0302908440c2e1101d100c0a00c2c0c14000700e1501461004c83d04d0780c90380c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 513281996 1250 513280746 513280751
    0x303030112120e130e010e01050411040e01091e031106090a0605060607031d03030d02120103050114010e060d210c0b0105010302040602070e09071208070303270f020423060301 77
    0x10480d4292031110450303c1d0f054102020b0380c0d081d544600190013103000424400d000090b0980d9066503242111002c0d03070301310b68002480314102c429152034094000200310b0035008004407074250341c0d00482642404085280034a640040c442810302424032440500025020780d01d43c0c3ca0541d10080c0c9402c44440112002c2d4031f0100405c04a0074044140e030405503054891844174181d444002000c00015540c840c3e0500c020401c094001c29140090006070400780c445450710350461030b1681c2074030318800420703206920480040024000b001b4919400c0035041c1e4440c1c08025541c05c4c20900e0b11100800e40c40d03400c0c421100e00c1c1c246980320100c840c88a001e5646078190741d803214011816803255100301001648a80805d200c00389000308603e41026905045070032040e03441c020241c1c642c0e00001c4c01d8640170b0001ca81c4c03400f8075405000c1d10641c0380f1845240c201d040c43c2c17030000c0c0304458607941c000b03880c02640b041100110b40b00c03640019410b12003903003040c030504103409448542001c00c0301d00b28001e50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 513283246 1250 513281996 513282023
    0x10902031b0f121803070c080601080a080d09230604030306210303110909160e0609060d1805060a0b0102010b181f0308160317220c03020303030112 65
    0x21100a40d03002c509034039069441c00b05400012541d2000c0644144e2113640d0071481e00c5140c20080004060103846020b0398800d552500c070a26080050591002c415500001100c500143d042c00440303640000800000a5500c440c0c10711a4001e940c0c0034088040e4520100c51042c0c69a000400522070352080d0b4083c0700240d00c03903806c40345158500428208000e604240c00c000280207030058520581141c694500b003821181c00506010390585e00800d810b01404940c20b000d80d404001c0e4114031100303a03046440c010320007010881d28410b1f0804030350511b03564000800c01c0d809080ac1000d140d03801400b20340f00c40c18084100d0008001e0300c160a40550320700b9143d1074003070811201d50190022003410b031140543d074203003903682e20300000003180c010742d4810103010000400b0880500300c0c0690241a00c00171051a1601900302420b02c04125044521030080199014912a44106402c9001e0310032084c0740881c41c0846a107407007031f0002035140c0000300010a0075a050005500301da80107426420081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 513284496 1250 513283246 513283291
    0x4051603080d0e010b010518030307080d051f03080a030b1210050907060e1c02011e020109020a090e060a0f060302040618060f03080f0318010507080603101401120c03050601090203 79
    0x200c11008000313005c28802e01c64441030800000c0d23440801c0c10041c0c00d491914040b40d03607850b01c0c0c0d40004800e266090380ca0040c00309080002e81d068000400d250103428130a81103450f082c0a601800107a4010161542c40040e02c54941481d05611000304038100d401550010079604040c0c0011504c0d04100d22415400003034080c170503400078441d100041c2030550314101c0c030004c0c58091b07a07050381c0070b0f41072250082a4035841031002d07010710001034242d80006250000b81c81001400f23603560740074600160510141b0150100d01043c542d4110300401000100252189070b030700060030980e031000e0f41c042d1505c6000960114820b1040ca64a0321049042101d1030721070300ba00c0604400c07800b02400300e1505201d29007061801200654101104240c0e0b54090810486c4c00c034250351044651a001900382c0d02440f032941070030408a50252070382c800c244850a0704501900d0444414420b0048541c0000c1c4050300b40100c5c10911009103420034141c409942c0c441c840840030751701c1654a41640c042c000c04030b1801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 513285746 1250 513284496 513284501
    0x30b07091e18050601030b19081203150d0318060302041502070609290c0f0d1b030503250503040c09050613090c080318090108011506050304051603080d0e01 69
    0xd0703540305800024201c0c000c4000c0801000f00a1210341807581e982c003052095580c0544c0c641030401900c4281e29440d091080345800d004100fa000c941c111418418050104010303a0701c1400c000c01902c2459101c44c8604084510300c441240b1002c0e0a19000302c0410607581c190001e0050b1521002c0f60103100303105020490f5660368034840c07400003803640542030124140c401700005400c001c200241d80119140d10b0380c0440366000032070a901c1e640c4101c428040d201418065010900e405007010102c90300c284080010350103001c800101000400000180c1c940c500510055441c03140e4078011159200c2c40c10043e04950080d502036451400c1c09400041d81229400340e14494200545600c0f0031500c00c2c400b2001a180c2c1030b004582c41203143c900852800d00c104041d180559607071003210408040e58003808103001040c1c01592441e4140a4188001541044180c044800c2850700d203582c1c0c1d455041c01e904180205841e407035202465100041886003e002512800940340400c224514040da00f2070708 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 513286996 1250 513285746 513285749
    0x70e180c0906063c180f0901090903020a05070f06020f0109110409030c1703060a0e06031c021e061b1315030b060d05150d2a030b07091e 60
    0xa02c96000c001d4400c01c111104401c40d20400c100c14180019025440b070180d85154400d0b6100710030202244174103600c07030031001a002030b0b581070b61480c2d41c1442c014042500781c80140a80c00a280d1249450810075100700030540460340c1003001da404d159210140c403404130105105180040c89010019120f58006204080166521078600b94107648100f06020160078a40016424048a4a18200811700c0c2000b00a400c42c0103040440e6039107481d50800514038416005282e00000107800c0140b10b480000355900c05540d6503c202498a1a090f0128a48103581c01200c031821007002c00c200030310f02c0015900d801648400e00e10307041070b4008582003000340031342e8401da02c5c000c84400d010450000461501d080d803100a10300850b0844d100c10105800c0c0d0700004c4664100e030390317850810a60895240040c1c1144200702c40b08141900c1548030315510002c02d103581500212111030200081358080381400055a100074641030394030f04440b001d003150040e0720a4101d0343e00c010003202c5601000c06410390 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 513288246 1250 513286996 513286999
    0x20a0e031204231201050901050702030715020d18030302070611090f0f12011d25090f06030f24110703050715110c120a1d03070e180c0906 61
    0x142818501030220b1030740300120a40a400309039030b40e9120000c2d194503013051590980704001266030b0810030301c01030071903e005080004540090180c1400601c10005104101e03010020150b25258403a107030ba8010004203500040ca009250022001c254154020b01030701405000c3c06c00c4541d01e1070050190307612500c1c069a40c00400c0003100a0286070400c131003a00c181024000b111101c0c030204c6030707070300f10ba2410b8082002800c0c056089144003500f0401c7d80040c51b41401c0c0c2c804c490110703154400311466540110492188c032082140c4545020340e11035801160400c82c0c0030035101007414184100c0002030825140602c0829952502014078042c040d0343c54120303e92645040c4164a0403246c44c0c220b035100306d81039a200400440c14901501405060891490000343d94080e40c0b64031514141c68580381c44207829007880145c00742c0b600048445011104103031720030030f8940d9a9000908050117500008110610780c818808040501c0d00045c1e0310b5030040d01181d800020380c0701008000c90089030120b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 513289496 1250 513288246 513288283
    0x61b170c0403060e0f0f25030b06060a02010b1e0f06280e0d030c0209060922080408070609050a0911040306020d020d060306020c0d1b1e050304031b050904020d0809061c020a0e03 78
    0x30380940bd00f1001441c00405510000034200503000010744192411403101d100720007101e0001509250490920181203411611586418100161348880c4400c1071620341c101c0025013000708641d405400b21102a02d0010700105460105280280c504081c40704141c0c05080900d0000d40607007890442c05000c0d250700c0440d0640210080c003150600d0880c98000c4035039107030502001403509000c0140b44040c02c12a10b130440442d05100c180600401c0b01c0d84412500c03401e000c02110603034100300444003603981041e800b69903242c480c03505a001c1c2c49800d0f00704810341e181080c000b092080940c041d022601c030000a44d928941000001c4420784440b1900c10348035086034080b00001041000c80c20010000d010788482030100a848043c2160810360054441c50100000a80c804c2510920340e00074000403114000d407402c0580214100221034035004102180c0000e0503040c0703680d182c041d1080c88241032840800c4c0c10885038020040d400969000011803ca0200c031400c41c9004100d805101c041c80c141d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 513290746 1250 513289496 513289501
    0xf110102090306012315090306060a030f0f0305040e15040c2f010908030f09010605040e0303061302040519360c0c061b170c0403060e0f0f25030b 64
    0xc62070b04626400a030351074024a0480d1095921221040100d090021b21410b4490160b0401d141c182240249a0f511842a0a0060001070380050300d0540c41c40e004021086901654901075640e40f00d5500208200d200e0301702080700e2011f0003a14002407440a85050005808000040d01e400030001024004030300b0b180010940000c6402c10031114000c0c80c0c00124501c1500d46a00401d0361090302c8400032414034004101d03a20009000d01c100900c0f056404108400d0b8034200640c481c00050300080c802c1e04c0307480801c860003440e0340595015220040003181b00e080d4840740148504441c0c03059154003080c0a01400f90907820816505945407654002e800660304009910020144040c960050055407003013900403540e5441030b82c024040c00d141c020784510510901030f14540303d41c0d1802484802e890304000e000036000c4107848c02c580d80010007007118103980035810b051640c9450b402100348140080c0311034145000412040c13440800c01d0f401517044520308070480d520714a000182000011201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 513291996 1250 513290746 513290759
    0x201f030b0a0302041b08090328090e090a0506090d0203031816060503061905010f0e0d080703030903080115020c0603220602040f050103050907090506010c050a030f11010209030601 79
    0x40154000002001c101901d0707100d60020b0100ca040760059925850285440d000702034020071100d42040c040401541020020554602d9280100d0551800000240c85407640079003d01307102c101034801406140c02d50320f0944141940c64600b19410f4441d40300e02d201180208002084103003002503603a020311300e1643d0b401e14448a0b030118200030314041c451780e040d000c102550f1800c803101401003a030311142d0b079060010420076940b25460308400000321982c410003040c0c0c0c2017110000381c4140760501e01c03030000101001580c42080000003820030240058500209030345a0b0014010382c3c843d498840003a40c0320581c9542c0003002d01e00c082c004d80e100b00741548071482e080001d1580150a60050318042107001ca204444500c403100403502550040b4050254000318004600906020b18080005181ca40d04041e501e41c100c4c440c0460860382d64020402c243d102d46954043c180e0003004641d014400ca00c0c1c014620b10040c2026400140d10000c07940382203206008035030b1191401001407400d80d00783710 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 513293246 1250 513291996 513292001
    0x12021f050609040221011b09061d2202070f020a060f0909150b0c0f0d030915051515030714040612050613150306110301030c030f03020118201f03 64
    0x40a04844845d581080010400d003401400b600c0c1c00d403007400003202814504003800c000c1064016200707001030b503001c0c540d9103041c007400c0c40f0b101070044506091010480c41034802820000f60b11819403130001030300e401404511480c0064051003070318251401c80d0380308400c81d08500821a41c10001d0085041080255180e4025480d58485030b005d03120b40343c0d9110300300a030030307444a5444025500002e803c550028000c2c8038524541c01c4900302070150708615503460405911107101e40d5400340c1d0340c03004a0a01c83d1000c080c21036012000c0d1410104c0e9401c00c04403100e50b0070446402d40041c080340e1072420002228000c3d03030300300e400d9130712403016005824000d00081c02d00100f10641040c03c1590344225254a40601e01d01100c007000c0e41c10700303c0d0039810950251001c1c0003c02c80020000c20042000030744107000301e000c880d0401604425410340f45000c030302422102c80d0b54001490011501d50a200703046542c00440000e511200c02106020340900c41421402c0040b43c075600748812101070307660b01a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 513294496 1250 513293246 513293269
    0x527031c0905030307050d06230a0906050303091201060312180803070308060f12030a1107050f060a11100203010f150215061512100e010f030b060d080712021f0506090402 75
    0x14004104189c460b500c1c8641d04401c00b5055011008507401407419040c40d119440152105050500c8598104404a5980d12417509058094079800c8100041007a0a45c801300c0555840b048120750360140700c00081840980845040882d15483c200142552001045038002d9605407100304403940e0719001c00c800301c00002c010756040a95580c100c603003810103200030f144965294940002004806a0046c40c003541500312030f0041c01810f4443c0410743c0d810040c0c0d41c1600261a204e100c00300c107501001d05140a8100c109d01050000c0004984800b403452a07400345ca0046003540601c10340b4480483e6500c251184d203c46800070340c004901182040c4087d0820141c3c81c256551400b40c5000075501140c1003103440744581c0050800a2003000041d506250040c94095681005241940c07a132071400100a0b0040d44140345a643ca08100840c00701924a069080400003000c40c60501002e91a2400002c45032a410031070090000c88170078900c215400782202411400f6665125070a003e141d4900d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 513295746 1250 513294496 513294517
    0xa0312020903011e0e0c1c0c0f090b13020304030c12170c09030c0105030118052715100b0315040225150507020c040527031c090503030705 61
    0x70402400e0945007409800780d1011158600c0782020040c1001e0b000721060380c110785d51310f46c110000b11741c900e03500d50b007100040c000e800c0c01390303e41c0352098500401000c1566000c44411416924000f8080c1215842004030102c01e80b0b00c0092a0341c070050325000c912003114005c020598406400c00403c21032400c91071001401c4c204480c621071099280b0300540001c0b10300074204c1c4000500d1300b4980c00c0900070111120001e081c01400c650601030140d03a10030071500742c05400d65490000900410b5104102c0d031041007020710708c003c4c0f01070f44a11151030340c100d1114410000e0002c0041403100c030070f4401d860121001001c0042c10750321088020440a441403903039540c0141c0070b005070b0f1038400904501022444007580704451140240c90a002c6041c2121400d2800b42e25140030400841c1e0007003a2500d2480c422a00010503603155903d020000080c605a0848210b810280c0071a003840040145030940001610b8907d09860b10045020b6800d070601c0100b1540040c0f011955050150002d8604100c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 513296996 1250 513295746 513295751
    0x120411011206121a0f0f0402010e060d1b020304050f040902031513050c03011514011e02010e0c0d0c03030c080f07060b010f0201420801020306120f0a0312 68
    0x50715039806081c1c1d50b103500521849a280c100b0f1804002c0340c2071042c040c5140007412481545816542080381010042c920040302d20202c000804680c420316104080c5c203401007442d511107403001c040300001c0c070054258030f0445400c81d0011840d1400001901c1c11903a0080c008a0141081c0c001d1101034000b000d0100d8141c41241070403031000542c80c00f558130075070200101070031800031070030010724240c0b509070341c0d03030003039140201e00003000d034152b51030340241c403040344110155800503c0120f80515103c01c030300a04040c080c1c060041158107400c514046903004080f201001d5250041020b400240c010007020321035090410000240200f01500802e401a03074003908105600c0400c1c80c07140d22a1034100c1d2119510075450304250b81000605234010707010310003003200b04020380c4000f01c0028402c0145000076031400b040c0750301000c0b42580301420500022a0f80780381d0b680d405035a0107908195500340c0b1070000c800114801c404c0c000b030300088502100b40281050706d41502e080d03402034131090010f0305268 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 513298246 1250 513296996 513297017
    0x1005071104020f072105030105060901020a02090a05011a03130308181b13140f06060d060e0106140a090e0c07050303070903030e03071a09041404080a08010b12041101 73
    0x20780e10310260400020030810340356a4021490241080465800415842d01e000750404000d80e921405886c15100c0030b59440781e070b4520105c0180e207000692140203510a210808102d078072200c0c0e0b000141240e0107051807c40c1e104180c20040d5084c0001c440217000451408201404170b4031600e05580c104802060103600760340b40f0951142400b641010740004100000001c503014242501c0040b0040c05002c400c003c0c003001a0704000c0314101c064030040240c4208004650b6561740d00d802c030740c000b140d103031803c03c0300c9599200040c44400003407040300003082c080c04080c1101d400013804c441241c041d40d92819181810310b400341083c21009880820030050512810000803401c10007540181d500781c03103207042c8901d54900102400900ca00c514000c0c0c1103110b04001c815500c400408039031a1103840c0a8440c4d010102207002031440c44c0284031080d85000c180414800b00c0030040181c05100d0ba901a11030fa2500652041031003041c13419098894588002070114050300742c960001c460501d401c59800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 513299496 1250 513298246 513298249
    0xe011b03030b0913050601140f0907050d0e06010e01210f080d0e1f060f0608041505041a100f050616080d060602010f090b0c210705090117040210050711 67
    0x8980c01c5860044c500070050303030001800342c2007140a005144520695200001440106d50240880d00400303004009440200d04c10b1030088007a40c00380c1c40002010410103903020540c079603401081c440c1018001e04140040344d038031004400c0390440c1400354280010645692346615000440e00301c00d8403002414001c520110089004140145032044001c0c00e0106902da0187d001c4182c61107404803c62800404000c2040c4405032141141d0603403d01040d913540c1c50400c030380c826100c1042c50b03010514000402c01041412480114040754402d002c0c2d2880e900e0001c003110404d554000c00001503040740c41008207180c40e20083c41c241d041004d4100e010642ca68581c24550007280f0300d03810164860030144902c503070904c43c8100a00c0d85c25014451510940c40e00d2203030708409080d00d422860005585000c401246080092003016a07281d6000f1703103850b40d00140190025400c00c1d00044281d00c001100c80103107020140a1a0000e000841010580d081a2000c0d0300c8070000301d826181c1c100c9514400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 513300746 1250 513299496 513299509
    0x7090503030f1b07080d0f03020403120906080c09180402030c030109260304171b06010906240210020a1803151407021b130213050906010e011b03030b 66
    0x80d0640700e103019458108480c0004410400e4582e806002e40c454101081281701c00540c0030100513042c285400c1d0111140e1046001e0b200342e4001419003410000d0903540725611100103000c07208650754240c42c6e5219a0b4000c0414420300d40c01a500010b00e5a007019502c4203190525007141c8002e04407000f6003c0345010038203580301842c06032000306007002502c489410445a02e01c0f10403551030860314500d840d0340d8001085080b1103000e1740f03582000c2642c0401c00b000c0d82d070b03411040b03401c18121290303907945d140803030b001e44001d009803100c40d08134030b0841001e0707003070391100c4000008180c015003101d18006c0a0f040094014038003c004018039232141c0d20781c1d681600b031050051401084071070788840c0040100c2084da155800d0414032203860b44100440c0340e1340825072a00c3c02420070034141c0350300703440000154495000b24032a9440f6100048804452030032400b407008480090700e40c0700c0c0d00d80d204001900c0c00e4000d42c10450204072403104150450703921000391803503244281400556030b02c007030000c15074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 513301996 1250 513300746 513300757
    0x30702102c090105041812020a0b010e15010f020d081b040b03090d02060105011407150507080a0605041116061404120210050c0f0d1d070303080a0902010c0b0709050303 74
    0x1500751004030521142088000c0d903002d000e00b9541031107a210070340c1221201100743c05000d0802d00a0f2010428078510074003846c4182c1e90003482200c42540c40c0d103c940402801900d40c2c110b44040b6001c41c0e22103501604481410600a4014203201e20208500340e41c4240d00420381c2c684109030001c5210450015800b5002400c107030039000c0d0f00c0c5d28250801e9894003034000c10080039584200010060340e81d0041080140e0301300d600340d20b52105910f1912007040308240181e19a400d041c913003040781a07540072340101d20817003401c1d001303100300c581e20703030a02080321910031480308461001c00c0f02c0290160712100c802483c0388640c50000f0100d40601e2428103400068404542c1e5510000903d03000c030b641000000007080711680c04011a08203012200654801d15501c0c5d031441c8404111001c0c020b440354098031032180c1140e44140403003080c2100c0398542c00140000c8022403014004256401964499904d0681d810b85601c03160200980703416a00f84002040301c400c005803140e020800380c03000e201401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 513303246 1250 513301996 513302057
    0x904180311061b0a0e2d0f040e1f0f0501060c0b0610080a1d0f0c1807120c0203091e2107030f020d06060e041101020a0515060409170a02010e0f03070210 67
    0x21081c0780180401c1082010350b00314074852401e162400d1146540840e902b407119162041d5044910384120584026201c0c0384004000e40d850038000050b5070360043c0d6111890791184d50b20000540d40c01d02048442c00c080c46e00c0400103081701000888030031155001a40c45c0c00d40c0b007070240291800b98441454180c20000c040525000b00b40c44012500b81524210708600704842040040d2400d40d000404c1c009800f0b801c1c010395900c5000f003064030b500030b0080320301c0b01c40040c00720844e032451151120450000503400d0303402040582030301240c81d04400703050344861203030401a14003e85943c1301c00392082d6840d001a41e1250b5140c0b141400101580f107072400500300ca4103050f08a00c1c0c24100007180d0220502400c0c155041010713207200048010901c10400401e40c80c007020300392201800b00e002807450312001810340c0b03840f000c070041069010001c1c1c44d030350040382d000b80102c6501b02c08250b110303034122100b0030240c1c0c020300c50780740146404254001010781078500710200d0494620111544494a4400c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 513304496 1250 513303246 513303319
    0x90519050301050711060403050f04081b1302042d15090303090b03040203100f0e10050f1012030f02150a1406030d12020904180311061b0a0e 62
    0x2004941400e029940d800615403d211082045c5c4011480d1940001000101040800114540e0518210090b1070107440c0050446036003500c414140d0016041011b03006206900b41c20a02503070350701c64002c9509640c4400b2843c00c2601007941803010080c5049071806010301c00b00c0001c0b4044e06041d180c00041401603807028500b40c5903050284c5110255000030000c06410410000940c50009101811018064001642c07485a0300640002c2002d807002032018065425000785020141e04a0780c081c5c0c6500310034002c2d80d1190011815040114403865003d15982d90506002c00d0103080d44202c1c080301c500645e440d000c0000003e41443c00100c45400b400340d17032400c803c03101030148021558030030b400b03500400d030751f40d680a00540812540e07880c10700030f0307500040c24402640301c942080c400c000c60400c07020318010306813402030302c80d03108150b050707109101d88000152110b1049400c0c0043c030341c10100052404d085050304032841d416182810780c00c8480b6010200380703004184040400d8141d4503100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 513305746 1250 513304496 513304499
    0x3020111190c060f14180102011d070609080703170a090503010c0c20130903020a050a060b1005090616060e0a2001080417031003080403060501051f0e01030507090519 73
    0x21304210003e00c000420040c4c0641c080401c81d1040701203440b08116178061440071414080101d0141104500740c2c000c01d2642080440b0100f03002540c40d0543d40c2d592102c99034240c0710030718150703906031511001c0c22110040507903554106800e0001c2c01c07400220f1610702100c80c6c0300c0340803901b03507900140500c00084001081c2c200b4040b400e000803005298041d02110a074060000150204950844049606d503030f851185041500801403a035034558130400ba1452001c0703074140304000b40f01e03680c0451f00507a88459400c036220310500c201c8040504c0101442d0901180c68030000e42411150803c0383d4040d03603140e201410400802c5040381161180f00780c0e181c0106688540303c0c0d150441c1c2c1c1018184403c0805000001d118061b400d484540c04419090301c03552901d420070280d5100d91300180200d0340010b004000d0180c1d41c0c1260341a5031040d41c103004a41002240070b07410701e1910001b103001522803d18034100350301c0fa420040d089001c0345002100c16841c0c400045092050200d0b040d42090320110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 513306996 1250 513305746 513305759
    0x9080f1c0f0213050f131103100611120d06170c10090f03060207170313050c09010e0f0a061701090203010e030f040b0a1803060905011104080703020111190c 69
    0x40c0c400c1d0001e000740103500b02500100303808030086007030090502c190003800d10f40c00b040e02e030001c0c03980c0180420003043c80013013000220613540e5131054800c2c0d80040801000491039034050000140e500107200001e01048502c4c001c43d0015801074884003034041c0e110384000889005416100d000c601130217018105955482007000300c1d007a405004241030120840b000c0203108038032f0140c00c04582c2c2004002d6607d004600d00b1032540110310000f000d0842011062080c031480303d4002070303c40d51154048840d035105030402c00c518054244550020008400000b13160700803401540d07500b204205e1b00101d0020f8903210cd89a441c810040c080007a41e42d155244019803601740101c81c4003c2440004e14a0565800802c0342188518001d05038070709400101d03240082d1240c0c0c0e00c100101001501c40c803200c2e441c1c0c500400548407444054603190309080070100a8040603003141c0c216600c180081481525640c0155100680c04c0440c0c58513020b62080c5e100400d4070103480822807842501402141c604041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 513308246 1250 513306996 513307001
    0x9160e07120203281b031d010615030e1902040c0c020303030a150b04050d03110c0312030403030f0e0304090e070e0c090307060309020f090402030a05011506020714060d09080f1c 78
    0x20051020390709040d01603103408003108421010701c04034078000c030700c80c020031f0710109800801498604045d0720f080c1d80005c11080c01c030381c030742e8001480f50780a0020100d0846507d07514064841c00c440854141d810240040c86e081d0b1042c030b041091070a00300e0b100866900003900f150421158240300c60349a407140c841c03401d00741d50320002400010380300b20b0800e406e080200c1e02c4100144001428404040c03012011a0420409401001c00050445a081c030090400d610183c106440440101e41800f016000303401160040d40c940304d15841c021400e041c078000e090702c003909000400700007030b015490004c2040c0c0302c8885001c1c0f240c0418a100399940d070003242414902921944500d00709031620441c02d005944802d0001c248000840d0303400000e487e40c0c00001e06200c0040c1c001407256213070046000452450103529000c40c1d500d038003960403195a810315055050490105168012070070072481c01d4400c0f00d0341c00980424050000d0506003d8070042e1000940d003c40000c81030b252040c03409a00104190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 513309352 1106 513308246 513308311
    0x30203040c03140a2001080708191a01090e010e15011101090b09071703190c05030c010204050307091b0806010e0303120f09160e07120203 61
    0x402c0100d503a88840304d000c42c2c1320501100f0340c022101c1ca01c150740500203c1038495504980e54050f040752403010041070b6103c078134022038048008040300d100c0d41060b00f14000007400d541e403050001510758040d079803040070600411001884201e419040e1150450101807120303603410004801683c080c800e90320010915842e00d403400c0c081c00382031041a0701810100c81621380a9031a0b000034407108100250284035070f88100924030503c198001302c2e5022516520380300451260070758a071415a800760521542e035a402180c01d20031464244040750080c07070682410441180200b2200b1a0200c10740c6110040c00300c41c500084e0f050f400b41160303440c0444020166a9254555080d40011007400c1d54070103200041000080c004040000340420b880c00c20b00030700d0084074540200010105001040902009011701714090032500d140069400b0700903144541d10b1048400c00404440c1051 = true := by decide +kernel

theorem cover : BRFrame.Cov 513129496 513309352 := by
  have h0 := BRFrame.cov_init 513129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 513129496 ≤ n) (h2 : n < 513309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
